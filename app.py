import streamlit as st
import pandas as pd
import sqlite3
import json
import os
import re
import math
import hashlib
from datetime import date, datetime, timedelta
from pathlib import Path
from io import BytesIO

try:
    from pypdf import PdfReader
except Exception:
    PdfReader = None

try:
    import plotly.express as px
except Exception:
    px = None

APP_DIR = Path(__file__).resolve().parent
DB_PATH = APP_DIR / "taxwise.db"
DOC_DIR = APP_DIR / "taxwise_documents"
DOC_DIR.mkdir(exist_ok=True)

st.set_page_config(page_title="TaxWise India", page_icon="₹", layout="wide", initial_sidebar_state="expanded")

# ----------------------------
# Tax configuration
# ----------------------------
AY_CONFIG = {
    "AY 2026-27": {
        "fy": "FY 2025-26",
        "new_slabs": [(400000,0),(800000,.05),(1200000,.10),(1600000,.15),(2000000,.20),(2400000,.25),(float("inf"),.30)],
        "old_slabs_below60": [(250000,0),(500000,.05),(1000000,.20),(float("inf"),.30)],
        "old_slabs_60_79": [(300000,0),(500000,.05),(1000000,.20),(float("inf"),.30)],
        "old_slabs_80plus": [(500000,0),(1000000,.20),(float("inf"),.30)],
        "rebate_new_limit": 1200000, "rebate_new": 60000,
        "rebate_old_limit": 500000, "rebate_old": 12500,
        "std_new": 75000, "std_old": 50000,
        "cess": .04, "ltcg_112a_exempt": 125000,
        "stcg_111a_rate": .20, "ltcg_112a_rate": .125,
        "surcharge": [(5000000,.00),(10000000,.10),(20000000,.15),(50000000,.25),(float("inf"),.25)],
        "old_surcharge": [(5000000,.00),(10000000,.10),(20000000,.15),(50000000,.25),(float("inf"),.37)],
        "special_surcharge_cap": .15,
    }
}

DISCLAIMER = "This calculator provides an estimated tax calculation based on the information entered and applicable rules for the selected Assessment Year. It is not an official Income Tax Department filing utility or a substitute for professional tax advice."

# ----------------------------
# Database
# ----------------------------
def db():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    return con

def init_db():
    con = db(); cur = con.cursor()
    cur.execute("""CREATE TABLE IF NOT EXISTS clients (
        id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, email TEXT, phone TEXT,
        pan TEXT, client_type TEXT, residential_status TEXT, created_at TEXT, notes TEXT DEFAULT ''
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS years (
        id INTEGER PRIMARY KEY AUTOINCREMENT, client_id INTEGER, ay TEXT, data TEXT, created_at TEXT,
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS activities (
        id INTEGER PRIMARY KEY AUTOINCREMENT, client_id INTEGER, activity TEXT, details TEXT, created_at TEXT,
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS tasks (
        id INTEGER PRIMARY KEY AUTOINCREMENT, client_id INTEGER, title TEXT, due_date TEXT, status TEXT, created_at TEXT,
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS documents (
        id INTEGER PRIMARY KEY AUTOINCREMENT, client_id INTEGER, ay TEXT, category TEXT, filename TEXT, path TEXT, uploaded_at TEXT,
        FOREIGN KEY(client_id) REFERENCES clients(id)
    )""")
    con.commit(); con.close()

init_db()

# ----------------------------
# Helpers
# ----------------------------
def num(x):
    try:
        if x is None or x == "": return 0.0
        return max(0.0, float(str(x).replace(",","").replace("₹","")))
    except Exception:
        return 0.0

def inr(x):
    x = int(round(max(0, float(x or 0))))
    return "₹" + format(x, ",")

def pct(x): return f"{x*100:.1f}%"

def slab_tax(income, slabs):
    income=max(0.0,income); tax=0.0; prev=0.0
    for upper, rate in slabs:
        if income <= prev: break
        taxable=min(income, upper)-prev
        if taxable>0: tax += taxable*rate
        if upper == float("inf"): break
        prev=upper
    return tax

def old_slabs(age,cfg):
    age=num(age)
    if age>=80: return cfg["old_slabs_80plus"]
    if age>=60: return cfg["old_slabs_60_79"]
    return cfg["old_slabs_below60"]

def surcharge_rate(total_income, regime, cfg):
    table=cfg["surcharge"] if regime=="New Regime" else cfg["old_surcharge"]
    r=0
    for upper, rate in table:
        if total_income<=upper: return rate
    return r

def calculate_regime(d, regime, cfg):
    salary=num(d.get("salary")); house_income=num(d.get("house_income")); business=num(d.get("business")); other=num(d.get("other"))
    stcg=num(d.get("stcg_111a")); ltcg=num(d.get("ltcg_112a")); other_cg=num(d.get("other_cg"))
    hp_interest=num(d.get("hp_interest")); hp_prelet=num(d.get("hp_prelet"))
    resident=d.get("residential_status","Resident")
    age=num(d.get("age"))
    gross_normal=salary+house_income+business+other+other_cg
    hp_loss=min(hp_interest, 0)
    # House property entered as net income before interest. Interest is deductible from house property.
    house_after_interest=house_income-hp_interest
    if regime=="New Regime":
        house_setoff=max(-200000, house_after_interest) if house_after_interest<0 else house_after_interest
        # New regime: self-occupied interest deduction not available; for simplicity only let positive HP through.
        if house_income==0:
            house_after_interest=0
        else:
            house_after_interest=max(0, house_income-hp_interest)
        gross_normal=salary+house_after_interest+business+other+other_cg
    else:
        house_after_interest=house_income-hp_interest
        gross_normal=salary+house_after_interest+business+other+other_cg
        if house_after_interest < -200000:
            gross_normal -= 200000 - abs(house_after_interest)
    std = cfg["std_new"] if regime=="New Regime" else cfg["std_old"]
    std_allowed=min(std,salary)
    deductions={}
    deductions["Standard Deduction"]=std_allowed
    if regime=="Old Regime":
        c80=num(d.get("80C")); d80=num(d.get("80D")); c1b=num(d.get("80CCD1B")); c2=num(d.get("80CCD2")); e80=num(d.get("80E")); g80=num(d.get("80G")); tta=num(d.get("80TTA")); ttb=num(d.get("80TTB")); otherded=num(d.get("other_deductions"))
        deductions["80C"]=min(c80,150000)
        max80d = 100000 if age>=60 else 75000
        deductions["80D"]=min(d80,max80d)
        deductions["80CCD(1B)"]=min(c1b,50000)
        deductions["80CCD(2)"]=c2
        deductions["80E"]=e80
        deductions["80G"]=g80
        if age>=60: deductions["80TTB"]=min(ttb,50000); deductions["80TTA"]=0
        else: deductions["80TTA"]=min(tta,10000); deductions["80TTB"]=0
        deductions["Other eligible deductions"]=otherded
    else:
        # Only selected new-regime eligible items are permitted here; do not silently apply old-regime deductions.
        deductions["80CCD(2)"]=num(d.get("80CCD2"))
        deductions["Other new-regime eligible deductions"]=num(d.get("new_regime_other_deductions"))
    total_ded=sum(deductions.values())
    normal_taxable=max(0,gross_normal-total_ded)
    special_stcg=stcg*cfg["stcg_111a_rate"]
    taxable_ltcg=max(0,ltcg-cfg["ltcg_112a_exempt"])*cfg["ltcg_112a_rate"]
    # Other capital gains are assumed slab-rate only for this estimator.
    slab=cfg["new_slabs"] if regime=="New Regime" else old_slabs(age,cfg)
    slab_base=max(0,normal_taxable)
    slab_tax_amt=slab_tax(slab_base,slab)
    rebate=0
    if resident=="Non-Resident":
        rebate=0
    elif regime=="New Regime" and normal_taxable<=cfg["rebate_new_limit"] and stcg<=0 and ltcg<=0:
        rebate=min(slab_tax_amt,cfg["rebate_new"])
    elif regime=="Old Regime" and normal_taxable<=cfg["rebate_old_limit"] and stcg<=0 and ltcg<=0:
        rebate=min(slab_tax_amt,cfg["rebate_old"])
    pre_surcharge=max(0,slab_tax_amt-rebate+special_stcg+taxable_ltcg)
    sr=surcharge_rate(normal_taxable+stcg+ltcg,regime,cfg)
    # Apply max 15% surcharge to specified special-rate tax; normal-rate tax follows regime table.
    normal_surcharge=max(0,(slab_tax_amt-rebate))*sr
    special_surcharge=(special_stcg+taxable_ltcg)*min(sr,cfg["special_surcharge_cap"])
    surcharge=normal_surcharge+special_surcharge
    cess=(pre_surcharge+surcharge)*cfg["cess"]
    total=max(0,pre_surcharge+surcharge+cess)
    tds=num(d.get("tds")); tcs=num(d.get("tcs")); advance=num(d.get("advance_tax")); self_tax=num(d.get("self_assessment"))
    credits=tds+tcs+advance+self_tax
    payable=max(0,total-credits); refund=max(0,credits-total)
    return {
        "regime":regime,"gross_total_income":max(0,gross_normal+stcg+ltcg),"normal_income":max(0,gross_normal),
        "deductions":deductions,"total_deductions":total_ded,"taxable_income":normal_taxable,
        "slab_tax":slab_tax_amt,"stcg_tax":special_stcg,"ltcg_tax":taxable_ltcg,"rebate":rebate,
        "surcharge":surcharge,"cess":cess,"tax":total,"tds":tds,"tcs":tcs,"advance_tax":advance,"self_assessment":self_tax,
        "credits":credits,"payable":payable,"refund":refund,"effective_rate":(total/max(1, max(0,gross_normal+stcg+ltcg))),
        "special_income":stcg+ltcg,"house_after_interest":house_after_interest
    }

def calculate_both(d,cfg):
    old=calculate_regime(d,"Old Regime",cfg); new=calculate_regime(d,"New Regime",cfg)
    diff=old["tax"]-new["tax"]
    return old,new,diff, ("New Regime" if diff>0 else "Old Regime" if diff<0 else "Same")

def extract_pdf_text(file_bytes):
    if not PdfReader: return "", "PDF reader dependency missing."
    try:
        reader=PdfReader(BytesIO(file_bytes))
        text="\n".join((p.extract_text() or "") for p in reader.pages)
        return text, ""
    except Exception as e:
        return "", str(e)

def money_from_text(text, patterns):
    for pat in patterns:
        m=re.search(pat,text,re.I|re.M)
        if m:
            s=m.group(1).replace(",","").replace(" ","")
            try: return float(s)
            except: pass
    return 0.0

def parse_tax_document(text, kind):
    result={"tds":0.0,"tcs":0.0,"tax_payments":0.0,"refund":0.0,"sft_hits":0,"rows":[]}
    if not text: return result
    result["tds"]=money_from_text(text,[r"total\s+(?:tax\s+)?deducted[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)",r"tax\s+deducted[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)"])
    result["tcs"]=money_from_text(text,[r"total\s+(?:tax\s+)?collected[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)",r"tax\s+collected[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)"])
    result["tax_payments"]=money_from_text(text,[r"tax\s+payments?[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)",r"advance\s+tax[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)"])
    result["refund"]=money_from_text(text,[r"refund[^\d₹]*₹?\s*([\d,]+(?:\.\d+)?)"])
    result["sft_hits"]=len(re.findall(r"SFT|Statement of Financial Transaction",text,re.I))
    # Capture lines that look like TDS/TCS/payment/SFT entries for review.
    for line in text.splitlines():
        if re.search(r"TDS|TCS|SFT|interest|dividend|salary|rent|payment|refund",line,re.I) and re.search(r"\d",line):
            result["rows"].append(line.strip()[:250])
    return result

def add_activity(client_id, activity, details=""):
    con=db(); con.execute("INSERT INTO activities(client_id,activity,details,created_at) VALUES(?,?,?,?)",(client_id,activity,details,datetime.now().isoformat(timespec="seconds"))); con.commit(); con.close()

def save_year(client_id, ay, data):
    con=db(); con.execute("INSERT INTO years(client_id,ay,data,created_at) VALUES(?,?,?,?)",(client_id,ay,json.dumps(data),datetime.now().isoformat(timespec="seconds"))); con.commit(); con.close()

def get_clients():
    con=db(); rows=con.execute("SELECT * FROM clients ORDER BY name").fetchall(); con.close(); return rows

def get_years(client_id):
    con=db(); rows=con.execute("SELECT * FROM years WHERE client_id=? ORDER BY id DESC",(client_id,)).fetchall(); con.close(); return rows

def query_count(sql,args=()):
    con=db(); v=con.execute(sql,args).fetchone()[0]; con.close(); return v

def make_token(client_id):
    return hashlib.sha256(f"{client_id}-{APP_DIR}-{DB_PATH}".encode()).hexdigest()[:16]

def format_activity(rows):
    return [{"Date":r["created_at"],"Activity":r["activity"],"Details":r["details"]} for r in rows]

# ----------------------------
# CSS / UI
# ----------------------------
st.markdown("""
<style>
@import url('https://fonts.googleapis.com/css2?family=DM+Sans:wght@400;500;600;700&family=Manrope:wght@600;700;800&display=swap');
html,body,[class*="css"]{font-family:'DM Sans',sans-serif}
[data-testid="stAppViewContainer"]{background:#f6f8fb}
[data-testid="stSidebar"]{background:linear-gradient(180deg,#0d1b2a 0%,#13283c 100%);color:white}
[data-testid="stSidebar"] *{color:#eaf2f8!important}
.hero{background:linear-gradient(135deg,#0d1b2a 0%,#174a63 55%,#0f766e 100%);padding:42px;border-radius:28px;color:white;box-shadow:0 20px 50px rgba(13,27,42,.18);margin-bottom:25px}
.hero h1{font-family:'Manrope';font-size:44px;line-height:1.05;margin:0 0 12px}.hero p{font-size:18px;opacity:.9;max-width:760px}
.card{background:white;border:1px solid #e8edf2;border-radius:20px;padding:22px;box-shadow:0 8px 30px rgba(13,27,42,.06);margin-bottom:16px}
.kpi{background:white;border:1px solid #e8edf2;border-radius:18px;padding:18px;box-shadow:0 8px 24px rgba(13,27,42,.05)}
.kpi .label{font-size:13px;color:#6b7280}.kpi .value{font-size:27px;font-weight:800;color:#102a43;margin-top:6px}
.badge{display:inline-block;padding:6px 10px;border-radius:999px;background:#e7f7f4;color:#0f766e;font-weight:700;font-size:12px}
.small{font-size:13px;color:#6b7280}.section-title{font-family:'Manrope';font-size:24px;font-weight:800;color:#102a43;margin:8px 0 12px}
div.stButton>button{border-radius:12px;font-weight:700;min-height:42px}
[data-testid="stMetric"]{background:white;border:1px solid #e8edf2;padding:14px;border-radius:16px}
hr{border-color:#e5eaf0}
</style>
""", unsafe_allow_html=True)

# ----------------------------
# Sidebar / mode
# ----------------------------
if "page" not in st.session_state: st.session_state.page="Home"
if "quick_done" not in st.session_state: st.session_state.quick_done=False
if "last_calc" not in st.session_state: st.session_state.last_calc=None
if "client_id" not in st.session_state: st.session_state.client_id=None
if "ca_authenticated" not in st.session_state: st.session_state.ca_authenticated=False

with st.sidebar:
    st.markdown("## TAXWISE INDIA")
    st.caption("Tax Intelligence • CA Advisory • Client Workspace")
    page=st.radio("Navigate",["Home","Quick Tax","Tax Plan","Business / Professional","AIS / 26AS","Tax Opportunities","CA Practice","Client Workspace","Reports & History","Settings"],index=["Home","Quick Tax","Tax Plan","Business / Professional","AIS / 26AS","Tax Opportunities","CA Practice","Client Workspace","Reports & History","Settings"].index(st.session_state.page))
    st.session_state.page=page
    st.divider()
    st.markdown("**Current AY**")
    ay=st.selectbox("Assessment Year",list(AY_CONFIG.keys()),label_visibility="collapsed")
    st.caption(AY_CONFIG[ay]["fy"])
    st.divider()
    st.caption("Local-first demo workspace. For production, connect a secure database/authentication service.")

cfg=AY_CONFIG[ay]
CA_PIN=os.environ.get("TAXWISE_CA_PIN", "2468")

# ----------------------------
# Home
# ----------------------------
if page=="Home":
    st.markdown("""
    <div class='hero'>
      <div class='badge'>TAX INTELLIGENCE PLATFORM</div>
      <h1>Your Tax. Clearly.</h1>
      <p>Understand. Compare. Plan. A premium tax calculator plus client advisory workspace for taxpayers and CA practices.</p>
    </div>
    """,unsafe_allow_html=True)
    c1,c2,c3=st.columns(3)
    with c1:
        st.markdown("<div class='card'><h3>⚡ Quick Tax</h3><p>Get an Old vs New tax snapshot in minutes, with a clear explanation of the result.</p></div>",unsafe_allow_html=True)
        if st.button("Start Quick Tax →",use_container_width=True): st.session_state.page="Quick Tax"; st.rerun()
    with c2:
        st.markdown("<div class='card'><h3>🧠 Full Tax Plan</h3><p>Income, deductions, capital gains, TDS, tax opportunities and a detailed computation trail.</p></div>",unsafe_allow_html=True)
        if st.button("Open Tax Plan →",use_container_width=True): st.session_state.page="Tax Plan"; st.rerun()
    with c3:
        st.markdown("<div class='card'><h3>👩‍💼 CA Practice</h3><p>Clients, FY-wise records, documents, tasks, tax health, timelines and review alerts.</p></div>",unsafe_allow_html=True)
        if st.button("Open CA Workspace →",use_container_width=True): st.session_state.page="CA Practice"; st.rerun()
    st.markdown("### What this version includes")
    cols=st.columns(5)
    items=[("📊","Tax Snapshot"),("🏢","44AD / 44ADA"),("📥","AIS / 26AS Import"),("🔎","TDS Reconciliation"),("🗂️","Client Workspace")]
    for col,(ic,txt) in zip(cols,items):
        with col: st.markdown(f"<div class='kpi'><div style='font-size:25px'>{ic}</div><b>{txt}</b></div>",unsafe_allow_html=True)
    st.info("AIS/26AS portal credentials are never requested. The official portal requires authenticated access; this app therefore uses the safe alternative: download from the portal and import the file/PDF/text here.")

# ----------------------------
# Quick Tax
# ----------------------------
elif page=="Quick Tax":
    st.markdown("<div class='section-title'>Quick Tax</div><p class='small'>Quick answer first. Depth second.</p>",unsafe_allow_html=True)
    with st.form("quick"):
        c1,c2,c3=st.columns(3)
        with c1: taxpayer=st.selectbox("I am a",["Salaried","Business Owner","Consultant / Freelancer","Investor","Other"])
        with c2: age=st.number_input("Age",18,120,35)
        with c3: residential=st.selectbox("Residential Status",["Resident","Non-Resident","RNOR"])
        c1,c2,c3=st.columns(3)
        with c1: salary=st.number_input("Annual Salary / Pension",0.0,100000000.0,1200000.0,step=50000.0)
        with c2: other=st.number_input("Other Income",0.0,100000000.0,0.0,step=10000.0)
        with c3: business=st.number_input("Business / Professional Income",0.0,100000000.0,0.0,step=10000.0)
        submitted=st.form_submit_button("Compare Tax →",use_container_width=True)
    if submitted:
        d={"salary":salary,"other":other,"business":business,"age":age,"residential_status":residential}
        old,new,diff,rec=calculate_both(d,cfg)
        st.session_state.last_calc={"data":d,"old":old,"new":new,"diff":diff,"rec":rec,"ay":ay}
    if st.session_state.last_calc:
        r=st.session_state.last_calc
        old,new,diff,rec=r["old"],r["new"],r["diff"],r["rec"]
        st.markdown("### Your Tax Snapshot")
        a,b,c=st.columns(3)
        with a: st.metric("Old Regime Tax",inr(old["tax"]))
        with b: st.metric("New Regime Tax",inr(new["tax"]))
        with c: st.metric("Potential Saving",inr(abs(diff)),delta=("New Regime" if diff>0 else "Old Regime" if diff<0 else "Same"))
        st.success(f"Recommended based on current inputs: **{rec}**")
        with st.expander("Why did the app recommend this?"):
            st.write(f"Old regime estimated tax: {inr(old['tax'])}. New regime estimated tax: {inr(new['tax'])}.")
            st.write("The recommendation is purely computational and should be reviewed for deductions, exemptions, special-rate income and other facts before filing.")
        if st.button("Continue to Full Tax Plan →",use_container_width=True): st.session_state.page="Tax Plan"; st.rerun()

# ----------------------------
# Tax Plan
# ----------------------------
elif page=="Tax Plan":
    st.markdown("<div class='section-title'>Full Tax Plan</div><p class='small'>Build the complete tax position without forcing every user through every module.</p>",unsafe_allow_html=True)
    with st.form("taxplan"):
        st.markdown("#### 01 • Personal & Income")
        c1,c2,c3=st.columns(3)
        with c1: name=st.text_input("Name")
        with c2: age=st.number_input("Age",18,120,35)
        with c3: residential=st.selectbox("Residential Status",["Resident","Non-Resident","RNOR"])
        c1,c2,c3=st.columns(3)
        with c1: salary=st.number_input("Salary / Pension",0.0,100000000.0,1200000.0,step=25000.0)
        with c2: other=st.number_input("Other Sources",0.0,100000000.0,0.0,step=10000.0)
        with c3: tds=st.number_input("TDS",0.0,100000000.0,0.0,step=5000.0)
        c1,c2=st.columns(2)
        with c1: tcs=st.number_input("TCS",0.0,100000000.0,0.0,step=5000.0)
        with c2: advance=st.number_input("Advance Tax",0.0,100000000.0,0.0,step=5000.0)
        st.markdown("#### 02 • House Property")
        hp=st.toggle("I have House Property income / loss")
        hp_income=hp_interest=0.0
        if hp:
            c1,c2=st.columns(2)
            with c1: hp_income=st.number_input("Net annual value / house property income before interest",0.0,100000000.0,0.0,step=10000.0)
            with c2: hp_interest=st.number_input("Interest on housing loan",0.0,100000000.0,0.0,step=10000.0)
        st.markdown("#### 03 • Business / Profession")
        biz=st.toggle("I have Business / Professional income")
        business=0.0
        if biz:
            business=st.number_input("Net Business / Professional Income",0.0,100000000.0,0.0,step=10000.0)
        st.markdown("#### 04 • Capital Gains")
        cg=st.toggle("I have Capital Gains")
        stcg=ltcg=other_cg=0.0
        if cg:
            c1,c2,c3=st.columns(3)
            with c1: stcg=st.number_input("STCG u/s 111A",0.0,100000000.0,0.0,step=10000.0)
            with c2: ltcg=st.number_input("LTCG u/s 112A",0.0,100000000.0,0.0,step=10000.0)
            with c3: other_cg=st.number_input("Other Capital Gains (estimator)",0.0,100000000.0,0.0,step=10000.0)
        st.markdown("#### 05 • Deductions")
        c1,c2,c3=st.columns(3)
        with c1:
            d80c=st.number_input("80C",0.0,150000.0,0.0,step=5000.0)
            d80d=st.number_input("80D",0.0,100000.0,0.0,step=5000.0)
            d1b=st.number_input("80CCD(1B)",0.0,50000.0,0.0,step=5000.0)
        with c2:
            d2=st.number_input("80CCD(2)",0.0,10000000.0,0.0,step=5000.0)
            d80e=st.number_input("80E",0.0,10000000.0,0.0,step=5000.0)
            d80g=st.number_input("80G",0.0,10000000.0,0.0,step=5000.0)
        with c3:
            dtta=st.number_input("80TTA",0.0,10000.0,0.0,step=1000.0)
            dttb=st.number_input("80TTB",0.0,50000.0,0.0,step=1000.0)
            otherded=st.number_input("Other eligible deductions",0.0,100000000.0,0.0,step=5000.0)
        newded=st.number_input("New-regime eligible employer NPS / other eligible deduction",0.0,10000000.0,0.0,step=5000.0)
        st.markdown("#### 06 • Tax Regime")
        regime_choice=st.selectbox("Tax Regime",["Old Regime","New Regime","Old vs New Comparison"])
        submit=st.form_submit_button("Calculate Full Tax Plan",use_container_width=True)
    if submit:
        d={"salary":salary,"other":other,"business":business,"age":age,"residential_status":residential,"tds":tds,"tcs":tcs,"advance_tax":advance,"hp_income":hp_income,"hp_interest":hp_interest,"stcg_111a":stcg,"ltcg_112a":ltcg,"other_cg":other_cg,"80C":d80c,"80D":d80d,"80CCD1B":d1b,"80CCD2":d2,"80E":d80e,"80G":d80g,"80TTA":dtta,"80TTB":dttb,"other_deductions":otherded,"new_regime_other_deductions":newded}
        old,new,diff,rec=calculate_both(d,cfg)
        st.session_state.last_calc={"data":d,"old":old,"new":new,"diff":diff,"rec":rec,"ay":ay,"name":name,"regime":regime_choice}
    if st.session_state.last_calc:
        r=st.session_state.last_calc; old,new=r["old"],r["new"]; diff=r["diff"]
        st.markdown("### Tax Dashboard")
        cols=st.columns(5)
        vals=[("Gross Total Income",max(old["gross_total_income"],new["gross_total_income"])),("Old Regime Tax",old["tax"]),("New Regime Tax",new["tax"]),("Tax Saving",abs(diff)),("TDS / Credits",new["credits"])]
        for c,(lab,val) in zip(cols,vals): c.metric(lab,inr(val))
        st.success(f"Recommended regime: **{r['rec']}**")
        c1,c2=st.columns(2)
        with c1:
            st.markdown("#### Old Regime")
            st.write({"Taxable income":inr(old["taxable_income"]),"Deductions":inr(old["total_deductions"]),"Tax":inr(old["tax"]),"Payable":inr(old["payable"]),"Refund":inr(old["refund"])})
        with c2:
            st.markdown("#### New Regime")
            st.write({"Taxable income":inr(new["taxable_income"]),"Deductions":inr(new["total_deductions"]),"Tax":inr(new["tax"]),"Payable":inr(new["payable"]),"Refund":inr(new["refund"])})
        with st.expander("Detailed computation"):
            selected=old if r.get("regime")=="Old Regime" else new if r.get("regime")=="New Regime" else new
            df=pd.DataFrame({"Component":["Normal taxable income","Standard deduction / eligible deductions","Slab tax","STCG u/s 111A tax","LTCG u/s 112A tax after exemption","87A rebate","Surcharge","Health & Education Cess","Final tax","TDS + TCS + Advance tax","Tax payable","Refund"],"Amount":[selected["taxable_income"],selected["total_deductions"],selected["slab_tax"],selected["stcg_tax"],selected["ltcg_tax"],selected["rebate"],selected["surcharge"],selected["cess"],selected["tax"],selected["credits"],selected["payable"],selected["refund"]]})
            df["Amount"]=df["Amount"].map(inr); st.dataframe(df,use_container_width=True,hide_index=True)
        if st.button("Save this tax computation to client workspace"):
            clients=get_clients()
            if clients:
                cid=st.selectbox("Choose client",[f"{c['id']} — {c['name']}" for c in clients],key="save_client").split(" — ")[0]
                save_year(int(cid),ay,r["data"]|{"old_tax":old["tax"],"new_tax":new["tax"],"recommended":r["rec"]})
                add_activity(int(cid),"Tax computation saved",ay)
                st.success("Saved to client history.")
            else: st.warning("Create a client first in CA Practice.")

# ----------------------------
# Business / Professional
# ----------------------------
elif page=="Business / Professional":
    st.markdown("<div class='section-title'>Business & Professional Tax Engine</div><p class='small'>A decision-oriented workflow for regular vs presumptive taxation.</p>",unsafe_allow_html=True)
    typ=st.selectbox("I am",["Business Owner","Consultant / Freelancer"])
    c1,c2=st.columns(2)
    with c1: structure=st.selectbox("Business structure",["Proprietorship","Partnership / LLP","Company","Other"])
    with c2: method=st.selectbox("Taxation approach",["Compare regular vs presumptive","Regular taxation","Presumptive taxation"])
    receipts=st.number_input("Annual gross receipts / professional receipts",0.0,100000000.0,3200000.0,step=50000.0)
    cash_share=st.slider("Approx. cash / non-electronic receipts share",0,100,10)
    expenses=st.number_input("Actual business expenses (regular method)",0.0,100000000.0,1000000.0,step=25000.0)
    tds=st.number_input("TDS on business/professional receipts",0.0,100000000.0,0.0,step=5000.0)
    foreign=st.toggle("Foreign clients / foreign receipts")
    st.info("Presumptive eligibility depends on facts and statutory conditions. This tool is an estimator and flags the option for CA review; it does not certify eligibility.")
    if typ=="Business Owner":
        presumptive=max(receipts*.06, receipts*.08 if cash_share>5 else receipts*.06)
        section="44AD"
    else:
        presumptive=receipts*.50
        section="44ADA"
    regular=max(0,receipts-expenses)
    c1,c2,c3=st.columns(3)
    c1.metric("Regular estimated income",inr(regular)); c2.metric(f"{section} estimated income",inr(presumptive)); c3.metric("Difference",inr(abs(regular-presumptive)))
    if presumptive<regular: st.success(f"Presumptive route may produce lower estimated taxable business income by {inr(regular-presumptive)} — review eligibility with your CA.")
    else: st.info("Regular method currently produces lower estimated business income based on your inputs. Keep supporting expense records.")
    st.markdown("### Tax structure")
    flow=pd.DataFrame({"Stage":["Gross receipts","Estimated taxable business income","TDS credit"],"Amount":[receipts,min(regular,presumptive) if method.startswith("Compare") else (regular if method=="Regular taxation" else presumptive),tds]})
    st.dataframe(flow.assign(Amount=flow.Amount.map(inr)),use_container_width=True,hide_index=True)
    if foreign: st.warning("Foreign receipts can trigger additional reporting / foreign tax credit considerations. Treat this as a review flag, not a tax conclusion.")

# ----------------------------
# AIS / 26AS
# ----------------------------
elif page=="AIS / 26AS":
    st.markdown("<div class='section-title'>AIS / 26AS Import & Reconciliation</div>",unsafe_allow_html=True)
    st.info("The Income Tax Department requires authenticated access to AIS/26AS. This app intentionally does not collect your e-filing password, OTP or PAN password. Use the official portal to download the information, then upload/paste it here.")
    st.markdown("**Official access path:** e-Filing login → AIS, and e-File → Income Tax Return → View Form 26AS. citeturn0search1turn0search12")
    c1,c2=st.columns(2)
    with c1:
        st.markdown("### AIS")
        ais_file=st.file_uploader("Upload AIS PDF",type=["pdf"],key="aispdf")
        ais_text=st.text_area("Or paste AIS text",height=180,key="aistext")
    with c2:
        st.markdown("### Form 26AS")
        f26=st.file_uploader("Upload 26AS PDF",type=["pdf"],key="26aspdf")
        f26_text=st.text_area("Or paste 26AS text",height=180,key="26astext")
    if st.button("Analyse & Reconcile",use_container_width=True):
        parsed={}
        for kind,file_obj,text in [("AIS",ais_file,ais_text),("26AS",f26,f26_text)]:
            raw=text or ""
            if file_obj:
                raw,err=extract_pdf_text(file_obj.getvalue())
                if err: st.warning(f"{kind} PDF extraction issue: {err}. Try copy/paste text or an unlocked PDF.")
            parsed[kind]=parse_tax_document(raw,kind)
        st.session_state["tax_docs"]=parsed
    if "tax_docs" in st.session_state:
        p=st.session_state["tax_docs"]
        cols=st.columns(4)
        for c,label,key in [(cols[0],"AIS TDS","AIS"),(cols[1],"26AS TDS","26AS"),(cols[2],"AIS SFT hits","AIS"),(cols[3],"AIS tax payments","AIS")]:
            val=p[key]["tds"] if label.endswith("TDS") else p[key]["sft_hits"] if "SFT" in label else p[key]["tax_payments"]
            c.metric(label,inr(val) if "TDS" in label or "payments" in label else str(val))
        entered_tds=st.number_input("TDS as per your computation",0.0,100000000.0,0.0,step=5000.0)
        ais_tds=p["AIS"]["tds"]; f26_tds=p["26AS"]["tds"]
        comparison=pd.DataFrame({"Source":["Your entry","AIS extracted","26AS extracted"],"TDS":[entered_tds,ais_tds,f26_tds]})
        st.dataframe(comparison.assign(TDS=comparison.TDS.map(inr)),use_container_width=True,hide_index=True)
        base=entered_tds
        reference=f26_tds or ais_tds
        difference=base-reference
        if reference and abs(difference)>1: st.error(f"⚠ TDS mismatch detected: {inr(abs(difference))}. Review deductor entries / AIS / 26AS before filing.")
        elif reference: st.success("No material TDS difference detected in the extracted summary.")
        st.markdown("### Review lines")
        rows=[]
        for kind in ["AIS","26AS"]:
            rows += [{"Source":kind,"Line":x} for x in p[kind]["rows"][:100]]
        st.dataframe(pd.DataFrame(rows),use_container_width=True,hide_index=True)
        st.caption("PDF extraction is heuristic. For filing-grade reconciliation, review the source statements and use the detailed transaction-level data.")

# ----------------------------
# Opportunities
# ----------------------------
elif page=="Tax Opportunities":
    st.markdown("<div class='section-title'>Tax Opportunities</div><p class='small'>Review opportunities, not guaranteed tax savings.</p>",unsafe_allow_html=True)
    if not st.session_state.last_calc:
        st.info("Run Quick Tax or Full Tax Plan first to populate opportunity cards.")
    else:
        r=st.session_state.last_calc; old,new=r["old"],r["new"]
        cards=[]
        diff=abs(old["tax"]-new["tax"])
        if diff>0: cards.append(("01","Regime comparison",f"Estimated difference: {inr(diff)}","Review deductions, special income and eligibility before choosing."))
        cards.append(("02","AIS / 26AS reconciliation","Check TDS/TCS consistency","Import AIS/26AS and reconcile credits."))
        cards.append(("03","Business taxation review","44AD / 44ADA","Compare presumptive and regular methods where applicable."))
        cards.append(("04","Deduction review","80C / 80D / NPS / education / donation","Review eligible deductions under the chosen regime."))
        cards.append(("05","Advance tax position","Avoid last-minute balance","Compare estimated final liability with TDS/advance tax."))
        for no,title,headline,body in cards:
            st.markdown(f"<div class='card'><div class='badge'>{no}</div><h3>{title}</h3><b>{headline}</b><p class='small'>{body}</p></div>",unsafe_allow_html=True)

# ----------------------------
# CA Practice
# ----------------------------
elif page=="CA Practice":
    st.markdown("<div class='section-title'>CA Practice Dashboard</div><p class='small'>Your practice cockpit: clients, attention items, tasks and tax health.</p>",unsafe_allow_html=True)
    clients=get_clients(); total=len(clients); pending=query_count("SELECT COUNT(*) FROM tasks WHERE status!='Completed'"); urgent=query_count("SELECT COUNT(*) FROM tasks WHERE status!='Completed' AND due_date<=?",((date.today()+timedelta(days=7)).isoformat(),))
    c1,c2,c3,c4=st.columns(4)
    c1.metric("Clients",total); c2.metric("Pending Tasks",pending); c3.metric("Due ≤ 7 days",urgent); c4.metric("Tax Computations",query_count("SELECT COUNT(*) FROM years"))
    st.markdown("### Create client")
    with st.form("newclient"):
        c1,c2,c3=st.columns(3)
        with c1: cname=st.text_input("Client name")
        with c2: email=st.text_input("Email")
        with c3: phone=st.text_input("Phone")
        c1,c2,c3=st.columns(3)
        with c1: pan=st.text_input("PAN")
        with c2: ctype=st.selectbox("Client type",["Individual","Business","Professional","Investor","Other"])
        with c3: cstatus=st.selectbox("Residential status",["Resident","Non-Resident","RNOR"])
        create=st.form_submit_button("Create Client")
    if create and cname.strip():
        con=db(); cur=con.execute("INSERT INTO clients(name,email,phone,pan,client_type,residential_status,created_at) VALUES(?,?,?,?,?,?,?)",(cname,email,phone,pan.upper(),ctype,cstatus,datetime.now().isoformat(timespec="seconds"))); cid=cur.lastrowid; con.commit(); con.close(); add_activity(cid,"Client created",ctype); st.success(f"Client {cname} created."); st.rerun()
    st.markdown("### Client attention")
    if clients:
        data=[]
        for c in clients:
            yrs=get_years(c["id"]); latest=json.loads(yrs[0]["data"]) if yrs else {}
            tax=max(num(latest.get("old_tax")),num(latest.get("new_tax"))) if latest else 0
            data.append({"Client":c["name"],"Type":c["client_type"],"Latest AY":yrs[0]["ay"] if yrs else "—","Estimated Tax":inr(tax),"Workspace":"Open"})
        st.dataframe(pd.DataFrame(data),use_container_width=True,hide_index=True)
    else: st.info("No clients yet. Create your first client above.")

# ----------------------------
# Client Workspace
# ----------------------------
elif page=="Client Workspace":
    st.markdown("<div class='section-title'>Client Workspace</div>",unsafe_allow_html=True)
    clients=get_clients()
    if not clients:
        st.warning("Create a client in CA Practice first.")
    else:
        options={f"{c['id']} — {c['name']}":c for c in clients}
        chosen=st.selectbox("Select client",list(options.keys()))
        c=options[chosen]; cid=c["id"]; st.session_state.client_id=cid
        yrs=get_years(cid)
        latest=json.loads(yrs[0]["data"]) if yrs else {}
        tax=max(num(latest.get("old_tax")),num(latest.get("new_tax"))) if latest else 0
        credits=num(latest.get("tds"))+num(latest.get("tcs"))+num(latest.get("advance_tax")) if latest else 0
        health=100
        if not yrs: health-=35
        if not latest.get("tds") and latest: health-=10
        st.markdown(f"### {c['name']} <span class='badge'>{c['client_type']}</span>",unsafe_allow_html=True)
        k1,k2,k3,k4=st.columns(4); k1.metric("Tax Health",f"{max(0,health)}/100"); k2.metric("Estimated Tax",inr(tax)); k3.metric("TDS / Credits",inr(credits)); k4.metric("FY Records",len(yrs))
        tabs=st.tabs(["Tax History","Documents","Tasks","Timeline","Client Intake"])
        with tabs[0]:
            if yrs:
                hist=[]
                for y in yrs:
                    d=json.loads(y["data"]); hist.append({"AY":y["ay"],"Old Tax":d.get("old_tax",0),"New Tax":d.get("new_tax",0),"Recommended":d.get("recommended","")})
                hdf=pd.DataFrame(hist); st.dataframe(hdf.assign(**{"Old Tax":hdf["Old Tax"].map(inr),"New Tax":hdf["New Tax"].map(inr)}),use_container_width=True,hide_index=True)
                if px and len(hdf)>1:
                    chart=hdf.melt(id_vars=["AY"],value_vars=["Old Tax","New Tax"],var_name="Regime",value_name="Tax")
                    st.plotly_chart(px.bar(chart,x="AY",y="Tax",color="Regime",barmode="group",title="Year-on-year tax journey"),use_container_width=True)
            else: st.info("No tax computation saved yet.")
        with tabs[1]:
            doc=st.file_uploader("Upload client document",type=["pdf","png","jpg","jpeg","xlsx","csv","docx"],key=f"doc_{cid}")
            category=st.selectbox("Category",["AIS","26AS","Bank Statement","Investment","GST","TDS Certificate","ITR","Other"],key=f"cat_{cid}")
            if doc and st.button("Save Document",key=f"save_doc_{cid}"):
                safe=re.sub(r"[^A-Za-z0-9_.-]","_",doc.name); target=DOC_DIR/f"{cid}_{datetime.now().strftime('%Y%m%d%H%M%S')}_{safe}"; target.write_bytes(doc.getvalue())
                con=db(); con.execute("INSERT INTO documents(client_id,ay,category,filename,path,uploaded_at) VALUES(?,?,?,?,?,?)",(cid,ay,category,doc.name,str(target),datetime.now().isoformat(timespec="seconds"))); con.commit(); con.close(); add_activity(cid,"Document uploaded",f"{category}: {doc.name}"); st.success("Document saved locally.")
            con=db(); docs=con.execute("SELECT * FROM documents WHERE client_id=? ORDER BY id DESC",(cid,)).fetchall(); con.close()
            if docs: st.dataframe(pd.DataFrame([{"AY":d["ay"],"Category":d["category"],"File":d["filename"],"Uploaded":d["uploaded_at"]} for d in docs]),use_container_width=True,hide_index=True)
        with tabs[2]:
            with st.form(f"task_{cid}"):
                title=st.text_input("Task")
                due=st.date_input("Due date",date.today()+timedelta(days=7))
                add=st.form_submit_button("Add Task")
            if add and title:
                con=db(); con.execute("INSERT INTO tasks(client_id,title,due_date,status,created_at) VALUES(?,?,?,?,?)",(cid,title,due.isoformat(),"Pending",datetime.now().isoformat(timespec="seconds"))); con.commit(); con.close(); add_activity(cid,"Task added",title); st.rerun()
            con=db(); tasks=con.execute("SELECT * FROM tasks WHERE client_id=? ORDER BY due_date",(cid,)).fetchall(); con.close()
            for t in tasks:
                col1,col2,col3=st.columns([5,2,1]); col1.write(t["title"]); col2.write(t["due_date"]); 
                if col3.button("✓",key=f"done_{t['id']}"):
                    con=db(); con.execute("UPDATE tasks SET status='Completed' WHERE id=?",(t["id"],)); con.commit(); con.close(); add_activity(cid,"Task completed",t["title"]); st.rerun()
        with tabs[3]:
            con=db(); acts=con.execute("SELECT * FROM activities WHERE client_id=? ORDER BY id DESC",(cid,)).fetchall(); con.close()
            if acts:
                for a in acts:
                    st.markdown(f"**{a['created_at']}**  •  {a['activity']}  ")
                    st.caption(a['details'])
            else: st.info("No activity yet.")
            note=st.text_input("Add note")
            if st.button("Save note",key=f"note_{cid}") and note: add_activity(cid,"CA note",note); st.success("Note added.")
        with tabs[4]:
            token=make_token(cid)
            base=st.get_option("server.baseUrlPath") or ""
            host=st.context.headers.get("host","") if hasattr(st,"context") else ""
            scheme="https" if host and not host.startswith("localhost") else "http"
            link=f"{scheme}://{host}{base}/?intake={token}" if host else f"/?intake={token}"
            st.code(link)
            st.caption("This intake-link mechanism is intended for controlled deployments. For production, use proper authentication and a hosted database.")
            st.write("Client checklist: Basic details • Business details • Bank information • Investments • TDS • AIS/26AS • Documents")

# ----------------------------
# Reports & history
# ----------------------------
elif page=="Reports & History":
    st.markdown("<div class='section-title'>Reports & Year-on-Year History</div>",unsafe_allow_html=True)
    clients=get_clients()
    if clients:
        rows=[]
        for c in clients:
            for y in get_years(c["id"]):
                d=json.loads(y["data"]); rows.append({"Client":c["name"],"AY":y["ay"],"Old Tax":d.get("old_tax",0),"New Tax":d.get("new_tax",0),"Recommended":d.get("recommended","")})
        if rows:
            df=pd.DataFrame(rows); st.dataframe(df.assign(**{"Old Tax":df["Old Tax"].map(inr),"New Tax":df["New Tax"].map(inr)}),use_container_width=True,hide_index=True)
            st.download_button("Download report CSV",df.to_csv(index=False).encode(),"taxwise_history.csv","text/csv")
        else: st.info("No saved computations.")
    else: st.info("Create clients and save computations to build reports.")

# ----------------------------
# Settings
# ----------------------------
elif page=="Settings":
    st.markdown("<div class='section-title'>Settings & Compliance Notes</div>",unsafe_allow_html=True)
    st.markdown("### Assessment-year engine")
    st.write("AY 2026-27 is configured now. The code uses an AY_CONFIG dictionary so future AYs can be added without changing the UI architecture.")
    st.markdown("### CA workspace access")
    st.write("Local demo PIN is 2468 unless TAXWISE_CA_PIN is set in the environment. For a public deployment, replace this with real authentication and role-based access control.")
    st.markdown("### Security")
    st.warning("This local demo stores client data and uploaded documents in a local SQLite database/folder. Do not deploy it publicly with real client data until authentication, encryption, access control, backups and a secure hosted database are implemented.")
    st.markdown("### AIS / 26AS")
    st.write("No e-filing password, OTP or portal credentials are collected. Use the official portal and import the resulting data. This is the intentional alternative to scraping or credential automation.")
    st.markdown("### Disclaimer")
    st.info(DISCLAIMER)

# ----------------------------
# Intake route (simple)
# ----------------------------
params=st.query_params
if "intake" in params:
    token=params["intake"]
    clients=get_clients(); target=None
    for c in clients:
        if make_token(c["id"])==token: target=c; break
    if target:
        st.sidebar.success(f"Client intake: {target['name']}")
        st.markdown(f"## {target['name']} — Tax Information Request")
        st.progress(0.25,text="25% complete")
        with st.form("intake_form"):
            st.text_input("Full name",value=target["name"])
            st.text_input("Email",value=target["email"] or "")
            st.text_input("Phone",value=target["phone"] or "")
            st.selectbox("Taxpayer type",["Individual","Business","Professional","Investor","Other"])
            st.multiselect("Documents you can provide",["AIS","26AS","Bank statement","Investment statement","TDS certificate","GST information","ITR acknowledgement"])
            notes=st.text_area("Anything else the CA should know?")
            if st.form_submit_button("Submit information"):
                add_activity(target["id"],"Client intake submitted",notes); st.success("Information submitted to the local workspace.")
    else:
        st.error("Invalid or expired intake link.")

st.markdown(f"<hr><p class='small'>{DISCLAIMER}</p>",unsafe_allow_html=True)
