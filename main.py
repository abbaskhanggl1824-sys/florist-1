# -*- coding: utf-8 -*-
"""
AI-Powered Contact Form Bot (Dynamic Engine Update)
- Engine Wrapper: Multi-Tier Fail-Safe Sheet Handler
- Patched: Each site runs in an isolated CHILD PROCESS with a hard kill timeout.
  signal.alarm could not interrupt Playwright/gRPC blocked-socket hangs (the
  handler never runs while the main thread is stuck in C). A child process can
  always be killed by the OS, so a single bad site can no longer freeze the run.
"""
import os
import json
import base64
import time
import logging
import sys
import re
import warnings
import multiprocessing as mp
from datetime import datetime

warnings.filterwarnings("ignore", category=FutureWarning)
import google.generativeai as genai
import gspread
from google.oauth2.service_account import Credentials
from playwright.sync_api import sync_playwright
import twocaptcha

# ------------------------------------------
#  CONFIGURATION - GitHub Secrets
# ------------------------------------------

GEMINI_API_KEY      = os.environ["GEMINI_API_KEY"]
CAPTCHA_API_KEY     = os.environ["CAPTCHA_API_KEY"]
GOOGLE_SHEET_ID     = os.environ["GOOGLE_SHEET_ID"]
GOOGLE_CREDS_JSON   = os.environ["GOOGLE_CREDS_JSON"]

GEMINI_MODEL_NAME = "gemini-3.1-flash-lite"

# Hard ceiling (seconds) for the ENTIRE processing of one website, enforced by
# killing the child process. This is the real protection against frozen sites.
PER_SITE_TIMEOUT = 150
# Inner timeouts on the two Gemini calls. Belt-and-suspenders; the process kill
# is what actually guarantees progress.
GEMINI_HOOK_TIMEOUT = 30
GEMINI_FORM_TIMEOUT = 40

FIRST_NAME  = "Ray"
LAST_NAME   = "Sharma"
FULL_NAME   = "Ray"
COMPANY     = "Zevahit"
EMAIL       = "sales@zevahit.com"
PHONE       = "+18005550199"

SUBJECT_TEMPLATE = "When locals search \"florist near me\" - do they find you?"
MESSAGE_TEMPLATE = "Hi,\n\n{intro}Quick question: when someone in your area searches \"florist near me,\" \"wedding flowers,\" or \"flower delivery today\" - does your shop show up at the top, or do the bigger chains and order-gatherer sites grab the order first?\n\nFor most local florists, those high-intent searches quietly go to competitors who simply rank higher and get featured more often across the web. No visibility, no clicks - and you never even see the orders you missed.\n\nThat's what we fix at Zevahit. We get your flower shop featured and cited on real, high-authority local and editorial sites - the exact signals that Google rankings AND the new AI search tools rely on to decide which florist to recommend.\n\nWant to see where you currently stand? Reply with your city and I'll send a free snapshot of how visible your shop is in local + AI search today, plus the 3 quickest wins to capture more local orders.\n\n- Ray, Zevahit\nzevahit.com\nClient reviews: https://clutch.co/profile/zevahit#reviews"

PROCESS_LIMIT = None

CONTACT_KEYWORDS = ["contact", "contact-us", "contactus", "contact-form", "get-in-touch",
                    "getintouch", "reach-us", "reachus", "reach-out", "write-to-us",
                    "get-started", "getstarted", "start-here", "enquiry", "enquire",
                    "enquiries", "inquiry", "inquire", "lets-talk", "let-s-talk", "lets-connect",
                    "work-with-us", "hire-us", "hire", "start-project", "start-a-project",
                    "request-quote", "request-a-quote", "get-a-quote", "get-quote", "quote",
                    "book-a-call", "book-call", "book-a-consultation", "book-consultation",
                    "free-consultation", "free-audit", "free-quote", "schedule", "schedule-a-call",
                    "consultation", "talk-to-us", "connect", "connect-with-us", "say-hello",
                    "hello", "support", "help", "get-in-touch-with-us", "contact-sales", "demo", "request-demo"]

# ------------------------------------------
#  LOGGING
# ------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)]
)
log = logging.getLogger(__name__)

# ------------------------------------------
#  GOOGLE SHEETS ENGINE (parent process only)
# ------------------------------------------

def init_sheets():
    """Dynamically loads sheet workspace or forces lowercase tab parsing."""
    creds_dict = json.loads(GOOGLE_CREDS_JSON)
    creds = Credentials.from_service_account_info(
        creds_dict,
        scopes=["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
    )
    gc = gspread.authorize(creds)
    sh = gc.open_by_key(GOOGLE_SHEET_ID)

    ws = None
    try:
        ws = sh.worksheet("websites")
    except gspread.WorksheetNotFound:
        for sheet in sh.worksheets():
            if sheet.title.lower().strip() == "websites":
                ws = sheet
                break
        if not ws:
            log.warning("Tab 'websites' not found. Creating a fresh tracking sheet tab...")
            ws = sh.add_worksheet("websites", rows=1000, cols=7)
            ws.update(range_name="A1:G1", values=[["website", "city", "status", "submitted_at", "notes", "fields_filled", "ai_actions"]])

    headers = [str(h).strip().lower() for h in ws.row_values(1)]
    if not headers or "website" not in headers:
        log.warning("Sheet Headers out of sync. Injecting structural automation grid row...")
        ws.update(range_name="A1:G1", values=[["website", "city", "status", "submitted_at", "notes", "fields_filled", "ai_actions"]])
        time.sleep(1)

    return ws


def update_sheet_row(ws, row_num, status, notes="", fields_filled="", ai_actions=""):
    """Deep structural cell mapping targeting directly into correct index offsets."""
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    excel_row = row_num + 1

    headers = [str(h).strip().lower() for h in ws.row_values(1)]
    try:
        status_idx = headers.index("status")
        start_col = chr(65 + status_idx)
        end_col = chr(65 + status_idx + 4)
        ws.update(range_name="{}{}:{}{}".format(start_col, excel_row, end_col, excel_row),
                  values=[[status, now, notes, fields_filled, ai_actions]])
    except Exception:
        ws.update(range_name="C{}:G{}".format(excel_row, excel_row),
                  values=[[status, now, notes, fields_filled, ai_actions]])

    log.info("  [Sheets Save Engine] Captured Row {} -> Sync status: {}".format(excel_row, status))


def get_pending_rows(ws):
    """Parses structural maps mapping non-blank rows while preserving casing variants."""
    rows = ws.get_all_records()
    pending = []
    for i, row in enumerate(rows):
        normalized_row = {str(k).strip().lower(): v for k, v in row.items()}
        url = str(normalized_row.get("website", "")).strip()
        status = str(normalized_row.get("status", "")).strip().lower()
        if url and status not in ("submitted", "processing", "no_form_found"):
            pending.append((i + 1, normalized_row))
    return pending

# ------------------------------------------
#  BROWSER AUTOMATION WRAPPERS (run in child)
# ------------------------------------------

def normalise_url(url):
    url = str(url).strip()
    if not url.startswith("http"):
        url = "https://" + url
    return url.rstrip("/")


def dismiss_cookie_banner(page):
    accept_texts = ["accept all", "accept all cookies", "accept cookies", "accept",
                    "i agree", "agree", "agree & continue", "got it", "allow all",
                    "allow cookies", "allow", "ok", "okay", "i accept", "accept & close"]
    try:
        buttons = page.locator("button, a, [role='button']").all()
        for btn in buttons[:30]:
            txt = (btn.inner_text(timeout=100) or "").strip().lower()
            if txt and any(t == txt for t in accept_texts):
                btn.click(timeout=1000)
                return True
    except: pass
    return False


def check_form_presence_deep(page):
    try:
        for sel in ['input:not([type="hidden"])', 'textarea', 'iframe[src*="forms"]', '.hs-form']:
            if page.locator(sel).first.count() > 0: return True
        return page.evaluate("""() => {
            let f = false;
            const scan = (r) => {
                if (!r || f) return;
                if (r.querySelector && (r.querySelector('input:not([type="hidden"])') || r.querySelector('textarea'))) { f = true; return; }
                let el = r.querySelectorAll ? r.querySelectorAll('*') : [];
                for (let i of el) { if (i.shadowRoot) scan(i.shadowRoot); }
            };
            scan(document); return f;
        }""")
    except: return False


def find_contact_page(page, base_url):
    current_url = page.url
    try:
        links = page.locator("a").all()
        for link in links:
            href = link.get_attribute("href") or ""
            txt = (link.inner_text(timeout=100) or "").lower()
            if any(kw in href.lower() for kw in CONTACT_KEYWORDS) or any(kw.replace("-", " ") in txt for kw in CONTACT_KEYWORDS):
                if any(kw in current_url.lower() for kw in CONTACT_KEYWORDS): return True
                try:
                    link.click(timeout=4000)
                    page.wait_for_load_state("domcontentloaded", timeout=6000)
                    return True
                except: pass
    except: pass

    if check_form_presence_deep(page): return True

    for kw in ["contact", "contact-us", "demo", "get-started"]:
        try:
            resp = page.goto("{}/{}".format(base_url, kw), timeout=6000, wait_until="domcontentloaded")
            if resp and resp.status < 400: return True
        except: pass
    return False

# ------------------------------------------
#  CAPTCHA & AI CONTEXT LOGIC (run in child)
# ------------------------------------------

def solve_captcha(page, website):
    try:
        solver = twocaptcha.TwoCaptcha(CAPTCHA_API_KEY)
        frame = page.locator('iframe[src*="recaptcha"], iframe[src*="hcaptcha"]').first
        if frame.is_visible(timeout=500):
            src = frame.get_attribute("src") or ""
            sitekey = ""
            for part in src.split("&"):
                if "k=" in part or "sitekey=" in part:
                    sitekey = part.split("=")[1].split("&")[0]; break
            if sitekey:
                log.info("  [CAPTCHA] Engine triggered...")
                res = solver.recaptcha(sitekey=sitekey, url=website)
                token = res["code"]
                page.evaluate(f"try {{ document.getElementById('g-recaptcha-response').innerHTML = '{token}'; }} catch(e) {{}}")
                return True
    except: pass
    return False


def generate_personalized_line(gemini_model, page, website):
    try:
        txt = page.evaluate("() => { let out = ''; document.querySelectorAll('h1,h2,title,p').forEach(el => { out += el.innerText + ' | ' }); return out; }")[:3000]
        if len(txt.strip()) < 40: return ""
        prompt = "Write ONE warm, specific cold-outreach opening hook sentence for a local florist/flower shop based on this text map from {website}: {txt}\nReference something real about their shop (e.g. their arrangements, weddings, local area, or specialty). Max 22 words, end with a comma, no explanations, no markdown format rules."
        resp = gemini_model.generate_content(
            prompt.format(website=website, txt=txt),
            request_options={"timeout": GEMINI_HOOK_TIMEOUT}
        )
        hook = resp.text.strip().replace("```", "").strip('"').split("\n")[0]
        if 5 < len(hook.split()) < 35: return hook
    except: pass
    return ""


def get_page_html(page):
    try:
        js = """() => {
            let out = '';
            document.querySelectorAll('form, input, textarea, button, select, label').forEach(el => {
                let attrs = []; ['id', 'name', 'type', 'placeholder'].forEach(a => { let v = el.getAttribute(a); if(v) attrs.push(`${a}="${v}"`); });
                out += `<${el.tagName.toLowerCase()} ${attrs.join(' ')}>${el.innerText || ''}</...>\n`;
            });
            return out;
        }"""
        chunks = [page.evaluate(js)]
        for f in page.frames:
            if f != page.main_frame:
                try: chunks.append(f.evaluate(js))
                except: pass
        return "\n".join(chunks)[:25000]
    except: return ""


def ask_gemini_for_form(gemini_model, page, website, subject, message):
    """Sends the form DOM map to Gemini and returns a list of fill/click actions."""
    html = get_page_html(page)
    prompt = """You are a functional web parser script executor. Return ONLY a standard structured JSON array list mapping actions for this DOM:
    {html}
    Mapping instructions:
    - Target matching standard form items using fields: Full Name={full_name}, Email={email}, Company={company}, Phone={phone}, Subject={subject}, Message Field={message}
    - Final element should always be the click element targeting button[type='submit'] inside form.
    Format example: [ {{"action": "fill", "selector": "input[name='email']", "value": "..."}} ]
    No explanations, no code block quotes wraps."""

    prompt = prompt.format(html=html, full_name=FULL_NAME, email=EMAIL, company=COMPANY, phone=PHONE, subject=subject, message=message)
    resp = gemini_model.generate_content(prompt, request_options={"timeout": GEMINI_FORM_TIMEOUT})
    raw = resp.text.strip()
    if "```" in raw:
        raw = raw.split("```")[1]
        if raw.startswith("json"): raw = raw[4:]
    return json.loads(raw.strip())


def execute_actions(page, actions):
    filled = []
    submitted = False
    if not actions: return filled, submitted

    for action in actions:
        act = action.get("action", "").lower()
        sel = action.get("selector", "")
        val = action.get("value", "")
        if not sel: continue

        target = None
        try:
            if page.locator(sel).first.is_visible(timeout=300): target = page.locator(sel).first
        except: pass

        if not target:
            for f in page.frames:
                try:
                    if f.locator(sel).first.is_visible(timeout=200): target = f.locator(sel).first; break
                except: pass

        if not target: continue

        try:
            if act == "fill":
                target.scroll_into_view_if_needed(timeout=1000)
                target.fill(val)
                filled.append(sel.split("[")[0][:15])
            elif act == "check":
                target.check(timeout=1000)
            elif act == "select":
                target.select_option(val)
            elif act == "click":
                url_before = page.url
                try: target.click(timeout=3000)
                except: target.evaluate("el => el.click()")

                time.sleep(5)
                success_keys = ["thank", "thanks", "sent", "success", "submitted", "received"]
                body_txt = ""
                try: body_txt = page.inner_text("body", timeout=1000).lower()
                except: pass

                if page.url != url_before or any(w in body_txt for w in success_keys):
                    submitted = True
        except: pass

    return filled, submitted

# ------------------------------------------
#  CHILD-PROCESS WORKER  (one site, fully isolated)
# ------------------------------------------

def process_single_site(website_raw, result_q):
    """
    Runs in a separate process. Does ALL the slow/hang-prone work for one site:
    its own Playwright instance, its own Gemini client. Puts a result dict on
    result_q. If this process hangs, the parent kills it after PER_SITE_TIMEOUT.
    """
    result = {"status": "error", "notes": "Worker exited before completion", "fields_filled": ""}
    try:
        genai.configure(api_key=GEMINI_API_KEY)
        gemini_model = genai.GenerativeModel(GEMINI_MODEL_NAME)

        website = normalise_url(website_raw)
        current_subject = SUBJECT_TEMPLATE

        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-setuid-sandbox", "--disable-dev-shm-usage", "--disable-gpu"]
            )
            context = browser.new_context(
                user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
            )
            tabs = []
            context.on("page", lambda pg_: tabs.append(pg_))
            pg = context.new_page()
            pg.set_default_timeout(25000)

            pg.goto(website, timeout=35000, wait_until="domcontentloaded")
            time.sleep(3)
            dismiss_cookie_banner(pg)

            try:
                intro_line = generate_personalized_line(gemini_model, pg, website)
            except:
                intro_line = ""

            intro_block = (intro_line.strip() + "\n\n") if intro_line.strip() else ""
            current_message = MESSAGE_TEMPLATE.format(intro=intro_block)

            find_contact_page(pg, website)
            time.sleep(2)

            active_page = tabs[-1] if tabs else pg
            dismiss_cookie_banner(active_page)
            solve_captcha(active_page, website)

            try:
                actions = ask_gemini_for_form(gemini_model, active_page, website, current_subject, current_message)
            except Exception as e:
                result = {"status": "error",
                          "notes": "Form Engine Structure Read Error: {}".format(str(e)[:45]),
                          "fields_filled": ""}
                browser.close()
                result_q.put(result)
                return

            filled, submitted = execute_actions(active_page, actions)

            if submitted:
                status, notes = "submitted", "Pipeline verified submission context."
            elif not filled:
                status, notes = "no_form_found", "Skipped: Structural layout forms not mapped."
            else:
                status, notes = "filled_not_submitted", "Trigger dropped redirect checks ({}).".format(", ".join(filled))

            result = {"status": status, "notes": notes, "fields_filled": ", ".join(filled)}
            browser.close()

    except Exception as worker_err:
        result = {"status": "error", "notes": str(worker_err)[:60], "fields_filled": ""}

    try:
        result_q.put(result)
    except:
        pass

# ------------------------------------------
#  MAIN RUNNER (parent: orchestration + Sheets only)
# ------------------------------------------

def main():
    log.info("=== Bot Workspace Execution Pipeline Started ===")
    ws = init_sheets()
    pending = get_pending_rows(ws)
    log.info("Pending rows parsed successfully from registry: {}".format(len(pending)))

    if not pending:
        log.info("Tracking register returns 0 workloads. Process Terminated.")
        return

    to_process = pending[:PROCESS_LIMIT]
    ctx = mp.get_context("spawn")  # clean, no inherited Playwright/gRPC state

    for row_idx, row_data in to_process:
        website_raw = row_data.get("website", row_data.get("url", ""))
        website = normalise_url(website_raw)
        log.info("\nLaunching Processing Vector: {}".format(website))

        result_q = ctx.Queue()
        worker = ctx.Process(target=process_single_site, args=(website_raw, result_q))
        worker.start()
        worker.join(PER_SITE_TIMEOUT)

        if worker.is_alive():
            # Site is wedged in a blocked socket call. Kill it outright.
            log.error("Hard per-site timeout ({}s) hit, killing worker: {}".format(PER_SITE_TIMEOUT, website))
            worker.terminate()
            worker.join(10)
            if worker.is_alive():
                worker.kill()  # SIGKILL if terminate wasn't enough
                worker.join(5)
            update_sheet_row(ws, row_idx, "error",
                             notes="Hard per-site timeout ({}s) - worker killed".format(PER_SITE_TIMEOUT))
            continue

        # Worker finished on its own; collect its result if present.
        try:
            result = result_q.get_nowait()
        except Exception:
            result = {"status": "error",
                      "notes": "Worker ended without result (exit {})".format(worker.exitcode),
                      "fields_filled": ""}

        update_sheet_row(ws, row_idx, result["status"],
                         notes=result.get("notes", ""),
                         fields_filled=result.get("fields_filled", ""))
        log.info("  [AI Grid Engine Map] Row complete -> {}".format(result["status"]))
        time.sleep(2)

    log.info("=== Bot Workspace Execution Pipeline Complete ===")

if __name__ == "__main__":
    main()
