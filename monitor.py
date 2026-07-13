#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Monitor webu SoaringSpot – T-cup 2026
======================================

Tento skript:
  1) stáhne hlavní stránku závodu a několik "kotevních" podstránek,
  2) na nich najde odkazy na další relevantní podstránky (výsledky,
     startovní listiny, úkoly, aktuality, downloads...) a přidá je
     do seznamu sledovaných stránek,
  3) z každé stránky vytáhne pouze "viditelný" textový obsah (bez
     <script>, <style>, cookie lišt, reklam a analytických prvků),
  4) porovná ho s verzí uloženou z minulého běhu,
  5) pokud se obsah liší, pošle e-mail s popisem změny,
  6) uloží novou verzi pro příští porovnání.

Skript je navržen tak, aby byl spouštěn opakovaně (např. z GitHub
Actions každých 15 minut). Mezi jednotlivými spuštěními si "pamatuje"
stav pomocí souborů v adresáři state/ (ty se commitují zpět do repozitáře).
"""

import hashlib
import json
import os
import re
import smtplib
import ssl
import sys
import time
import traceback
from datetime import datetime, timezone
from email.mime.text import MIMEText
from urllib.parse import urljoin, urlparse, urlunparse, parse_qsl, urlencode

import requests
from bs4 import BeautifulSoup, Comment

# --------------------------------------------------------------------------
# 1) KONFIGURACE – tyto hodnoty si můžete upravit
# --------------------------------------------------------------------------

# Hlavní (kořenová) stránka závodu, kterou sledujeme
BASE_URL = "https://www.soaringspot.com/en_gb/tcup2026/"

# "Kotevní" podstránky, které se kontrolují vždy (i kdyby na ně hlavní
# stránka přestala odkazovat)
SEED_PATHS = [
    "",             # News / hlavní stránka
    "pilots",
    "results",
    "downloads",
    "gallery",
]

# Povolený prefix cesty – skript smí procházet (crawlovat) jen odkazy,
# jejichž cesta začíná tímto řetězcem (plus výjimka pro download-contest-file
# na kořeni domény, viz ALLOWED_EXTRA_PREFIXES)
ALLOWED_PREFIX = "/en_gb/tcup2026"
ALLOWED_EXTRA_PREFIXES = [
    "/en_gb/download-contest-file",  # odkazy na soubory ke stažení
]

# Cesty/vzory, které nikdy nechceme sledovat ani procházet (přihlášení,
# přepínání jazyků atd.)
EXCLUDED_PATTERNS = [
    r"/login",
    r"^/[a-z]{2,3}(_[a-z]{2})?/tcup2026",  # odkazy na jiné jazykové mutace (cs/, de/, fr/, sl/, en/...)
]

# Maximální počet stránek, které skript v jednom běhu sleduje (pojistka
# proti nekontrolovanému růstu, kdyby web měl obrovské množství odkazů)
MAX_PAGES = 80

# Maximální "hloubka" procházení od kotevních stránek (1 = jen odkazy
# přímo na kotevních stránkách)
MAX_CRAWL_DEPTH = 2

# HTML/CSS selektory (id, class, tag), které se před porovnáváním obsahu
# ODSTRAŇUJÍ, protože jde o "šum" (cookies, reklama, analytika, časovače...)
NOISE_SELECTORS = [
    "script", "style", "noscript", "template", "iframe",
    "[id*=cookie]", "[class*=cookie]",
    "[id*=consent]", "[class*=consent]",
    "[id*=gdpr]", "[class*=gdpr]",
    "[id*=onetrust]", "[class*=onetrust]",
    "[id*=analytics]", "[class*=analytics]",
    "[class*=advert]", "[id*=advert]",
    "[class*=banner-ad]",
    "[class*=ga-]",
    "[data-nosnippet]",
]

# Kolikrát se má opakovat pokus o stažení stránky, než ji skript označí
# za dočasně nedostupnou (aby výpadek webu nebyl vyhodnocen jako "změna")
FETCH_RETRIES = 3
FETCH_RETRY_DELAY_SEC = 8

# Po kolika po sobě jdoucích neúspěšných BĚZÍCH (ne pokusech v rámci
# jednoho běhu, ale samostatných spuštěních skriptu) poslat upozornění,
# že stránka je dlouhodobě nedostupná. Nastavte na 0 pro vypnutí.
NOTIFY_AFTER_CONSECUTIVE_FAILED_RUNS = 4  # při intervalu 15 min = cca 1 hodina

# Adresář pro ukládání stavu (musí se commitovat zpět do repozitáře)
STATE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "state")

# --------------------------------------------------------------------------
# E-mailové nastavení – hodnoty se берou z proměnných prostředí (GitHub
# Secrets), aby nebyly natvrdo v kódu. Popis nastavení je v README.
# --------------------------------------------------------------------------
SMTP_HOST = os.environ.get("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT = int(os.environ.get("SMTP_PORT", "465"))
SMTP_USER = os.environ.get("SMTP_USER", "")           # odesílající e-mail
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD", "")   # heslo aplikace (App Password)
EMAIL_TO = os.environ.get("EMAIL_TO", "")             # kam posílat upozornění
# volitelně více příjemců oddělených čárkou: "a@x.cz,b@y.cz"

REQUEST_HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; TCup2026Monitor/1.0; +https://github.com/)",
    "Accept-Language": "en,cs;q=0.9",
}

TIMEOUT = 20  # sekund na jeden HTTP požadavek


# --------------------------------------------------------------------------
# 2) POMOCNÉ FUNKCE
# --------------------------------------------------------------------------

def normalize_url(url: str) -> str:
    """Odstraní 'šumové' query parametry a fragmenty z URL, aby se stejná
    stránka nesledovala vícekrát pod různými variantami adresy."""
    parsed = urlparse(url)
    noisy_params = {"utm_source", "utm_medium", "utm_campaign", "utm_term",
                     "utm_content", "sid", "session", "csrf", "_", "t", "ts",
                     "cache", "v"}
    q = [(k, v) for k, v in parse_qsl(parsed.query) if k.lower() not in noisy_params]
    new_query = urlencode(q)
    cleaned = parsed._replace(query=new_query, fragment="")
    return urlunparse(cleaned)


def is_allowed_url(url: str) -> bool:
    parsed = urlparse(url)
    if parsed.netloc and parsed.netloc != urlparse(BASE_URL).netloc:
        return False
    path = parsed.path
    for pat in EXCLUDED_PATTERNS:
        if re.search(pat, path):
            return False
    if path.startswith(ALLOWED_PREFIX):
        return True
    for extra in ALLOWED_EXTRA_PREFIXES:
        if path.startswith(extra):
            return True
    return False


def is_downloadable_file_url(url: str) -> bool:
    """Odkazy na binární soubory ke stažení (PDF, CUP, GPX...) se
    nestahují celé (jsou to binární data), pouze se sleduje jejich
    přítomnost a metadata na stránce Downloads."""
    path = urlparse(url).path
    for extra in ALLOWED_EXTRA_PREFIXES:
        if path.startswith(extra):
            return True
    return False


def url_state_filename(url: str) -> str:
    h = hashlib.sha256(url.encode("utf-8")).hexdigest()[:24]
    return os.path.join(STATE_DIR, "pages", f"{h}.json")


def load_json(path, default):
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return default
    return default


def save_json(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def fetch(url):
    """Stáhne URL s několika opakovanými pokusy. Vrací (response, error)."""
    last_err = None
    for attempt in range(1, FETCH_RETRIES + 1):
        try:
            resp = requests.get(url, headers=REQUEST_HEADERS, timeout=TIMEOUT)
            if resp.status_code >= 500:
                last_err = f"HTTP {resp.status_code}"
                time.sleep(FETCH_RETRY_DELAY_SEC)
                continue
            return resp, None
        except requests.RequestException as e:
            last_err = str(e)
            time.sleep(FETCH_RETRY_DELAY_SEC)
    return None, last_err


def extract_visible_text_and_links(html: str, page_url: str):
    """Vrátí (normalizovaný_text, seznam_odkazů) ze stránky."""
    soup = BeautifulSoup(html, "html.parser")

    # odstranit komentáře
    for c in soup.find_all(string=lambda t: isinstance(t, Comment)):
        c.extract()

    # odstranit šumové elementy
    for selector in NOISE_SELECTORS:
        for el in soup.select(selector):
            el.decompose()

    # posbírat odkazy dřív, než text vyčistíme (chceme i href u <a>)
    links = set()
    for a in soup.find_all("a", href=True):
        abs_url = normalize_url(urljoin(page_url, a["href"]))
        links.add(abs_url)

    text = soup.get_text(separator="\n")
    # sjednotit bílé znaky – více mezer/prázdných řádků na jeden
    lines = [re.sub(r"[ \t]+", " ", ln).strip() for ln in text.splitlines()]
    lines = [ln for ln in lines if ln]
    normalized = "\n".join(lines)
    return normalized, links


def content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def send_email(subject: str, body: str):
    if not (SMTP_USER and SMTP_PASSWORD and EMAIL_TO):
        print("[VAROVÁNÍ] E-mailové údaje nejsou nastavené, e-mail se neodesílá.")
        print("---- OBSAH, KTERÝ BY BYL ODESLÁN ----")
        print(subject)
        print(body)
        return

    recipients = [r.strip() for r in EMAIL_TO.split(",") if r.strip()]
    msg = MIMEText(body, "plain", "utf-8")
    msg["Subject"] = subject
    msg["From"] = SMTP_USER
    msg["To"] = ", ".join(recipients)

    context = ssl.create_default_context()
    with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, context=context) as server:
        server.login(SMTP_USER, SMTP_PASSWORD)
        server.sendmail(SMTP_USER, recipients, msg.as_string())
    print(f"[OK] E-mail odeslán na: {', '.join(recipients)}")


def make_diff_summary(old_text: str, new_text: str, max_lines: int = 120) -> str:
    import difflib
    old_lines = old_text.splitlines()
    new_lines = new_text.splitlines()
    diff = list(difflib.unified_diff(old_lines, new_lines, lineterm="", n=1))
    # přeskočit hlavičku diffu (---/+++)
    diff = [d for d in diff if not d.startswith("---") and not d.startswith("+++")]
    if not diff:
        return "(Změna byla zjištěna na úrovni formátování, obsah beze změny textu.)"
    added = [d[1:].strip() for d in diff if d.startswith("+") and not d.startswith("+++")]
    removed = [d[1:].strip() for d in diff if d.startswith("-") and not d.startswith("---")]

    parts = []
    if added:
        parts.append("PŘIDÁNO / ZMĚNĚNO:")
        for line in added[:max_lines]:
            parts.append(f"  + {line}")
        if len(added) > max_lines:
            parts.append(f"  ... a dalších {len(added) - max_lines} řádků")
    if removed:
        parts.append("")
        parts.append("ODEBRÁNO / PŮVODNÍ ZNĚNÍ:")
        for line in removed[:max_lines]:
            parts.append(f"  - {line}")
        if len(removed) > max_lines:
            parts.append(f"  ... a dalších {len(removed) - max_lines} řádků")
    return "\n".join(parts)


def now_str():
    return datetime.now(timezone.utc).astimezone().strftime("%d.%m.%Y %H:%M:%S %Z")


# --------------------------------------------------------------------------
# 3) HLAVNÍ LOGIKA
# --------------------------------------------------------------------------

def discover_pages():
    """Najde seznam stránek ke sledování: kotevní stránky + odkazy z nich."""
    seeds = [normalize_url(urljoin(BASE_URL, p)) for p in SEED_PATHS]
    to_visit = list(dict.fromkeys(seeds))  # zachovat pořadí, bez duplicit
    discovered = list(to_visit)
    depth_map = {u: 1 for u in to_visit}

    i = 0
    while i < len(to_visit) and len(discovered) < MAX_PAGES:
        url = to_visit[i]
        i += 1
        depth = depth_map.get(url, 1)
        if depth >= MAX_CRAWL_DEPTH:
            continue
        if is_downloadable_file_url(url):
            continue  # binární soubory neprocházíme

        resp, err = fetch(url)
        if resp is None or not resp.ok:
            continue
        ctype = resp.headers.get("Content-Type", "")
        if "html" not in ctype:
            continue
        _, links = extract_visible_text_and_links(resp.text, url)
        for link in links:
            if not is_allowed_url(link):
                continue
            if link not in discovered and len(discovered) < MAX_PAGES:
                discovered.append(link)
                to_visit.append(link)
                depth_map[link] = depth + 1
    return discovered


def check_page(url: str, run_timestamp: str, notifications: list):
    state_path = url_state_filename(url)
    state = load_json(state_path, {
        "url": url,
        "hash": None,
        "notified_hash": None,
        "text": "",
        "consecutive_fail_runs": 0,
        "last_checked": None,
        "last_changed": None,
        "unavailable_notified": False,
    })

    is_binary = is_downloadable_file_url(url)

    if is_binary:
        # U binárních souborů sledujeme jen metadata (Last-Modified,
        # Content-Length) přes HTTP HEAD, ne obsah samotný.
        try:
            resp = requests.head(url, headers=REQUEST_HEADERS, timeout=TIMEOUT,
                                  allow_redirects=True)
            meta = f"size={resp.headers.get('Content-Length')} last_modified={resp.headers.get('Last-Modified')}"
            fetch_ok = resp.ok
        except requests.RequestException as e:
            meta = None
            fetch_ok = False
        new_text = meta or state["text"]
        fetch_error = None if fetch_ok else "HEAD request selhal"
    else:
        resp, fetch_error = fetch(url)
        if resp is not None and resp.ok and "html" in resp.headers.get("Content-Type", ""):
            new_text, _ = extract_visible_text_and_links(resp.text, url)
        else:
            new_text = None
            if resp is not None and fetch_error is None:
                fetch_error = f"HTTP {resp.status_code}"

    state["last_checked"] = run_timestamp

    if new_text is None:
        # Stránka je dočasně nedostupná / chyba - NEPOVAŽUJEME za změnu obsahu
        state["consecutive_fail_runs"] += 1
        print(f"[CHYBA] {url} -> {fetch_error} "
              f"(neúspěšných běhů za sebou: {state['consecutive_fail_runs']})")

        if (NOTIFY_AFTER_CONSECUTIVE_FAILED_RUNS
                and state["consecutive_fail_runs"] >= NOTIFY_AFTER_CONSECUTIVE_FAILED_RUNS
                and not state["unavailable_notified"]):
            notifications.append({
                "type": "unavailable",
                "url": url,
                "detail": fetch_error,
            })
            state["unavailable_notified"] = True
        save_json(state_path, state)
        return

    # Úspěšné stažení - reset počítadla chyb
    state["consecutive_fail_runs"] = 0
    if state["unavailable_notified"]:
        notifications.append({"type": "recovered", "url": url})
        state["unavailable_notified"] = False

    new_hash = content_hash(new_text)

    if state["hash"] is None:
        # První běh pro tuto URL - jen uložíme výchozí stav, nic neposíláme
        print(f"[INIT] {url} - uložen počáteční stav.")
        state["hash"] = new_hash
        state["notified_hash"] = new_hash
        state["text"] = new_text
        save_json(state_path, state)
        return

    if new_hash != state["notified_hash"]:
        diff_summary = make_diff_summary(state["text"], new_text)
        notifications.append({
            "type": "change",
            "url": url,
            "diff": diff_summary,
        })
        state["notified_hash"] = new_hash
        state["last_changed"] = run_timestamp
        print(f"[ZMĚNA] {url}")
    else:
        print(f"[BEZE ZMĚNY] {url}")

    state["hash"] = new_hash
    state["text"] = new_text
    save_json(state_path, state)


def build_email_body(notifications: list, run_timestamp: str) -> str:
    lines = []
    changes = [n for n in notifications if n["type"] == "change"]
    unavail = [n for n in notifications if n["type"] == "unavailable"]
    recovered = [n for n in notifications if n["type"] == "recovered"]

    lines.append(f"Kontrola provedena: {run_timestamp}")
    lines.append(f"Sledovaný web: {BASE_URL}")
    lines.append("=" * 60)

    for n in changes:
        lines.append("")
        lines.append(f"ZMĚNA NA STRÁNCE: {n['url']}")
        lines.append("-" * 60)
        lines.append(n["diff"])
        lines.append("")

    for n in unavail:
        lines.append("")
        lines.append(f"UPOZORNĚNÍ: Stránka je dlouhodobě nedostupná: {n['url']}")
        lines.append(f"Poslední chyba: {n['detail']}")

    for n in recovered:
        lines.append("")
        lines.append(f"Stránka je opět dostupná: {n['url']}")

    lines.append("")
    lines.append("=" * 60)
    lines.append(f"Odkaz na hlavní stránku závodu: {BASE_URL}")
    return "\n".join(lines)


def main():
    run_timestamp = now_str()
    print(f"=== Kontrola spuštěna: {run_timestamp} ===")

    try:
        pages = discover_pages()
    except Exception:
        print("[CHYBA] Selhalo zjišťování podstránek, používám jen výchozí seznam.")
        traceback.print_exc()
        pages = [normalize_url(urljoin(BASE_URL, p)) for p in SEED_PATHS]

    print(f"Sledovaných stránek: {len(pages)}")

    # uložit aktuální seznam sledovaných stránek (pro přehled / ladění)
    save_json(os.path.join(STATE_DIR, "known_urls.json"),
              {"updated": run_timestamp, "urls": pages})

    notifications = []
    for url in pages:
        try:
            check_page(url, run_timestamp, notifications)
        except Exception:
            print(f"[CHYBA] Neočekávaná chyba při kontrole {url}")
            traceback.print_exc()

    if notifications:
        subject = f"[T-cup 2026] Zjištěna změna na webu ({len(notifications)}x) - {run_timestamp}"
        body = build_email_body(notifications, run_timestamp)
        try:
            send_email(subject, body)
        except Exception:
            print("[CHYBA] Odeslání e-mailu selhalo:")
            traceback.print_exc()
            sys.exit(1)
    else:
        print("Žádné změny nebyly nalezeny, e-mail se neodesílá.")


if __name__ == "__main__":
    main()
