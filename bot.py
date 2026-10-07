# -*- coding: utf-8 -*-
"""
Continental News Telegram Bot v8.3 FINAL — Korbach Strategic + Production-First

Логіка:
- запуск через GitHub Actions за розкладом;
- стан Queue/архіву зберігається у JSON-файлах репозиторію та комітується після кожного запуску;
- пошук новин працює цілодобово;
- автоматичний випуск о 09:00 за Europe/Berlin; FORCE_RUN=1 дозволяє ручний запуск у будь-який час;
- Telegram-архів не очищається;
- прямі офіційні джерела та RSS мають пріоритет; Google News лише резервний агрегатор;
- публікується реальний URL джерела;
- фото береться тільки з реального сайту;
- дублікати URL, схожі заголовки та одні й ті самі події з різних джерел не публікуються;
- v5.3 блокує біржовий/SEO-філер без конкретної корпоративної події;
- Korbach має найвищий пріоритет;
- 4 aktive розділи:
  🏭 Continental-Werke
  🛞 Reifen
  👥 Mitarbeiter & Jobs
  📊 Management & Unternehmen
"""

from __future__ import annotations

import html
import json
import os
import re
import time
import warnings
from datetime import datetime, timedelta, timezone
from difflib import SequenceMatcher
from io import BytesIO
from pathlib import Path
from typing import Any, Optional
from urllib.parse import quote, urljoin, urlparse
from zoneinfo import ZoneInfo

import feedparser
import requests
from bs4 import BeautifulSoup, MarkupResemblesLocatorWarning
from PIL import Image

warnings.filterwarnings("ignore", category=MarkupResemblesLocatorWarning)

try:
    from googlenewsdecoder import gnewsdecoder
except Exception:
    gnewsdecoder = None


# ============================================================
# ENV / CONSTANTS
# ============================================================

BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
CHANNEL_ID = os.environ.get("TELEGRAM_CHANNEL_ID", "").strip()

if not BOT_TOKEN:
    raise RuntimeError("TELEGRAM_BOT_TOKEN не заданий у GitHub Secrets")
if not CHANNEL_ID:
    raise RuntimeError("TELEGRAM_CHANNEL_ID не заданий у GitHub Secrets")

GERMANY_TZ = ZoneInfo("Europe/Berlin")

SEARCH_LOOKBACK_HOURS = 24 * 14  # discovery window; editorial freshness decides publication eligibility
NORMAL_NEWS_MAX_AGE_HOURS = 48
IMPORTANT_NEWS_MAX_AGE_HOURS = 24 * 14
FACTORY_NEWS_MAX_AGE_HOURS = 24 * 7
CRITICAL_NEWS_MAX_AGE_HOURS = 24 * 7
KORBACH_STRATEGIC_MAX_AGE_HOURS = 24 * 60
OFFICIAL_CONTENT_MAX_AGE_HOURS = 24 * 14
STRATEGIC_TOPIC_LOOKBACK_HOURS = 24 * 90
STORIES_LOOKBACK_HOURS = 336
PENDING_MAX_AGE_HOURS = 24 * 7
PENDING_MIN_RELEVANCE = 45
PRODUCTION_MIN_RELEVANCE = 35
KORBACH_PRODUCTION_MIN_RELEVANCE = 30
KORBACH_STRATEGIC_MIN_RELEVANCE = 30
TIRE_TECH_MIN_RELEVANCE = 40
MAX_PENDING_ITEMS = 20
MAX_PRODUCTION_ITEMS_PER_RUN = 6
MAX_KORBACH_ITEMS_PER_RUN = 2
MAX_KORBACH_STRATEGIC_ITEMS_PER_RUN = 2
MAX_TIRE_TECH_ITEMS_PER_RUN = 3
MAX_COMPANY_ITEMS_PER_RUN = 2

# v5.5 test diagnostics: count every news rejection reason so the
# publication path can be audited without guessing.
REJECTION_STATS: dict[str, int] = {}

def record_rejection(reason: str) -> None:
    REJECTION_STATS[reason] = REJECTION_STATS.get(reason, 0) + 1

JOB_PENDING_MAX_AGE_HOURS = 24 * 7
JOB_LOOKBACK_HOURS = 24 * 30
JOB_REACTIVATION_GAP_HOURS = 24 * 7
PUBLISH_HOUR = 9
MAX_POSTS_PER_RUN = 10

# Manual/initial runs may bypass the 09:00 publication-time gate.
FORCE_RUN = os.getenv("FORCE_RUN", "0") == "1"
BOOTSTRAP_MODE = os.getenv("BOOTSTRAP_MODE", "0") == "1"

# v5.3 quality gates: block finance/SEO filler unless the article also
# contains a concrete Continental event. This protects the channel from
# stock-price calculators, historical investment hypotheticals and similar
# traffic articles that do not inform employees.
STOCK_SEO_FILLER_PATTERNS = [
    r"\bdax\s*40[^\n]{0,100}continental",
    r"\bcontinental[- ]aktie[^\n]{0,120}(gewinn|rendite|investition|anlage|million|euro)",
    r"\bso viel (gewinn|rendite)[^\n]{0,120}continental",
    r"\b(hätte|haette) eine investition[^\n]{0,120}continental",
    r"\bkursziel[^\n]{0,100}continental",
    r"\baktienanalyse[^\n]{0,100}continental",
    r"\baktiencheck[^\n]{0,100}continental",
    r"\bdividendenrendite[^\n]{0,100}continental",
]

# v5.10.3: hard-block pure stock-market / investment commentary. These are
# never considered editorial news unless the article is clearly about a new
# operational/corporate event (plant, product, workforce, transaction etc.).
PURE_STOCK_TERMS = (
    "aktie im fokus", "aktien im fokus", "chartanalyse", "aktienanalyse",
    "kursanalyse", "kursziel", "kurs-prognose", "kursprognose",
    "gewinn mit der continental-aktie", "rendite mit der continental-aktie",
    "investition in continental", "investment in continental",
    "trading continental", "continental aktie heute", "continental stock today",
)

OPERATIONAL_EVENT_TERMS = (
    "werk", "produktion", "reif", "reifen", "technologie", "produkt",
    "investition", "kapazität", "kapazitaet", "erweiterung", "ausbau",
    "verlagerung", "schließung", "schliessung", "stellenabbau",
    "mitarbeiter", "arbeitsplätze", "arbeitsplaetze", "betriebsrat",
    "übernahme", "uebernahme", "verkauf", "fusion", "spinoff", "spin-off",
    "ceo", "vorstand", "aufsichtsrat", "strategie", "quartalszahlen",
)

def is_pure_stock_commentary(title: str, summary: str = "") -> bool:
    text = normalize_text(f"{title} {summary}")
    if any(term in text for term in PURE_STOCK_TERMS):
        return not any(term in text for term in OPERATIONAL_EVENT_TERMS)
    return False

# Hard block for market/SEO analysis pieces. Unlike ordinary relevance scoring,
# these patterns are editorial exclusions: an article whose main purpose is
# stock-price/technical/investment analysis must never become the best remaining
# item merely because it mentions a real Continental corporate event.
STOCK_MARKET_HARD_PATTERNS = [
    r"\bcontinental[- ]aktie\b.*\b(im fokus|chartanalyse|kursanalyse|prognose|kursziel|bewertung)\b",
    r"\baktie\b.*\b(im fokus|chartanalyse|kursanalyse|kursziel)\b.*\bcontinental\b",
    r"\bcontinental\b.*\baktienanalyse\b",
    r"\bcontinental\b.*\bchartanalyse\b",
    r"\bcontinental\b.*\bkursanalyse\b",
    r"\bcontinental\b.*\bkursziel\b",
    r"\bcontinental\b.*\bgewinnpotenzial\b",
    r"\bcontinental\b.*\baktienprognose\b",
]

# Explicit phrases used by job pages when a vacancy is closed/withdrawn.
# We do not rely on the presence of an application button because the
# Continental portal is client-rendered, but we still reject an explicit
# closed-status signal when it is present in the fetched detail page.
INACTIVE_JOB_PATTERNS = [
    r"stelle nicht mehr verfügbar",
    r"stelle nicht mehr verfuegbar",
    r"position nicht mehr verfügbar",
    r"position nicht mehr verfuegbar",
    r"job nicht mehr verfügbar",
    r"job nicht mehr verfuegbar",
    r"vacancy is no longer available",
    r"position is no longer available",
    r"this job is no longer available",
    r"requisition is closed",
    r"requisition closed",
]

# Event families are deliberately broader than individual keywords.
# They are used only for duplicate-event detection, not relevance scoring.
# Example: relocation + production transfer + workforce impact should be one
# Telegram event even when HNA, Reifenpresse and Hessenschau use different
# headlines.
EVENT_FAMILIES = {
    "restructuring": (
        "stellenabbau", "job cuts", "layoffs", "kündigung", "kuendigungen",
        "kurzarbeit", "abbau von arbeitsplätzen", "abbau von arbeitsplaetzen",
        "personalabbau", "entlassungen", "personeller aderlass", "arbeitsplätze",
        "arbeitsplaetze", "mitarbeiter betroffen",
    ),
    "relocation": (
        "verlagerung", "verlagert", "produktion verlagert", "production transfer",
        "production relocation", "transfer production", "nach asien", "nach europa",
        "ins ausland", "ausland verlagert", "produktionsverlagerung",
    ),
    "closure_stop": (
        "schließung", "schliessung", "geschlossen", "werksschließung",
        "werksschliessung", "produktionsstopp", "produktion stoppt", "production stop",
        "shutdown", "closure",
    ),
    "investment": (
        "investition", "investitionen", "investment", "investments",
        "kapazität", "kapazitaet", "capacity", "erweiterung", "expansion",
        "modernisierung", "modernization",
    ),
    "results": (
        "quartalszahlen", "quarterly results", "umsatz", "revenue", "ebit",
        "ebitda", "gewinn", "profit", "jahreszahlen", "halbjahreszahlen",
    ),
    "management": (
        "vorstand", "aufsichtsrat", "ceo", "cfo", "geschäftsführung",
        "geschaeftsfuehrung", "chairman", "management",
    ),
    "labor": (
        "betriebsrat", "ig metall", "tarifvertrag", "gewerkschaft", "streik",
        "strike", "tarifrunde",
    ),
}

OFFICIAL_RSS_FEEDS = [
    "https://www.continental.com/en/general/rss/press-releases/",
    "https://www.continental.com/en/general/rss/investors/",
]

# Official German Continental Reifen Stories page. It is HTML, not RSS,
# therefore we crawl the listing page and then open the individual story.
CONTINENTAL_REIFEN_STORIES_URL = "https://www.continental-reifen.de/about-us/stories/"
CONTINENTAL_UNERMUEDLICH_URL = "https://www.continental-reifen.de/products/truck/unermuedlich-blog/"
CONTINENTAL_REIFEN_SITEMAP_URLS = [
    "https://www.continental-reifen.de/sitemap.xml",
    "https://www.continental-reifen.de/sitemap_index.xml",
]

# Primary official Continental job portal filtered to Korbach.
# The portal is a JavaScript application, so we first inspect the rendered
# HTML for job-detail links and keep the dedicated Korbach careers page as
# an authoritative fallback when the SPA does not expose links to requests.
KORBACH_JOBS_URL = (
    "https://jobs.continental.com/de/#/?location="
    "%7B%22title%22:%22Korbach,%20Deutschland%22,%22type%22:%22location%22,"
    "%22coordinates%22:%7B%22latitude%22:51.2742,%22longitude%22:8.8717%7D%7D"
)
KORBACH_CAREERS_URL = "https://www.continental.com/de/karriere/arbeiten-bei-continental/standorte/korbach/"

HNA_KORBACH_URL = "https://www.hna.de/lokales/frankenberg/korbach-ort55370/"

DIRECT_MEDIA_RSS = [
    ("https://www.tagesschau.de/wirtschaft/unternehmen/index~rss2.xml", "tagesschau Unternehmen", 980),
    ("https://www.tagesschau.de/inland/index~rss2.xml", "tagesschau Inland", 900),
    ("https://www.hessenschau.de/index.rss", "hessenschau", 980),
    ("https://www.hessenschau.de/nordhessen/index.rss", "hessenschau Nordhessen", 1100),
]

# Official Continental jobs are discovered first through the official
# jobs.continental.com Korbach filter, with the official Korbach careers page
# as fallback. Only jobs.continental.com detail pages are accepted.
OFFICIAL_JOBS_DOMAIN = "jobs.continental.com"

REQUEST_TIMEOUT = 25
IMAGE_TIMEOUT = 25
GOOGLE_DECODE_DELAY = 0.55
SOURCE_PAGE_DELAY = 0.20

PUBLISHED_FILE = Path("continental_published.json")
PENDING_FILE = Path("continental_pending.json")
MESSAGES_FILE = Path("continental_messages.json")

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36"
)

HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept-Language": "de-DE,de;q=0.9,en;q=0.8,uk;q=0.7",
}

GOOGLE_DOMAINS = {
    "news.google.com",
    "google.com",
    "www.google.com",
    "googleusercontent.com",
    "lh3.googleusercontent.com",
    "gstatic.com",
}

BLOCKED_SOURCE_DOMAINS = {
    "facebook.com",
    "instagram.com",
    "youtube.com",
    "youtu.be",
    "tiktok.com",
    "x.com",
    "twitter.com",
    "telegram.me",
    "t.me",
    "wikipedia.org",
    "pinterest.com",
}

BAD_IMAGE_TERMS = (
    "logo", "placeholder", "no-photo", "no_photo",
    "default-image", "default_image", "avatar",
    "favicon", "icon", "sprite", "pixel", "tracking",
)

BAD_REIFEN_TITLE_PATTERNS = [
    r"^über das unternehmen$",
    r"^unternehmen$",
    r"^kontakt$",
    r"^impressum$",
    r"^datenschutz$",
    r"^newsletter$",
    r"^sitemap$",
    r"^unermüdlich[- ]blog$",
    r"^unermüdlich[- ]blog\s*[|:-]",
    r"^der laufsport in zahlen$",
]

# Freshness tiers. Discovery may look back 14 days, but publication eligibility
# remains strict: normal 96h, important 7d, critical 14d.
IMPORTANT_EVENT_TERMS = [
    "investition", "investitionen", "ausbau", "erweiterung", "eröffnet",
    "eroeffnet", "neueröffnung", "neuroeffnung", "werk", "produktionskapazität",
    "produktionskapazitaet", "produktion", "baut aus", "erweitert",
    "betriebsrat", "ig metall", "tarifvertrag", "tarifverhandlungen",
    "arbeitsplätze", "arbeitsplaetze", "jobs", "stellen", "mitarbeiter",
    "quartalszahlen", "umsatz", "gewinn", "vorstand", "aufsichtsrat",
    "ceo", "strategie", "restrukturierung", "reorganisation", "umbau",
]

CRITICAL_EVENT_TERMS = [
    "stellenabbau", "entlassung", "entlassungen", "kündigung", "kuendigung",
    "arbeitsplatzabbau", "arbeitsplätze betroffen", "arbeitsplaetze betroffen",
    "schließung", "schliessung", "werksschließung", "werksschliessung",
    "werk wird geschlossen", "werk soll geschlossen", "produktion wird verlagert",
    "produktion soll verlagert", "verlagerung", "produktionsverlagerung",
    "produktionsstopp", "produktion eingestellt", "produktionsende",
    "insolvenz", "verkauf", "verkauft", "übernahme", "uebernahme",
    "carve-out", "spin-off", "restrukturierung", "massiver stellenabbau",
]

NEWS_HUB_PATTERNS = [
    r"\bcontinental news\b",
    r"\baktuelle nachrichten.*continental",
    r"\bnachrichten.*continental ag",
    r"\bpressemitteilungen.*continental ag",
    r"\bcontinental.*news.*heute",
    r"\bnews.*continental.*heute",
]

BAD_TITLE_PATTERNS = [
    r"\bcontinental breakfast\b",
    r"\bcontinental hotel\b",
    r"\bintercontinental\b",
    r"\bcontinental drift\b",
    r"\bcontinental divide\b",
    r"\bcontinental cup\b",
    r"\bcontinental championship\b",
    r"\bcontinental league\b",
    r"\brezept\b",
    r"\brecipe\b",
    r"\bhoroskop\b",
    r"\bhoroscope\b",
    r"\berror 500\b",
    r"\bserver error\b",
    r"\berror 404\b",
    r"\bpage not found\b",
    r"\bthat.?s an error\b",
    r"\bthere was an error\b",
    r"\bplease try again later\b",
    r"\bthat.?s all we know\b",
    r"\bbad gateway\b",
    r"\bservice unavailable\b",
    r"\baccess denied\b",
    r"\bforbidden\b",
]


# ============================================================
# TELEGRAM SECTIONS
# ============================================================

SECTIONS = {
    "plants": {"title": "🏭 Continental-Werke", "topic_env": "TOPIC_PLANTS_ID"},
    "tires": {"title": "🛞 Reifen", "topic_env": "TOPIC_TIRES_ID"},
    "people": {"title": "👥 Mitarbeiter & Jobs", "topic_env": "TOPIC_PEOPLE_ID"},
    "company": {"title": "📊 Management & Unternehmen", "topic_env": "TOPIC_COMPANY_ID"},
}


TOPIC_IDS = {
    "plants": 4,
    "tires": 5,
    "people": 6,
    "company": 7,
}


def get_topic_id(section_key: str) -> Optional[int]:
    raw = os.environ.get(SECTIONS[section_key]["topic_env"], "").strip()
    if raw:
        try:
            return int(raw)
        except ValueError:
            pass
    return TOPIC_IDS.get(section_key)


# ============================================================
# CONTINENTAL PLANTS
# ============================================================

PLANTS = [
    {"city": "Korbach", "country": "Germany", "country_de": "Deutschland", "flag": "🇩🇪", "priority": 1000,
     "aliases": ["korbach", "reifenwerk korbach", "continentalstrasse korbach", "continentalstraße korbach"]},
    {"city": "Lousado", "country": "Portugal", "country_de": "Portugal", "flag": "🇵🇹", "priority": 300,
     "aliases": ["lousado"]},
    {"city": "Otrokovice", "country": "Czech Republic", "country_de": "Tschechien", "flag": "🇨🇿", "priority": 300,
     "aliases": ["otrokovice"]},
    {"city": "Púchov", "country": "Slovakia", "country_de": "Slowakei", "flag": "🇸🇰", "priority": 300,
     "aliases": ["púchov", "puchov"]},
    {"city": "Sarreguemines", "country": "France", "country_de": "Frankreich", "flag": "🇫🇷", "priority": 300,
     "aliases": ["sarreguemines"]},
    {"city": "Timișoara", "country": "Romania", "country_de": "Rumänien", "flag": "🇷🇴", "priority": 300,
     "aliases": ["timișoara", "timisoara"]},
    {"city": "Cuenca", "country": "Ecuador", "country_de": "Ecuador", "flag": "🇪🇨", "priority": 250,
     "aliases": ["cuenca", "cuenca ecuador"]},
    {"city": "Camaçari", "country": "Brazil", "country_de": "Brasilien", "flag": "🇧🇷", "priority": 250,
     "aliases": ["camaçari", "camacari"]},
    {"city": "Clinton", "country": "USA", "country_de": "USA", "flag": "🇺🇸", "priority": 250,
     "aliases": ["clinton mississippi", "clinton ms"]},
    {"city": "Mount Vernon", "country": "USA", "country_de": "USA", "flag": "🇺🇸", "priority": 250,
     "aliases": ["mount vernon illinois", "mount vernon il"]},
    {"city": "Plymouth", "country": "USA", "country_de": "USA", "flag": "🇺🇸", "priority": 250,
     "aliases": ["plymouth indiana", "plymouth in"]},
    {"city": "Sumter", "country": "USA", "country_de": "USA", "flag": "🇺🇸", "priority": 250,
     "aliases": ["sumter south carolina", "sumter sc"]},
    {"city": "San Luis Potosí", "country": "Mexico", "country_de": "Mexiko", "flag": "🇲🇽", "priority": 250,
     "aliases": ["san luis potosí", "san luis potosi"]},
    {"city": "Hefei", "country": "China", "country_de": "China", "flag": "🇨🇳", "priority": 250,
     "aliases": ["hefei"]},
    {"city": "Kalutara", "country": "Sri Lanka", "country_de": "Sri Lanka", "flag": "🇱🇰", "priority": 250,
     "aliases": ["kalutara"]},
    {"city": "Modipuram", "country": "India", "country_de": "Indien", "flag": "🇮🇳", "priority": 250,
     "aliases": ["modipuram"]},
    {"city": "Petaling Jaya", "country": "Malaysia", "country_de": "Malaysia", "flag": "🇲🇾", "priority": 250,
     "aliases": ["petaling jaya"]},
    {"city": "Rayong", "country": "Thailand", "country_de": "Thailand", "flag": "🇹🇭", "priority": 250,
     "aliases": ["rayong"]},
    {"city": "Gqeberha", "country": "South Africa", "country_de": "Südafrika", "flag": "🇿🇦", "priority": 250,
     "aliases": ["gqeberha", "port elizabeth"]},
]


# ============================================================
# KEYWORDS
# ============================================================

COMPANY_TERMS = [
    "continental ag", "continental tires", "continental tyres",
    "continental reifen", "continental deutschland",
    "continental reifen deutschland", "continental automotive",
    "continental konzern", "continental group",
]

TIRE_TERMS = [
    "reifen", "tire", "tires", "tyre", "tyres",
    "winterreifen", "sommerreifen", "allseason", "all-season",
    "premiumcontact", "sportcontact", "ecocontact",
    "ultracontact", "vancontact", "fahrradreifen",
    "bicycle tire", "bicycle tyre",
]

PLANT_TERMS = [
    "werk", "werke", "factory", "factories", "plant",
    "production site", "manufacturing", "produktion",
    "produktionsstandort", "fertigung", "reifenwerk",
    "erweiterung", "expansion", "modernisierung",
    "modernization", "reconstruction", "umbau",
    "investition", "investment", "kapazität", "capacity",
    "produktionslinie", "production line", "standort",
]

PEOPLE_TERMS = [
    "mitarbeiter", "mitarbeitende", "beschäftigte", "arbeitnehmer",
    "arbeitsplatz", "arbeitsplätze", "stellenabbau", "job cuts",
    "layoff", "layoffs", "kündigung", "kündigungen", "kurzarbeit",
    "betriebsrat", "ig metall", "gewerkschaft", "tarifvertrag",
    "streik", "strike", "jobs", "job", "karriere", "career",
    "vacancy", "vacancies", "stellenangebot", "stellenangebote",
    "ausbildung", "azubi", "hiring", "recruitment", "recruiting",
    "neueinstellungen", "personal",
]

COMPANY_MANAGEMENT_TERMS = [
    "vorstand", "aufsichtsrat", "ceo", "cfo", "management",
    "geschäftsführung", "chairman", "geschäftsbericht",
    "jahresbericht", "annual report", "quartalszahlen",
    "quarterly results", "halbjahreszahlen", "umsatz", "revenue",
    "gewinn", "profit", "ebit", "ebitda", "dividende", "dividend",
    "aktionär", "aktionäre", "shareholder", "hauptversammlung",
    "annual general meeting", "investor", "investoren",
    "aktie", "shares", "stock", "prognose", "forecast", "guidance",
    "strategie", "strategy", "übernahme", "acquisition",
    "verkauf", "sale", "spin-off", "spinoff",
    "contitech", "aumiov", "automotive spin-off",
]

GERMANY_TERMS = [
    "deutschland", "germany", "german", "deutsche",
    "hannover", "hanover", "korbach", "hessen",
    "hamburg", "niedersachsen",
]

PREFERRED_SOURCE_DOMAINS = {
    "continental.com": 1400,
    "continental-tires.com": 1400,
    "continental-reifen.de": 1450,
    "jobs.continental.com": 1500,
    "reuters.com": 950,
    "handelsblatt.com": 930,
    "faz.net": 920,
    "sueddeutsche.de": 920,
    "tagesschau.de": 920,
    "wiwo.de": 910,
    "manager-magazin.de": 910,
    "automobilwoche.de": 910,
    "hessenschau.de": 1050,
    "hna.de": 1030,
    "reifenpresse.de": 1000,
}


# ============================================================
# HELPERS
# ============================================================

def load_json(path: Path, default: Any) -> Any:
    try:
        if not path.exists():
            return default
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_json(path: Path, value: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
    tmp.replace(path)


def _coerce_text(value: Any) -> str:
    """Convert messy RSS/JSON/HTML values into safe plain text."""
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, (int, float, bool)):
        return str(value)
    if isinstance(value, dict):
        # Prefer human-readable fields and avoid stringifying whole metadata blobs.
        preferred = ("text", "title", "name", "label", "value", "description",
                     "content", "summary", "city", "country", "url")
        parts = []
        for key in preferred:
            if key in value:
                part = _coerce_text(value.get(key))
                if part:
                    parts.append(part)
        if parts:
            return " ".join(parts)
        return " ".join(
            _coerce_text(v) for v in value.values()
            if isinstance(v, (str, int, float, bool))
        )
    if isinstance(value, (list, tuple, set)):
        return " ".join(_coerce_text(v) for v in value)
    return str(value)


def clean_text(value: Any) -> str:
    """Safely clean strings and tolerate malformed structured source fields."""
    text = _coerce_text(value)
    if not text:
        return ""
    try:
        text = html.unescape(text)
    except Exception:
        pass
    try:
        text = BeautifulSoup(text, "html.parser").get_text(" ", strip=True)
    except Exception:
        # A malformed field must never kill the whole candidate.
        text = re.sub(r"<[^>]+>", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def normalize_text(value: str) -> str:
    value = clean_text(value).lower()
    value = value.replace("’", "'").replace("ʼ", "'").replace("`", "'")
    value = re.sub(r"[^\w\s'\-äöüß]+", " ", value, flags=re.UNICODE)
    return re.sub(r"\s+", " ", value).strip()


def contains_any(text: str, terms: list[str]) -> bool:
    normalized = normalize_text(text)
    return any(normalize_text(term) in normalized for term in terms)


def hostname_from_url(url: str) -> str:
    try:
        return (urlparse(url).hostname or "").lower().lstrip("www.")
    except Exception:
        return ""


def domain_matches(host: str, domain: str) -> bool:
    return host == domain or host.endswith("." + domain)


def source_domain_allowed(url: str) -> bool:
    host = hostname_from_url(url)
    if not host:
        return False
    return not any(domain_matches(host, d) for d in BLOCKED_SOURCE_DOMAINS)


def source_score(url: str) -> int:
    host = hostname_from_url(url)
    for domain, score in PREFERRED_SOURCE_DOMAINS.items():
        if domain_matches(host, domain):
            return score
    return 500


def canonical_url(url: str) -> str:
    try:
        parsed = urlparse(url)
        scheme = parsed.scheme or "https"
        host = (parsed.hostname or "").lower().lstrip("www.")
        path = re.sub(r"/+", "/", parsed.path or "/").rstrip("/") or "/"
        return f"{scheme}://{host}{path}"
    except Exception:
        return (url or "").split("?", 1)[0].split("#", 1)[0].rstrip("/")


def source_quality(item: dict[str, Any]) -> int:
    return int(item.get("search_priority", 0)) + source_score(item.get("article_url") or item.get("google_url", ""))


def extract_job_key(title: str, url: str = "") -> str:
    m = re.search(r"\b(REF\d+[A-Z]?)\b", f"{title} {url}", flags=re.IGNORECASE)
    if m:
        return m.group(1).upper()
    return canonical_url(url)


def looks_like_bad_title(title: str) -> bool:
    text = normalize_text(title)
    return any(re.search(p, text, flags=re.IGNORECASE) for p in BAD_TITLE_PATTERNS)


def is_google_host(url: str) -> bool:
    host = hostname_from_url(url)
    return any(host == d or host.endswith("." + d) for d in GOOGLE_DOMAINS)


def detect_plant(text: str) -> Optional[dict[str, Any]]:
    normalized = normalize_text(text)
    for plant in sorted(PLANTS, key=lambda x: x["priority"], reverse=True):
        for alias in [plant["city"], *plant["aliases"]]:
            if normalize_text(alias) in normalized:
                return plant
    return None


def is_germany_related(text: str, plant: Optional[dict[str, Any]]) -> bool:
    if plant and plant["country"] == "Germany":
        return True
    return contains_any(text, GERMANY_TERMS)


def matched_event_families(text: str) -> set[str]:
    normalized = normalize_text(text)
    return {
        family for family, terms in EVENT_FAMILIES.items()
        if any(normalize_text(term) in normalized for term in terms)
    }


def is_stock_seo_filler(title: str, summary: str = "") -> bool:
    text = normalize_text(f"{title} {summary}")
    if not re.search(r"\bcontinental\b", text):
        return False
    if is_pure_stock_commentary(title, summary):
        return True
    return any(re.search(pattern, text, flags=re.IGNORECASE) for pattern in STOCK_SEO_FILLER_PATTERNS)


def is_stock_market_analysis(title: str, summary: str = "") -> bool:
    text = normalize_text(f"{title} {summary}")
    if not re.search(r"\bcontinental\b", text):
        return False
    return any(re.search(pattern, text, flags=re.IGNORECASE) for pattern in STOCK_MARKET_HARD_PATTERNS)


def relevance_score(title: str, summary: str, article_url: str = "") -> int:
    """Return a relevance score for information useful to Continental employees.

    v4.0 principle:
    - do not require the word "Continental" in the headline;
    - evaluate headline + RSS summary + fetched article text;
    - Korbach/local Continental reporting gets a strong boost;
    - trusted German media can qualify when the article body establishes the
      Continental connection;
    - official Continental domains are accepted with a lower content threshold;
    - generic "Continental" meanings (hotel, breakfast, airlines, etc.) are blocked.
    """
    if looks_like_bad_title(title):
        return -9999

    if is_stock_seo_filler(title, summary):
        return -9999

    if is_stock_market_analysis(title, summary):
        return -9999

    hub_text = normalize_text(f"{title} {summary}")
    if any(re.search(pattern, hub_text, flags=re.IGNORECASE) for pattern in NEWS_HUB_PATTERNS):
        return -9999

    text = clean_text(f"{title} {summary}")
    normalized = normalize_text(text)
    host = hostname_from_url(article_url)

    # Hard false-positive block for the word "Continental".
    if re.search(
        r"\bcontinental\s+(congress|breakfast|hotel|hotels|airlines?|divide|drift|cup|championship|league)\b",
        normalized,
    ):
        return -9999

    score = 0

    # Source trust.
    if domain_matches(host, "continental.com") or domain_matches(host, "continental-tires.com"):
        score += 110
    elif domain_matches(host, "continental-reifen.de"):
        score += 85
    elif domain_matches(host, "jobs.continental.com"):
        return 220 if "korbach" in normalized else -9999
    elif domain_matches(host, "hessenschau.de"):
        score += 18
    elif domain_matches(host, "tagesschau.de"):
        score += 20
    elif domain_matches(host, "hna.de"):
        score += 30
    elif domain_matches(host, "reifenpresse.de"):
        score += 35

    # Explicit company signals.
    strong_company_terms = [
        "continental ag", "continental reifen", "continental tires",
        "continental tyres", "continental reifen deutschland",
        "continental deutschland", "continental konzern",
        "continental group", "continental automotive", "continental tires deutschland",
        "continental deutschland gmbh", "continental reifen deutschland gmbh",
        "contitech",
    ]
    company_signal = contains_any(text, strong_company_terms)
    plain_continental = bool(re.search(r"\bcontinental\b", normalized))

    if company_signal:
        score += 100
    elif plain_continental:
        score += 48

    # Local/company context.
    plant = detect_plant(text)
    if plant:
        score += 30
        if plant["city"] == "Korbach":
            score += 105

    context_terms = TIRE_TERMS + PLANT_TERMS + PEOPLE_TERMS + COMPANY_MANAGEMENT_TERMS
    context_signal = contains_any(text, context_terms)
    if context_signal:
        score += 38

    # Strong event terms matter because they describe things employees care about.
    high_value_terms = [
        "stellenabbau", "arbeitsplätze", "arbeitsplaetze", "entlassung",
        "verlagerung", "schließung", "schliessung", "werksschließung",
        "werksschliessung", "produktion wird", "produktion soll",
        "investition", "investitionen", "ausbau", "erweiterung",
        "umbau", "restrukturierung", "reorganisation", "betriebsrat",
        "ig metall", "tarifvertrag", "tarifverhandlungen", "quartalszahlen",
        "jahreszahlen", "umsatz", "gewinn", "verlust", "vorstand",
        "aufsichtsrat", "neuer ceo", "neuer vorstand", "jobs", "arbeitsplätze",
    ]
    if contains_any(text, high_value_terms):
        score += 32

    # Korbach exception: a local article may omit Continental from the headline.
    # Require a meaningful Continental/plant/workforce/business context.
    if "korbach" in normalized:
        if plain_continental or "reifenwerk" in normalized or context_signal:
            score = max(score, 120)
        if high_value_terms and contains_any(text, high_value_terms):
            score += 35

    # Other identified Continental plants: if the article clearly names a plant
    # but not Continental, keep it only when there is substantial industrial context.
    if plant and plant["city"] != "Korbach" and not plain_continental:
        score -= 35

    # Official Reifen pages can contain useful material without the literal
    # company name in the title, but generic/lifestyle pages should stay out.
    if domain_matches(host, "continental-reifen.de"):
        path = urlparse(article_url).path.lower()
        useful_path = any(x in path for x in (
            "/stories/", "/products/", "/technology/", "/news/"
        ))
        if useful_path and (plain_continental or context_signal or contains_any(text, TIRE_TERMS)):
            score += 30

    # v8.2 relevance calibration:
    # Useful Continental tyre/product stories can legitimately score in the
    # mid-40s/50s. The queue gate is now 45, while hard junk/stock filters
    # remain active. Strong factory/product/technology signals receive boosts.
    # v5.10.6: concrete product/OE launches are high-value news even when
    # the publisher uses a brand/model headline that produces a modest base score.
    product_terms = [
        "contitread", "new tire", "new tyre", "new product", "product launch",
        "reifenneuheit", "neuer reifen", "neue reifengeneration",
        "erstausrüstung", "erstausruestung", "oe approval", "oe-approval",
        "original equipment", "freigabe für", "freigabe fuer", "approvals for",
        "audi q3", "volkswagen id. polo", "id. polo",
    ]
    if contains_any(text, product_terms):
        score += 28
    if contains_any(text, ("launch", "launched", "released", "vorgestellt", "präsentiert", "praesentiert", "introduced", "expands portfolio")):
        score += 12

    specific_tire_terms = [
        "spezialreifen", "spezialreifen", "steinbruch", "gewinnungsindustrie",
        "lkw-reifen", "nutzfahrzeugreifen", "truckreifen", "pkw-reifen",
        "reifenneuheit", "konzeptreifen", "reifenentwicklung", "reifentechnologie",
        "neuer reifen", "neue reifengeneration", "reifeninnovation",
        "profil", "laufleistung", "rollwiderstand", "reifentest",
        "reifenproduktion", "reifenerprobung",
    ]
    if contains_any(text, specific_tire_terms):
        score += 18

    # A concrete company/product action in an authoritative Continental tyre
    # source deserves a small additional bump, while generic/lifestyle pages
    # remain governed by the normal content signals above.
    if (domain_matches(host, "continental-reifen.de") and
            contains_any(text, (
                "reifen", "reifentechnologie", "spezialreifen",
                "konzeptreifen", "reifentest", "reifenproduktion",
            ))):
        score += 8

    # v5.10.1: news-first calibration. Concrete factory/production stories
    # and real tyre/product launches must outrank generic company mentions.
    if plant:
        score += 20
    if contains_any(text, (
        "produktion", "production", "fertigung", "manufacturing",
        "produktionslinie", "production line", "produktionsanlage",
        "production facility", "manufacturing plant", "manufacturing site",
        "factory", "plant", "tire plant", "tyre plant",
        "kapazität", "kapazitaet", "capacity", "capacity expansion",
        "investition", "investment", "ausbau", "expansion",
    )):
        score += 15
    if contains_any(text, (
        "neuer reifen", "neue reifengeneration", "reifenneuheit",
        "new tire", "new tyre", "new product", "new tire line",
        "tyre launch", "tire launch", "expands portfolio",
        "erweitert das portfolio", "portfolioerweiterung",
    )):
        score += 20
    if "650" in text and contains_any(text, ("dimension", "dimensionen", "sizes", "größen", "groessen", "portfolio", "uhp")):
        score += 32
    if contains_any(text, ("uhp", "ultra high performance", "high performance tire", "high performance tyre")):
        score += 14

    # v4.1: expose a stable 0–100 relevance scale while keeping the
    # underlying weighted scoring model. The score is intentionally capped so
    # logs, queue ranking and future thresholds remain easy to understand.
    if score <= 0:
        return score
    return min(100, round(score / 2))


def is_continental_relevant(title: str, summary: str, article_url: str = "") -> bool:
    if is_stock_seo_filler(title, summary) or is_stock_market_analysis(title, summary):
        return False
    hub_text = normalize_text(f"{title} {summary}")
    if any(re.search(pattern, hub_text, flags=re.IGNORECASE) for pattern in NEWS_HUB_PATTERNS):
        return False
    score = relevance_score(title, summary, article_url)
    host = hostname_from_url(article_url)
    text = normalize_text(f"{title} {summary}")

    # v8.1: editorial class is decided BEFORE the generic relevance gate.
    # v8.0 had PRODUCTION_MIN_RELEVANCE=35, but production stories were still
    # rejected here at 50/55 before classify_item() ever ran. That made the
    # lower production threshold ineffective.
    strong_production_terms = [
        "produktion", "produktionslinie", "produktionsanlage",
        "produktionskapazität", "produktionskapazitaet", "fertigung",
        "fertigungslinie", "manufacturing", "production line",
        "production facility", "manufacturing plant", "manufacturing site",
        "tire plant", "tyre plant", "factory", "plant investment",
        "capacity", "kapazität", "kapazitaet", "kapazitätsausbau",
        "capacity expansion", "investition", "investitionen", "investment", "ausbau",
        "erweiterung", "expansion", "modernisierung", "verlagerung",
        "produktionsverlagerung", "production relocation", "großreifen",
        "grossreifen", "large tires", "large tyres", "hochlauf",
        "anlauf der produktion", "neue anlage", "neue produktionslinie",
    ]
    tire_tech_terms = [
        "neuer reifen", "neue reifen", "reifengeneration", "reifenneuheit",
        "reifenentwicklung", "reifentechnologie", "reifeninnovation",
        "new tire", "new tyre", "new tire line", "new tyre line",
        "tire launch", "tyre launch", "smart tire", "smart tyre",
        "conticonnect", "concept tire", "concept tyre", "recycling",
        "recycled materials", "recyclinganteil", "oem tire", "oem tyre",
        "truck tire", "truck tires", "truck tyre", "truck tyres",
        "regional truck tire", "regional truck tires", "regional truck tyre",
        "regional truck tyres", "lkw-reifen", "lkw reifen", "introduces new",
        "introduces", "launches", "launched", "introduced",
        "uhp", "ultra high performance", "new dimensions", "dimensionen",
        "650", "portfolio expansion", "portfolioerweiterung",
    ]
    korbach_signal = "korbach" in text
    production_signal = contains_any(text, strong_production_terms)
    tire_tech_signal = contains_any(text, tire_tech_terms)
    explicit_continental = bool(re.search(r"\bcontinental\b", text)) or "continental reifen" in text

    if domain_matches(host, "jobs.continental.com"):
        return score >= 90

    # Official sources can publish technical/product material with a compact
    # headline and little body text, so category-specific floors are used.
    if domain_matches(host, "continental.com") or domain_matches(host, "continental-tires.com"):
        if korbach_signal and production_signal:
            return score >= KORBACH_PRODUCTION_MIN_RELEVANCE
        if production_signal:
            return score >= PRODUCTION_MIN_RELEVANCE
        if tire_tech_signal:
            return score >= TIRE_TECH_MIN_RELEVANCE
        return score >= 50
    if domain_matches(host, "continental-reifen.de"):
        if korbach_signal and production_signal:
            return score >= KORBACH_PRODUCTION_MIN_RELEVANCE
        if production_signal:
            return score >= PRODUCTION_MIN_RELEVANCE
        if tire_tech_signal:
            return score >= TIRE_TECH_MIN_RELEVANCE
        return score >= 50

    # Local German reporting: Korbach production stories are the most valuable
    # local signal and are allowed at the production floor when Continental or
    # Reifenwerk context is present.
    if korbach_signal:
        local_signal = (
            explicit_continental
            or "reifenwerk" in text
            or ("reifen" in text and contains_any(text, PLANT_TERMS + PEOPLE_TERMS))
        )
        if local_signal:
            if production_signal:
                return score >= KORBACH_PRODUCTION_MIN_RELEVANCE
            if tire_tech_signal:
                return score >= TIRE_TECH_MIN_RELEVANCE
            return score >= 50

    # National/international media: explicit Continental plus a concrete event
    # gets a lower editorial floor than generic company mentions.
    if explicit_continental and production_signal:
        return score >= PRODUCTION_MIN_RELEVANCE
    if explicit_continental and tire_tech_signal:
        return score >= TIRE_TECH_MIN_RELEVANCE
    return score >= 55 and explicit_continental


# ============================================================
# SEARCH
# ============================================================

def google_rss_url(query: str, language: str = "de", country: str = "DE") -> str:
    return (
        "https://news.google.com/rss/search?"
        f"q={quote(query)}"
        f"&hl={language}"
        f"&gl={country}"
        f"&ceid={country}:{language}"
    )


def now_utc_minus_hours(hours: int) -> datetime:
    return datetime.now(timezone.utc) - timedelta(hours=hours)


def parse_entry_datetime(entry: Any) -> Optional[datetime]:
    st = getattr(entry, "published_parsed", None) or getattr(entry, "updated_parsed", None)
    if not st:
        return None
    try:
        return datetime(*st[:6], tzinfo=timezone.utc)
    except Exception:
        return None


def entry_source_name(entry: Any) -> str:
    source = getattr(entry, "source", None)
    if source is not None:
        title = getattr(source, "title", "") or ""
        return clean_text(title)
    return ""


def entry_description(entry: Any) -> str:
    value = getattr(entry, "summary", "") or getattr(entry, "description", "") or ""
    return clean_text(value)


def build_queries() -> list[tuple[str, str, str, int]]:
    """German discovery layer.

    Direct official/RSS sources remain primary. Google News is deliberately
    broader in v4.0 so important employee-facing stories are not lost because
    Continental is absent from the headline.
    """
    queries: list[tuple[str, str, str, int]] = []

    primary = [
        ('"Continental" Korbach', 1350),
        ('"Korbach" Reifenwerk', 1450),
        ('"Korbach" Reifenproduktion', 1420),
        ('"Korbach" Verlagerung Reifen', 1480),
        ('"Korbach" Stellenabbau Continental', 1460),
        ('"Korbach" Betriebsrat Reifen', 1420),
        ('"Continental" Korbach Reifenwerk', 1380),
        ('"Continental" Korbach Produktion', 1360),
        ('"Continental" Korbach Mitarbeiter', 1340),
        ('"Continental" Korbach Betriebsrat', 1360),
        ('"Continental" Korbach IG Metall', 1360),
        ('"Continental" Korbach Verlagerung', 1400),
        ('"Continental" Korbach Schließung OR Schliessung', 1400),
        ('"Continental" Korbach Investition', 1350),
        ('"Continental Reifen" Korbach', 1350),
        ('"Reifenwerk Korbach" Continental', 1350),
        ('"Continental" Deutschland Werk Produktion', 1080),
        ('"Continental" Deutschland Stellenabbau', 1100),
        ('"Continental" Deutschland Verlagerung', 1120),
        ('"Continental" Deutschland Betriebsrat OR IG Metall', 1080),
        ('"Continental" Vorstand OR Aufsichtsrat', 1050),
        ('"Continental" Quartalszahlen OR Umsatz OR Gewinn', 1050),
        ('"Continental" Reifen Produktion Werk Investition', 1080),
        ('"Continental" Reifen neue Technologie', 980),
        ('"Continental" Werk Schließung OR Verlagerung', 1100),
        ('"Continental" Werk Produktion Fertigung', 1180),
        ('"Continental" Reifenwerk Produktion Fertigung', 1320),
        ('"Continental" Reifenwerk Kapazität', 1280),
        ('"Continental" Reifenwerk Investition', 1280),
        ('"Continental" Produktionslinie Reifen', 1260),
        ('"Continental" Produktionskapazität Reifen', 1260),
        ('"Continental" Großreifen Produktion', 1240),
        ('"Continental" Reifen Produktion Sensor', 1160),
        ('"Continental" Reifenwerk Ausbau', 1240),
    ]
    for query, priority in primary:
        queries.append((query, "de", "DE", priority))

    plant_queries = [
        ('"Continental" Lousado Reifenwerk', 900),
        ('"Continental" Puchov Reifenwerk', 900),
        ('"Continental" Otrokovice Reifenwerk', 900),
        ('"Continental" Timisoara Reifenwerk', 900),
        ('"Continental" Sarreguemines Reifenwerk', 900),
        ('"Continental" Rayong Reifenwerk', 920),
        ('"Continental" Hefei Reifenwerk', 900),
        ('"Continental" Modipuram Reifenwerk', 900),
        ('"Continental" Camaçari Reifenwerk', 900),
        ('"Continental" San Luis Potosi Reifenwerk', 900),
        ('"Continental" Mount Vernon Reifenwerk', 900),
        ('"Continental" Sumter Reifenwerk', 900),
    ]
    for query, priority in plant_queries:
        queries.append((query, "de", "DE", priority))

    # Broad Continental / tyre / company-life discovery. These are deliberately
    # wider than Korbach so the bot can surface interesting company, tyre,
    # technology, motorsport, sustainability and product stories.
    broad_queries = [
        ('"Continental" Reifen', 1030),
        ('"Continental Reifen" Technologie', 1020),
        ('"Continental" Reifen Neuheit', 1020),
        ('"Continental" Reifen Test', 980),
        ('"Continental" Reifen Innovation', 1010),
        ('"Continental" Nutzfahrzeugreifen', 1010),
        ('"Continental" Lkw Reifen', 1000),
        ('"Continental" Pkw Reifen', 980),
        ('"Continental" Werksführung', 980),
        ('"Continental" Werk Mitarbeiter', 1000),
        ('"Continental" Produktion', 1000),
        ('"Continental" Werk Investition', 1010),
        ('"Continental" Nachhaltigkeit', 940),
        ('"Continental" Elektromobilität Reifen', 960),
        ('"Continental" Motorsport Reifen', 920),
        ('"Continental" Truck Reifen', 1000),
        ('"Continental" Truck Show', 930),
        ('"Continental" Messe Reifen', 930),
        ('"Continental" Steinexpo', 1200),
        ('"Continental" Unermüdlich', 1250),
    ]
    for query, priority in broad_queries:
        queries.append((query, "de", "DE", priority))

    # Source-oriented searches are useful when Google News has indexed a
    # German publisher but the publisher's own RSS feed did not expose the item.
    source_queries = [
        ('site:reuters.com Continental Germany', 1050),
        ('site:reuters.com Continental Korbach', 1200),
        ('site:handelsblatt.com Continental', 1050),
        ('site:faz.net Continental', 1020),
        ('site:sueddeutsche.de Continental', 1020),
        ('site:wiwo.de Continental', 1010),
        ('site:manager-magazin.de Continental', 1010),
        ('site:automobilwoche.de Continental', 1040),
        ('site:hna.de Continental Korbach', 1450),
        ('site:hna.de Reifenwerk Korbach', 1450),
        ('site:hna.de Korbach Reifen Produktion', 1400),
        ('site:reifenpresse.de Continental Korbach', 1260),
        ('site:reifenpresse.de Continental Reifen Deutschland', 1120),
        ('site:reifenpresse.de Continental Reifenwerk', 1080),
        ('site:hessenschau.de Continental Korbach', 1320),
        ('site:hessenschau.de Korbach Reifen Continental', 1320),
        ('site:tagesschau.de Continental Reifen', 1040),
        ('site:tagesschau.de Continental Deutschland', 1040),
        ('site:automobilwoche.de Continental Reifenwerk', 1060),
        ('site:automobilwoche.de Continental Produktion', 1060),
        ('site:profi-werkstatt.net Continental Reifen', 980),
        ('site:tyrepress.com Continental Korbach', 1080),
    ]
    for query, priority in source_queries:
        queries.append((query, "de", "DE", priority))

    # International discovery fallback. Continental news is frequently
    # published first in English by tyre, fleet, manufacturing and automotive
    # media and never appears in the German Google News result set. Keep this
    # layer compact so it adds coverage without doubling the runtime.
    international_queries = [
        ("Continental Tires", 1040),
        ("Continental tyre", 1020),
        ("Continental tire technology", 1010),
        ("Continental tire new product", 1030),
        ("Continental tire test", 980),
        ("Continental factory production", 1160),
        ("Continental tire factory production", 1180),
        ("Continental tire plant production", 1180),
        ("Continental manufacturing plant tires", 1160),
        ("Continental tire production capacity", 1160),
        ("Continental tire plant investment", 1140),
        ("Continental large tire production", 1120),
        ("Continental truck tire production", 1100),
        ("Continental smart tire production", 1080),
        ("Continental plant investment", 1010),
        ("Continental workers jobs restructuring", 1080),
        ("Continental tire relocation", 1120),
        ("Continental OEM tires", 980),
        ("Continental motorsport tires", 940),
        ("Continental sustainability tires", 940),
    ]
    for query, priority in international_queries:
        queries.append((query, "en", "US", priority))

    return queries


def decode_google_url(url: str) -> Optional[str]:
    """Resolve a Google News RSS article URL to the publisher URL.

    googlenewsdecoder 0.2.x returns a dict with ``success=True`` (and may
    also expose ``status`` in other versions).  Older code checked only
    ``status`` and therefore silently rejected almost every Google News
    candidate as ``invalid_or_google_url``.
    """
    if not url:
        return None
    if "news.google.com/rss/articles/" not in url:
        return url
    if gnewsdecoder is None:
        print("⚠️ googlenewsdecoder не встановлений")
        return None
    try:
        result = gnewsdecoder(url, interval=GOOGLE_DECODE_DELAY)
        if isinstance(result, dict):
            decoded = result.get("decoded_url") or result.get("url") or result.get("original_url")
            success = result.get("success")
            status = result.get("status")
            if decoded and (success is True or status is True or status == "success" or not ("success" in result or "status" in result)):
                return decoded
            # Some releases return a useful URL even when the success flag is
            # represented differently.  A non-Google URL is still safe to
            # validate later through fetch_article()/source_domain_allowed().
            if decoded and not is_google_host(str(decoded)):
                return str(decoded)
            print(f"⚠️ Google News decode unsuccessful: {result}")
        elif isinstance(result, str):
            decoded = result.strip()
            if decoded and not is_google_host(decoded):
                return decoded
    except Exception as exc:
        print(f"⚠️ decode error: {exc}")
    return None


def _extract_xml_locs(xml_text: str) -> list[str]:
    soup = BeautifulSoup(xml_text, "xml")
    return [clean_text(tag.get_text()) for tag in soup.find_all("loc") if clean_text(tag.get_text())]


def _story_urls_from_sitemaps(limit: int = 80) -> list[str]:
    found: list[str] = []
    visited: set[str] = set()
    queue = list(CONTINENTAL_REIFEN_SITEMAP_URLS)
    while queue and len(found) < limit:
        sitemap = queue.pop(0)
        if sitemap in visited:
            continue
        visited.add(sitemap)
        try:
            r = requests.get(sitemap, headers=HEADERS, timeout=REQUEST_TIMEOUT)
            if r.status_code != 200:
                continue
            for loc in _extract_xml_locs(r.text):
                low = loc.lower()
                if low.endswith('.xml') and loc not in visited and len(queue) < 30:
                    queue.append(loc)
                elif (('/about-us/stories/' in low and loc.rstrip('/') != CONTINENTAL_REIFEN_STORIES_URL.rstrip('/'))
                      or '/products/truck/unermuedlich-blog/' in low):
                    if loc not in found:
                        found.append(loc)
                        if len(found) >= limit:
                            break
        except Exception:
            continue
    return found


def _story_page_metadata(url: str) -> tuple[str, str, Optional[datetime]]:
    try:
        r = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT, allow_redirects=True)
        if r.status_code >= 400 or 'text/html' not in r.headers.get('content-type', '').lower():
            return '', '', None
        title = extract_original_title(r.text)
        summary, _ = extract_article_data(r.text, r.url)
        dt = extract_original_published_datetime(r.text)
        return title, summary, dt
    except Exception:
        return '', '', None


def fetch_official_unermuedlich_blog(cutoff: datetime) -> list[dict[str, Any]]:
    """Direct discovery for Continental Reifen's Unermüdlich blog.

    This source is intentionally separate from /about-us/stories/ because
    important tyre/truck/company-life articles live under /products/truck/.
    """
    results: list[dict[str, Any]] = []
    urls: list[str] = []
    card_data: dict[str, tuple[str, str, Optional[datetime]]] = {}
    print(f"🛞 Direkt: Continental Unermüdlich-Blog {CONTINENTAL_UNERMUEDLICH_URL}")
    try:
        r = requests.get(CONTINENTAL_UNERMUEDLICH_URL, headers=HEADERS, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
    except Exception as exc:
        print(f"⚠️ Unermüdlich-Blog nicht lesbar: {exc}")
        return results

    for a in soup.find_all("a", href=True):
        href = urljoin(r.url, a.get("href", "")).split("#", 1)[0]
        if hostname_from_url(href) != hostname_from_url(CONTINENTAL_UNERMUEDLICH_URL):
            continue
        path_low = urlparse(href).path.lower()
        if href.rstrip("/") == CONTINENTAL_UNERMUEDLICH_URL.rstrip("/") or path_low.endswith(".pdf"):
            continue
        if "/products/truck/unermuedlich-blog/" not in path_low:
            continue
        if href not in urls:
            urls.append(href)
        title = clean_text(a.get_text(" ", strip=True))
        container = a
        context = ""
        for _ in range(6):
            container = getattr(container, "parent", None)
            if not container:
                break
            context = clean_text(container.get_text(" ", strip=True))
            if re.search(r"20\d{2}[./-]\d{2}[./-]\d{2}", context):
                break
        dt = None
        m = re.search(r"(20\d{2})[./-](\d{2})[./-](\d{2})", context)
        if m:
            try:
                dt = datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), tzinfo=GERMANY_TZ).astimezone(timezone.utc)
            except Exception:
                dt = None
        card_data[href] = (title, context[:1200], dt)

    for url in _story_urls_from_sitemaps(limit=120):
        if "/products/truck/unermuedlich-blog/" in url.lower() and url not in urls:
            urls.append(url)

    story_cutoff = datetime.now(timezone.utc) - timedelta(hours=STORIES_LOOKBACK_HOURS)
    seen: set[str] = set()
    for url in urls[:120]:
        if url in seen:
            continue
        seen.add(url)
        card_title, card_summary, card_dt = card_data.get(url, ("", "", None))
        title, summary, page_dt = _story_page_metadata(url)
        dt = page_dt or card_dt
        title = title or card_title
        summary = summary or card_summary
        if (not title or looks_like_bad_title(title) or not dt or dt < story_cutoff):
            continue
        results.append({
            "title": title,
            "summary": summary,
            "google_url": url,
            "source_name": "Continental Reifen – Unermüdlich",
            "published_at": dt.isoformat(),
            "search_priority": 1900,
            "found_at": datetime.now(timezone.utc).isoformat(),
            "direct_source": True,
        })
    print(f"   Frische Unermüdlich-Artikel: {len(results)}")
    return results


def fetch_official_reifen_stories(cutoff: datetime) -> list[dict[str, Any]]:
    """Robust direct discovery for continental-reifen.de Stories.

    1) collect links from the listing page;
    2) use card date when present;
    3) open the story page and read datePublished/time/meta;
    4) use sitemap discovery as fallback.
    """
    results: list[dict[str, Any]] = []
    urls: list[str] = []
    card_data: dict[str, tuple[str, str, Optional[datetime]]] = {}
    print(f"🛞 Official Stories direkt: {CONTINENTAL_REIFEN_STORIES_URL}")

    try:
        response = requests.get(CONTINENTAL_REIFEN_STORIES_URL, headers=HEADERS, timeout=REQUEST_TIMEOUT)
        response.raise_for_status()
        soup = BeautifulSoup(response.text, "html.parser")
        for a in soup.find_all("a", href=True):
            href = urljoin(response.url, a.get("href", "")).split("#", 1)[0]
            if hostname_from_url(href) != hostname_from_url(CONTINENTAL_REIFEN_STORIES_URL):
                continue
            path_low = urlparse(href).path.lower()
            if (href.rstrip("/") == CONTINENTAL_REIFEN_STORIES_URL.rstrip("/") or
                    path_low in {"/", "/about-us/", "/products/"} or
                    path_low.endswith(".pdf")):
                continue
            if not any(seg in path_low for seg in ("/about-us/stories/", "/products/", "/technology/", "/news/")):
                continue
            if href not in urls:
                urls.append(href)
            title = clean_text(a.get_text(" ", strip=True))
            container = a
            context = ''
            for _ in range(5):
                container = getattr(container, 'parent', None)
                if not container:
                    break
                context = clean_text(container.get_text(" ", strip=True))
                if re.search(r"20\d{2}[./-]\d{2}[./-]\d{2}", context):
                    break
            dt = None
            m = re.search(r"(20\d{2})[./-](\d{2})[./-](\d{2})", context)
            if m:
                try:
                    dt = datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), tzinfo=GERMANY_TZ).astimezone(timezone.utc)
                except Exception:
                    dt = None
            card_data[href] = (title, context[:900], dt)
    except Exception as exc:
        print(f"⚠️ Stories-Liste nicht lesbar: {exc}")

    # Sitemap fallback also catches stories not rendered server-side on the listing.
    for url in _story_urls_from_sitemaps():
        if url not in urls:
            urls.append(url)

    seen: set[str] = set()
    for url in urls[:80]:
        if url in seen:
            continue
        seen.add(url)
        card_title, card_summary, card_dt = card_data.get(url, ('', '', None))
        title, summary, page_dt = _story_page_metadata(url)
        dt = page_dt or card_dt
        title = title or card_title
        summary = summary or card_summary
        story_cutoff = datetime.now(timezone.utc) - timedelta(hours=STORIES_LOOKBACK_HOURS)
        if (not title or looks_like_bad_title(title) or
                any(re.search(p, normalize_text(title), flags=re.IGNORECASE) for p in BAD_REIFEN_TITLE_PATTERNS) or
                not dt or dt < story_cutoff):
            continue
        results.append({
            "title": title,
            "summary": summary,
            "google_url": url,
            "source_name": "Continental Reifen",
            "published_at": dt.isoformat(),
            "search_priority": 1700,
            "found_at": datetime.now(timezone.utc).isoformat(),
            "direct_source": True,
        })
        time.sleep(0.05)

    print(f"   Frische offizielle Reifen-Stories: {len(results)}")
    return results


def fetch_hna_korbach(cutoff: datetime) -> list[dict[str, Any]]:
    """Directly crawl HNA's Korbach section. This is a high-value local source.

    HNA does not need to expose a public RSS feed for us to discover the local
    listing. We use the section page as discovery, then open the original article
    for title/date/body/image validation.
    """
    results: list[dict[str, Any]] = []
    print(f"📰 Direkt: HNA Korbach {HNA_KORBACH_URL}")
    try:
        r = requests.get(HNA_KORBACH_URL, headers=HEADERS, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")
    except Exception as exc:
        print(f"⚠️ HNA Korbach nicht lesbar: {exc}")
        return results

    urls: list[str] = []
    for a in soup.find_all("a", href=True):
        href = urljoin(r.url, a.get("href", "")).split("#", 1)[0]
        if hostname_from_url(href) != "hna.de":
            continue
        path = urlparse(href).path.lower()
        if not path.endswith(".html") or "/lokales/" not in path:
            continue
        title = clean_text(a.get_text(" ", strip=True))
        if len(title) < 12 or href in urls:
            continue
        urls.append(href)

    checked = 0
    for url in urls[:80]:
        final_url, article_text, _, original_title, original_dt = fetch_article(url)
        if not final_url:
            continue
        checked += 1
        title = original_title or ""
        if not title or looks_like_bad_title(title):
            continue
        dt = original_dt
        if not dt or dt < cutoff:
            continue
        combined = f"{title} {article_text}"
        # HNA is local discovery: only keep Korbach + meaningful Continental
        # plant/tire/workforce/business context. Ordinary city news is ignored.
        normalized = normalize_text(combined)
        if "korbach" not in normalized:
            continue
        if not (re.search(r"\bcontinental\b", normalized) or
                "reifenwerk" in normalized or
                ("reifen" in normalized and contains_any(normalized, PLANT_TERMS + PEOPLE_TERMS)) or
                contains_any(normalized, ["contitech", "industrireifen", "vollgummireifen"])):
            continue
        results.append({
            "title": title,
            "summary": article_text[:1200],
            "google_url": final_url,
            "source_name": "HNA",
            "published_at": dt.isoformat(),
            "search_priority": 1500,
            "found_at": datetime.now(timezone.utc).isoformat(),
            "direct_source": True,
        })
    print(f"   HNA-Korbach relevant: {len(results)} | Artikel geprüft: {checked}")
    return results


def fetch_direct_media_rss(cutoff: datetime) -> list[dict[str, Any]]:
    """Read original articles before applying Continental relevance.

    This fixes the common case where a local article headline does not mention
    Continental but the body clearly reports on the Korbach plant, employees,
    production or restructuring.
    """
    results: list[dict[str, Any]] = []
    for feed_url, source_name, priority in DIRECT_MEDIA_RSS:
        print(f"📰 Direkt-RSS: {source_name}")
        try:
            feed = feedparser.parse(feed_url)
        except Exception as exc:
            print(f"⚠️ Direkt-RSS Fehler: {exc}")
            continue
        relevant = 0
        checked = 0
        for entry in feed.entries[:60]:
            dt = parse_entry_datetime(entry)
            if not dt or dt < cutoff:
                continue
            title = clean_text(getattr(entry, 'title', ''))
            link = getattr(entry, 'link', '') or ''
            summary = entry_description(entry)
            if not title or not link or looks_like_bad_title(title):
                continue
            checked += 1

            # Open the original page first. For Hessenschau/Nordhessen this is
            # especially important because local headlines often omit the company name.
            final_url, article_text, _, original_title, original_dt = fetch_article(link)
            if not final_url:
                continue
            real_title = original_title if original_title and not looks_like_bad_title(original_title) else title
            real_dt = original_dt or dt
            combined = f"{real_title} {summary} {article_text}"
            if real_dt < cutoff or not is_continental_relevant(real_title, combined, final_url):
                continue

            relevant += 1
            results.append({
                "title": real_title,
                "summary": article_text[:1200] or summary,
                "google_url": final_url,
                "source_name": source_name,
                "published_at": real_dt.isoformat(),
                "search_priority": priority,
                "found_at": datetime.now(timezone.utc).isoformat(),
                "direct_source": True,
            })
            time.sleep(SOURCE_PAGE_DELAY)
        print(f"   relevant: {relevant} | Artikel geprüft: {checked}")
    return results


def _collect_job_links_from_html(html: str, base_url: str) -> list[str]:
    """Extract official Continental job-detail URLs from a portal/career page."""
    soup = BeautifulSoup(html, "html.parser")
    links: list[str] = []
    seen: set[str] = set()
    for a in soup.find_all("a", href=True):
        href = urljoin(base_url, a.get("href", "")).split("#", 1)[0]
        host = hostname_from_url(href)
        if host != OFFICIAL_JOBS_DOMAIN:
            continue
        if "/detail-page/job-detail/" not in href:
            continue
        href = canonical_url(href)
        if href not in seen:
            seen.add(href)
            links.append(href)
    return links


def candidate_age_hours(candidate: dict[str, Any], now_utc: Optional[datetime] = None) -> Optional[float]:
    """Return candidate age in hours from its discovery/publication timestamp.

    This helper is deliberately tolerant because Google News/feeds can provide
    either ``published_at`` or a fallback discovery timestamp. A malformed or
    missing timestamp returns None instead of ever crashing candidate processing.
    """
    if candidate.get("is_job"):
        return None

    now_utc = now_utc or datetime.now(timezone.utc)
    raw_values = (
        candidate.get("published_at"),
        candidate.get("discovery_published_at"),
        candidate.get("found_at"),
    )

    for raw in raw_values:
        if not raw:
            continue
        try:
            dt = datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            age = (now_utc - dt.astimezone(timezone.utc)).total_seconds() / 3600
            return round(max(0.0, age), 1)
        except (TypeError, ValueError, OverflowError):
            continue

    return None


def freshness_limit_hours(candidate: dict[str, Any]) -> int:
    """Publication freshness by editorial topic.

    - Normal company news: 48h.
    - Product/tyre/technology: 14d.
    - Factory/production/investment: 7d.
    - strategic Korbach restructuring/relocation/closure/investment: 60d; ordinary Korbach production: 7d.
    """
    text = normalize_text(
        f"{candidate.get('title', '')} {candidate.get('summary', '')} {candidate.get('article_text', '')}"
    )

    # Korbach is the primary factory for this channel. Strategic plant events
    # (closure, relocation, job impact, restructuring, major investment) remain
    # publishable for 60 days so an important event is not lost after 7 days.
    if "korbach" in text and contains_any(text, KORBACH_STRATEGIC_TERMS):
        return KORBACH_STRATEGIC_MAX_AGE_HOURS

    if "korbach" in text and contains_any(text, [
        "reifenwerk", "werk", "produktion", "produktions", "fertigung",
        "factory", "plant", "manufacturing", "investition", "ausbau",
        "kapazität", "kapazitaet", "windpark", "verlagerung", "produktion",
    ]):
        return CRITICAL_NEWS_MAX_AGE_HOURS

    if contains_any(text, CRITICAL_EVENT_TERMS):
        return CRITICAL_NEWS_MAX_AGE_HOURS

    factory_terms = PLANT_TERMS + [
        'werk', 'factory', 'plant', 'produktionsanlage', 'produktion',
        'production', 'manufacturing', 'fertigung', 'produktionskapazitaet',
        'produktionskapazität', 'kapazität', 'kapazitaet', 'capacity',
        'investition', 'investitionen', 'investment', 'investments',
        'ausbau', 'erweiterung', 'expansion', 'modernisierung',
        'modernization', 'groundbreaking', 'baut aus', 'erweitert',
    ]
    if contains_any(text, factory_terms):
        return FACTORY_NEWS_MAX_AGE_HOURS

    durable_terms = TIRE_TERMS + [
        'technologie', 'technology', 'innovation', 'innovationen',
        'concept tire', 'concept tyre', 'konzeptreifen', 'recycling',
        'recycled', 'recycelt', 'oem', 'oe-approval', 'oe approval',
        'erstausrüstung', 'erstausruestung', 'freigabe', 'approvals',
        'approval', 'test', 'testing', 'all-season', 'suv', 'pkw',
        'truck', 'lkw', 'bus', 'motorsport', 'sustainability',
        'nachhaltigkeit', 'new tire', 'new tyre', 'new product',
        'new tire line', 'tire launch', 'tyre launch', 'reifenneuheit',
        'reifentest', 'reifenentwicklung', 'reifeninnovation',
    ]
    if contains_any(text, durable_terms):
        return IMPORTANT_NEWS_MAX_AGE_HOURS

    host = hostname_from_url(candidate.get('article_url', '') or candidate.get('google_url', ''))
    if (domain_matches(host, 'continental.com')
            or domain_matches(host, 'continental-tires.com')
            or domain_matches(host, 'continental-reifen.de')):
        return OFFICIAL_CONTENT_MAX_AGE_HOURS

    return NORMAL_NEWS_MAX_AGE_HOURS

def candidate_fresh_enough(candidate: dict[str, Any], now_utc: Optional[datetime] = None) -> bool:
    """Apply the editorial freshness tiers: 48h normal, 7d factory, 14d tyre-tech, 60d strategic Korbach."""
    if candidate.get("is_job"):
        return True
    now_utc = now_utc or datetime.now(timezone.utc)
    try:
        dt = datetime.fromisoformat(candidate.get("published_at", ""))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
    except Exception:
        return False
    age_hours = (now_utc - dt).total_seconds() / 3600
    limit = freshness_limit_hours(candidate)
    candidate["freshness_limit_hours"] = limit
    candidate["age_hours"] = round(max(0.0, age_hours), 1)
    return age_hours <= limit

def freshness_label(candidate: dict[str, Any]) -> str:
    limit = int(candidate.get('freshness_limit_hours', freshness_limit_hours(candidate)))
    if limit <= NORMAL_NEWS_MAX_AGE_HOURS:
        return '48h'
    if limit <= CRITICAL_NEWS_MAX_AGE_HOURS:
        return '7 Tage'
    if limit <= IMPORTANT_NEWS_MAX_AGE_HOURS:
        return '14 Tage'
    if limit <= KORBACH_STRATEGIC_MAX_AGE_HOURS:
        return '60 Tage'
    return f'{limit // 24} Tage'


def raw_candidate_key(item: dict[str, Any]) -> str:
    # Prefer the resolved source URL when available. This collapses the same
    # article discovered through multiple Google News queries.
    resolved = item.get("_resolved_article_url") or item.get("google_url", "")
    url = canonical_url(resolved)
    if url:
        return url
    return normalize_text(clean_headline_source_suffix(item.get("title", "")))


def deduplicate_raw_candidates(items: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Collapse repeated discovery hits before expensive enrichment."""
    merged: dict[str, dict[str, Any]] = {}
    # Cheap title-first collapse removes most repeated RSS hits without a
    # network request. Exact URL deduplication is completed later after URL
    # resolution in main().
    title_best: dict[str, dict[str, Any]] = {}
    for item in items:
        title_key = normalize_text(clean_headline_source_suffix(item.get("title", "")))
        if title_key:
            old = title_best.get(title_key)
            if old is None or (item.get("search_priority", 0), len(item.get("summary", ""))) > (old.get("search_priority", 0), len(old.get("summary", ""))):
                title_best[title_key] = item
    for item in title_best.values():
        key = raw_candidate_key(item)
        if not key:
            continue
        old = merged.get(key)
        if old is None or (item.get("search_priority", 0), len(item.get("summary", ""))) > (old.get("search_priority", 0), len(old.get("summary", ""))):
            merged[key] = item
    return sorted(merged.values(), key=lambda x: (x.get("search_priority", 0), x.get("published_at", "")), reverse=True)


def fetch_candidates(cutoff: datetime) -> list[dict[str, Any]]:
    found: dict[str, dict[str, Any]] = {}

    # A. Official Continental corporate RSS
    for feed_url in OFFICIAL_RSS_FEEDS:
        print(f"🔵 Official RSS: {feed_url}")
        try:
            feed = feedparser.parse(feed_url)
            print(f"   HTTP: {getattr(feed, 'status', 'n/a')}")
            print(f"   RSS-Einträge: {len(feed.entries)}")
        except Exception as exc:
            print(f"⚠️ Official RSS error: {exc}")
            continue
        for entry in feed.entries[:100]:
            dt = parse_entry_datetime(entry)
            if not dt or dt < cutoff:
                continue
            title = clean_text(getattr(entry, "title", ""))
            link = getattr(entry, "link", "") or ""
            summary = entry_description(entry)
            if not title or not link:
                continue
            # v4.0: do not reject official RSS items solely from title/summary.
            # enrich_candidate() opens the original page and performs the final
            # relevance decision using the complete article text.
            found[f"{normalize_text(title)}|{canonical_url(link)}"] = {
                "title": title, "summary": summary, "google_url": link,
                "source_name": "Continental", "published_at": dt.isoformat(),
                "search_priority": 1800, "found_at": datetime.now(timezone.utc).isoformat(),
                "direct_source": True,
            }

    # B. Official German tire stories
    for item in fetch_official_reifen_stories(cutoff):
        found[f"{normalize_text(item['title'])}|{canonical_url(item['google_url'])}"] = item

    # B2. Official Unermüdlich truck/tire blog.
    # Fetch exactly once: v5.9.1 accidentally called this source twice,
    # causing duplicate network requests and duplicate discovery logs.
    for item in fetch_official_unermuedlich_blog(cutoff):
        found[f"{normalize_text(item['title'])}|{canonical_url(item['google_url'])}"] = item

    # C. Direct German media RSS
    for item in fetch_direct_media_rss(cutoff):
        found[f"{normalize_text(item['title'])}|{canonical_url(item['google_url'])}"] = item

    # C2. HNA Korbach listing is a dedicated local discovery source.
    for item in fetch_hna_korbach(cutoff):
        found[f"{normalize_text(item['title'])}|{canonical_url(item['google_url'])}"] = item

    # D. Job discovery is intentionally disabled in v6.0.

    # E. German Google News fallback only
    for query, lang, country, priority in build_queries():
        print(f"🔎 Google-RSS fallback [{lang}/{country}]: {query}")
        try:
            feed = feedparser.parse(google_rss_url(query, lang, country))
        except Exception as exc:
            print(f"⚠️ Google RSS error: {exc}")
            continue
        relevant_count = 0
        for entry in feed.entries[:80]:
            dt = parse_entry_datetime(entry)
            if not dt or dt < cutoff:
                continue
            title = clean_text(getattr(entry, "title", ""))
            link = getattr(entry, "link", "") or ""
            summary = entry_description(entry)
            if not title or not link or looks_like_bad_title(title):
                continue
            # Google RSS is only discovery. Do not reject here based on the
            # aggregator title/summary; enrich_candidate opens the original
            # article and applies the full relevance test there.
            discovery_text = normalize_text(f"{title} {summary}")
            if not any(term in discovery_text for term in (
                "continental", "korbach", "reifenwerk", "reifen", "betriebsrat",
                "ig metall", "stellenabbau", "produktion", "verlagerung",
                "schließung", "investition", "werk", "vorstand", "quartalszahlen",
            )):
                continue
            relevant_count += 1
            key = f"{normalize_text(title)}|{link}"
            found[key] = {
                "title": title, "summary": summary, "google_url": link,
                "source_name": entry_source_name(entry), "published_at": dt.isoformat(),
                "discovery_published_at": dt.isoformat(),
                "search_priority": priority, "found_at": datetime.now(timezone.utc).isoformat(),
            }
        print(f"   relevant: {relevant_count}")

    # E2. Strategic Continental topics: older event dates are used only for
    # discovery. The normal freshness gate still decides whether a newly
    # published follow-up may enter the channel. This catches new developments
    # around long-running themes such as the ContiTech sale and board changes.
    strategic_queries = [
        ('"Continental" ContiTech Verkauf Lone Star', 1220),
        ('"Continental" ContiTech Lone Star', 1210),
        ('"Continental" Pure-Play-Reifenhersteller', 1180),
        ('"Continental" pure-play tire company', 1180),
        ('"Continental" Sabrina Soussan', 1170),
        ('"Continental" Wolfgang Reitzle', 1170),
        ('"Continental" Aufsichtsrat', 1160),
        ('"Continental" transformation strategy', 1120),
        ('"Continental" transformation', 1110),
        ('"Continental" announced sale ContiTech', 1210),
        ('"Continental" completes ContiTech sale', 1210),
    ]
    strategic_cutoff = datetime.now(timezone.utc) - timedelta(hours=STRATEGIC_TOPIC_LOOKBACK_HOURS)
    for query, priority in strategic_queries:
        print(f"🔎 Strategic Google-RSS [{STRATEGIC_TOPIC_LOOKBACK_HOURS//24}d]: {query}")
        try:
            feed = feedparser.parse(google_rss_url(query, 'de', 'DE'))
        except Exception as exc:
            print(f"⚠️ Strategic Google RSS error: {exc}")
            continue
        for entry in feed.entries[:50]:
            dt = parse_entry_datetime(entry)
            if not dt or dt < strategic_cutoff:
                continue
            title = clean_text(getattr(entry, 'title', ''))
            link = getattr(entry, 'link', '') or ''
            summary = entry_description(entry)
            if not title or not link or looks_like_bad_title(title):
                continue
            discovery_text = normalize_text(f"{title} {summary}")
            if 'continental' not in discovery_text and 'contitech' not in discovery_text:
                continue
            found[f"STRAT|{normalize_text(title)}|{canonical_url(link)}"] = {
                'title': title, 'summary': summary, 'google_url': link,
                'source_name': entry_source_name(entry), 'published_at': dt.isoformat(),
                'search_priority': priority, 'found_at': datetime.now(timezone.utc).isoformat(),
                'strategic_topic': True,
            }

    # F. Jobs search is intentionally disabled in v6.0.

    return deduplicate_raw_candidates(list(found.values()))


# ============================================================
# ARTICLE / IMAGE
# ============================================================

def image_candidate_allowed(url: str) -> bool:
    if not url.startswith(("http://", "https://")):
        return False
    if is_google_host(url):
        return False
    low = url.lower()
    return not any(term in low for term in BAD_IMAGE_TERMS)


def add_image_url(candidates: list[str], value: Optional[str], base_url: str) -> None:
    if not value:
        return
    absolute = urljoin(base_url, value.strip()).split("#", 1)[0]
    if image_candidate_allowed(absolute) and absolute not in candidates:
        candidates.append(absolute)


def clean_headline_source_suffix(title: str) -> str:
    title = clean_text(title)
    if not title:
        return ""
    # Google/aggregator pages sometimes append the publisher to the headline.
    title = re.sub(r"\s+\|\s+(?:Reifenpresse\.de|AD HOC NEWS|4investors(?:\.de)?|Allgemeine Bauzeitung)\s*$", "", title, flags=re.IGNORECASE)
    return clean_text(title)


def extract_original_title(html_text: str) -> str:
    soup = BeautifulSoup(html_text, "html.parser")
    candidates: list[str] = []

    # 1. Explicit social/article metadata is normally the cleanest headline.
    for attrs in ({"property": "og:title"}, {"name": "twitter:title"}, {"property": "twitter:title"}):
        for tag in soup.find_all("meta", attrs=attrs):
            value = clean_text(tag.get("content", ""))
            if value:
                candidates.append(value)

    # 2. Prefer JSON-LD headline. Only use "name" for article/webpage objects,
    # never a nested Organization name such as just "Continental".
    json_names: list[str] = []
    for script in soup.find_all("script", type="application/ld+json"):
        raw = script.string or script.get_text()
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue
        stack = data if isinstance(data, list) else [data]
        while stack:
            obj = stack.pop()
            if isinstance(obj, dict):
                headline = obj.get("headline")
                if isinstance(headline, str) and headline.strip():
                    candidates.append(clean_text(headline))
                obj_type = obj.get("@type")
                types = obj_type if isinstance(obj_type, list) else [obj_type]
                types = {str(x).lower() for x in types if x}
                if types & {"article", "newsarticle", "blogposting", "webpage"}:
                    name = obj.get("name")
                    if isinstance(name, str) and name.strip():
                        json_names.append(clean_text(name))
                for value in obj.values():
                    if isinstance(value, (dict, list)):
                        stack.append(value)
            elif isinstance(obj, list):
                stack.extend(obj)

    candidates.extend(json_names)

    # 3. HTML title is the final fallback.
    if soup.title and soup.title.string:
        candidates.append(clean_text(soup.title.string))

    for value in candidates:
        if value and len(value) >= 5 and not looks_like_bad_title(value):
            return value[:500]
    return ""


def extract_article_data(html_text: str, article_url: str) -> tuple[str, list[str]]:
    soup = BeautifulSoup(html_text, "html.parser")
    images: list[str] = []

    for attrs in (
        {"property": "og:image"},
        {"name": "twitter:image"},
        {"property": "twitter:image"},
    ):
        for tag in soup.find_all("meta", attrs=attrs):
            add_image_url(images, tag.get("content"), article_url)

    for tag in soup.find_all("img", limit=40):
        for attr in ("src", "data-src", "data-original", "data-lazy-src"):
            add_image_url(images, tag.get(attr), article_url)

    description = ""
    for attrs in (
        {"property": "og:description"},
        {"name": "description"},
        {"name": "twitter:description"},
    ):
        tag = soup.find("meta", attrs=attrs)
        if tag and tag.get("content"):
            description = clean_text(tag.get("content"))
            if len(description) >= 80:
                break

    if len(description) < 80:
        paragraphs = []
        for p in soup.find_all("p", limit=20):
            text = clean_text(p.get_text(" ", strip=True))
            if len(text) >= 60:
                paragraphs.append(text)
            if sum(len(x) for x in paragraphs) >= 700:
                break
        description = " ".join(paragraphs)

    return description[:900], images[:30]



def _parse_datetime_value(value: str) -> Optional[datetime]:
    try:
        cleaned = value.strip().replace("Z", "+00:00")
        dt = datetime.fromisoformat(cleaned)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        return None


def extract_original_published_datetime(html_text: str) -> Optional[datetime]:
    """Extract the original publication date with strict source priority.

    Priority: explicit publication meta tags -> JSON-LD datePublished ->
    publication-looking <time> values -> JSON-LD dateCreated as last resort.
    This prevents an updated/modified timestamp from replacing the real
    publication date when a page exposes both.
    """
    soup = BeautifulSoup(html_text, "html.parser")
    published_candidates: list[str] = []
    time_candidates: list[str] = []
    fallback_created_candidates: list[str] = []

    # 1) Explicit publication metadata.
    for attrs in (
        {"property": "article:published_time"},
        {"property": "og:published_time"},
        {"name": "datePublished"},
        {"name": "publishdate"},
        {"name": "pubdate"},
        {"name": "date"},
    ):
        for tag in soup.find_all("meta", attrs=attrs):
            value = tag.get("content")
            if value:
                published_candidates.append(value.strip())

    # 2) JSON-LD datePublished is authoritative over dateCreated.
    for script in soup.find_all("script", type="application/ld+json"):
        raw = script.string or script.get_text()
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue
        stack = data if isinstance(data, list) else [data]
        while stack:
            obj = stack.pop()
            if isinstance(obj, dict):
                value = obj.get("datePublished")
                if isinstance(value, str):
                    published_candidates.append(value.strip())
                value = obj.get("dateCreated")
                if isinstance(value, str):
                    fallback_created_candidates.append(value.strip())
                for nested in obj.values():
                    if isinstance(nested, (dict, list)):
                        stack.append(nested)
            elif isinstance(obj, list):
                stack.extend(obj)

    # 3) Only after explicit publication metadata, inspect <time>.
    for tag in soup.find_all("time"):
        value = tag.get("datetime")
        if value:
            time_candidates.append(value.strip())

    for value in published_candidates + time_candidates + fallback_created_candidates:
        dt = _parse_datetime_value(value)
        if dt is not None:
            return dt

    return None

def fetch_article(url: str, is_job: bool = False, trusted_job: bool = False) -> tuple[Optional[str], str, list[str], str, Optional[datetime]]:
    try:
        response = requests.get(
            url,
            headers=HEADERS,
            timeout=REQUEST_TIMEOUT,
            allow_redirects=True,
        )
        response.raise_for_status()

        content_type = response.headers.get("content-type", "").lower()
        if "text/html" not in content_type:
            return response.url, "", [], "", None

        original_title = extract_original_title(response.text)
        published_dt = extract_original_published_datetime(response.text)

        # v5.6: do not apply the generic 14-day discovery cutoff here.
        # Publication age is decided after the full original article is read
        # by candidate_fresh_enough(), which can correctly allow important
        # stories for 7 days and critical events for 14 days.

        # Job pages are current if the vacancy is still open, even when the
        # original posting date is older than the news lookback window.
        if is_job:
            page_text = normalize_text(response.text)
            job_url = normalize_text(response.url)
            if "vergoelst" in page_text or "vergölst" in page_text or "vergoelst" in job_url:
                print("⛔ Vergölst-Stelle außerhalb des Korbach-Filters")
                return None, "", [], "", published_dt

            if any(re.search(pattern, page_text, flags=re.IGNORECASE) for pattern in INACTIVE_JOB_PATTERNS):
                print("⛔ Stelle ausdrücklich als nicht mehr verfügbar gekennzeichnet")
                return None, "", [], "", published_dt

            # A vacancy linked directly from the official Korbach careers page
            # is considered active by source authority. Some Continental job
            # detail pages are rendered client-side and therefore do not expose
            # the application button in the raw HTML fetched by requests.
            if trusted_job:
                if "jobs.continental.com" not in job_url:
                    print("⛔ Nicht-offizielle Jobquelle")
                    return None, "", [], "", published_dt
                # The official Korbach portal is authoritative, but the detail
                # page must still identify Korbach. This prevents accidentally
                # publishing a global Continental vacancy from a portal shell.
                korbach_evidence = ("korbach" in page_text or "korbach" in job_url)
                if not korbach_evidence:
                    print("⛔ Offizielle Stelle, aber Korbach nicht bestätigt")
                    return None, "", [], "", published_dt
            else:
                job_signal = any(term in page_text for term in (
                    "jetzt bewerben", "jetzt bewerben!", "bewerben", "online bewerben",
                    "apply now", "apply", "bewerbung"
                ))
                if "korbach" not in page_text and "korbach" not in job_url:
                    print("⛔ Keine aktive Korbach-Stelle erkannt")
                    return None, "", [], "", published_dt
                if not job_signal:
                    print("⛔ Keine aktive Bewerbungsoption erkannt")
                    return None, "", [], "", published_dt

        description, images = extract_article_data(response.text, response.url)
        return response.url, description, images, original_title, published_dt

    except Exception as exc:
        print(f"⚠️ Не вдалося відкрити статтю: {exc}")
        return None, "", [], "", None


def download_real_image(candidates: list[str]) -> Optional[bytes]:
    for url in candidates:
        try:
            r = requests.get(url, headers=HEADERS, timeout=IMAGE_TIMEOUT, allow_redirects=True)
            if r.status_code != 200 or "image/" not in r.headers.get("content-type", "").lower():
                continue
            if len(r.content) < 5000:
                continue

            img = Image.open(BytesIO(r.content))
            img.load()

            width, height = img.size
            if width < 300 or height < 170:
                continue
            if width / max(height, 1) > 5.5:
                continue

            if img.mode != "RGB":
                img = img.convert("RGB")

            img.thumbnail((1800, 1800), Image.Resampling.LANCZOS)

            out = BytesIO()
            img.save(out, format="JPEG", quality=88, optimize=True)
            data = out.getvalue()

            if 8000 <= len(data) <= 5 * 1024 * 1024:
                return data

        except Exception:
            continue

    return None


# ============================================================
# CLASSIFICATION
# ============================================================

def classify_item(item: dict[str, Any]) -> dict[str, Any]:
    text = f'{item.get("title", "")} {item.get("summary", "")} {item.get("article_text", "")}'
    plant = detect_plant(text)
    categories: list[str] = []

    if plant or contains_any(text, PLANT_TERMS):
        categories.append("plants")
    if contains_any(text, TIRE_TERMS):
        categories.append("tires")
    if contains_any(text, PEOPLE_TERMS):
        categories.append("people")
    if contains_any(text, COMPANY_MANAGEMENT_TERMS):
        categories.append("company")

    categories = list(dict.fromkeys(categories))

    if item.get("is_job"):
        primary = "people"
    elif plant:
        primary = "plants"
    elif "people" in categories:
        primary = "people"
    elif "tires" in categories:
        primary = "tires"
    elif "company" in categories:
        primary = "company"
    else:
        # Every accepted Continental item must have a useful topic.
        # Generic Germany/world buckets are intentionally removed.
        primary = "company"

    item["categories"] = categories or [primary]
    item["primary_category"] = primary
    item["plant"] = plant
    item["event_families"] = sorted(matched_event_families(text))
    item["event_key"] = concrete_event_key(item)

    plant_priority = plant["priority"] if plant else 0
    relevance = relevance_score(
        item.get("title", ""),
        f'{item.get("summary", "")} {item.get("article_text", "")}',
        item.get("article_url", ""),
    )
    item["relevance_score"] = relevance
    item["editorial_class"] = item_editorial_class(item)
    item["production_bonus"] = production_priority_bonus(item)
    item["priority_score"] = (
        item.get("search_priority", 0)
        + source_score(item.get("article_url", ""))
        + plant_priority
        + max(0, relevance)
        + item.get("production_bonus", 0)
    )
    return item


# ============================================================
# DUPLICATES
# ============================================================

STOPWORDS = {
    "continental", "ag", "gmbh", "the", "der", "die", "das",
    "und", "and", "von", "für", "mit", "auf", "in", "im",
    "at", "to", "of", "a", "an",
}


def title_tokens(title: str) -> set[str]:
    return {
        t for t in re.findall(r"\w+", normalize_text(title), flags=re.UNICODE)
        if len(t) >= 4 and t not in STOPWORDS
    }


def title_similarity(a: str, b: str) -> float:
    seq = SequenceMatcher(None, normalize_text(a), normalize_text(b)).ratio()
    ta, tb = title_tokens(a), title_tokens(b)
    overlap = len(ta & tb) / max(1, min(len(ta), len(tb))) if ta and tb else 0.0
    return max(seq, overlap)


def content_tokens(text: str) -> set[str]:
    return {
        t for t in re.findall(r"\w+", normalize_text(text), flags=re.UNICODE)
        if len(t) >= 4 and t not in STOPWORDS
    }


def content_similarity(a: dict[str, Any], b: dict[str, Any]) -> float:
    """Compare article substance, not just headlines, for event-level dedup."""
    ta = content_tokens(
        f"{a.get('title','')} {a.get('summary','')} {a.get('article_text','')}"
    )
    tb = content_tokens(
        f"{b.get('title','')} {b.get('summary','')} {b.get('article_text','')}"
    )
    if not ta or not tb:
        return 0.0
    inter = len(ta & tb)
    union = len(ta | tb)
    jaccard = inter / max(1, union)
    containment = inter / max(1, min(len(ta), len(tb)))
    return max(jaccard, containment * 0.75)


def item_plant_city(item: dict[str, Any]) -> str:
    plant = item.get("plant")
    if isinstance(plant, dict):
        city = clean_text(str(plant.get("city", "")))
        if city:
            return city
    return (detect_plant(f"{item.get('title', '')} {item.get('summary', '')} {item.get('article_text', '')}") or {}).get("city", "")


def item_event_families(item: dict[str, Any]) -> set[str]:
    stored = item.get("event_families")
    if isinstance(stored, list):
        return {str(x) for x in stored if x}
    return matched_event_families(f"{item.get('title', '')} {item.get('summary', '')} {item.get('article_text', '')}")


def event_similarity(a: dict[str, Any], b: dict[str, Any]) -> float:
    """Similarity for duplicate detection, not event-family matching.

    Same event family or same plant is NOT enough to suppress a new article.
    """
    ta = clean_text(a.get("title", ""))
    tb = clean_text(b.get("title", ""))
    base = title_similarity(ta, tb)
    aa, bb = title_tokens(ta), title_tokens(tb)
    union = aa | bb
    jaccard = len(aa & bb) / max(1, len(union)) if union else 0.0
    substance = content_similarity(a, b)
    return max(base, jaccard, substance * 0.90)


def publication_dedup_keys(item: dict[str, Any]) -> set[str]:
    """Stable keys surviving source/URL variations and workflow runs."""
    keys: set[str] = set()
    url = canonical_url(item.get("article_url", "") or item.get("_resolved_article_url", ""))
    if url:
        keys.add("url:" + url)
    title = normalize_text(clean_headline_source_suffix(item.get("title", "")))
    if title:
        keys.add("title:" + title)
    # Compact title key tolerates punctuation/source suffix changes.
    toks = sorted(title_tokens(title))
    if toks:
        keys.add("title_tokens:" + " ".join(toks))
    event_key = clean_text(item.get("event_key", "")) or concrete_event_key(item)
    if event_key:
        keys.add("event:" + event_key)
    return keys

def archive_has_exact_publication(item: dict[str, Any], records: list[dict[str, Any]]) -> bool:
    keys = publication_dedup_keys(item)
    for record in records:
        if keys & publication_dedup_keys(record):
            return True
    return False

def duplicate_decision(item: dict[str, Any], records: list[dict[str, Any]]) -> tuple[bool, str, float]:
    """Return (is_duplicate, reason, score).

    Rules: exact URL always duplicates; near-identical title/body duplicates;
    same event alone never duplicates because follow-up reporting can contain
    materially new facts.
    """
    url = canonical_url(item.get("article_url", ""))
    item_keys = publication_dedup_keys(item)
    best_reason = "none"
    best_score = 0.0
    for record in records:
        record_keys = publication_dedup_keys(record)
        if item_keys & record_keys:
            if url and canonical_url(record.get("article_url", "")) == url:
                return True, "same_url", 1.0
            return True, "stable_publication_key", 1.0
        ta = clean_text(item.get("title", ""))
        tb = clean_text(record.get("title", ""))
        title_sim = title_similarity(ta, tb)
        substance = content_similarity(item, record)
        score = max(title_sim, substance * 0.90)
        if score > best_score:
            best_score = score
            best_reason = f"title={title_sim:.2f},substance={substance:.2f}"
        if title_sim >= 0.93 and substance < 0.68:
            return True, "near_identical_title", score
        if title_sim >= 0.80 and substance >= 0.72:
            return True, "strong_title_and_substance", score
    return False, best_reason, best_score


def is_duplicate_event(item: dict[str, Any], records: list[dict[str, Any]]) -> bool:
    return duplicate_decision(item, records)[0]


def merge_pending_best(pending: list[dict[str, Any]], item: dict[str, Any]) -> tuple[list[dict[str, Any]], bool, bool]:
    """Merge item into pending, replacing a duplicate event only if the source is better.
    Returns (pending, added, replaced).
    """
    for idx, old in enumerate(pending):
        same_url = canonical_url(item.get("article_url", "")) == canonical_url(old.get("article_url", ""))
        is_dup, _, _ = duplicate_decision(item, [old])
        if is_dup:
            if source_quality(item) > source_quality(old):
                pending[idx] = item
                return pending, True, True
            return pending, False, False
    pending.append(item)
    return pending, True, False


# ============================================================
# JOB FIRST-SEEN / REACTIVATION TRACKING
# ============================================================

# ============================================================
# TITLE TRANSLATION (headline only)
# ============================================================

TRANSLATION_CACHE: dict[tuple[str, str, str], str] = {}


def probably_german(text: str) -> bool:
    """Lightweight language heuristic for headline translation.

    We only need to choose between German and English for the translation
    provider; this is intentionally conservative and does not affect news
    relevance or publication decisions.
    """
    t = f" {normalize_text(text).lower()} "
    if not t.strip():
        return False

    german_markers = (
        " der ", " die ", " das ", " den ", " dem ", " des ",
        " ein ", " eine ", " einen ", " einer ", " und ", " mit ",
        " für ", " von ", " zum ", " zur ", " auf ", " aus ",
        " wird ", " werden ", " baut ", " neue ", " neuen ",
        " reifen ", " werk ", " produktion ", " continental ",
        " über ", "ä", "ö", "ü", "ß",
    )
    score = sum(1 for marker in german_markers if marker in t)
    return score >= 2 or any(ch in t for ch in ("ä", "ö", "ü", "ß"))


def translation_result_is_error(text: str) -> bool:
    normalized = normalize_text(text)
    if not normalized:
        return True
    bad = (
        "error 429", "error 500", "too many requests", "server error",
        "service unavailable", "internal server error", "please try again",
    )
    return any(x in normalized for x in bad)


def _headline_translation_quality(source: str, translated: str) -> bool:
    if not translated or translation_result_is_error(translated):
        return False
    if normalize_text(source) == normalize_text(translated):
        return False
    # Reject obvious provider error/HTML responses and absurdly short output.
    if len(translated.strip()) < 4:
        return False
    if len(translated) > max(300, len(source) * 3):
        return False
    if "<html" in translated.lower() or "<!doctype" in translated.lower():
        return False
    return True


def translate_headline_uk(text: str) -> str:
    """Translate ONLY the headline to Ukrainian.

    Primary provider: MyMemory (no API key required), with Google GTX as a
    fallback. Successful results are cached so the same headline is never
    translated twice during one run. The article description/body is never
    sent to a translation provider.
    """
    text = clean_text(text)
    if not text:
        return ""
    key = ("auto", "uk", text[:700])
    if key in TRANSLATION_CACHE:
        return TRANSLATION_CACHE[key]

    source_lang = "de" if probably_german(text) else "en"

    # MyMemory is used first to avoid the Google GTX 429 problem seen in the
    # previous run. One headline is a tiny request and the daily volume is low.
    try:
        response = requests.get(
            "https://api.mymemory.translated.net/get",
            params={
                "q": text[:700],
                "langpair": f"{source_lang}|uk",
                "mt": "1",
            },
            headers=HEADERS,
            timeout=15,
        )
        if response.ok:
            data = response.json()
            translated = clean_text(
                ((data.get("responseData") or {}).get("translatedText") or "")
            )
            if _headline_translation_quality(text, translated):
                TRANSLATION_CACHE[key] = translated
                return translated
        else:
            print(f"⚠️ MyMemory UK {response.status_code}; Google fallback")
    except Exception as exc:
        print(f"⚠️ MyMemory UK error: {exc}; Google fallback")

    # Fallback only. Unlike the old implementation, this is a single request
    # and never retries a 429, preventing a burst of repeated requests.
    try:
        response = requests.get(
            "https://translate.googleapis.com/translate_a/single",
            params={
                "client": "gtx", "sl": "auto", "tl": "uk", "dt": "t",
                "q": text[:700],
            },
            headers=HEADERS,
            timeout=12,
        )
        if response.ok:
            data = response.json()
            parts = data[0] if isinstance(data, list) and data else []
            translated = clean_text("".join(
                str(part[0]) for part in parts
                if isinstance(part, list) and part and isinstance(part[0], str)
            ))
            if _headline_translation_quality(text, translated):
                TRANSLATION_CACHE[key] = translated
                return translated
        elif response.status_code == 429:
            print("⚠️ Google UK translation 429 — headline remains original")
    except Exception as exc:
        print(f"⚠️ Google UK translation error: {exc}")

    return ""


# ============================================================
# TELEGRAM
# ============================================================

def telegram_api(method: str, data: Optional[dict[str, Any]] = None, files: Any = None) -> dict[str, Any]:
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/{method}"

    try:
        if files:
            response = requests.post(url, data=data or {}, files=files, timeout=REQUEST_TIMEOUT)
        else:
            response = requests.post(url, data=data or {}, timeout=REQUEST_TIMEOUT)
        response.raise_for_status()
        return response.json()
    except Exception as exc:
        return {"ok": False, "description": str(exc)}


def format_location(item: dict[str, Any]) -> str:
    plant = item.get("plant")
    if plant:
        return f'{plant["flag"]} {plant["city"]}, {plant["country_de"]}'
    if item.get("primary_category") == "company":
        return "🌍 Continental / Konzern"
    return "🌍 Continental"


def format_categories(item: dict[str, Any]) -> str:
    return " • ".join(SECTIONS[k]["title"] for k in item.get("categories", []) if k in SECTIONS)


def build_post_text(item: dict[str, Any], for_photo: bool = False) -> str:
    title = clean_text(item.get("title") or "")
    title_uk = clean_text(item.get("title_uk") or "")
    # IMPORTANT: the description/body stays in the original language.
    summary = clean_text(item.get("summary") or "")
    source = item.get("source_name") or hostname_from_url(item.get("article_url", "")) or "Quelle"

    def esc(value: Any) -> str:
        return html.escape(str(value or ""), quote=False)

    if len(summary) > 500:
        summary = summary[:497].rstrip(" .,!?:;—-") + "…"

    parts = [f"<b>{esc(title)}</b>"]
    if title_uk and normalize_text(title_uk) != normalize_text(title):
        parts += ["", f"🇺🇦 <b>{esc(title_uk)}</b>"]
    if summary:
        parts += ["", esc(summary)]
    parts += [
        "",
        f"📍 {esc(format_location(item))}",
        f"🏷️ {esc(format_categories(item))}",
        f"📰 Quelle: {esc(source)}",
        f"🔗 {esc(item['article_url'])}",
    ]

    text = "\n".join(parts)
    return text[:1024] if for_photo else text[:4096]

def send_item(item: dict[str, Any]) -> Optional[int]:
    """Publish one news item to Telegram; translate headline only."""
    final_url, article_text, images, original_title, original_dt = fetch_article(
        item["article_url"],
        is_job=False,
        trusted_job=False,
    )

    if final_url:
        item["article_url"] = final_url
    if original_title and not looks_like_bad_title(original_title):
        item["title"] = clean_headline_source_suffix(original_title)

    # Translate the headline only. Never translate the article description.
    if not item.get("title_uk"):
        item["title_uk"] = translate_headline_uk(item.get("title", ""))
    if article_text:
        item["article_text"] = article_text
        if not clean_text(item.get("summary", "")):
            item["summary"] = clean_text(article_text[:3000])
    if original_dt is not None:
        item["published_at"] = original_dt.isoformat()

    final_title = clean_text(item.get("title", ""))
    if not final_title or looks_like_bad_title(final_title):
        print("⛔ Veröffentlichung blockiert: fehlerhafter Titel")
        return None

    photo = download_real_image(images)
    data: dict[str, Any] = {"chat_id": CHANNEL_ID}

    if photo:
        result = telegram_api(
            "sendPhoto",
            data={**data, "caption": build_post_text(item, True), "parse_mode": "HTML"},
            files={"photo": ("continental_news.jpg", photo, "image/jpeg")},
        )
        if result.get("ok"):
            return result["result"]["message_id"]

    result = telegram_api(
        "sendMessage",
        data={
            **data,
            "text": build_post_text(item, False),
            "parse_mode": "HTML",
            "disable_web_page_preview": "true",
        },
    )

    if result.get("ok"):
        return result["result"]["message_id"]

    print(f"❌ Telegram error: {result}")
    return None

# ============================================================
# MAIN PROCESS
# ============================================================

KORBACH_STRATEGIC_TERMS = [
    "schließung", "schliessung", "closure", "closed", "closing",
    "verlagerung", "produktionsverlagerung", "relocation", "shift production",
    "restrukturierung", "restructuring", "umbau", "transformation",
    "abbau", "stellenabbau", "jobs affected", "arbeitsplätze", "arbeitsplaetze",
    "140 jobs", "entlassungen", "layoffs", "redundancy",
    "contitech", "strategisch", "strategic", "investition", "investitionen",
    "investment", "windpark", "kapazität", "kapazitaet", "capacity",
]

PRODUCTION_TERMS = [
    "produktion", "produktions", "fertigung", "manufacturing", "production",
    "produktionslinie", "production line", "produktionsanlage", "production facility",
    "kapazität", "kapazitaet", "capacity", "ausbau", "erweiterung", "expansion",
    "investition", "investitionen", "investment", "anlage", "maschinen", "fertigungslinie",
    "reifennwerk", "reifenwerk", "plant", "factory", "werk", "großreifen", "grossreifen",
    "large tires", "large tyres", "verlagerung", "produktionsverlagerung", "neue anlage",
    "neue produktionslinie", "baut aus", "ausgebaut", "hochlauf", "anlauf der produktion",
]
KORBACH_TERMS = ["korbach", "reifenwerk korbach", "reifenwerk", "korbacher"]
TIRE_TECH_TERMS = [
    "neuer reifen", "neue reifen", "reifengeneration", "reifenneuheit", "reifenentwicklung",
    "reifentechnologie", "reifeninnovation", "new tire", "new tyre", "new tire line",
    "tire launch", "tyre launch", "truck tire", "truck tires", "truck tyre",
    "truck tyres", "regional truck tire", "regional truck tires",
    "regional truck tyre", "regional truck tyres", "lkw-reifen", "lkw reifen",
    "introduces new", "introduces", "launches", "launched", "introduced",
    "sensor", "smart tire", "smart tyre", "conticonnect",
    "recycling", "recycled", "recycelt", "concept tire", "concept tyre", "oem",
    "uhp", "ultra high performance", "high performance tire", "high performance tyre",
    "new dimensions", "new tire sizes", "new tyre sizes", "dimensionen", "größen", "groessen",
    "portfolio expansion", "portfolioerweiterung", "650 new", "650", "large tires", "large tyres",
]

# Concrete event identifiers used for cross-source deduplication.  These are
# intentionally narrow: a generic event family such as "production" must NOT
# suppress a different production story.
PRODUCT_EVENT_PATTERNS = [
    r"hsr\s*5\s*ep", r"hdr\s*5\s*ep", r"conti\s*eco\s*(?:ht\s*)?5",
    r"rainexpert\s*6", r"allseasoncontact\s*2", r"contimotion\s*evo",
    r"conti(?:tread|crosscontact|sportcontact|premiumcontact|ultracontact|vancontact)[a-z0-9\s-]{0,24}",
]

def concrete_event_key(item: dict[str, Any]) -> str:
    """Return a narrow cross-source event key, or empty when no concrete key exists."""
    text = normalize_text(f"{item.get('title','')} {item.get('summary','')} {item.get('article_text','')}")
    # Strategic Korbach events are intentionally one-time per concrete topic.
    if "korbach" in text:
        if contains_any(text, ("windpark", "windparkbau", "wind turbines", "wind turbine", "windräder", "windraeder")):
            return "korbach:windpark"
        if contains_any(text, ("verlagerung", "produktionsverlagerung", "relocation", "production transfer")) and contains_any(text, ("solid", "massiv", "vollgummi", "industrial tyre", "industrial tire", "industrie-reifen", "industriereifen")):
            return "korbach:industrial-tire-relocation"
        if contains_any(text, ("schließung", "schliessung", "closure", "shutdown", "produktionsstopp")):
            return "korbach:closure"
        if contains_any(text, ("stellenabbau", "jobs affected", "layoffs", "arbeitsplätze", "arbeitsplaetze", "personalabbau")):
            return "korbach:workforce"
    # Product/model launches: normalize spaces and punctuation so different
    # publishers describing the same model family collapse into one event.
    for pattern in PRODUCT_EVENT_PATTERNS:
        m = re.search(pattern, text, flags=re.IGNORECASE)
        if m:
            token = re.sub(r"\s+", " ", m.group(0)).strip().replace(" ", "-")
            return "product:" + token
    # The >40% recycling concept is a distinct event even when headlines differ.
    if "recycling" in text and ("40%" in text or "40 %" in text or "43%" in text or "43 %" in text or "recycled materials" in text):
        return "product:recycled-materials-concept"
    # Portfolio expansion with 650+ dimensions is a concrete strategic tire event.
    if "650" in text and contains_any(text, ("dimension", "dimensionen", "sizes", "größen", "groessen", "portfolio")):
        return "product:650-plus-dimensions"
    return ""


def item_editorial_class(item: dict[str, Any]) -> str:
    text = normalize_text(f"{item.get('title','')} {item.get('summary','')} {item.get('article_text','')}")
    # v8.1: only an explicit Korbach mention qualifies as Korbach. The old
    # KORBACH_TERMS list also contained “reifenwerk”, which incorrectly turned
    # every Continental tyre plant article into a Korbach story.
    korbach_explicit = "korbach" in text
    if korbach_explicit and contains_any(text, KORBACH_STRATEGIC_TERMS):
        return "korbach_strategic"
    if korbach_explicit and contains_any(text, PRODUCTION_TERMS):
        return "korbach_production"
    if contains_any(text, PRODUCTION_TERMS):
        return "production"
    if contains_any(text, TIRE_TECH_TERMS):
        return "tire_technology"
    return "company"

def production_relevance_floor(item: dict[str, Any]) -> int:
    cls = item_editorial_class(item)
    if cls in {"korbach_strategic", "korbach_production"}:
        return KORBACH_STRATEGIC_MIN_RELEVANCE if cls == "korbach_strategic" else KORBACH_PRODUCTION_MIN_RELEVANCE
    if cls == "production":
        return PRODUCTION_MIN_RELEVANCE
    if cls == "tire_technology":
        return TIRE_TECH_MIN_RELEVANCE
    return PENDING_MIN_RELEVANCE

def production_priority_bonus(item: dict[str, Any]) -> int:
    text = normalize_text(f"{item.get('title','')} {item.get('summary','')} {item.get('article_text','')}")
    bonus = 0
    weighted = [
        ("korbach", 150), ("reifenwerk", 120), ("produktion", 100),
        ("produktionslinie", 110), ("fertigung", 90), ("kapazität", 90),
        ("kapazitaet", 90), ("investition", 90), ("ausbau", 100),
        ("erweiterung", 90), ("verlagerung", 100), ("produktionsverlagerung", 110),
        ("neue anlage", 90), ("produktionsanlage", 100), ("großreifen", 80),
        ("large tires", 80), ("sensor", 80), ("smart tire", 80),
        ("smart tyre", 80), ("conticonnect", 70), ("reifengeneration", 70),
        ("reifenneuheit", 70), ("reifentechnologie", 70), ("reifeninnovation", 70),
        ("recycling", 60), ("betriebsrat", 70), ("mitarbeiter", 60),
    ]
    for term, value in weighted:
        if normalize_text(term) in text:
            bonus += value
    return bonus

def enrich_candidate(candidate: dict[str, Any]) -> Optional[dict[str, Any]]:
    article_url = candidate.get("_resolved_article_url") or (candidate["google_url"] if candidate.get("direct_source") else decode_google_url(candidate["google_url"]))
    if not article_url or is_google_host(article_url):
        record_rejection("invalid_or_google_url")
        return None
    if not source_domain_allowed(article_url):
        record_rejection("source_domain_not_allowed")
        return None

    final_url, article_text, _, original_title, original_dt = fetch_article(
        article_url,
        is_job=bool(candidate.get("is_job")),
        trusted_job=bool(candidate.get("trusted_job")),
    )
    if not final_url:
        # Some reputable media block automated requests with 403/anti-bot.
        # candidate_age_hours() is always available in v5.10.4, so a blocked
        # article can safely enter the controlled snippet-fallback path.
        # For strong Continental discovery hits, preserve the news using the
        # Google/portal title+snippet rather than silently losing the story.
        fallback_text = clean_text(candidate.get("summary", ""))
        fallback_score = relevance_score(
            candidate.get("title", ""), fallback_text, article_url
        )
        fallback_source = hostname_from_url(article_url)
        fallback_event = matched_event_families(
            f"{candidate.get('title','')} {fallback_text}"
        )
        fallback_plant = detect_plant(f"{candidate.get('title','')} {fallback_text}")
        fallback_age = candidate_age_hours(candidate)
        fallback_limit = freshness_limit_hours({**candidate, "event_families": sorted(fallback_event)})
        # For a 403 fallback, the Google/portal publication timestamp is the
        # best available age signal. Never let a missing timestamp crash the
        # candidate; a missing age is handled conservatively by the quality gate.
        fallback_fresh = fallback_age is None or fallback_age <= fallback_limit
        strong_fallback = (
            fallback_score >= 55
            and fallback_source not in {"", "jobs.continental.com"}
            and not candidate.get("is_job")
            and fallback_fresh
            and (
                len(fallback_text) >= 80
                or bool(fallback_event)
                or bool(fallback_plant)
                or fallback_source in PREFERRED_SOURCE_DOMAINS
            )
        )
        trusted_fallback_source = (
            fallback_source in PREFERRED_SOURCE_DOMAINS
            or any(domain_matches(fallback_source, d) for d in (
                "reuters.com", "reifenpresse.de", "tyrepress.com",
                "automobilwoche.de", "hessenschau.de", "hna.de",
                "handelsblatt.com", "faz.net", "sueddeutsche.de",
                "wiwo.de", "manager-magazin.de", "profi-werkstatt.net",
                "tyreandrubberrecycling.com", "automotiveworld.com",
            ))
        )
        # v5.10.3: a fresh, high-value operational story from a reputable
        # publisher may survive a 403 even when the RSS snippet is short.
        if strong_fallback and trusted_fallback_source and (
            fallback_event or fallback_plant or fallback_score >= 70
        ):
            candidate["article_text"] = fallback_text[:5000]
            candidate["article_url"] = article_url
            candidate["_fallback_from_snippet"] = True
            candidate["_fallback_source"] = fallback_source
            candidate["_fallback_discovery"] = True
            candidate["_fallback_relevance_score"] = fallback_score
            # Keep the discovery timestamp authoritative when the original
            # article cannot be fetched. This allows fresh 403 stories to
            # pass the normal 48h / 7d / 14d freshness rules.
            print(
                f"🟡 Original nicht erreichbar – Qualitäts-Fallback aktiv: "
                f"{candidate.get('title','')[:110]} | Score={fallback_score} | "
                f"Alter={fallback_age if fallback_age is not None else '?'}h | "
                f"Event={','.join(sorted(fallback_event)) or '-'} | "
                f"Werk={fallback_plant.get('city','-') if fallback_plant else '-'}"
            )
            final_url = article_url
            original_title = candidate.get("title", "")
            original_dt = None
        elif trusted_fallback_source and fallback_score >= 60 and not candidate.get("is_job") and fallback_fresh:
            candidate["article_text"] = fallback_text[:5000]
            candidate["article_url"] = article_url
            candidate["_fallback_from_snippet"] = True
            candidate["_fallback_source"] = fallback_source
            print(f"🟡 Original nicht erreichbar – Snippet-Fallback aktiv: {candidate.get('title','')[:110]} | Score={fallback_score}")
            final_url = article_url
            original_title = candidate.get("title", "")
            original_dt = None
        else:
            record_rejection("original_unavailable_or_too_old")
            print(f"⛔ Quelle nicht erreichbar/zu alt: {article_url}")
            return None

    candidate["article_url"] = final_url
    # Preserve controlled snippet-fallback content. When fetch_article() fails
    # with 403/anti-bot, article_text is empty but the fallback path above has
    # already populated candidate["article_text"] from the trusted RSS/Google
    # snippet. Do not overwrite that evidence with an empty string.
    if article_text:
        candidate["article_text"] = article_text
    elif not candidate.get("article_text"):
        candidate["article_text"] = clean_text(candidate.get("summary", ""))

    # v5.6: the original article timestamp is authoritative for publication
    # freshness. Discovery/RSS dates can describe the aggregator update time
    # and must not override the source article date.
    if original_dt is not None and not candidate.get("is_job"):
        candidate["published_at"] = original_dt.isoformat()
        candidate["original_published_at"] = original_dt.isoformat()

    # Prefer the real title from the original page. Never allow an HTTP/Google
    # error page to become a Telegram headline.
    if original_title and not looks_like_bad_title(original_title):
        candidate["title"] = clean_headline_source_suffix(original_title)

    if looks_like_bad_title(candidate.get("title", "")):
        record_rejection("bad_title")
        print("⛔ Service-/Fehlerseite als Titel erkannt")
        return None

    # IMPORTANT v5.6: freshness is evaluated only after the original article
    # has been fetched, because the discovery headline/RSS snippet can omit
    # terms such as relocation, closure or workforce impact.
    candidate["summary"] = f"{candidate.get('summary', '')} {article_text[:3000]}".strip()
    if not candidate_fresh_enough(candidate, datetime.now(timezone.utc)):
        record_rejection("freshness_gate_after_original")
        limit = freshness_limit_hours(candidate)
        age = candidate.get("age_hours")
        print(
            f"⏭️ Frische-Gate: {candidate.get('title','')[:110]} | "
            f"Alter={age if age is not None else '?'}h | Grenze={limit}h | "
            f"Original={candidate.get('published_at','?')} | "
            f"Event={','.join(matched_event_families(candidate)) or '-'}"
        )
        return None

    relevance_text = f'{candidate.get("summary", "")} {candidate.get("article_text", "")} {article_text}'
    fallback_relevance = int(candidate.get("_fallback_relevance_score", 0) or 0)
    relevance_ok = is_continental_relevant(
        candidate["title"],
        relevance_text,
        candidate["article_url"],
    )
    # If the source itself is blocked, a trusted fallback may still have a strong
    # editorial score (especially Korbach/restructuring stories). In that case do
    # not reject it merely because the original page's headline/body was unavailable.
    if not relevance_ok and candidate.get("_fallback_from_snippet") and fallback_relevance >= 70:
        fallback_host = hostname_from_url(candidate.get("article_url", ""))
        fallback_event = matched_event_families(relevance_text)
        fallback_plant = detect_plant(relevance_text)
        trusted_fallback = fallback_host in PREFERRED_SOURCE_DOMAINS or any(
            domain_matches(fallback_host, d) for d in (
                "reuters.com", "reifenpresse.de", "tyrepress.com",
                "automobilwoche.de", "hessenschau.de", "hna.de",
                "handelsblatt.com", "faz.net", "sueddeutsche.de",
                "wiwo.de", "manager-magazin.de", "profi-werkstatt.net",
                "tyreandrubberrecycling.com", "automotiveworld.com",
            )
        )
        relevance_ok = bool(trusted_fallback and (fallback_event or fallback_plant or fallback_relevance >= 55))
    if not relevance_ok:
        record_rejection("not_continental_relevant")
        print(
            f"⛔ Relevanz-Gate: {candidate.get('title','')[:110]} | "
            f"Score={relevance_score(candidate.get('title',''), relevance_text, candidate.get('article_url',''))} | "
            f"URL={candidate.get('article_url','')}"
        )
        return None

    if not candidate.get("source_name"):
        candidate["source_name"] = hostname_from_url(candidate["article_url"])

    candidate = classify_item(candidate)

    # v8.3 audit: make category-based acceptance visible in the workflow log.
    if candidate.get("editorial_class") in {"korbach_strategic", "korbach_production", "production", "tire_technology"}:
        print(
            f"   🏭 Editorial-Klasse={candidate.get('editorial_class')} | "
            f"Floor={production_relevance_floor(candidate)} | "
            f"Rel={candidate.get('relevance_score', 0)} | "
            f"Pri={candidate.get('priority_score', 0)}"
        )

    # Translate ONLY the headline. The article description remains untouched
    # and is published in its original language.
    candidate["title_uk"] = translate_headline_uk(candidate.get("title", ""))

    if not candidate.get("title_uk"):
        print(
            f"🟠 UK-Übersetzung vorübergehend nicht verfügbar; "
            f"Originaltitel bleibt erhalten: {candidate.get('title','')[:110]}"
        )

    if not candidate.get("is_job"):
        print(
            f"🟢 NEWS AKZEPTIERT | {candidate.get('title','')[:120]} | "
            f"Quelle={candidate.get('source_name','')} | "
            f"Original={candidate.get('published_at','')} | "
            f"Alter={candidate.get('age_hours','?')}h/{candidate.get('freshness_limit_hours','?')}h | "
            f"Rel={candidate.get('relevance_score',0)} | "
            f"Pri={candidate.get('priority_score',0)} | "
            f"Event={','.join(item_event_families(candidate)) or '-'} | "
            f"Werk={candidate.get('plant',{}).get('city','-') if isinstance(candidate.get('plant'),dict) else '-'}"
        )

    return candidate


def publication_allowed(now_de: datetime) -> bool:
    return PUBLISH_START_HOUR <= now_de.hour < PUBLISH_END_HOUR


def prune_pending(pending: list[dict[str, Any]], now_utc: datetime) -> list[dict[str, Any]]:
    """Keep the queue fresh and useful.

    v5.1 rules:
    - pending news may remain up to 14 days;
    - publication freshness is separately controlled by 72h/7d/10d/14d tiers;
    - jobs may stay longer because vacancies can remain active;
    - weak news below PENDING_MIN_RELEVANCE is dropped;
    - the queue is capped so overnight accumulation cannot grow forever.
    """
    result: list[dict[str, Any]] = []

    for item in pending:
        try:
            found_at = datetime.fromisoformat(item.get("found_at", ""))
            if found_at.tzinfo is None:
                found_at = found_at.replace(tzinfo=timezone.utc)
        except Exception:
            found_at = now_utc

        if item.get("is_job"):
            continue
        max_age = PENDING_MAX_AGE_HOURS
        if found_at < now_utc - timedelta(hours=max_age):
            continue

        if not item.get("is_job"):
            relevance = int(item.get("relevance_score", 0) or 0)
            if relevance and relevance < PENDING_MIN_RELEVANCE:
                continue

        result.append(item)

    # Keep the strongest items. Stable sorting preserves the newest material
    # when two items have the same priority.
    result.sort(
        key=lambda x: (
            x.get("priority_score", 0),
            x.get("relevance_score", 0),
            x.get("published_at", ""),
        ),
        reverse=True,
    )
    return result[:MAX_PENDING_ITEMS]


def trim_pending(pending: list[dict[str, Any]]) -> list[dict[str, Any]]:
    news = [x for x in pending if not x.get("is_job")]
    for x in news:
        x["editorial_class"] = x.get("editorial_class") or item_editorial_class(x)
    news.sort(key=lambda x: (
        {"korbach_strategic": 5, "korbach_production": 4, "production": 3, "tire_technology": 2, "company": 1}.get(x.get("editorial_class"), 1),
        x.get("priority_score", 0), x.get("relevance_score", 0), x.get("published_at", "")
    ), reverse=True)
    return news[:MAX_PENDING_ITEMS]

def log_publication_candidates(pending: list[dict[str, Any]], published: list[dict[str, Any]]) -> None:
    """Detailed v5.6 publication audit."""
    news = [x for x in pending if not x.get("is_job")]
    print(f"📊 Publikationsprüfung: News={len(news)}")
    if REJECTION_STATS:
        print("🧪 News-/Kandidaten-Ausschlussgründe:")
        for reason, count in sorted(REJECTION_STATS.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"   - {reason}: {count}")
    if news:
        print("📰 NEWS IN DER QUEUE:")
    for idx, item in enumerate(news[:12], 1):
        duplicate = is_duplicate_event(item, published)
        print(
            f"   #{idx} NEWS | Pri {item.get('priority_score', 0)} | Rel {item.get('relevance_score', 0)} | "
            f"Frische {freshness_label(item)} | Event {','.join(item_event_families(item)) or '-'} | "
            f"Dup {'JA' if duplicate else 'NEIN'} | {item.get('title','')[:120]}"
        )


def select_publication_batch(pending: list[dict[str, Any]], published: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """v8.3 production-first editorial selection.

    Rules:
      - up to 2 strategic Korbach stories + up to 2 fresh Korbach production stories;
      - up to 3 other factory/production stories;
      - up to 3 tyre/technology stories;
      - up to 2 company/management stories;
      - never fill a slot with a duplicate;
      - if a production category has no fresh candidate, its slots remain empty;
        the bot is allowed to publish fewer than 10 items instead of filling
        the channel with stale 14-day tyre/finance material.
    """
    news = []
    for x in pending:
        if x.get("is_job") or is_duplicate_event(x, published):
            continue
        floor = production_relevance_floor(x)
        if int(x.get("relevance_score", 0) or 0) < floor:
            continue
        news.append(x)

    for x in news:
        x["editorial_class"] = x.get("editorial_class") or item_editorial_class(x)

    def rank(x: dict[str, Any]) -> tuple[int, int, int, str]:
        cls = x.get("editorial_class") or item_editorial_class(x)
        bucket = {"korbach_strategic": 5, "korbach_production": 4, "production": 3, "tire_technology": 2, "company": 1}.get(cls, 1)
        return (bucket, int(x.get("priority_score", 0) or 0), int(x.get("relevance_score", 0) or 0), x.get("published_at", ""))

    news.sort(key=rank, reverse=True)
    selected: list[dict[str, Any]] = []
    used: set[str] = set()

    def add_candidates(classes: set[str], limit: int) -> None:
        if limit <= 0 or len(selected) >= MAX_POSTS_PER_RUN:
            return
        for item in news:
            if len(selected) >= MAX_POSTS_PER_RUN or limit <= 0:
                return
            if item.get("editorial_class") not in classes:
                continue
            key = canonical_url(item.get("article_url", ""))
            event_key = clean_text(item.get("event_key", "")) or concrete_event_key(item)
            if key and key in used:
                continue
            if event_key and event_key in used:
                continue
            selected.append(item)
            if key:
                used.add(key)
            if event_key:
                used.add(event_key)
            limit -= 1

    # Hard category ceilings. These are ceilings, not artificial minimums.
    # Strategic Korbach stories get the highest priority and are still protected
    # by canonical URL/event duplicate checks, so the 60-day window cannot spam.
    add_candidates({"korbach_strategic"}, MAX_KORBACH_STRATEGIC_ITEMS_PER_RUN)
    add_candidates({"korbach_production"}, MAX_KORBACH_ITEMS_PER_RUN)
    add_candidates({"production"}, max(0, MAX_PRODUCTION_ITEMS_PER_RUN - len([x for x in selected if x.get("editorial_class") == "korbach_production"])))
    add_candidates({"tire_technology"}, MAX_TIRE_TECH_ITEMS_PER_RUN)
    add_candidates({"company"}, MAX_COMPANY_ITEMS_PER_RUN)

    # If fewer than 10 high-quality items exist, stop here. This is deliberate:
    # stale filler is worse for this channel than a short daily edition.
    return selected[:MAX_POSTS_PER_RUN]

def published_url_is_republishable(candidate: dict[str, Any], published_record: dict[str, Any]) -> bool:
    """Allow a materially newer revision of the same canonical URL.

    Some official publisher pages keep one stable URL and update the article.
    Treat a revision published at least 18 hours after the archived version as
    a new editorial item; exact same-day duplicates remain blocked.
    """
    if not candidate.get("direct_source"):
        return False
    new_raw = candidate.get("published_at") or candidate.get("discovery_published_at")
    old_raw = published_record.get("published_at") or published_record.get("original_published_at")
    if not new_raw or not old_raw:
        return False
    try:
        new_dt = datetime.fromisoformat(str(new_raw).replace("Z", "+00:00"))
        old_dt = datetime.fromisoformat(str(old_raw).replace("Z", "+00:00"))
        if new_dt.tzinfo is None:
            new_dt = new_dt.replace(tzinfo=timezone.utc)
        if old_dt.tzinfo is None:
            old_dt = old_dt.replace(tzinfo=timezone.utc)
        return (new_dt - old_dt).total_seconds() >= 18 * 3600
    except (TypeError, ValueError, OverflowError):
        return False


def main() -> None:
    now_de = datetime.now(GERMANY_TZ)
    now_utc = datetime.now(timezone.utc)
    cutoff = now_utc - timedelta(hours=SEARCH_LOOKBACK_HOURS)

    print("=" * 78)
    print("🟢 CONTINENTAL NEWS BOT v8.2 — PRODUCTION-FIRST")
    print("=" * 78)
    print(f"🇩🇪 Zeit in Deutschland: {now_de:%Y-%m-%d %H:%M:%S}")
    print(f"🔎 Discovery: letzte {SEARCH_LOOKBACK_HOURS} Stunden | Veröffentlichung: 48h normal / 14 Tage Produkt-Technologie / 7 Tage Werk-Investition / 7 Tage kritisch/Korbach | Reifen-Stories: {STORIES_LOOKBACK_HOURS} Stunden")
    print("🛞 Direkt: Continental Reifen Stories + Unermüdlich-Blog + Sitemap-Fallback (7 Tage)")
    print("📰 Direkt-RSS: tagesschau + hessenschau")
    print("🚫 Jobs/Vakanzen: Suche und Veröffentlichung vollständig deaktiviert")
    print("🔎 Google News: breiter deutscher Fallback + Originalartikel-Prüfung")
    print(f"🧠 Relevanz: 0–100 | Mindestwert: {PENDING_MIN_RELEVANCE} | Queue-Limit: {MAX_PENDING_ITEMS}")
    print("⏱️ Frische: 48h normal → 14 Tage Produkt/Technologie → 7 Tage Werk/Investition → 7 Tage kritisch/Korbach")
    print("📢 Täglicher Such- und Veröffentlichungszeitpunkt: 09:00 Europe/Berlin")
    print(f"📌 Maximal pro Tag: {MAX_POSTS_PER_RUN} News")
    print("⭐ Prioritäten: Continental News → Werke/Produktion → Reifen/Technologie → Unternehmen/Management → Mitarbeiterleben")
    print("🧹 Queue: schwache/alte News werden automatisch entfernt; Status wird nach jeder erfolgreichen Veröffentlichung gespeichert")
    print("=" * 78)

    published = load_json(PUBLISHED_FILE, [])
    published_url_keys = {canonical_url(x.get("article_url", "")) for x in published if x.get("article_url")}
    published_dedup_keys = set().union(*(publication_dedup_keys(x) for x in published)) if published else set()
    seen_run_urls: set[str] = set()
    pending = prune_pending(load_json(PENDING_FILE, []), now_utc)
    messages = load_json(MESSAGES_FILE, [])
    print(f"💾 Стан GitHub: published={len(published)} | queue={len(pending)}")

    if now_de.hour != PUBLISH_HOUR and not FORCE_RUN and not BOOTSTRAP_MODE:
        print(f"⏳ Nicht 09:00 Uhr in Deutschland (aktuell {now_de:%H:%M}). Dieser Lauf wird übersprungen.")
        return
    if FORCE_RUN:
        print("⚡ FORCE_RUN=1: Zeitprüfung für manuellen Lauf übersprungen.")
    elif BOOTSTRAP_MODE:
        print("🚀 BOOTSTRAP_MODE=1: Zeitprüfung übersprungen.")

    raw = fetch_candidates(cutoff)
    discovered_news = len(raw)
    print(f"🔎 Gefunden: {len(raw)} | 📰 News: {discovered_news}")

    queued_news_added = 0
    accepted_news = 0

    for candidate in raw:
        try:
            if candidate.get("is_job"):
                record_rejection("jobs_disabled")
                continue

            # v5.6: do NOT apply freshness before opening the original article.
            # Discovery metadata often lacks the event terms needed to classify
            # a 7/14-day important story. The authoritative freshness decision
            # happens after article text has been fetched in enrich_candidate().

            # Resolve Google News once and eliminate exact-source duplicates
            # before enrichment. This is the main protection against
            # translation 429s and repeated processing of the same article.
            resolved_url = candidate.get("google_url", "") if candidate.get("direct_source") else decode_google_url(candidate.get("google_url", ""))
            if not resolved_url:
                record_rejection("invalid_or_google_url")
                continue
            candidate["_resolved_article_url"] = resolved_url
            candidate_key = canonical_url(resolved_url)
            if candidate_key in seen_run_urls:
                record_rejection("duplicate_source_within_run")
                print(f"⏭️ Doppelte Entdeckung im selben Lauf übersprungen: {candidate.get('title','')[:110]}")
                continue
            if candidate_key in published_url_keys:
                matching_published = next(
                    (x for x in published if canonical_url(x.get("article_url", "")) == candidate_key),
                    None,
                )
                if not matching_published or not published_url_is_republishable(candidate, matching_published):
                    record_rejection("duplicate_against_published")
                    print(f"⏭️ Bereits veröffentlicht – vor Übersetzung übersprungen: {candidate.get('title','')[:110]}")
                    continue
                print(f"🔄 Stable-URL revision erkannt – erneute Prüfung: {candidate.get('title','')[:110]}")
            seen_run_urls.add(candidate_key)

            # Permanent archive guard before expensive enrichment. This also catches
            # the same story when the publisher changes tracking parameters or
            # the Google News URL resolves differently on a later run.
            candidate_keys = publication_dedup_keys({"article_url": resolved_url, "title": candidate.get("title", "")})
            if candidate_keys & published_dedup_keys:
                record_rejection("duplicate_against_published")
                print(f"⏭️ Permanenter Archiv-Dedup: {candidate.get('title','')[:110]}")
                continue

            item = enrich_candidate(candidate)
            if not item:
                continue

            # v5.9.1: hard relevance gate BEFORE queue insertion.
            if not item.get("is_job"):
                floor = production_relevance_floor(item)
                if int(item.get("relevance_score", 0) or 0) < floor:
                    record_rejection("below_queue_relevance_gate")
                    print(f"⛔ Queue-Gate: {item.get('title','')[:110]} | Relevanz={item.get('relevance_score',0)} < {floor} | Klasse={item.get('editorial_class','company')}")
                    continue

            if archive_has_exact_publication(item, published):
                record_rejection("duplicate_against_published")
                print(f"⏭️ Archiv-Dedup nach Originalauflösung: {item.get('title','')[:110]}")
                continue

            if is_duplicate_event(item, published):
                record_rejection("duplicate_against_published")
                dup_reason = duplicate_decision(item, published)[1]
                print(f"⏭️ Bereits veröffentlicht/technischer Duplikat-Check: {item.get('title','')[:120]} | Grund={dup_reason}")
                continue

            pending, added, replaced = merge_pending_best(pending, item)
            if added:
                queued_news_added += 1
            if not added:
                record_rejection("duplicate_against_pending")
                print(
                    f"⏭️ Bereits in Queue/gleiches Ereignis: {item.get('title','')[:120]} | "
                    f"Quelle={item.get('source_name','')} | "
                    f"Event={','.join(item_event_families(item)) or '-'}"
                )
                continue
            if replaced:
                print(f"🔁 Queue-Quelle verbessert: {item.get('title','')[:120]}")

            accepted_news += 1

            action = "Quelle ersetzt" if replaced else "In Warteschlange"
            print(
                f"📥 {action}: {item['title'][:120]} | Relevanz {item.get('relevance_score', 0)}"
            )

        except Exception as exc:
            print(
                f"⚠️ Kandidatenfehler: {type(exc).__name__}: {exc} | "
                f"Titel={candidate.get('title','')[:100]} | "
                f"URL={candidate.get('google_url','')[:180]}"
            )

    # v5.10.3 coverage safeguard: keep at least the strongest fresh news
    # candidates in the queue; do not inject low-relevance filler merely to
    # make the queue look full. The queue is therefore allowed to be small
    # when there truly are no additional quality stories.
    pending = trim_pending(pending)
    news_count = sum(1 for x in pending if not x.get("is_job"))
    if news_count < 2:
        print(f"ℹ️ Coverage-Hinweis: nur {news_count} hochwertige News in der Queue; kein künstlicher Füller")
    save_json(PENDING_FILE, pending)

    queue_news_before_publish = sum(1 for x in pending if not x.get("is_job"))
    print(
        f"📦 Lauf-Zusammenfassung: gefunden={len(raw)} (News={discovered_news}, Jobs=0) | "
        f"akzeptiert={accepted_news} (News={accepted_news}) | "
        f"neu/ersetzt in Queue={queued_news_added} (News={queued_news_added}) | "
        f"Queue vor Publikation={len(pending)} (News={queue_news_before_publish})"
    )


    pending.sort(
        key=lambda x: (
            {"korbach_strategic": 5, "korbach_production": 4, "production": 3, "tire_technology": 2, "company": 1}.get(x.get("editorial_class") or item_editorial_class(x), 1),
            x.get("priority_score", 0),
            x.get("published_at", ""),
        ),
        reverse=True,
    )

    log_publication_candidates(pending, published)
    eligible_news_count = sum(1 for x in pending if not x.get("is_job") and not is_duplicate_event(x, published))
    print(f"🎯 Veröffentlichungsfähig: News={eligible_news_count}")
    batch = select_publication_batch(pending, published)
    selected_keys = {canonical_url(x.get("article_url", "")) for x in batch}
    print(f"📤 Auswahl für heute: {len(batch)} News | Maximum {MAX_POSTS_PER_RUN}")
    for idx, selected in enumerate(batch, 1):
        print(
            f"   📌 Auswahl #{idx}: NEWS | "
            f"{selected.get('title','')[:120]} | "
            f"Rel={selected.get('relevance_score',0)} | Pri={selected.get('priority_score',0)}"
        )

    remaining = []
    published_now = 0

    for item in pending:
        item_key = canonical_url(item.get("article_url", ""))
        if item_key not in selected_keys:
            remaining.append(item)
            continue
        # FINAL HARD GUARD: never send an item whose permanent publication key
        # is already in the archive, even if queue state survived an interruption.
        if archive_has_exact_publication(item, published):
            print(f"⛔ FINAL ARCHIVE DEDUP: {item.get('title','')[:110]}")
            continue

        is_dup, dup_reason, dup_score = duplicate_decision(item, published)
        if is_dup:
            print(
                f"⏭️ Veröffentlichung übersprungen (Duplikat): {item.get('title','')[:100]} | "
                f"Grund={dup_reason} | Score={dup_score:.2f}"
            )
            continue
        if dup_score >= 0.70:
            print(
                f"🟡 Gleiches Thema möglich, neue Meldung zugelassen: "
                f"{item.get('title','')[:100]} | Score={dup_score:.2f}"
            )

        message_id = send_item(item)

        if message_id is None:
            remaining.append(item)
            continue

        record = {
            "article_url": item["article_url"],
            "title": item["title"],
            "source_name": item.get("source_name", ""),
            "primary_category": item["primary_category"],
            "categories": item["categories"],
            "plant": item.get("plant"),
            "event_families": item.get("event_families", []),
            "event_key": item.get("event_key", ""),
            "summary": clean_text(item.get("summary", ""))[:5000],
            "summary_de": clean_text(item.get("summary_de", ""))[:5000],
            "article_text": clean_text(item.get("article_text", ""))[:12000],
            "published_at": item.get("published_at", ""),
            "sent_at": datetime.now(timezone.utc).isoformat(),
            "message_id": message_id,
            "dedup_keys": sorted(publication_dedup_keys(item)),
        }

        published.append(record)
        published_dedup_keys.update(publication_dedup_keys(record))
        messages.append({
            "message_id": message_id,
            "article_url": item["article_url"],
            "title": item["title"],
            "primary_category": item["primary_category"],
            "sent_at": record["sent_at"],
        })

        published_now += 1

        save_json(PUBLISHED_FILE, published)
        save_json(MESSAGES_FILE, messages)

        # v5.10.2+: checkpoint the queue after EVERY successful Telegram send.
        # This prevents a crash/interruption later in the same run from leaving
        # already-published items in continental_pending.json and causing the
        # next GitHub Actions run to rediscover stale queue state.
        checkpoint_remaining = [
            x for x in pending
            if canonical_url(x.get("article_url", "")) != item_key
        ]
        save_json(PENDING_FILE, checkpoint_remaining)

        time.sleep(0.5)

    save_json(PUBLISHED_FILE, published)
    save_json(PENDING_FILE, remaining)
    save_json(MESSAGES_FILE, messages)

    print("=" * 78)
    print("✅ FERTIG")
    print(f"📢 Jetzt veröffentlicht: {published_now}")
    print(f"📚 Archiv: {len(published)}")
    print(f"📥 Noch in Warteschlange: {len(remaining)}")
    print("🗄️ Alte Telegram-Nachrichten werden NICHT gelöscht.")
    print("=" * 78)


if __name__ == "__main__":
    main()
