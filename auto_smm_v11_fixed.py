from __future__ import annotations
from typing import TYPE_CHECKING, Dict, List, Optional, Tuple
from collections import deque
if TYPE_CHECKING:
    from cardinal import Cardinal

from urllib.parse import quote
import re
import os
import json
import logging
import random
import threading
import requests
import shutil
import time
import io
import html
import hmac
import sys
import sqlite3
import subprocess

from datetime import datetime, timedelta

from FunPayAPI.updater.events import NewMessageEvent, NewOrderEvent
from FunPayAPI import enums

import uuid
import hashlib
from telebot import types
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton


NAME = "AutoSMM"
VERSION = "4.2"
DESCRIPTION = "Плагин для автоматической накрутки через 2+ сервис"
CREDITS = ""
UUID = "c800e7e9-05ce-43eb-addc-4f5841f79726"
SETTINGS_PAGE = False


LOGGER_PREFIX = "[AUTO autosmm]"
logger = logging.getLogger("FPC.autosmm")

waiting_for_lots_upload = set()

UPDATE = """
Примечания к обновлению:

- Можно включить/выключить подтверждение ссылки
- Теперь правильно считается чистая прибыль
- Исправлены некоторые мелкие баги
"""


VALID_LINKS_PATH = os.path.join("storage", "cache", "valid_link.json")

def load_valid_links() -> List[str]:
    if os.path.exists(VALID_LINKS_PATH):
        with open(VALID_LINKS_PATH, 'r', encoding='utf-8') as f:
            links = json.load(f)
            if not links:
                default_links = [
                    "vk.com", "t.me", "instagram.com", "tiktok.com", "youtube.com",
                    "youtu.be", "twitch.tv", "vt.tiktok.com", "vm.tiktok.com",
                    "www.youtu.be", "www.youtube.com", "twitter.com"
                ]
                save_valid_links(default_links)
                return default_links
            return links
    else:
        default_links = [
            "vk.com", "t.me", "instagram.com", "tiktok.com", "youtube.com",
            "youtu.be", "twitch.tv", "vt.tiktok.com", "vm.tiktok.com",
            "www.youtu.be", "www.youtube.com", "twitter.com"
        ]
        save_valid_links(default_links)
        return default_links

def save_valid_links(links: List[str]):
    os.makedirs(os.path.dirname(VALID_LINKS_PATH), exist_ok=True)
    with open(VALID_LINKS_PATH, 'w', encoding='utf-8') as f:
        json.dump(links, f, ensure_ascii=False, indent=4)

def add_website(message: types.Message, new_site: str):
    valid_links = load_valid_links()
    if new_site not in valid_links:
        valid_links.append(new_site)
        save_valid_links(valid_links)
        bot.send_message(message.chat.id, f"✅ Сайт {new_site} успешно добавлен в список.")
    else:
        bot.send_message(message.chat.id, f"❌ Сайт {new_site} уже есть в списке.")

def remove_website(message: types.Message, site_to_remove: str):
    valid_links = load_valid_links()
    if site_to_remove in valid_links:
        valid_links.remove(site_to_remove)
        save_valid_links(valid_links)
        bot.send_message(message.chat.id, f"✅ Сайт {site_to_remove} успешно удалён из списка.")
    else:
        bot.send_message(message.chat.id, f"❌ Сайт {site_to_remove} не найден в списке.")

LOG_DIR = os.path.join("storage", "logs")
os.makedirs(LOG_DIR, exist_ok=True)
LOG_PATH = os.path.join(LOG_DIR, "auto_smm.log")

logger = logging.getLogger("FPC.autosmm")
logger.setLevel(logging.INFO)


class _JsonLogFormatter(logging.Formatter):
    """
    P.19: компактный JSON-логгер для auto_smm.log. Каждая запись —
    одна строка JSON со стабильными ключами (ts, level, logger, msg, +
    любые поля, переданные через `extra=...`). Греп по полям тривиальный:
        grep '"order_id":"GQBSN1RZ"' auto_smm.log
    Стандартные поля LogRecord (`args`, `pathname`, и т.д.) в вывод не
    попадают — только то, что код явно положил в `extra`.
    """
    _STANDARD_FIELDS = {
        "name", "msg", "args", "levelname", "levelno", "pathname", "filename",
        "module", "exc_info", "exc_text", "stack_info", "lineno", "funcName",
        "created", "msecs", "relativeCreated", "thread", "threadName",
        "processName", "process", "message", "asctime", "taskName",
    }

    def format(self, record: logging.LogRecord) -> str:
        payload = {
            "ts": self.formatTime(record, "%Y-%m-%dT%H:%M:%S"),
            "level": record.levelname,
            "logger": record.name,
            "msg": record.getMessage(),
        }
        for k, v in record.__dict__.items():
            if k in self._STANDARD_FIELDS or k.startswith("_"):
                continue
            try:
                json.dumps(v)  # only include JSON-serialisable extras
                payload[k] = v
            except TypeError:
                payload[k] = repr(v)
        if record.exc_info:
            payload["exc"] = self.formatException(record.exc_info)
        return json.dumps(payload, ensure_ascii=False)


# JSON-handler пишет в auto_smm.log (для парсинга/grep по полям).
file_handler = logging.FileHandler(LOG_PATH, encoding='utf-8')
file_handler.setLevel(logging.INFO)
file_handler.setFormatter(_JsonLogFormatter())
logger.addHandler(file_handler)

# Человеческий handler пишет в кардинал-лог (FPC.autosmm пробрасывается выше).
# Если хочется зеркала JSON в stdout — раскомментировать ниже.
# _stream_h = logging.StreamHandler()
# _stream_h.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
# logger.addHandler(_stream_h)

RUNNING = True
IS_STARTED = True
ORDER_CHECK_THREAD = None
AUTO_LOTS_SEND_THREAD = None

# === P.17: graceful shutdown. ===
# При выгрузке плагина FPC вызывает BIND_TO_DELETE-функцию, она ставит флаг,
# все фоновые потоки засыпают через _SHUTDOWN_EVENT.wait(N) (а не time.sleep)
# и выходят из своих циклов. Таймеры check_order_status тоже проверяют флаг
# перед планированием следующего цикла.
_SHUTDOWN_EVENT = threading.Event()

orders_info = {}
processed_users = {}
waiting_for_link: Dict[str, Dict] = {}

bot = None
config = {}
lot_mapping = {}
cardinal_instance = None

CONFIG_PATH = os.path.join("storage", "cache", "auto_lots.json")
ORDERS_PATH = os.path.join("storage", "cache", "auto_smm_orders.json")
ORDERS_DATA_PATH = os.path.join("storage", "cache", "orders_data.json")
STATE_PATH = os.path.join("storage", "cache", "auto_smm_state.json")
BACKUP_DIR = os.path.join("storage", "cache", "backups")
# === P.29: customer profiles ===
CUSTOMER_PROFILES_PATH = os.path.join("storage", "cache", "auto_smm_customers.json")
# === v10: SQLite ===
DB_PATH = os.path.join("storage", "cache", "auto_smm.db")
os.makedirs(os.path.dirname(ORDERS_PATH), exist_ok=True)
os.makedirs(os.path.dirname(ORDERS_DATA_PATH), exist_ok=True)
os.makedirs(BACKUP_DIR, exist_ok=True)


def _rebind_paths_for_account(account_id) -> None:
    """
    P.32: при наличии нескольких FPC-аккаунтов разводим state по подкаталогам:
        storage/cache/auto_smm/<account_id>/auto_lots.json
        storage/cache/auto_smm/<account_id>/orders_data.json
        ...
    Если нашли legacy-файлы (storage/cache/auto_lots.json и т.д.) — мигрируем
    их в новый префикс ОДИН раз, оставив legacy-файлы как .legacy.bak (для отката).
    """
    global CONFIG_PATH, ORDERS_PATH, ORDERS_DATA_PATH, STATE_PATH
    global BACKUP_DIR, CUSTOMER_PROFILES_PATH, DB_PATH
    if not account_id:
        return
    base = os.path.join("storage", "cache", "auto_smm", str(account_id))
    os.makedirs(base, exist_ok=True)
    new_paths = {
        "CONFIG_PATH": os.path.join(base, "auto_lots.json"),
        "ORDERS_PATH": os.path.join(base, "auto_smm_orders.json"),
        "ORDERS_DATA_PATH": os.path.join(base, "orders_data.json"),
        "STATE_PATH": os.path.join(base, "auto_smm_state.json"),
        "BACKUP_DIR": os.path.join(base, "backups"),
        "CUSTOMER_PROFILES_PATH": os.path.join(base, "auto_smm_customers.json"),
        "DB_PATH": os.path.join(base, "auto_smm.db"),
    }
    os.makedirs(new_paths["BACKUP_DIR"], exist_ok=True)
    legacy_pairs = [
        (CONFIG_PATH, new_paths["CONFIG_PATH"]),
        (ORDERS_PATH, new_paths["ORDERS_PATH"]),
        (ORDERS_DATA_PATH, new_paths["ORDERS_DATA_PATH"]),
        (STATE_PATH, new_paths["STATE_PATH"]),
        (CUSTOMER_PROFILES_PATH, new_paths["CUSTOMER_PROFILES_PATH"]),
        (DB_PATH, new_paths["DB_PATH"]),
    ]
    migrated = 0
    for legacy, new in legacy_pairs:
        if os.path.exists(legacy) and not os.path.exists(new):
            try:
                shutil.copy2(legacy, new)
                shutil.move(legacy, legacy + ".legacy.bak")
                migrated += 1
            except Exception as e:
                logger.error(f"_rebind_paths_for_account: migrate {legacy}->{new} failed: {e}")
    CONFIG_PATH = new_paths["CONFIG_PATH"]
    ORDERS_PATH = new_paths["ORDERS_PATH"]
    ORDERS_DATA_PATH = new_paths["ORDERS_DATA_PATH"]
    STATE_PATH = new_paths["STATE_PATH"]
    BACKUP_DIR = new_paths["BACKUP_DIR"]
    CUSTOMER_PROFILES_PATH = new_paths["CUSTOMER_PROFILES_PATH"]
    DB_PATH = new_paths["DB_PATH"]
    logger.info(
        f"P.32: paths rebound to per-account dir {base}; migrated={migrated}",
        extra={"event": "paths_rebind", "account_id": str(account_id), "migrated": migrated},
    )

# === P.1: Один общий ре-входный лок для всех JSON-файлов плагина. ===
# Раньше каждая функция создавала локальный threading.Lock() — это означало
# полное отсутствие синхронизации между потоками (разные локи => разные
# мьютексы). Один module-level RLock решает гонки на чтение/запись JSON.
_FILES_LOCK = threading.RLock()

# =====================================================================
# === v10: SQLite слой для orders + customer profiles =================
# =====================================================================
# JSON-массивы при каждом апдейте перезаписывают весь файл — это бьёт по
# I/O и держит _FILES_LOCK на сотни миллисекунд при 1000+ заказах.
# SQLite c WAL: per-row upsert (≪1 мс), читатели не блокируют писателей.
# load_orders_data/save_orders_data остаются как фасад для существующих
# call-sites (50+ мест), внутри идёт чтение/запись из БД.
# =====================================================================

_DB_LOCK = threading.RLock()
_DB_INITIALIZED = False
# Все обязательные поля order'а с дефолтами для UPSERT.
_ORDER_COLUMNS = [
    "order_id", "date", "service_name", "chat_id", "id_zakaz",
    "status", "summa", "chistota", "spent", "spent_rub", "currency",
    "customer_url", "quantity", "service_number", "is_refunded",
    "completed_notification_sent", "buyer_id", "buyer_username",
    "twiboost_id", "last_refill_at", "refill_count",
    # extra хранится как JSON-блоб для будущих полей без миграций
    "extra_json",
]


def _db_connect() -> sqlite3.Connection:
    """Открывает соединение с WAL и нормальным sync."""
    conn = sqlite3.connect(DB_PATH, timeout=30, isolation_level=None)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode = WAL")
    conn.execute("PRAGMA synchronous = NORMAL")
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def _db_init() -> None:
    """Идемпотентная инициализация схемы. Вызывается из init_commands после rebind путей."""
    global _DB_INITIALIZED
    with _DB_LOCK:
        os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
        conn = _db_connect()
        try:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS orders (
                order_id TEXT PRIMARY KEY,
                date TEXT,
                service_name TEXT,
                chat_id INTEGER,
                id_zakaz TEXT,
                status TEXT,
                summa REAL,
                chistota REAL,
                spent REAL,
                spent_rub REAL,
                currency TEXT,
                customer_url TEXT,
                quantity INTEGER,
                service_number INTEGER,
                is_refunded INTEGER DEFAULT 0,
                completed_notification_sent INTEGER DEFAULT 0,
                buyer_id INTEGER,
                buyer_username TEXT,
                twiboost_id TEXT,
                last_refill_at REAL,
                refill_count INTEGER DEFAULT 0,
                extra_json TEXT,
                updated_at REAL DEFAULT 0
            );
            CREATE INDEX IF NOT EXISTS idx_orders_status ON orders(status);
            CREATE INDEX IF NOT EXISTS idx_orders_buyer ON orders(buyer_id);
            CREATE INDEX IF NOT EXISTS idx_orders_date ON orders(date);
            CREATE INDEX IF NOT EXISTS idx_orders_refunded ON orders(is_refunded);

            CREATE TABLE IF NOT EXISTS customers (
                buyer_id TEXT PRIMARY KEY,
                buyer_username TEXT,
                first_order_at REAL,
                orders_count INTEGER DEFAULT 0,
                total_spent_rub REAL DEFAULT 0,
                last_order_at REAL DEFAULT 0,
                history_30d_json TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_customers_total ON customers(total_spent_rub DESC);
            CREATE INDEX IF NOT EXISTS idx_customers_last ON customers(last_order_at DESC);
            """)
        finally:
            conn.close()
        _DB_INITIALIZED = True
        logger.info("_db_init: schema ready", extra={"event": "db_init", "path": DB_PATH})


_KNOWN_ORDER_KEYS = set(_ORDER_COLUMNS)


def _row_to_order(row: sqlite3.Row) -> Dict:
    """Приводит sqlite-строку к dict в формате, который ждут существующие call-sites."""
    if row is None:
        return {}
    d = dict(row)
    extra_json = d.pop("extra_json", None)
    d.pop("updated_at", None)
    if extra_json:
        try:
            extra = json.loads(extra_json)
            if isinstance(extra, dict):
                for k, v in extra.items():
                    d.setdefault(k, v)
        except Exception:
            pass
    # bool-нормализация
    d["is_refunded"] = bool(d.get("is_refunded"))
    d["completed_notification_sent"] = bool(d.get("completed_notification_sent"))
    return d


def _order_to_row(order: Dict) -> Dict:
    """Готовит dict для INSERT/UPDATE: вытаскивает known-поля + кладёт остальное в extra_json."""
    row = {col: None for col in _ORDER_COLUMNS}
    extra: Dict = {}
    for k, v in (order or {}).items():
        if k in _KNOWN_ORDER_KEYS and k != "extra_json":
            row[k] = v
        else:
            extra[k] = v
    row["extra_json"] = json.dumps(extra, ensure_ascii=False) if extra else None
    # типы
    if row["is_refunded"] is not None:
        row["is_refunded"] = 1 if row["is_refunded"] else 0
    if row["completed_notification_sent"] is not None:
        row["completed_notification_sent"] = 1 if row["completed_notification_sent"] else 0
    return row


def _db_load_all_orders() -> List[Dict]:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            rows = conn.execute("SELECT * FROM orders ORDER BY date").fetchall()
            return [_row_to_order(r) for r in rows]
        finally:
            conn.close()


def _db_upsert_orders(orders: List[Dict]) -> int:
    if not _DB_INITIALIZED:
        _db_init()
    if not orders:
        return 0
    cols = _ORDER_COLUMNS
    placeholders = ", ".join("?" for _ in cols)
    update_assignments = ", ".join(f"{c}=excluded.{c}" for c in cols if c != "order_id")
    sql = (
        f"INSERT INTO orders ({', '.join(cols)}, updated_at) VALUES ({placeholders}, ?) "
        f"ON CONFLICT(order_id) DO UPDATE SET {update_assignments}, updated_at=excluded.updated_at"
    )
    n = 0
    with _DB_LOCK:
        conn = _db_connect()
        try:
            conn.execute("BEGIN")
            now = time.time()
            for o in orders:
                if not o.get("order_id"):
                    continue
                row = _order_to_row(o)
                values = [row[c] for c in cols] + [now]
                conn.execute(sql, values)
                n += 1
            conn.execute("COMMIT")
        except Exception as e:
            conn.execute("ROLLBACK")
            logger.error(f"_db_upsert_orders failed: {e}", extra={"event": "db_upsert_fail"})
            raise
        finally:
            conn.close()
    return n


def _db_get_order(order_id: str) -> Optional[Dict]:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            row = conn.execute("SELECT * FROM orders WHERE order_id = ?", (str(order_id),)).fetchone()
            return _row_to_order(row) if row else None
        finally:
            conn.close()


def _db_remove_order(order_id: str) -> bool:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            cur = conn.execute("DELETE FROM orders WHERE order_id = ?", (str(order_id),))
            return cur.rowcount > 0
        finally:
            conn.close()


def _db_clear_orders() -> int:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            cur = conn.execute("DELETE FROM orders")
            return cur.rowcount
        finally:
            conn.close()


def _db_migrate_from_json(path: str) -> int:
    """
    Одноразовая миграция: если БД пустая и есть orders_data.json — переносим
    содержимое в SQLite, JSON переименовываем в .legacy.bak. Идемпотентно:
    повторный вызов ничего не делает, если в БД уже есть записи.
    """
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            n_existing = conn.execute("SELECT COUNT(*) FROM orders").fetchone()[0]
        finally:
            conn.close()
    if n_existing > 0:
        return 0
    if not os.path.exists(path):
        return 0
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, list):
            logger.warning(f"_db_migrate_from_json: {path} не список, пропуск")
            return 0
        n = _db_upsert_orders(data)
        try:
            shutil.move(path, path + ".legacy.bak")
        except Exception as e:
            logger.warning(f"_db_migrate_from_json: rename {path} failed: {e}")
        logger.info(
            f"v10: мигрировано {n} заказов из {path} в SQLite",
            extra={"event": "db_migrated", "n": n, "src": path},
        )
        return n
    except Exception as e:
        logger.error(f"_db_migrate_from_json failed: {e}", extra={"event": "db_migrate_fail"})
        return 0


# === Customer profiles helpers (SQLite) ===
def _db_load_all_customers() -> Dict[str, Dict]:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            rows = conn.execute("SELECT * FROM customers").fetchall()
            out: Dict[str, Dict] = {}
            for r in rows:
                d = dict(r)
                hist = d.pop("history_30d_json", None)
                try:
                    d["history_30d"] = json.loads(hist) if hist else []
                except Exception:
                    d["history_30d"] = []
                out[str(d.get("buyer_id"))] = d
            return out
        finally:
            conn.close()


def _db_upsert_customers(profiles: Dict[str, Dict]) -> int:
    if not _DB_INITIALIZED:
        _db_init()
    if not profiles:
        return 0
    sql = (
        "INSERT INTO customers (buyer_id, buyer_username, first_order_at, orders_count, "
        "total_spent_rub, last_order_at, history_30d_json) VALUES (?, ?, ?, ?, ?, ?, ?) "
        "ON CONFLICT(buyer_id) DO UPDATE SET "
        "buyer_username=excluded.buyer_username, "
        "orders_count=excluded.orders_count, "
        "total_spent_rub=excluded.total_spent_rub, "
        "last_order_at=excluded.last_order_at, "
        "history_30d_json=excluded.history_30d_json"
    )
    n = 0
    with _DB_LOCK:
        conn = _db_connect()
        try:
            conn.execute("BEGIN")
            for bid, prof in profiles.items():
                values = (
                    str(bid),
                    prof.get("buyer_username"),
                    float(prof.get("first_order_at", 0) or 0),
                    int(prof.get("orders_count", 0) or 0),
                    float(prof.get("total_spent_rub", 0) or 0),
                    float(prof.get("last_order_at", 0) or 0),
                    json.dumps(prof.get("history_30d", []), ensure_ascii=False),
                )
                conn.execute(sql, values)
                n += 1
            conn.execute("COMMIT")
        except Exception as e:
            conn.execute("ROLLBACK")
            logger.error(f"_db_upsert_customers failed: {e}")
            raise
        finally:
            conn.close()
    return n


def _db_migrate_customers_from_json(path: str) -> int:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            n_existing = conn.execute("SELECT COUNT(*) FROM customers").fetchone()[0]
        finally:
            conn.close()
    if n_existing > 0:
        return 0
    if not os.path.exists(path):
        return 0
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return 0
        n = _db_upsert_customers(data)
        try:
            shutil.move(path, path + ".legacy.bak")
        except Exception:
            pass
        logger.info(
            f"v10: мигрировано {n} customer-профилей из {path} в SQLite",
            extra={"event": "db_customers_migrated", "n": n},
        )
        return n
    except Exception as e:
        logger.error(f"_db_migrate_customers_from_json failed: {e}")
        return 0


# === P.7: Единые таймауты на любые HTTP-запросы наружу (SMM-сервисы, FunPay). ===
# (connect, read) в секундах. Всегда используйте HTTP_SESSION.get/post —
# голый requests.get(...) без таймаута может повесить поток навсегда.
HTTP_TIMEOUT = (5, 15)
HTTP_SESSION = requests.Session()
HTTP_SESSION.headers.update({"User-Agent": f"AutoSMM/{VERSION}"})


# =====================================================================
# === v11 Foundation: error classification, URL normalization, =========
# === degraded mode, CSRF cache, error log buffer ======================
# =====================================================================

# v11.P2.4: классификация ошибок. Используется в JSON-логах (extra.error_type)
# и в /autosmm_errors дашборде.
ERROR_TYPE_NETWORK = "network"          # таймауты, ConnectionError, DNS
ERROR_TYPE_PROVIDER_4XX = "provider_4xx"  # 400/404 — permanent, не ретраить
ERROR_TYPE_PROVIDER_5XX = "provider_5xx"  # 5xx — retryable
ERROR_TYPE_AUTH = "auth"                 # 401/403 — ключ протух
ERROR_TYPE_RATE_LIMIT = "rate_limit"     # 429
ERROR_TYPE_JSON = "json"                 # сервис вернул не-JSON / битый JSON
ERROR_TYPE_FUNDS = "funds"               # not_enough_funds
ERROR_TYPE_BAD_LINK = "bad_link"         # TwiBoost не принял ссылку
ERROR_TYPE_BAD_QUANTITY = "bad_quantity" # quantity вне пределов
ERROR_TYPE_SSL_EXPIRED = "ssl_expired"   # CERTIFICATE_VERIFY_FAILED
ERROR_TYPE_REFUND_DUP = "refund_dup"     # «Деньги уже возвращены» — benign
ERROR_TYPE_UNKNOWN = "unknown"

# Регексы под текст ответа TwiBoost-совместимых SMM-сервисов.
_TWIBOOST_BAD_LINK = re.compile(r'\b(neworder\.error\.bad-?link|invalid[_\s-]?link|bad[_\s-]?link)\b', re.I)
_TWIBOOST_BAD_QTY = re.compile(r'\b(quantity|min[_\s-]?quantity|max[_\s-]?quantity|bad[_\s-]?quantity)\b', re.I)
_TWIBOOST_NOT_ENOUGH = re.compile(r'\b(not[_\s-]?enough[_\s-]?funds|insufficient|low[_\s-]?balance)\b', re.I)
_TWIBOOST_NOT_ALLOWED = re.compile(r'\b(not[_\s-]?allowed|service[_\s-]?disabled|inactive)\b', re.I)


def classify_error(exc: Optional[BaseException] = None, response: Optional[requests.Response] = None,
                   text: Optional[str] = None) -> str:
    """v11.P2.4: возвращает error_type из набора ERROR_TYPE_*. Один вход — exc или response/text."""
    body = text or ""
    if response is not None:
        try:
            body = response.text or body
        except Exception:
            pass
        sc = response.status_code
        if sc == 401 or sc == 403:
            return ERROR_TYPE_AUTH
        if sc == 429:
            return ERROR_TYPE_RATE_LIMIT
        if 500 <= sc < 600:
            return ERROR_TYPE_PROVIDER_5XX
        if 400 <= sc < 500:
            # 400 — пробуем детализировать по телу ответа
            low = body.lower()
            if _TWIBOOST_NOT_ENOUGH.search(low):
                return ERROR_TYPE_FUNDS
            if _TWIBOOST_BAD_LINK.search(low):
                return ERROR_TYPE_BAD_LINK
            if _TWIBOOST_BAD_QTY.search(low):
                return ERROR_TYPE_BAD_QUANTITY
            return ERROR_TYPE_PROVIDER_4XX
    if exc is not None:
        s = repr(exc)
        if "CERTIFICATE_VERIFY_FAILED" in s or "certificate has expired" in s:
            return ERROR_TYPE_SSL_EXPIRED
        if isinstance(exc, requests.exceptions.Timeout):
            return ERROR_TYPE_NETWORK
        if isinstance(exc, requests.exceptions.SSLError):
            return ERROR_TYPE_SSL_EXPIRED
        if isinstance(exc, requests.exceptions.ConnectionError):
            return ERROR_TYPE_NETWORK
        if isinstance(exc, json.JSONDecodeError):
            return ERROR_TYPE_JSON
        if isinstance(exc, requests.exceptions.RequestException):
            return ERROR_TYPE_NETWORK
    if body:
        low = body.lower()
        if "уже возвращены" in low or "already refunded" in low:
            return ERROR_TYPE_REFUND_DUP
        if _TWIBOOST_NOT_ENOUGH.search(low):
            return ERROR_TYPE_FUNDS
    return ERROR_TYPE_UNKNOWN


def normalize_smm_link(link: str, *, strip_telegram_startapp: bool = False) -> List[str]:
    """
    v11.1: НИКАКОЙ модификации ссылки. Возвращаем только оригинал.

    Раньше функция генерировала «варианты» с обрезанным query — это ломало
    реферальные ссылки на ботов (`?startapp=r_...`, `?start=...`, mini-app
    просмотры). Покупатель шлёт ссылку → она должна уйти провайдеру as-is.

    Аргумент `strip_telegram_startapp` сохранён для обратной совместимости,
    но игнорируется (default=False).
    """
    if not link:
        return []
    return [link.strip()]


# v11.P2.6: Degraded mode — глобальный флаг, выставляется при шторме одинаковых
# ошибок. Пока активен, новые SMM-заказы откладываются (или блокируются — см. cfg).
class _DegradedState:
    def __init__(self):
        self.until_ts: float = 0.0
        self.reason: str = ""
        self.lock = threading.RLock()

    def enter(self, duration_sec: int, reason: str) -> None:
        with self.lock:
            self.until_ts = max(self.until_ts, time.time() + duration_sec)
            self.reason = reason
        logger.warning(
            f"DEGRADED MODE on for {duration_sec}s: {reason}",
            extra={"event": "degraded_enter", "duration_sec": duration_sec, "reason": reason},
        )

    def is_active(self) -> bool:
        with self.lock:
            return time.time() < self.until_ts

    def remaining_sec(self) -> int:
        with self.lock:
            return max(0, int(self.until_ts - time.time()))


_DEGRADED = _DegradedState()

# v11.P2.6: rate-limiter — учитывает ошибки за окно времени.
# Если в окне (default 300s) накоплено >= threshold (default 5) одинаковых
# (error_type, service_number), включаем degraded mode на ERROR_BACKOFF_SEC.
ERROR_RATE_WINDOW_SEC = 300
ERROR_RATE_THRESHOLD = 5
DEGRADED_BACKOFF_SEC = 600  # 10 мин

# Кольцевой буфер последних ошибок для /autosmm_errors. Каждый элемент:
# {"ts": float, "error_type": str, "service": int|None, "order_id": str|None, "msg": str}
_ERROR_LOG_BUF: deque = deque(maxlen=500)
_ERROR_LOG_LOCK = threading.RLock()


def record_error(error_type: str, *, service: Optional[int] = None,
                 order_id: Optional[str] = None, msg: str = "") -> None:
    """v11.P2.4: фиксирует ошибку в буфере + чекает rate-limit для degraded mode."""
    now = time.time()
    with _ERROR_LOG_LOCK:
        _ERROR_LOG_BUF.append({
            "ts": now,
            "error_type": error_type,
            "service": service,
            "order_id": order_id,
            "msg": msg[:300],
        })
        # Считаем сколько (error_type, service) попало в окно.
        threshold_ts = now - ERROR_RATE_WINDOW_SEC
        same = sum(
            1 for e in _ERROR_LOG_BUF
            if e["ts"] >= threshold_ts and e["error_type"] == error_type and e["service"] == service
        )
    # При шторме не-permanent ошибок включаем degraded.
    if same >= ERROR_RATE_THRESHOLD and error_type in (
        ERROR_TYPE_PROVIDER_5XX, ERROR_TYPE_NETWORK, ERROR_TYPE_RATE_LIMIT, ERROR_TYPE_SSL_EXPIRED, ERROR_TYPE_JSON
    ):
        _DEGRADED.enter(DEGRADED_BACKOFF_SEC, f"{same} ошибок типа {error_type} за {ERROR_RATE_WINDOW_SEC}s")


# v11.P4.12: CSRF token cache для FunPay refund. Один токен живёт ~6 минут на FP,
# так что 60–120с кеша экономит ~50% запросов и снижает нагрузку.
_CSRF_TOKEN: Optional[str] = None
_CSRF_TOKEN_TS: float = 0.0
_CSRF_TTL_SEC = 60.0
_CSRF_LOCK = threading.RLock()


def get_cached_csrf(c: "Cardinal") -> Optional[str]:
    """v11: возвращает CSRF из кеша или None если просрочен."""
    with _CSRF_LOCK:
        if _CSRF_TOKEN and (time.time() - _CSRF_TOKEN_TS) < _CSRF_TTL_SEC:
            return _CSRF_TOKEN
    return None


def store_csrf(token: str) -> None:
    global _CSRF_TOKEN, _CSRF_TOKEN_TS
    if not token:
        return
    with _CSRF_LOCK:
        _CSRF_TOKEN = token
        _CSRF_TOKEN_TS = time.time()


# v11.P3.8: SSL fallback — если у провайдера протух cert, временно отключаем verify.
_SSL_FALLBACK_ACTIVE = False
_SSL_FALLBACK_LOCK = threading.RLock()


def maybe_enable_ssl_fallback() -> bool:
    """v11.P3.8: если за окно >2 SSL ошибок — отключаем verify до перезапуска плагина."""
    global _SSL_FALLBACK_ACTIVE
    with _SSL_FALLBACK_LOCK:
        if _SSL_FALLBACK_ACTIVE:
            return True
        # Чекаем буфер ошибок
        now = time.time()
        with _ERROR_LOG_LOCK:
            ssl_errs = sum(
                1 for e in _ERROR_LOG_BUF
                if e["ts"] >= now - 600 and e["error_type"] == ERROR_TYPE_SSL_EXPIRED
            )
        if ssl_errs >= 2:
            _SSL_FALLBACK_ACTIVE = True
            logger.error(
                "v11.P3.8: SSL fallback ENABLED — у провайдера протух cert, "
                "временно отключаю verify до перезапуска плагина.",
                extra={"event": "ssl_fallback_on", "ssl_errs_10min": ssl_errs},
            )
            return True
    return False


def smm_verify() -> bool:
    """v11.P3.8: текущее значение verify для SMM-API запросов."""
    with _SSL_FALLBACK_LOCK:
        return not _SSL_FALLBACK_ACTIVE


# v11.P1.2: pending_refunds — таблица для not_enough_funds очереди.
def _db_init_pending_refunds() -> None:
    if not _DB_INITIALIZED:
        _db_init()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS pending_refunds (
                order_id TEXT PRIMARY KEY,
                buyer_id INTEGER,
                buyer_chat_id INTEGER,
                service_number INTEGER,
                service_id INTEGER,
                link TEXT,
                quantity INTEGER,
                summa REAL,
                first_failed_at REAL,
                last_attempt_at REAL,
                attempts INTEGER DEFAULT 0,
                next_retry_at REAL,
                last_error TEXT,
                state TEXT DEFAULT 'pending'  -- pending|resolved|refunded|cancelled
            );
            CREATE INDEX IF NOT EXISTS idx_pending_next ON pending_refunds(next_retry_at);
            CREATE INDEX IF NOT EXISTS idx_pending_state ON pending_refunds(state);
            """)
        finally:
            conn.close()


# Backoff-расписание для пендинга: 5, 15, 60 минут (всего 3 попытки).
PENDING_RETRY_SCHEDULE_SEC = [5 * 60, 15 * 60, 60 * 60]
PENDING_MAX_ATTEMPTS = len(PENDING_RETRY_SCHEDULE_SEC)


def pending_enqueue(order_id: str, *, buyer_id: int, buyer_chat_id: int, service_number: int,
                    service_id: int, link: str, quantity: int, summa: float, last_error: str) -> None:
    """v11.P1.2: ставим заказ в очередь повторных попыток (not_enough_funds, etc)."""
    _db_init_pending_refunds()
    now = time.time()
    next_at = now + PENDING_RETRY_SCHEDULE_SEC[0]
    sql = (
        "INSERT INTO pending_refunds (order_id, buyer_id, buyer_chat_id, service_number, service_id, "
        "link, quantity, summa, first_failed_at, last_attempt_at, attempts, next_retry_at, last_error, state) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, ?, ?, 'pending') "
        "ON CONFLICT(order_id) DO UPDATE SET "
        "last_attempt_at=excluded.last_attempt_at, "
        "next_retry_at=excluded.next_retry_at, "
        "last_error=excluded.last_error, "
        "state=excluded.state"
    )
    with _DB_LOCK:
        conn = _db_connect()
        try:
            conn.execute(sql, (
                str(order_id), int(buyer_id) if buyer_id else None,
                int(buyer_chat_id) if buyer_chat_id else None,
                int(service_number) if service_number else None,
                int(service_id) if service_id else None,
                link, int(quantity) if quantity else 0, float(summa) if summa else 0.0,
                now, now, next_at, last_error[:500],
            ))
        finally:
            conn.close()
    logger.warning(
        f"v11.P1.2: order #{order_id} → pending_refunds queue (next retry in {PENDING_RETRY_SCHEDULE_SEC[0]//60}m)",
        extra={"event": "pending_enqueue", "order_id": order_id, "service": service_number, "error": last_error},
    )


def pending_due() -> List[Dict]:
    """Возвращает заказы, у которых next_retry_at <= now и state='pending'."""
    _db_init_pending_refunds()
    now = time.time()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            rows = conn.execute(
                "SELECT * FROM pending_refunds WHERE state='pending' AND next_retry_at <= ? ORDER BY next_retry_at",
                (now,),
            ).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()


def pending_mark_attempt_failed(order_id: str, error: str) -> bool:
    """Инкремент attempts, если перевалили MAX — state='refunded' (вызывается дальше refund_order)."""
    _db_init_pending_refunds()
    now = time.time()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            row = conn.execute("SELECT attempts FROM pending_refunds WHERE order_id=?", (str(order_id),)).fetchone()
            if not row:
                return False
            attempts = int(row["attempts"]) + 1
            if attempts >= PENDING_MAX_ATTEMPTS:
                conn.execute(
                    "UPDATE pending_refunds SET attempts=?, last_attempt_at=?, last_error=?, state='refunded' WHERE order_id=?",
                    (attempts, now, error[:500], str(order_id)),
                )
                return True  # надо рефандить
            else:
                next_at = now + PENDING_RETRY_SCHEDULE_SEC[attempts]
                conn.execute(
                    "UPDATE pending_refunds SET attempts=?, last_attempt_at=?, last_error=?, next_retry_at=? WHERE order_id=?",
                    (attempts, now, error[:500], next_at, str(order_id)),
                )
                return False
        finally:
            conn.close()


def pending_mark_resolved(order_id: str) -> None:
    _db_init_pending_refunds()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            conn.execute("UPDATE pending_refunds SET state='resolved' WHERE order_id=?", (str(order_id),))
        finally:
            conn.close()


def pending_count() -> int:
    _db_init_pending_refunds()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            r = conn.execute("SELECT COUNT(*) FROM pending_refunds WHERE state='pending'").fetchone()
            return int(r[0])
        finally:
            conn.close()


def _admin_notify(text: str) -> None:
    """v11: безопасный TG-алерт админу. Молча игнорирует ошибки доставки."""
    try:
        cfg = load_config()
    except Exception:
        return
    admin = cfg.get("notification_chat_id")
    if not admin:
        return
    try:
        # Используем модульный bot если он уже создан, иначе пропускаем.
        if "bot" in globals() and globals()["bot"] is not None:
            globals()["bot"].send_message(admin, text, parse_mode="HTML")
    except Exception as e:
        logger.debug(f"_admin_notify failed: {e}")


def _redact_url(url: str) -> str:
    """Маскирует параметр key=... в URL для безопасного логирования."""
    return re.sub(r'(?i)(key=)[^&]+', r'\1***', url or "")


# === P.16: ретраи с экспоненциальным backoff для исходящих SMM-запросов. ===
# Раньше один таймаут TwiBoost = автоматический refund покупателю. Теперь
# 4 попытки (1s, 2s, 4s, 8s + jitter), и только если все упали — поднимаем
# исключение и вызывающая сторона решает что делать (refund или retry-later).
HTTP_MAX_RETRIES = 4
HTTP_BACKOFF_BASE = 1.0  # секунды
_RETRYABLE_STATUSES = {429, 500, 502, 503, 504}


def http_request_with_retries(
    method: str,
    url: str,
    *,
    max_retries: int = HTTP_MAX_RETRIES,
    backoff_base: float = HTTP_BACKOFF_BASE,
    timeout: Optional[Tuple[float, float]] = None,
    log_extra: Optional[Dict] = None,
    **kwargs,
) -> requests.Response:
    """
    P.16: универсальный HTTP-вызов с ретраями. Бросает последнее исключение
    или последний неуспешный response (как HTTPError), если все попытки
    провалились. Используется во всех запросах к SMM-API.

    Что считается ретраябельным:
      - сетевые исключения (ConnectionError, Timeout, RequestException);
      - HTTP-коды 429, 500, 502, 503, 504.
    Остальные 4xx (400, 403, 404, …) НЕ ретраятся — это ошибки клиента.
    """
    method = method.upper()
    timeout = timeout if timeout is not None else HTTP_TIMEOUT
    last_exc: Optional[BaseException] = None
    last_resp: Optional[requests.Response] = None
    extra = dict(log_extra or {})

    for attempt in range(1, max_retries + 1):
        if _SHUTDOWN_EVENT.is_set():
            raise RuntimeError("plugin shutting down — abort retries")
        try:
            resp = HTTP_SESSION.request(method, url, timeout=timeout, **kwargs)
            if resp.status_code in _RETRYABLE_STATUSES:
                last_resp = resp
                logger.warning(
                    "http_retry: server returned retryable status",
                    extra={
                        **extra,
                        "url": _redact_url(url),
                        "method": method,
                        "status": resp.status_code,
                        "attempt": attempt,
                        "max_retries": max_retries,
                    },
                )
            else:
                return resp
        except requests.exceptions.RequestException as ex:
            last_exc = ex
            logger.warning(
                "http_retry: request exception",
                extra={
                    **extra,
                    "url": _redact_url(url),
                    "method": method,
                    "error": repr(ex),
                    "attempt": attempt,
                    "max_retries": max_retries,
                },
            )

        if attempt < max_retries:
            sleep_for = backoff_base * (2 ** (attempt - 1))
            sleep_for += random.uniform(0, sleep_for * 0.25)  # jitter
            # Уважаем shutdown — не задерживаем выгрузку.
            if _SHUTDOWN_EVENT.wait(sleep_for):
                raise RuntimeError("plugin shutting down — abort retries")

    # все попытки кончились
    if last_exc is not None:
        raise last_exc
    if last_resp is not None:
        last_resp.raise_for_status()
        return last_resp
    raise RuntimeError("http_request_with_retries: no attempt was made")


# === P.4: Лимит попыток проверки статуса заказа в SMM-сервисе. ===
# 288 попыток × 5 минут (default) ≈ 24 часа. Дальше — авто-рефанд и
# уведомление админу, чтобы цепочка таймеров не крутилась бесконечно.
MAX_STATUS_ATTEMPTS = 288

# === P.14: таймауты диалога с покупателем (await_link / await_confirm). ===
# Если покупатель не присылает ссылку 30 минут — напоминаем (один раз).
# Если 24 часа без ответа — авто-рефанд + удаление записи из waiting_for_link.
DIALOG_REMINDER_AFTER_SEC = 30 * 60      # 30 минут
DIALOG_TIMEOUT_AFTER_SEC = 24 * 60 * 60  # 24 часа
DIALOG_WATCHER_INTERVAL_SEC = 60         # как часто сканируем
_DIALOG_WATCHER_THREAD: Optional[threading.Thread] = None


def load_state():
    """Восстанавливает waiting_for_link из STATE_PATH (для переживания рестартов FPC)."""
    global waiting_for_link
    with _FILES_LOCK:
        if os.path.exists(STATE_PATH):
            try:
                with open(STATE_PATH, 'r', encoding='utf-8') as f:
                    waiting_for_link = json.load(f)
                logger.info(f"load_state: восстановлено {len(waiting_for_link)} диалогов.")
            except Exception as e:
                logger.error(f"load_state failed: {e}")
                waiting_for_link = {}


def save_state():
    """Атомарно пишет waiting_for_link на диск; ошибка записи только логируется."""
    with _FILES_LOCK:
        try:
            os.makedirs(os.path.dirname(STATE_PATH) or ".", exist_ok=True)
            with open(STATE_PATH, 'w', encoding='utf-8') as f:
                json.dump(waiting_for_link, f, indent=4, ensure_ascii=False)
        except Exception as e:
            logger.error(f"save_state failed: {e}")


load_state()

def load_config() -> Dict:
    logger.info("Загрузка конфигурации (auto_lots.json)...")
    
    file_lock = _FILES_LOCK
    
    try:
        with file_lock:
            if os.path.exists(CONFIG_PATH):
                try:
                    with open(CONFIG_PATH, 'r', encoding='utf-8') as f:
                        file_content = f.read()
                        
                    if not file_content.strip():
                        logger.error(f"Файл конфигурации {CONFIG_PATH} пуст. Создаем новый файл конфигурации.")
                        cfg = create_default_config()
                        save_config(cfg)
                        return cfg
                        
                    try:
                        cfg = json.loads(file_content)
                    except json.JSONDecodeError as e:
                        logger.error(f"Ошибка при чтении JSON: {e}. Создаем новый файл конфигурации.")
                        cfg = create_default_config()
                        save_config(cfg)
                        return cfg
                    
                    if "services" not in cfg:
                        cfg["services"] = {
                            "1": {
                                "api_url": "https://service1.com/api/v2",
                                "api_key": "SERVICE_1_KEY"
                            },
                            "2": {
                                "api_url": "https://service2.com/api/v2",
                                "api_key": "SERVICE_2_KEY"
                            }
                        }
                    if "auto_refunds" not in cfg:
                        cfg["auto_refunds"] = True
                    if "confirm_link" not in cfg:
                        cfg["confirm_link"] = True
                    if "messages" not in cfg:
                        cfg["messages"] = {
                            "after_payment": "❤️ Благодарим за оплату!\n\nЧтобы начать накрутку, отправьте корректную ссылку на вашу страницу или пост в социальных сетях. Ссылка должна начинаться с \"https://\", например:\n\nПример: https://t.me/durov\n\nБез правильной ссылки накрутка не будет запущена. Убедитесь, что она ведет на активную страницу, доступную для общего просмотра.",
                            "after_confirmation": "🎉 Ваш заказ успешно оформлен!\n\n🔢 ID заказа в сервисе: {twiboost_id}\n🔗 Для отслеживания переходите по ссылке: {link}\n\n📋 Доступные команды:\n🔍 чек {twiboost_id} — Проверить статус заказа (выводит информацию о заказе)\n🔄 рефилл {twiboost_id} — Запросить рефилл (работает лишь с гарантией - восстанавливает отписанных подписчиков)\n\nЕсли у вас возникнут вопросы, не стесняйтесь обращаться!"
                        }
                    if "notification_chat_id" not in cfg:
                        cfg["notification_chat_id"] = None
                    if "send_auto_lots" not in cfg:
                        cfg["send_auto_lots"] = True
                    if "send_auto_lots_interval" not in cfg:
                        cfg["send_auto_lots_interval"] = 30
                    if "auto_start" not in cfg:
                        cfg["auto_start"] = True
                    if "lot_mapping" not in cfg:
                        cfg["lot_mapping"] = {}
                    if "new_order_notifications" not in cfg:
                        cfg["new_order_notifications"] = False
                    # backfill v8 keys (currency / auto_refill / balance / webhook)
                    _v8_defaults = {
                        "usd_rub_rate": 95.0,
                        "usd_rub_auto_refresh": True,
                        "usd_rub_last_refreshed": 0,
                        "auto_refill_enabled": True,
                        "auto_refill_interval_hours": 6,
                        "auto_refill_warranty_days": 60,
                        "auto_refill_min_remains_pct": 5,
                        "balance_watcher_enabled": True,
                        "balance_watcher_interval_hours": 1,
                        "webhook_enabled": False,
                        "webhook_port": 8800,
                        "webhook_secret": "",
                        "backup_enabled": True,
                        "backup_remote_url": "",
                        "backup_remote_token": "",
                        "vip_skip_confirmation": True,
                        "vip_bonus_pct": 5,
                        "vip_min_orders_30d": 3,
                    }
                    for _k, _v in _v8_defaults.items():
                        cfg.setdefault(_k, _v)
                    # per-service v8 fields
                    for _svc_key, _svc in cfg.get("services", {}).items():
                        if isinstance(_svc, dict):
                            _svc.setdefault("currency", "USD")
                            _svc.setdefault("balance_alert_threshold", 10.0)
                    return cfg
                except Exception as e:
                    logger.error(f"Ошибка при чтении файла конфигурации: {e}. Создаем новый файл конфигурации.")
                    cfg = create_default_config()
                    save_config(cfg)
                    return cfg
            else:
                logger.info(f"Файл конфигурации {CONFIG_PATH} не найден. Создаем новый файл.")
                cfg = create_default_config()
                save_config(cfg)
                return cfg
    except Exception as e:
        logger.error(f"Общая ошибка при загрузке конфигурации: {e}. Возвращаем конфигурацию по умолчанию.")
        cfg = create_default_config()
        try:
            save_config(cfg)
        except:
            pass
        return cfg

def create_default_config() -> Dict:
    """Создает конфигурацию по умолчанию"""
    return {
        "services": {
            "1": {
                "api_url": "https://twiboost.com/api/v2",
                "api_key": "YOUR_API_KEY",
                "currency": "USD",  # native-валюта SMM-сервиса; auto-detect при /autosmm_health
                "balance_alert_threshold": 10.0,  # пуш админу при balance < threshold
            }
        },
        "auto_refunds": True,
        "confirm_link": True,
        "messages": {
            "after_payment": "❤️ Благодарим за оплату!\n\nЧтобы начать накрутку, отправьте корректную ссылку на вашу страницу или пост в социальных сетях. Ссылка должна начинаться с \"https://\", например:\n\nПример: https://t.me/durov\n\nБез правильной ссылки накрутка не будет запущена. Убедитесь, что она ведет на активную страницу, доступную для общего просмотра.",
            "after_confirmation": "🎉 Ваш заказ успешно оформлен!\n\n🔢 ID заказа в сервисе: {twiboost_id}\n🔗 Для отслеживания переходите по ссылке: {link}\n\n📋 Доступные команды:\n🔍 чек {twiboost_id} — Проверить статус заказа (выводит информацию о заказе)\n🔄 рефилл {twiboost_id} — Запросить рефилл (работает лишь с гарантией - восстанавливает отписанных подписчиков)\n\nЕсли у вас возникнут вопросы, не стесняйтесь обращаться!"
        },
        "notification_chat_id": None,
        "send_auto_lots": True,
        "send_auto_lots_interval": 30,
        "auto_start": True,
        "lot_mapping": {},
        "new_order_notifications": False,

        # === Currency: USD/RUB конверсия для P&L и health (новое в v8) ===
        "usd_rub_rate": 95.0,                # курс по умолчанию
        "usd_rub_auto_refresh": True,        # тянуть курс из CBR раз в 6ч
        "usd_rub_last_refreshed": 0,         # unix-ts последнего обновления

        # === П.26 Авторефилл по гарантии ===
        "auto_refill_enabled": True,
        "auto_refill_interval_hours": 6,     # как часто сканируем
        "auto_refill_warranty_days": 60,     # рефиллим только заказы моложе N дней
        "auto_refill_min_remains_pct": 5,    # рефилл, если remains > X% от quantity

        # === П.27 Балансовый watchdog ===
        "balance_watcher_enabled": True,
        "balance_watcher_interval_hours": 1,

        # === П.21 Webhook receiver (опциональный) ===
        "webhook_enabled": False,
        "webhook_port": 8800,
        "webhook_secret": "",                # для HMAC; пусто = генерируется на старте

        # === П.28 Бэкапы state-файлов ===
        "backup_enabled": True,
        "backup_remote_url": "",             # опц. PUT endpoint (S3 presigned, своя ручка и т.п.)
        "backup_remote_token": "",           # опц. Bearer token

        # === П.29 VIP-логика ===
        "vip_skip_confirmation": True,       # для VIP пропускаем шаг "+/-"
        "vip_bonus_pct": 5,                  # +5% к кол-ву от SMM-сервиса (как бонус)
        "vip_min_orders_30d": 3,             # порог для VIP
    }

def save_config(cfg: Dict):
    logger.info("Сохранение конфигурации (auto_lots.json)...")
    os.makedirs(os.path.dirname(CONFIG_PATH), exist_ok=True)
    with open(CONFIG_PATH, 'w', encoding='utf-8') as f:
        json.dump(cfg, f, ensure_ascii=False, indent=4)
    logger.info("Конфигурация сохранена.")

def reindex_lots(cfg: Dict):
    lot_map = cfg.get("lot_mapping", {})
    sorted_lots = sorted(
        lot_map.items(),
        key=lambda x: int(x[0].split('_')[1]) if x[0].startswith('lot_') and x[0].split('_')[1].isdigit() else 0
    )
    new_lot_map = {}
    for idx, (lot_key, lot_data) in enumerate(sorted_lots, start=1):
        new_key = f"lot_{idx}"
        new_lot_map[new_key] = lot_data
    cfg["lot_mapping"] = new_lot_map
    save_config(cfg)
    logger.info("Лоты были переиндексированы после удаления.")


def _next_lot_key(lot_map: Dict) -> str:
    """
    Возвращает уникальный ключ вида ``lot_<N>`` для нового лота.

    Берёт максимальный существующий числовой суффикс среди ключей
    ``lot_<N>`` и прибавляет 1. Это защищает от коллизий, когда в
    ``lot_mapping`` есть пропуски в нумерации (например, после импорта
    JSON или если предыдущие удаления по какой-то причине не вызвали
    ``reindex_lots``). Старая логика ``f"lot_{len(lot_map) + 1}"``
    приводила к молчаливой перезаписи уже существующего лота с тем же
    индексом.
    """
    max_n = 0
    for k in lot_map.keys():
        if not isinstance(k, str) or not k.startswith("lot_"):
            continue
        tail = k.split("_", 1)[1]
        if tail.isdigit():
            n = int(tail)
            if n > max_n:
                max_n = n
    candidate_n = max_n + 1
    candidate = f"lot_{candidate_n}"
    # Дополнительная подстраховка на случай нестандартных ключей.
    while candidate in lot_map:
        candidate_n += 1
        candidate = f"lot_{candidate_n}"
    return candidate


# Запоминание текущей страницы каталога лотов на пользователя/чат.
# Простой in-memory словарь: chat_id -> номер страницы. Сохраняется до
# перезапуска плагина — этого достаточно, т.к. пользователь хочет
# вернуться на ту же страницу после действия с лотом, а не между
# перезапусками FPC.
_lot_page_by_chat: Dict[int, int] = {}


def _lots_total_pages(lot_count: int, per_page: int = 10) -> int:
    return max(1, (lot_count + per_page - 1) // per_page)


def _get_lot_page(chat_id: int) -> int:
    """Возвращает сохранённую страницу для чата (0, если ничего нет)."""
    return _lot_page_by_chat.get(chat_id, 0)


def _save_lot_page(chat_id: int, page: int) -> int:
    """
    Сохраняет страницу для чата с обрезкой по текущему числу лотов и
    возвращает фактически сохранённое значение.
    """
    if page is None or page < 0:
        page = 0
    try:
        cfg = load_config()
        lot_count = len(cfg.get("lot_mapping", {}))
    except Exception:
        lot_count = 0
    total_pages = _lots_total_pages(lot_count)
    if page >= total_pages:
        page = total_pages - 1
    if page < 0:
        page = 0
    _lot_page_by_chat[chat_id] = page
    return page

def load_orders_data() -> List[Dict]:
    """
    v10: фасад над SQLite. Возвращает список заказов в том же формате, что
    раньше возвращал JSON-вариант. Существующие call-sites не трогаются.
    """
    try:
        return _db_load_all_orders()
    except Exception as e:
        logger.error(f"load_orders_data (sqlite) failed: {e}", extra={"event": "db_load_fail"})
        return []


def save_orders_data(orders: List[Dict]):
    """
    v10: фасад. Делает атомарный transactional upsert ВСЕХ заказов в SQLite.
    Это всё ещё O(N) на запись, но в ТРАНЗАКЦИИ (~5–10мс на 1000 заказов
    против ~200–500мс полной перезаписи JSON), и читатели не блокируются.
    После апдейта всё ещё материализует view ORDERS_PATH (для совместимости
    с любыми внешними скриптами, которые могут грепать его).
    """
    try:
        _db_upsert_orders(orders)
    except Exception as e:
        logger.error(f"save_orders_data (sqlite) failed: {e}", extra={"event": "db_save_fail"})
        return
    # view для совместимости — но его теперь можно делать реже, или вообще
    # отключить через cfg["legacy_orders_view"]; по умолчанию пишем.
    try:
        cfg = load_config() if os.path.exists(CONFIG_PATH) else {}
        if cfg.get("legacy_orders_view", True):
            _rebuild_orders_view(orders)
    except Exception as e:
        logger.error(f"_rebuild_orders_view skipped: {e}")


def save_one_order(order: Dict) -> None:
    """
    v10: целевой быстрый путь для апдейта одного заказа (per-row upsert).
    Используй вместо save_orders_data там, где меняется ровно одна запись.
    """
    if not order or not order.get("order_id"):
        return
    try:
        _db_upsert_orders([order])
    except Exception as e:
        logger.error(f"save_one_order failed: {e}", extra={"event": "db_save_one_fail"})


def _rebuild_orders_view(orders: Optional[List[Dict]] = None) -> None:
    """
    P.13: ORDERS_PATH (auto_smm_orders.json) — это derived view над
    каноническим ORDERS_DATA_PATH. Перестраивается всякий раз, когда
    canonical меняется. Раньше эти два файла писались раздельно и поля
    рассинхронизировались — отчёты врали. Теперь правда одна.
    """
    with _FILES_LOCK:
        if orders is None:
            orders = load_orders_data()
        view = []
        for o in orders:
            view.append({
                "date": o.get("date") or datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "order_id": o.get("order_id"),
                "summa": o.get("summa", 0),
                "service_name": o.get("service_name", ""),
                "chistota": o.get("chistota", o.get("summa", 0) - o.get("spent", 0)),
                "spent": o.get("spent", 0),
                "currency": o.get("currency", "RUB"),
                "completed_notification_sent": bool(o.get("completed_notification_sent", False)),
            })
        try:
            os.makedirs(os.path.dirname(ORDERS_PATH) or ".", exist_ok=True)
            tmp = f"{ORDERS_PATH}.tmp"
            with open(tmp, 'w', encoding='utf-8') as f:
                json.dump(view, f, indent=4, ensure_ascii=False)
            os.replace(tmp, ORDERS_PATH)
        except Exception as e:
            logger.error(f"_rebuild_orders_view failed: {e}")


def reconcile_storages() -> None:
    """
    P.13: одноразовая миграция. Старые записи могли остаться в ORDERS_PATH без
    парных в ORDERS_DATA_PATH (или наоборот) — переносим в каноническое
    хранилище и логируем дрифт. После работы ORDERS_PATH уже будет согласован
    через _rebuild_orders_view().
    """
    with _FILES_LOCK:
        canonical = load_orders_data()
        canonical_ids = {str(o.get("order_id")) for o in canonical if o.get("order_id") is not None}

        legacy: List[Dict] = []
        if os.path.exists(ORDERS_PATH):
            try:
                with open(ORDERS_PATH, 'r', encoding='utf-8') as f:
                    content = f.read().strip()
                    if content:
                        legacy = json.loads(content)
            except Exception as e:
                logger.error(f"reconcile_storages: чтение {ORDERS_PATH} не удалось: {e}")
                legacy = []

        migrated = 0
        merged = 0
        for rec in legacy:
            oid = rec.get("order_id")
            if oid is None:
                continue
            sid = str(oid)
            if sid in canonical_ids:
                # Подтягиваем legacy-only поля в canonical-запись.
                for cr in canonical:
                    if str(cr.get("order_id")) == sid:
                        for fld in ("date", "service_name", "completed_notification_sent"):
                            if fld in rec and fld not in cr:
                                cr[fld] = rec[fld]
                                merged += 1
                        break
            else:
                canonical.append({
                    "order_id": oid,
                    "date": rec.get("date") or datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                    "service_name": rec.get("service_name", ""),
                    "summa": rec.get("summa", 0),
                    "chistota": rec.get("chistota", rec.get("summa", 0)),
                    "spent": rec.get("spent", 0),
                    "currency": rec.get("currency", "RUB"),
                    "completed_notification_sent": rec.get("completed_notification_sent", False),
                    "status": "legacy",
                    "is_refunded": False,
                })
                migrated += 1

        if migrated or merged:
            logger.info(
                f"reconcile_storages: мигрировано {migrated} legacy-записей, "
                f"объединено {merged} полей."
            )
            save_orders_data(canonical)
        else:
            # Даже без миграции — выровняем view, чтобы файлы перестали дрифтовать.
            _rebuild_orders_view(canonical)


def save_order_data(
    chat_id: int,
    order_id: str,
    twiboost_id: int,
    status: str,
    chistota: float,
    customer_url: str,
    quantity: int,
    service_number: int,
    is_refunded: bool = False,
):
    """
    P.13: UPSERT-семантика. Если для order_id уже есть стаб (записан
    save_order_info при NewOrderEvent) — обогащаем его. Если нет — создаём
    новую запись. Это устраняет дубликаты и поддерживает single-source-of-truth.
    """
    with _FILES_LOCK:
        orders = load_orders_data()
        existing = next(
            (o for o in orders if str(o.get("order_id")) == str(order_id)),
            None,
        )
        patch = {
            "chat_id": chat_id,
            "order_id": order_id,
            "id_zakaz": twiboost_id,
            "status": status,
            "chistota": chistota,
            "customer_url": customer_url,
            "quantity": quantity,
            "service_number": service_number,
            "is_refunded": is_refunded,
        }
        if existing is None:
            existing = {
                "spent": 0.0,
                "summa": chistota,
                "currency": "RUB",
                "date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "service_name": "",
                "completed_notification_sent": False,
            }
            existing.update(patch)
            orders.append(existing)
            logger.info(f"save_order_data: создана запись #{order_id} (twiboost ID: {twiboost_id}).")
        else:
            existing.update(patch)
            logger.info(f"save_order_data: обновлена запись #{order_id} (twiboost ID: {twiboost_id}).")
        save_orders_data(orders)


def save_order_info(order_id: int, order_summa: float, service_name: str, order_chistota: float):
    """
    P.13: пишем stub в каноническое ORDERS_DATA_PATH (раньше — в ORDERS_PATH).
    После save_orders_data() автоматически перестроится derived view ORDERS_PATH.
    """
    with _FILES_LOCK:
        orders = load_orders_data()
        existing = next(
            (o for o in orders if str(o.get("order_id")) == str(order_id)),
            None,
        )
        stub_fields = {
            "date": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "order_id": order_id,
            "summa": order_summa,
            "service_name": service_name,
            "chistota": order_chistota,
            "completed_notification_sent": False,
        }
        if existing is None:
            stub_fields.update({
                "status": "awaiting_link",
                "is_refunded": False,
                "spent": 0.0,
                "currency": "RUB",
            })
            orders.append(stub_fields)
        else:
            for k, v in stub_fields.items():
                existing.setdefault(k, v)
        save_orders_data(orders)
        logger.info(f"save_order_info: stub для #{order_id} записан в ORDERS_DATA_PATH.")

def update_order_status(order_id_funpay: str, new_status: str):
    orders = load_orders_data()
    updated = False

    for order in orders:
        if str(order["order_id"]) == str(order_id_funpay):
            order["status"] = new_status
            updated = True
            logger.info(f"Статус заказа #{order_id_funpay} обновлён на '{new_status}'.")
            break

    if updated:
        save_orders_data(orders)
    else:
        logger.warning(f"Заказ #{order_id_funpay} не найден в orders_data.json.")

def update_order_refunded_status(order_id_funpay: str):
    orders = load_orders_data()
    updated = False
    for order in orders:
        if str(order["order_id"]) == str(order_id_funpay):
            if not order.get("is_refunded", False):
                order["is_refunded"] = True
                updated = True
                logger.info(f"Статус заказа #{order_id_funpay} обновлён на 'is_refunded': True.")
            break

    if updated:
        save_orders_data(orders)
    else:
        logger.warning(f"Заказ #{order_id_funpay} не найден или уже отмечен как 'is_refunded'.")

def refund_order(c: Cardinal, order_id_funpay: str, buyer_chat_id: int, reason: str, detailed_reason: str = None):
    """
    Обработка возврата средств с уведомлением клиента и получателя уведомлений.

    P.10: атомарный refund. Раньше is_refunded=True ставилось ПОСЛЕ
    c.account.refund(...), и две гонящиеся ветки (таймер + ручной /refund)
    могли обе пройти проверку и обе вызвать FunPay refund. Теперь:
      1) под общим _FILES_LOCK проверяем is_refunded и атомарно ставим True;
      2) только победитель гонки вызывает c.account.refund(...) дальше;
      3) при ошибке refund() флаг НЕ снимаем — лучше один пропущенный возврат
         и алерт админу, чем двойной возврат с разъярённой поддержкой FunPay.
    """
    cfg = load_config()
    auto_refunds = cfg.get("auto_refunds", True)
    notification_chat_id = cfg.get("notification_chat_id")

    if detailed_reason is None:
        detailed_reason = reason

    # === Атомарный захват флага is_refunded ===
    with _FILES_LOCK:
        orders = load_orders_data()
        order_data = next((o for o in orders if str(o["order_id"]) == str(order_id_funpay)), None)
        if order_data and order_data.get("is_refunded", False):
            logger.info(f"Заказ #{order_id_funpay} уже был возвращен. Пропуск.")
            return
        if order_data is not None:
            order_data["is_refunded"] = True
            save_orders_data(orders)

    order_url = f"https://funpay.com/orders/{order_id_funpay}/"

    if auto_refunds:
        try:
            c.account.refund(order_id_funpay)
            c.send_message(buyer_chat_id, f"❌ Ваши средства возвращены по причине: {reason}")
            if notification_chat_id:
                detailed_message = f"""
⚠️ Автоматический возврат средств для заказа #{order_id_funpay}.
🔢 Номер заказа: {order_id_funpay}
📝 Причина: {detailed_reason}
🔗 Ссылка на заказ: {order_url}
                """.strip()
                bot.send_message(notification_chat_id, detailed_message)
            logger.info(
                f"Заказ #{order_id_funpay} был отменён (refund) для покупателя {buyer_chat_id}. Причина: {reason}",
                extra={"order_id": str(order_id_funpay), "buyer_chat_id": buyer_chat_id, "event": "refund"},
            )

            with _FILES_LOCK:
                waiting_for_link.pop(str(order_id_funpay), None)
                save_state()
        except Exception as ex:
            # v11.P1.3: refund preflight — если FunPay говорит «уже возвращены», это
            # benign: либо плагин дёрнул refund дважды, либо админ вернул вручную.
            # Раньше логировалось как ERROR со всем тельцем запроса (53 случая в логе
            # за 9 месяцев). Теперь — INFO без шума.
            ex_str = str(ex)
            if classify_error(text=ex_str) == ERROR_TYPE_REFUND_DUP:
                logger.info(
                    f"refund для #{order_id_funpay}: уже возвращён (FunPay benign)",
                    extra={"event": "refund_dup", "order_id": str(order_id_funpay), "error_type": ERROR_TYPE_REFUND_DUP},
                )
                # Вернёмся раньше — нет смысла шумно алертить.
                with _FILES_LOCK:
                    waiting_for_link.pop(str(order_id_funpay), None)
                    save_state()
                return
            logger.error(
                f"Не удалось вернуть средства для заказа #{order_id_funpay}: {ex}",
                extra={"event": "refund_fail", "order_id": str(order_id_funpay),
                       "error_type": classify_error(exc=ex if isinstance(ex, BaseException) else None, text=ex_str)},
            )
            record_error(classify_error(text=ex_str), order_id=str(order_id_funpay), msg=ex_str[:300])
            if notification_chat_id:
                detailed_message = f"""
⚠️ Ошибка при автоматическом возврате средств для заказа #{order_id_funpay}.
🔢 Номер заказа: {order_id_funpay}
📝 Причина: {detailed_reason}
❗ Ошибка: {ex}
🔗 Ссылка на заказ: {order_url}
                """.strip()
                bot.send_message(notification_chat_id, detailed_message)
    else:
        if notification_chat_id:
            detailed_message = f"""
⚠️ Требуется ручной возврат средств для заказа #{order_id_funpay}.
🔢 Номер заказа: {order_id_funpay}
📝 Причина: {detailed_reason}
🔗 Перейдите по ссылке, чтобы отменить заказ: {order_url}
            """.strip()
            bot.send_message(notification_chat_id, detailed_message)
        else:
            logger.warning("Notification chat_id не задан для уведомления о возврате.")


def update_order_charge_and_net(order_id_funpay: str, spent: float, currency: str = "USD", net_profit: float = None):
    """
    v11.P4.11: hot-path использует save_one_order() — per-row UPSERT в SQLite,
    O(1) вместо O(N) при каждом апдейте чека. Раньше при 1000+ заказов это
    превращалось в 200–500мс на каждый чек статуса.
    """
    # v11: получаем именно одну запись из SQLite, мутируем, сохраняем.
    o = _db_get_order(str(order_id_funpay))
    if not o:
        logger.warning(
            f"update_order_charge_and_net: запись #{order_id_funpay} не найдена."
        )
        return
    o["spent"] = spent
    o["currency"] = currency
    if net_profit is not None:
        o["chistota"] = net_profit
    else:
        spent_rub = convert_to_rub(spent, currency)
        net = float(o.get("summa", 0) or 0) - spent_rub
        o["chistota"] = round(net, 2)
        o["spent_rub"] = spent_rub
    save_one_order(o)
    # rebuild legacy view опционально (раз в N апдейтов — но тут один upsert,
    # пусть фоновый сборщик подберёт; либо явно при критичных переходах).

def check_order_status(
    c: Cardinal,
    twiboost_order_id: int,
    buyer_chat_id: int,
    link: str,
    order_id_funpay: str,
    attempt: int = 1
):
    """
    Потоковая проверка статуса заказа на соответствующем SMM-сервисе.
    P.13: читаем флаг completed_notification_sent из канонического
    ORDERS_DATA_PATH, не из ORDERS_PATH (который теперь — derived view).
    """
    try:
        orders = load_orders_data()
    except Exception as e:
        logger.error(f"Ошибка при загрузке данных о заказах: {e}")
        orders = []

    order_data = next((o for o in orders if str(o.get("order_id")) == str(order_id_funpay)), None)
    if order_data and order_data.get("completed_notification_sent", False):
        logger.info(
            f"{LOGGER_PREFIX} Уведомление о завершении для заказа "
            f"#{order_id_funpay} уже было отправлено. Пропускаем проверку."
        )
        return

    if not order_data:
        logger.warning(f"Заказ {order_id_funpay} не найден при check_order_status.")
        order_data = {"service_number": 1}

    service_number = order_data["service_number"]
    
    try:
        cfg = load_config()
        service_cfg = cfg["services"].get(str(service_number))
    except Exception as e:
        logger.error(f"Ошибка при загрузке конфигурации: {e}")
        return
    
    if not service_cfg:
        logger.warning(f"Не найден config.services[{service_number}] — прерываем проверку.")
        return

    # === P.4: ограничиваем число попыток, чтобы не плодить таймеры навсегда. ===
    if attempt > MAX_STATUS_ATTEMPTS:
        logger.warning(
            f"{LOGGER_PREFIX} Заказ #{twiboost_order_id} (FunPay #{order_id_funpay}) "
            f"не завершился за {MAX_STATUS_ATTEMPTS} попыток — авто-рефанд."
        )
        try:
            refund_order(
                c,
                order_id_funpay,
                buyer_chat_id,
                reason="Заказ не выполнен сервисом за разумное время.",
                detailed_reason=(
                    f"Превышен лимит попыток проверки статуса "
                    f"({MAX_STATUS_ATTEMPTS}) для twiboost_order={twiboost_order_id}."
                ),
            )
        except Exception as ex:
            logger.error(f"Не удалось выполнить финальный refund для #{order_id_funpay}: {ex}")
        return

    api_url = service_cfg["api_url"]
    api_key = service_cfg["api_key"]

    url_ = f"{api_url}?action=status&order={twiboost_order_id}&key={api_key}"
    logger.info(
        f"{LOGGER_PREFIX} Проверка статуса заказа #{twiboost_order_id}, попытка {attempt}/{MAX_STATUS_ATTEMPTS}..."
    )

    completed_statuses = ["completed", "done", "success", "partial"]
    failed_statuses = ["failed", "error", "canceled"]

    try:
        # P.16: ретраи на исходящий запрос. Раньше один таймаут TwiBoost мог
        # выглядеть как «failed» на следующей итерации и привести к рефанду.
        response = http_request_with_retries(
            "GET",
            url_,
            log_extra={
                "order_id": order_id_funpay,
                "twiboost_order_id": twiboost_order_id,
                "service_number": service_number,
                "attempt": attempt,
                "stage": "status_poll",
            },
        )
        logger.debug(f"Запрос к {_redact_url(url_)} вернул статус {response.status_code}")
        if response.status_code == 200:
            data_ = response.json()
            status_ = data_.get("status", "Unknown")
            remains_ = data_.get("remains", "Unknown")
            charge_ = data_.get("charge", "0")
            currency_ = data_.get("currency", "USD")

            logger.info(f"Ответ сервиса #{twiboost_order_id}: {data_}")
            try:
                remains_ = int(remains_)
            except ValueError:
                remains_ = None
            try:
                spent_ = float(charge_)
            except ValueError:
                spent_ = 0.0

            status_lower = status_.lower()

            if status_lower in completed_statuses or (remains_ is not None and remains_ == 0):
                # P.13: ставим флаг completed_notification_sent в каноническом
                # ORDERS_DATA_PATH; ORDERS_PATH перестроится автоматически.
                try:
                    with _FILES_LOCK:
                        latest = load_orders_data()
                        for rec in latest:
                            if str(rec.get("order_id")) == str(order_id_funpay):
                                rec["completed_notification_sent"] = True
                                break
                        save_orders_data(latest)
                    logger.info(f"Успешно обновлён статус уведомления для заказа #{order_id_funpay}")
                except Exception as e:
                    logger.error(f"Ошибка при сохранении статуса уведомления для заказа #{order_id_funpay}: {e}")

                order_link = f"https://funpay.com/orders/{order_id_funpay}/"
                message = (
                    f"🎉 Ваш заказ успешно завершён!\n"
                    f"🔢 Номер заказа: {twiboost_order_id}\n"
                    f"🔗 Подтвердите заказ: {order_link}"
                )
                c.send_message(buyer_chat_id, message)
                logger.info(f"Уведомление о завершении отправлено покупателю {buyer_chat_id} (заказ #{twiboost_order_id}).")

                return

            elif status_lower in failed_statuses:
                refund_order(
                    c,
                    order_id_funpay,
                    buyer_chat_id,
                    reason="Заказ не выполнен.",
                    detailed_reason=f"Заказ в сервисе имеет статус '{status_}'."
                )
                return

            else:
                logger.info(f"Заказ #{twiboost_order_id} в статусе '{status_}' (осталось: {remains_}).")
                delay = 300

        elif response.status_code == 429:
            logger.warning(f"Получен статус 429 (Too Many Requests) для заказа #{twiboost_order_id}.")
            delay = 3600


        else:
            logger.error(f"Ошибка при проверке заказа #{twiboost_order_id}: {response.status_code}, {response.text}")
            delay = 300

    except requests.exceptions.RequestException as req_ex:
        logger.error(f"RequestException при проверке #{twiboost_order_id}: {req_ex}")
        delay = min(300 * (2 ** (attempt - 1)), 3600)
    except Exception as ex:
        logger.error(f"Неизвестная ошибка при проверке заказа #{twiboost_order_id}: {ex}")
        delay = 300

    # P.17: при выгрузке плагина не планируем новый цикл проверки.
    if _SHUTDOWN_EVENT.is_set():
        logger.info(
            f"check_order_status: shutdown, не планируем повторную проверку #{twiboost_order_id}"
        )
        return
    logger.info(f"Повторная проверка заказа #{twiboost_order_id} через {delay} сек.")
    t = threading.Timer(
        delay,
        check_order_status,
        args=(c, twiboost_order_id, buyer_chat_id, link, order_id_funpay, attempt + 1),
    )
    t.daemon = True
    t.start()

def _dialog_timeout_watcher_loop(c: "Cardinal"):
    """
    P.14: фоновый поток. Раз в DIALOG_WATCHER_INTERVAL_SEC обходит
    waiting_for_link и:
      - после DIALOG_REMINDER_AFTER_SEC отправляет покупателю одно напоминание
        (отмечается reminded_at, чтобы не спамить);
      - после DIALOG_TIMEOUT_AFTER_SEC — авто-рефанд через refund_order(),
        запись из waiting_for_link удаляется.
    Раньше «забытые» записи висели вечно, копились и мешали при дебаге.
    """
    logger.info(
        f"dialog_timeout_watcher started "
        f"(reminder={DIALOG_REMINDER_AFTER_SEC}s, timeout={DIALOG_TIMEOUT_AFTER_SEC}s)."
    )
    while not _SHUTDOWN_EVENT.is_set():
        # P.17: вместо time.sleep — wait() с уважением к shutdown.
        if _SHUTDOWN_EVENT.wait(DIALOG_WATCHER_INTERVAL_SEC):
            break
        try:
            now = time.time()
            with _FILES_LOCK:
                snapshot = list(waiting_for_link.items())

            for order_id, data in snapshot:
                created = data.get("created_at")
                if created is None:
                    # Бэкфилл для записей, созданных до v6.
                    with _FILES_LOCK:
                        if order_id in waiting_for_link:
                            waiting_for_link[order_id]["created_at"] = now
                            save_state()
                    continue

                age = now - float(created)
                step = data.get("step")
                buyer_chat_id = data.get("chat_id")
                if buyer_chat_id is None:
                    continue

                # 1) Тайм-аут: рефанд + удаление.
                if age >= DIALOG_TIMEOUT_AFTER_SEC:
                    logger.warning(
                        f"dialog_timeout: #{order_id} висит {int(age)}s в "
                        f"step={step}. Запускаем авто-рефанд."
                    )
                    try:
                        refund_order(
                            c,
                            str(order_id),
                            buyer_chat_id,
                            reason="Заказ отменён по таймауту: ссылка не получена.",
                            detailed_reason=(
                                f"Покупатель {data.get('buyer_id')} не отправил ссылку "
                                f"за {DIALOG_TIMEOUT_AFTER_SEC // 3600} ч в step={step}."
                            ),
                        )
                    except Exception as ex:
                        logger.error(f"dialog_timeout refund failed for #{order_id}: {ex}")
                    # refund_order сам чистит waiting_for_link при успехе;
                    # подстрахуемся для случая, когда auto_refunds выключен.
                    with _FILES_LOCK:
                        waiting_for_link.pop(str(order_id), None)
                        save_state()
                    continue

                # 2) Напоминание ровно один раз.
                # === v11.4 FIX (2026-05): добавили await_confirm ===
                # Раньше watcher напоминал только в step="await_link". Если
                # покупатель прислал ссылку и забил на «+/-», запись висела
                # 24 часа без напоминания, потом авто-рефанд. Теперь
                # напоминаем и тех, кто застрял на подтверждении ссылки.
                if (
                    age >= DIALOG_REMINDER_AFTER_SEC
                    and not data.get("reminded_at")
                    and step in ("await_link", "await_confirm")
                ):
                    if step == "await_confirm":
                        reminder_text = (
                            "⏳ Напоминание: подтвердите ссылку, отправив + (запустить заказ) "
                            "или - (ввести другую ссылку). Если не ответите, заказ будет "
                            "автоматически отменён с возвратом средств."
                        )
                    else:
                        reminder_text = (
                            "⏳ Напоминание: пришлите, пожалуйста, ссылку для запуска "
                            "вашего заказа. Если ссылка не поступит, заказ будет "
                            "автоматически отменён с возвратом средств."
                        )
                    try:
                        c.send_message(buyer_chat_id, reminder_text)
                        with _FILES_LOCK:
                            if str(order_id) in waiting_for_link:
                                waiting_for_link[str(order_id)]["reminded_at"] = now
                                save_state()
                        logger.info(f"dialog_reminder: отправлено для #{order_id}")
                    except Exception as ex:
                        logger.error(f"dialog_reminder send failed for #{order_id}: {ex}")
        except Exception as e:
            # Любая ошибка не должна прибить watcher.
            logger.error(f"dialog_timeout_watcher loop error: {e}")
    logger.info("dialog_timeout_watcher finished (shutdown).")


def _start_dialog_timeout_watcher(c: "Cardinal") -> None:
    global _DIALOG_WATCHER_THREAD
    if _DIALOG_WATCHER_THREAD and _DIALOG_WATCHER_THREAD.is_alive():
        return
    _DIALOG_WATCHER_THREAD = threading.Thread(
        target=_dialog_timeout_watcher_loop,
        args=(c,),
        daemon=True,
        name="auto_smm_dialog_timeout_watcher",
    )
    _DIALOG_WATCHER_THREAD.start()


def start_order_checking(c: Cardinal):
    if not RUNNING:
        return
    try:
        all_data = load_orders_data()
    except Exception as e:
        logger.error(f"Ошибка при загрузке данных о заказах в start_order_checking: {e}")
        all_data = []

    # P.13: completed_notification_sent теперь живёт в каноническом
    # ORDERS_DATA_PATH (тех же all_data), отдельный файл больше не читаем.
    for od_ in all_data:
        try:
            status_ = (od_.get("status") or "").lower()
            if status_ in ("legacy", "awaiting_link"):
                # стаб-записи — нет id_zakaz/chat_id/customer_url
                continue
            if status_ != "completed" and not od_.get("is_refunded", False):
                if od_.get("completed_notification_sent", False):
                    logger.info(
                        f"{LOGGER_PREFIX} Пропуск проверки #{od_.get('order_id')}, "
                        f"уведомление уже отправлено"
                    )
                    continue
                if not all(k in od_ for k in ("id_zakaz", "chat_id", "customer_url")):
                    continue
                threading.Thread(
                    target=check_order_status,
                    args=(c, od_["id_zakaz"], od_["chat_id"], od_["customer_url"], od_["order_id"]),
                ).start()
                time.sleep(0.5)
        except Exception as e:
            logger.error(f"Ошибка при обработке заказа в start_order_checking: {e}")
            continue

def get_tg_id_by_description(description: str, order_amount: int) -> Tuple[int, int, int] | None:
    """
    P.12: ранжируем матчи лотов по длине `lot_name` (по убыванию).
    Раньше функция возвращала ПЕРВЫЙ найденный лот через re.search — но
    «Telegram подписчики» сматчит и заказ для лота «Telegram подписчики PRO»;
    в зависимости от порядка ключей в lot_mapping выбирался не тот service_id.
    Теперь сначала ищем все совпадения, выбираем самое специфичное (длинное).
    """
    matches: List[Tuple[str, dict]] = []
    for lot_key, lot_data in lot_mapping.items():
        lot_name = lot_data.get("name") or ""
        if not lot_name:
            continue
        if re.search(re.escape(lot_name), description, re.IGNORECASE):
            matches.append((lot_name, lot_data))

    if not matches:
        return None

    # Самый длинный (= самый специфичный) матч.
    matches.sort(key=lambda kv: len(kv[0]), reverse=True)
    if len(matches) > 1:
        logger.info(
            f"get_tg_id_by_description: {len(matches)} матчей, "
            f"выбран самый специфичный: '{matches[0][0]}' "
            f"(остальные: {[m[0] for m in matches[1:]]})"
        )
    lot_name, lot_data = matches[0]
    service_id = lot_data["service_id"]
    base_q = lot_data["quantity"]
    real_q = base_q * order_amount
    srv_num = lot_data.get("service_number", 1)
    return service_id, real_q, srv_num

def is_valid_link(link: str) -> Tuple[bool, str]:
    valid_links = load_valid_links()
    if not link.startswith(("http://", "https://")):
        return False, "❌ Ссылка должна начинаться с http:// или https://."
    for pf in valid_links:
        if pf in link:
            return True, f"✅ Ссылка корректна ({pf})."
    return False, "❌ Недопустимая ссылка."

def _normalize_user_text(s: str) -> str:
    """v10.2: убираем zero-width / NBSP / прочий невидимый мусор + strip()."""
    if not s:
        return ""
    # Список «невидимых» Unicode которые иногда добавляют мобильные клиенты.
    invisibles = ("\u200b", "\u200c", "\u200d", "\u2060", "\ufeff", "\u00a0")
    out = s
    for ch in invisibles:
        out = out.replace(ch, "")
    return out.strip()


def auto_smm_handler(c: Cardinal, e, *args):
    global RUNNING, orders_info, waiting_for_link

    if not RUNNING:
        return

    # v10.2: топ-уровневый catch-all. Раньше любое исключение в ветке
    # await_confirm/процесса заказа всплывало в FPC-Cardinal и тихо
    # глоталось — пользователь видел тишину на «+».
    try:
        return _auto_smm_handler_inner(c, e, *args)
    except Exception as ex:
        logger.exception(f"auto_smm_handler crashed: {ex}", extra={"event": "handler_crash"})
        try:
            if isinstance(e, NewMessageEvent):
                c.send_message(e.message.chat_id, "❌ Внутренняя ошибка обработки. Админ оповещён.")
        except Exception:
            pass


def _auto_smm_handler_inner(c: Cardinal, e, *args):
    global RUNNING, orders_info, waiting_for_link

    my_id = c.account.id
    bot_ = c.telegram.bot

    if isinstance(e, NewMessageEvent):
        if e.message.author_id == my_id:
            return

        msg_text = _normalize_user_text(e.message.text or "")
        msg_author_id = e.message.author_id
        msg_chat_id = e.message.chat_id

        logger.info(
            f"Новое сообщение от {e.message.author}: {msg_text!r}",
            extra={
                "event": "new_message",
                "author_id": msg_author_id,
                "chat_id": msg_chat_id,
                "raw_text": msg_text,
                "wfl_size": len(waiting_for_link),
            },
        )

        m_check = re.match(r'^чек\s+(\d+)$', msg_text.lower())
        if m_check:
            order_num = m_check.group(1)
            od_ = load_orders_data()
            found = next((o for o in od_ if str(o["id_zakaz"]) == order_num), None)
            if not found:
                c.send_message(msg_chat_id, "❌ Заказ не найден в базе.")
                return
            cfg = load_config()
            service_cfg = cfg["services"].get(str(found["service_number"]))
            if not service_cfg:
                c.send_message(msg_chat_id, f"❌ Не найден конфиг для service_number={found['service_number']}")
                return
            api_url = service_cfg["api_url"]
            api_key = service_cfg["api_key"]
            url_ = f"{api_url}?action=status&order={order_num}&key={api_key}"
            try:
                rr = HTTP_SESSION.get(url_, timeout=HTTP_TIMEOUT)
                rr.raise_for_status()
                rdata = rr.json()
                st_ = rdata.get("status", "неизв.")
                rm_ = rdata.get("remains", "неизв.")
                ch_ = rdata.get("charge", "неизв.")
                cur_ = rdata.get("currency", "неизв.")
                c.send_message(msg_chat_id, f"Статус: {st_}")
            except Exception as ex:
                c.send_message(msg_chat_id, f"Ошибка при проверке")
            return

        m_refill = re.match(r'^рефилл\s+(\d+)$', msg_text.lower())
        if m_refill:
            order_num = m_refill.group(1)
            c.send_message(msg_chat_id, "Запрашиваю рефилл...")
            od_ = load_orders_data()
            found = next((o for o in od_ if str(o["id_zakaz"]) == order_num), None)
            if not found:
                c.send_message(msg_chat_id, "❌ Заказ не найден в базе.")
                return
            cfg = load_config()
            service_cfg = cfg["services"].get(str(found["service_number"]))
            if not service_cfg:
                c.send_message(msg_chat_id, f"❌ Не найден конфиг для service_number={found['service_number']}")
                return
            api_url = service_cfg["api_url"]
            api_key = service_cfg["api_key"]
            url_ = f"{api_url}?action=refill&order={order_num}&key={api_key}"
            try:
                rr = HTTP_SESSION.get(url_, timeout=HTTP_TIMEOUT)
                rr.raise_for_status()
                rdata = rr.json()
                st_ = rdata.get("status", 0)
                if str(st_) in ("1", "true"):
                    c.send_message(msg_chat_id, "✅ Рефилл успешно запущен.")
                else:
                    c.send_message(msg_chat_id, f"❌ Рефилл отклонён (status={st_}).")
            except Exception as ex:
                c.send_message(msg_chat_id, f"Ошибка при запросе рефилла")
            return

        # P.11: снимаем снапшот словаря под локом — не держим _FILES_LOCK во
        # время сетевых вызовов (process_link_without_confirmation тянет
        # SMM-API на секунды). Все модификации `data` и `save_state()`
        # делаем под локом точечно.
        with _FILES_LOCK:
            wfl_snapshot = list(waiting_for_link.items())

        # v10.2: явный лог о матчах диалога — упростит диагностику если
        # «+» снова не сработает.
        matched_count = 0

        for order_id, data in wfl_snapshot:
            # str-сравнение: после load_state() buyer_id может быть числом,
            # а msg_author_id всегда int. Дополнительно matchим по chat_id —
            # бывает что после миграций buyer_id уезжает, но chat_id остаётся.
            buyer_match = str(data.get("buyer_id")) == str(msg_author_id)
            chat_match = str(data.get("chat_id") or "") == str(msg_chat_id)
            if not (buyer_match or chat_match):
                continue
            matched_count += 1
            logger.info(
                f"auto_smm_handler match: order_id={order_id}, step={data.get('step')!r}, "
                f"buyer_match={buyer_match}, chat_match={chat_match}",
                extra={
                    "event": "wfl_match",
                    "order_id": order_id,
                    "step": data.get("step"),
                    "buyer_id": data.get("buyer_id"),
                    "msg_author_id": msg_author_id,
                },
            )
            if True:
                if data["step"] == "await_link":
                    link_m = re.search(r'(https?://\S+)', msg_text)
                    if not link_m:
                        c.send_message(msg_chat_id, "❌ Неверная ссылка, повторите...")
                        return
                    link_ = link_m.group(0)
                    ok, reason = is_valid_link(link_)
                    if not ok:
                        c.send_message(msg_chat_id, reason)
                        return

                    cfg = load_config()
                    # P.29: VIP пропускает шаг подтверждения, остальные — по cfg.confirm_link
                    confirm_link = cfg.get("confirm_link", True)
                    if data.get("vip_skip_confirmation"):
                        confirm_link = False
                        if data.get("vip_tier") == "vip":
                            try:
                                c.send_message(
                                    msg_chat_id,
                                    "⭐ Спасибо что вы с нами! Подтверждение пропущено — заказ оформляется автоматически.",
                                )
                            except Exception:
                                pass

                    if confirm_link:
                        with _FILES_LOCK:
                            data["link"] = link_
                            data["step"] = "await_confirm"
                            save_state()
                        c.send_message(msg_chat_id, f"✅ Ссылка принята: {link_}\nПодтвердите: + / -")
                        return
                    else:
                        with _FILES_LOCK:
                            data["link"] = link_
                            save_state()
                        process_link_without_confirmation(c, data)
                    return

                elif data["step"] == "await_confirm":
                    text_low = msg_text.lower()
                    # v10.2: «плюс» иногда приходит с лишними символами или
                    # альтернативными плюсами (＋ U+FF0B). Поддерживаем все.
                    is_plus = text_low in ("+", "＋", "плюс", "да", "yes", "y") or text_low.startswith("+")
                    is_minus = text_low in ("-", "−", "минус", "нет", "no", "n") or text_low.startswith("-")
                    logger.info(
                        f"await_confirm: text={msg_text!r}, is_plus={is_plus}, is_minus={is_minus}",
                        extra={"event": "await_confirm", "order_id": order_id, "text": msg_text},
                    )
                    if is_plus:
                        try:
                            c.send_message(msg_chat_id, "🚀 Запускаю заказ...")
                        except Exception:
                            pass
                        try:
                            process_link_without_confirmation(c, data)
                        except Exception as e_proc:
                            logger.exception(
                                f"process_link_without_confirmation failed: {e_proc}",
                                extra={"event": "plwc_fail", "order_id": order_id},
                            )
                            try:
                                c.send_message(msg_chat_id, f"❌ Ошибка при оформлении заказа: {e_proc}")
                            except Exception:
                                pass
                        return
                    elif is_minus:
                        with _FILES_LOCK:
                            data["step"] = "await_link"
                            save_state()
                        c.send_message(msg_chat_id, "❌ Подтверждение отклонено. Введите другую ссылку.")
                        return
                    else:
                        c.send_message(msg_chat_id, "❌ Используйте + или -. Повторите.")
                        return

        # v10.2: если ни одна запись не сматчилась — это диагностический сигнал,
        # пишем в лог, но пользователю молчим (он мог просто болтать).
        if not matched_count and waiting_for_link:
            logger.info(
                f"new_message: ни одна запись waiting_for_link не сматчилась "
                f"(author_id={msg_author_id}, chat_id={msg_chat_id}, "
                f"keys={list(waiting_for_link.keys())[:5]})",
                extra={"event": "wfl_no_match"},
            )

    elif isinstance(e, NewOrderEvent):
        order_ = e.order
        orderID = order_.id
        orderDesc = order_.description
        orderAmount = order_.amount
        orderPrice = order_.price

        logger.info(f"Новый заказ #{orderID}: {orderDesc}, x{orderAmount}")

        # === P.3: идемпотентность.
        # FPC иногда переотправляет NewOrderEvent (рестарт, восстановление
        # очереди, повторное подключение). Дважды процессить один и тот же
        # FunPay-заказ нельзя — это создаёт второй заказ в SMM-сервисе и
        # двойное списание у нас. Блокируем дубль на двух уровнях:
        #   1) waiting_for_link — заказ уже ждёт ссылку от покупателя;
        #   2) orders_data.json — заказ уже отправлен в SMM (есть запись).
        order_key = str(orderID)
        if order_key in waiting_for_link:
            logger.warning(
                f"Дубликат NewOrderEvent для #{orderID} — уже в waiting_for_link "
                f"(step={waiting_for_link[order_key].get('step')}). Пропуск."
            )
            return
        try:
            existing_orders = load_orders_data()
            if any(str(o.get("order_id")) == order_key for o in existing_orders):
                logger.warning(
                    f"Дубликат NewOrderEvent для #{orderID} — уже создан заказ в SMM. Пропуск."
                )
                return
        except Exception as e_idem:
            # Лучше пропустить idempotency-чек, чем заблокировать обработку.
            logger.error(f"idempotency check failed for #{orderID}: {e_idem}")

        cfg = load_config()
        found_lot = get_tg_id_by_description(orderDesc, orderAmount)
        if found_lot is None:
            logger.info("Лот не найден по описанию. Пропуск обработки.")
            return

        service_id, real_amount, srv_number = found_lot

        # === v11.4 FIX (2026-05): retry для get_order() ===
        # Раньше один сетевой сбой к FunPay API на свежесозданном заказе
        # (FunPay часто отдаёт 403/404 в первые секунды после оплаты, пока
        # заказ ещё не «прокатился» по их кэшам) → исключение всплывало в
        # auto_smm_handler catch-all, покупатель видел «Внутренняя ошибка»,
        # а запись в waiting_for_link не успевала создаться. Заказ «терялся»
        # навсегда (его не подхватывал ни один watcher).
        #
        # Теперь: 3 попытки с короткой задержкой, при полном провале —
        # fallback на данные из NewOrderEvent (e.order и e.message содержат
        # минимум: buyer_id, chat_id, buyer_username), чтобы хотя бы создать
        # запись в waiting_for_link и принять ссылку.
        od_full = None
        last_get_order_err: Optional[BaseException] = None
        for _attempt in range(1, 4):
            try:
                od_full = c.account.get_order(orderID)
                break
            except Exception as _ge:
                last_get_order_err = _ge
                logger.warning(
                    f"get_order({orderID}) attempt {_attempt}/3 failed: {_ge}",
                    extra={
                        "event": "get_order_retry",
                        "order_id": str(orderID),
                        "attempt": _attempt,
                        "error": str(_ge)[:200],
                    },
                )
                if _attempt < 3:
                    # Короткий backoff: 2с, 5с. Уважаем shutdown.
                    if _SHUTDOWN_EVENT.wait(2 if _attempt == 1 else 5):
                        return

        if od_full is not None:
            buyer_chat_id = od_full.chat_id
            buyer_id = od_full.buyer_id
            buyer_username = _safe_username(od_full.buyer_username)
        else:
            # Fallback: используем данные из NewOrderEvent. У FunPayAPI поле
            # order_.buyer_id есть, chat_id и username — могут отсутствовать.
            logger.error(
                f"get_order({orderID}) исчерпал 3 попытки. "
                f"Fallback на данные из NewOrderEvent. last_err={last_get_order_err!r}",
                extra={
                    "event": "get_order_exhausted",
                    "order_id": str(orderID),
                    "error": str(last_get_order_err)[:200],
                },
            )
            buyer_id = getattr(order_, "buyer_id", None)
            buyer_chat_id = getattr(order_, "chat_id", None) or buyer_id
            buyer_username = _safe_username(getattr(order_, "buyer_username", None))
            if not buyer_chat_id:
                # без chat_id мы вообще не можем общаться с покупателем —
                # пишем в админ-чат и выходим, заказ останется висеть на FP.
                logger.error(
                    f"NewOrderEvent для #{orderID}: buyer_chat_id неизвестен, "
                    f"невозможно начать диалог. Заказ требует ручной обработки."
                )
                _admin_notify(
                    f"⚠ <b>Не удалось получить данные заказа</b> <code>{orderID}</code>\n"
                    f"FunPay API недоступен 3 попытки подряд, и в NewOrderEvent "
                    f"не было buyer_chat_id. Обработай заказ вручную: "
                    f"<a href='https://funpay.com/orders/{orderID}/'>открыть</a>\n"
                    f"Последняя ошибка: <code>{html.escape(str(last_get_order_err)[:200])}</code>"
                )
                return

        # P.29: вычисляем профиль покупателя ДО инкремента счётчика
        # (его обновим уже после успешного оформления через update_customer_profile).
        tier_info = get_customer_tier(buyer_id)
        if tier_info["bonus_pct"] > 0:
            bonus_qty = int(real_amount * tier_info["bonus_pct"] / 100)
            real_amount = real_amount + bonus_qty
            logger.info(
                f"P.29 VIP bonus: +{tier_info['bonus_pct']}% к qty (#{orderID}, buyer={buyer_id})",
                extra={
                    "event": "vip_bonus_applied",
                    "order_id": str(orderID),
                    "buyer_id": str(buyer_id),
                    "bonus_pct": tier_info["bonus_pct"],
                    "real_amount_after_bonus": real_amount,
                },
            )

        orders_info[orderID] = {
            "buyer_id": buyer_id,
            "chat_id": buyer_chat_id,
            "summa": orderPrice
        }

        save_order_info(orderID, orderPrice, orderDesc, orderPrice)

        # P.29: для VIP сразу пропускаем шаг подтверждения — но ссылку всё равно
        # ждём (шаг await_link). Хранится в state.skip_confirmation.
        skip_conf = bool(tier_info.get("skip_confirmation", False))

        # СНАЧАЛА фиксируем state на диске. Любой сбой ниже (упавший
        # send_message, недоступная сеть и т.п.) больше не оставит покупателя
        # без записи в waiting_for_link, и сообщение со ссылкой будет
        # корректно обработано. P.11 — пишем под общим _FILES_LOCK.
        with _FILES_LOCK:
            waiting_for_link[str(orderID)] = {
                "buyer_id": buyer_id,
                "chat_id": buyer_chat_id,
                "service_id": service_id,
                "real_amount": real_amount,
                "order_id_funpay": orderID,
                "price": orderPrice,
                "service_number": srv_number,
                "step": "await_link",
                "created_at": time.time(),  # P.14: для dialog_timeout_watcher
                "reminded_at": None,
                "vip_skip_confirmation": skip_conf,  # P.29
                "vip_tier": tier_info["tier"],       # P.29
                "vip_bonus_pct": tier_info["bonus_pct"],
            }
            save_state()
        logger.info(
            f"waiting_for_link[{orderID}] = await_link (buyer_id={buyer_id})",
            extra={
                "order_id": str(orderID),
                "buyer_id": buyer_id,
                "service_id": service_id,
                "event": "new_order",
            },
        )

        try:
            msg_payment = cfg["messages"]["after_payment"].format(
                buyer_username=buyer_username,
                orderDesc=orderDesc,
                orderPrice=orderPrice,
                orderAmount=orderAmount
            )
        except KeyError as e:
            logger.error(f"Ошибка в шаблоне сообщения: отсутствует переменная {e}")
            msg_payment = "❤️ Спасибо за оплату! Укажите ссылку для запуска заказа."

        try:
            c.send_message(buyer_chat_id, msg_payment)
        except Exception as e:
            logger.error(f"send greeting to buyer {buyer_chat_id} failed: {e}")

def start_smm(message: types.Message):
    # Плагин всегда работает; на всякий случай гарантируем запуск потоков.
    global RUNNING, IS_STARTED, ORDER_CHECK_THREAD, AUTO_LOTS_SEND_THREAD, cardinal_instance
    RUNNING = True
    IS_STARTED = True
    c_ = cardinal_instance
    if c_ is not None:
        if not ORDER_CHECK_THREAD or not ORDER_CHECK_THREAD.is_alive():
            ORDER_CHECK_THREAD = threading.Thread(target=start_order_checking, args=(c_,))
            ORDER_CHECK_THREAD.daemon = True
            ORDER_CHECK_THREAD.start()
        if not AUTO_LOTS_SEND_THREAD or not AUTO_LOTS_SEND_THREAD.is_alive():
            AUTO_LOTS_SEND_THREAD = threading.Thread(target=start_auto_lots_sender, args=(c_,))
            AUTO_LOTS_SEND_THREAD.daemon = True
            AUTO_LOTS_SEND_THREAD.start()
    bot.send_message(message.chat.id, "✅ Плагин работает (always-on, остановить нельзя).")

def stop_smm(message: types.Message):
    # Отключение запрещено: плагин должен работать всегда.
    bot.send_message(message.chat.id, "ℹ️ Плагин настроен на постоянную работу и не может быть остановлен.")

def _backup_data_files() -> Optional[str]:
    """
    P.8: Снимает резервный архив всех data-файлов плагина (ORDERS_PATH,
    ORDERS_DATA_PATH, STATE_PATH, CONFIG_PATH) в BACKUP_DIR. Возвращает
    путь до tar.gz или None при ошибке.
    """
    import tarfile
    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    archive = os.path.join(BACKUP_DIR, f"auto_smm_{ts}.tar.gz")
    try:
        with _FILES_LOCK:
            with tarfile.open(archive, "w:gz") as tar:
                for p in (ORDERS_PATH, ORDERS_DATA_PATH, STATE_PATH, CONFIG_PATH):
                    if os.path.exists(p):
                        tar.add(p, arcname=os.path.basename(p))
        logger.info(f"backup created: {archive}")
        return archive
    except Exception as e:
        logger.error(f"backup failed: {e}")
        return None


_DELETE_CONFIRM_TOKEN = "DELETE"


def _auto_smm_delete_confirmed(message: types.Message):
    """P.8: следующий шаг после /auto_smm_delete — ждём токен подтверждения."""
    chat_id = message.chat.id
    text = (message.text or "").strip()
    if text != _DELETE_CONFIRM_TOKEN:
        bot.send_message(
            chat_id,
            f"❌ Удаление отменено: ожидался токен <code>{_DELETE_CONFIRM_TOKEN}</code>.",
            parse_mode="HTML",
        )
        return
    archive = _backup_data_files()
    with _FILES_LOCK:
        for p in (ORDERS_PATH, ORDERS_DATA_PATH):
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception as ex:
                logger.error(f"delete {p} failed: {ex}")
    if archive:
        bot.send_message(
            chat_id,
            "🗑 Файлы заказов удалены.\n"
            f"📦 Резервная копия: <code>{archive}</code>",
            parse_mode="HTML",
        )
    else:
        bot.send_message(
            chat_id,
            "🗑 Файлы заказов удалены.\n"
            "⚠️ Бэкап создать не удалось — проверьте логи.",
        )


def auto_smm_delete(message: types.Message):
    """
    P.8: двухшаговое удаление data-файлов с автобэкапом.
    Шаг 1 — /auto_smm_delete: спрашиваем подтверждение.
    Шаг 2 — admin отвечает словом DELETE в течение 60с → файлы удаляются,
    но предварительно сохраняется tar.gz-бэкап в BACKUP_DIR.
    """
    chat_id = message.chat.id
    msg_ = bot.send_message(
        chat_id,
        "⚠️ Подтвердите удаление файлов заказов.\n\n"
        f"Отправьте следующим сообщением слово <code>{_DELETE_CONFIRM_TOKEN}</code> "
        "(заглавными). Любой другой текст отменит удаление.\n\n"
        "Перед удалением будет автоматически создан резервный архив в "
        f"<code>{BACKUP_DIR}</code>.",
        parse_mode="HTML",
    )
    bot.register_next_step_handler(msg_, _auto_smm_delete_confirmed)

def auto_smm_settings(message: types.Message):

    cfg = load_config()
    lmap = cfg.get("lot_mapping", {})
    auto_refunds = cfg.get("auto_refunds", True)
    confirm_link = cfg.get("confirm_link", True)
    notif_chat_id = cfg.get("notification_chat_id", "Не задан")
    send_auto_lots = cfg.get("send_auto_lots", True)
    send_auto_lots_interval = cfg.get("send_auto_lots_interval", 30)
    auto_start = cfg.get("auto_start", False)

    status_text = "✅ АКТИВИРОВАН"

    txt_ = f"""
🚀 <b>AUTOSMM ПАНЕЛЬ УПРАВЛЕНИЯ v{VERSION}</b> 🚀
━━━━━━━━━━━━━━━━━━━━━━━━
👨‍💻 <b>Разработчик:</b> {CREDITS}

📊 <b>СТАТУС:</b> {status_text}

💡 <b>ОСНОВНЫЕ ПАРАМЕТРЫ:</b>
 • Лотов в базе: <code>{len(lmap)}</code>
 • Автовозвраты: {'✅' if auto_refunds else '❌'}
 • Подтверждение ссылки: {'✅' if confirm_link else '❌'}
 • Отправка auto_lots.json: {'✅' if send_auto_lots else '❌'}
 • Интервал отправки: <code>{send_auto_lots_interval} мин</code>
 • Автозапуск: {'✅' if auto_start else '❌'}

📞 <b>УВЕДОМЛЕНИЯ:</b> <code>{notif_chat_id}</code>

📝 <b>О ПЛАГИНЕ:</b> <i>{DESCRIPTION}</i>
━━━━━━━━━━━━━━━━━━━━━━━━
    """.strip()

    kb = InlineKeyboardMarkup(row_width=2)
    
    kb.add(
        InlineKeyboardButton("🛍️ Каталог лотов", callback_data="lot_settings"),
        InlineKeyboardButton("➕ Создать новый лот", callback_data="add_new_lot")
    )
    
    kb.add(
        InlineKeyboardButton("🔌 Интеграция API", callback_data="api_settings"),
    )
    
    kb.add(
        InlineKeyboardButton("🌐 Доверенные сайты", callback_data="manage_websites"),
        InlineKeyboardButton("💬 Шаблоны сообщений", callback_data="edit_messages")
    )
    
    kb.add(
        InlineKeyboardButton("📊 Бэкап и аналитика", callback_data="files_menu"),
        InlineKeyboardButton("⚙️ Тонкая настройка", callback_data="misc_settings")
    )
    
    kb.add(
        InlineKeyboardButton("📚 Полезные ресурсы", callback_data="links_menu")
    )
    
    bot.send_message(message.chat.id, txt_, parse_mode='HTML', reply_markup=kb)

def files_menu(call: types.CallbackQuery):
        
    txt_ = """
<b>📁 Работа с файлами</b>

Здесь вы можете управлять файлами плагина, экспортировать данные и очищать историю заказов.
    """.strip()
    
    kb_ = InlineKeyboardMarkup(row_width=2)
    
    kb_.row(
        InlineKeyboardButton("📤 Экспорт файлов", callback_data="export_files"),
        InlineKeyboardButton("📥 Загрузить JSON", callback_data="upload_lots_json")
    )
    
    kb_.row(
        InlineKeyboardButton("📝 Логи ошибок", callback_data="export_errors"),
        InlineKeyboardButton("🗑 Удалить заказы", callback_data="delete_orders")
    )
    
    kb_.add(InlineKeyboardButton("🔙 Вернуться в настройки", callback_data="return_to_settings"))
    
    bot.edit_message_text(txt_, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb_)

def misc_settings(call: types.CallbackQuery):
        
    cfg = load_config()
    auto_refunds = cfg.get("auto_refunds", True)
    confirm_link = cfg.get("confirm_link", True)
    send_auto_lots = cfg.get("send_auto_lots", True)
    send_auto_lots_interval = cfg.get("send_auto_lots_interval", 30)
    auto_start = cfg.get("auto_start", False)
    
    txt_ = f"""
<b>⚙️ Дополнительные настройки</b>

Здесь вы можете настроить дополнительные параметры работы плагина.

<b>Текущие настройки:</b>
• Автовозвраты: <code>{'Включены ✅' if auto_refunds else 'Выключены ❌'}</code>
• Подтверждение ссылки: <code>{'Включено ✅' if confirm_link else 'Выключено ❌'}</code>
• Отправка файла auto_lots.json: <code>{'Включена ✅' if send_auto_lots else 'Выключена ❌'}</code>
• Интервал отправки (минуты): <code>{send_auto_lots_interval}</code>
• Автозапуск плагина: <code>{'Включен ✅' if auto_start else 'Выключен ❌'}</code>
    """.strip()
    
    kb_ = InlineKeyboardMarkup(row_width=1)
    
    kb_.add(
        InlineKeyboardButton(f"🔄 {'Выключить' if auto_refunds else 'Включить'} автовозвраты", callback_data="toggle_auto_refunds"),
        InlineKeyboardButton(f"✅ {'Выключить' if confirm_link else 'Включить'} подтверждение ссылки", callback_data="toggle_confirm_link")
    )
    
    kb_.add(
        InlineKeyboardButton(f"📤 {'Выключить' if send_auto_lots else 'Включить'} отправку auto_lots.json", callback_data="toggle_send_auto_lots"),
        InlineKeyboardButton("⏱️ Изменить интервал отправки", callback_data="change_send_interval")
    )
    
    kb_.add(
        InlineKeyboardButton(f"🚀 {'Выключить' if auto_start else 'Включить'} автозапуск плагина", callback_data="toggle_auto_start"),
        InlineKeyboardButton("🔄 Обновить номера лотов", callback_data="update_lot_ids")
    )
    
    kb_.add(
        InlineKeyboardButton("🗑 Удалить все лоты", callback_data="delete_all_lots"),
        InlineKeyboardButton("📩 Указать Chat ID для уведомлений", callback_data="set_notification_chat_id")
    )
    
    kb_.add(
        InlineKeyboardButton("🔙 Вернуться в настройки", callback_data="return_to_settings")
    )
    
    bot.edit_message_text(txt_, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb_)

def links_menu(call: types.CallbackQuery):
        
    txt_ = """
<b>🔗 Полезные ссылки</b>

Здесь вы найдете важные ссылки для работы с плагином и сервисами SMM.
    """.strip()
    
    kb_ = InlineKeyboardMarkup(row_width=2)
    
    kb_.row(
        InlineKeyboardButton("🌐 Twiboost", url="https://twiboost.com"),
        InlineKeyboardButton("🌐 Vexboost", url="https://vexboost.ru")
    )

    kb_.add(InlineKeyboardButton("🔙 Вернуться в настройки", callback_data="return_to_settings"))
    
    bot.edit_message_text(txt_, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb_)

def get_statistics():
    if not os.path.exists(ORDERS_PATH):
        return None
    with open(ORDERS_PATH, 'r', encoding='utf-8') as f:
        orders = json.load(f)

    now_ = datetime.now()
    day_ago = now_ - timedelta(days=1)
    week_ago = now_ - timedelta(days=7)
    month_ago = now_ - timedelta(days=30)

    day_orders = [o for o in orders if datetime.strptime(o["date"], "%Y-%m-%d %H:%M:%S") >= day_ago]
    week_orders = [o for o in orders if datetime.strptime(o["date"], "%Y-%m-%d %H:%M:%S") >= week_ago]
    month_orders = [o for o in orders if datetime.strptime(o["date"], "%Y-%m-%d %H:%M:%S") >= month_ago]
    all_orders = orders

    day_total = sum(o["summa"] for o in day_orders)
    week_total = sum(o["summa"] for o in week_orders)
    month_total = sum(o["summa"] for o in month_orders)
    all_total = sum(o["summa"] for o in all_orders)

    day_chistota = sum(o.get("chistota", o["summa"] - o.get("spent", 0)) for o in day_orders)
    week_chistota = sum(o.get("chistota", o["summa"] - o.get("spent", 0)) for o in week_orders)
    month_chistota = sum(o.get("chistota", o["summa"] - o.get("spent", 0)) for o in month_orders)
    all_chistota = sum(o.get("chistota", o["summa"] - o.get("spent", 0)) for o in all_orders)

    return {
        "day_orders": len(day_orders),
        "day_total": day_total,
        "day_chistota": round(day_chistota, 2),
        "week_orders": len(week_orders),
        "week_total": week_total,
        "week_chistota": round(week_chistota, 2),
        "month_orders": len(month_orders),
        "month_total": month_total,
        "month_chistota": round(month_chistota, 2),
        "all_time_orders": len(all_orders),
        "all_time_total": all_total,
        "all_time_chistota": round(all_chistota, 2),
    }

def generate_lots_keyboard(page: int = 0) -> InlineKeyboardMarkup:
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    items = list(lot_map.items())

    per_page = 10
    # Защитная обрезка номера страницы по текущему числу лотов —
    # чтобы при удалении/изменениях не показывать пустую страницу.
    total_pages = _lots_total_pages(len(items), per_page)
    if page is None or page < 0:
        page = 0
    if page >= total_pages:
        page = total_pages - 1
    if page < 0:
        page = 0
    start_ = page * per_page
    end_ = start_ + per_page
    chunk = items[start_:end_]

    kb_ = InlineKeyboardMarkup(row_width=1)
    for lot_key, lot_data in chunk:
        name_ = lot_data["name"]
        sid_ = lot_data["service_id"]
        qty_ = lot_data["quantity"]
        snum_ = lot_data.get("service_number", 1)
        btn_text = f"{name_} [ID={sid_}, Q={qty_}, S={snum_}]"
        cd_ = f"edit_lot_{lot_key}"
        kb_.add(InlineKeyboardButton(btn_text, callback_data=cd_))

    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton("⬅️", callback_data=f"prev_page_{page-1}"))
    if end_ < len(items):
        nav_buttons.append(InlineKeyboardButton("➡️", callback_data=f"next_page_{page+1}"))
    if nav_buttons:
        kb_.row(*nav_buttons)

    kb_.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
    return kb_

def edit_lot(call: types.CallbackQuery, lot_key: str):
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    if lot_key not in lot_map:
        bot.edit_message_text(f"❌ Лот {lot_key} не найден.", call.message.chat.id, call.message.message_id)
        return

    ld_ = lot_map[lot_key]
    txt_ = f"""
<b>{lot_key}</b>
Название: <code>{ld_['name']}</code>
ID услуги: <code>{ld_['service_id']}</code>
Кол-во: <code>{ld_['quantity']}</code>
S#: <code>{ld_.get('service_number', 1)}</code>
""".strip()

    kb_ = InlineKeyboardMarkup(row_width=1)
    kb_.add(
        InlineKeyboardButton("Изменить название", callback_data=f"change_name_{lot_key}"),
        InlineKeyboardButton("Изменить ID услуги", callback_data=f"change_id_{lot_key}"),
        InlineKeyboardButton("Изменить количество", callback_data=f"change_quantity_{lot_key}"),
        InlineKeyboardButton("Изменить сервис#", callback_data=f"change_snum_{lot_key}"),
    )
    kb_.add(InlineKeyboardButton("❌ Удалить лот", callback_data=f"delete_one_lot_{lot_key}"))
    kb_.add(InlineKeyboardButton("◀️ К списку", callback_data="return_to_lots"))
    bot.edit_message_text(txt_, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=kb_)

def delete_one_lot(call: types.CallbackQuery, lot_key: str):
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    if lot_key in lot_map:
        del lot_map[lot_key]
        cfg["lot_mapping"] = lot_map
        reindex_lots(cfg)
        # После удаления возвращаемся на ту же страницу каталога
        # (с обрезкой, если последняя страница исчезла).
        page = _save_lot_page(call.message.chat.id, _get_lot_page(call.message.chat.id))
        bot.edit_message_text(f"✅ Лот {lot_key} удалён и лоты переиндексированы.", call.message.chat.id, call.message.message_id, reply_markup=generate_lots_keyboard(page))
    else:
        bot.edit_message_text(f"❌ Лот {lot_key} не найден.", call.message.chat.id, call.message.message_id)

def delete_all_lots_func(call: types.CallbackQuery):
    cfg = load_config()
    preserved_notification_chat_id = cfg.get("notification_chat_id")
    preserved_services = cfg.get("services", {})
    
    new_config = {
        "lot_mapping": {},
        "services": preserved_services,
        "auto_refunds": cfg.get("auto_refunds", True),
        "messages": cfg.get("messages", {}),
        "notification_chat_id": preserved_notification_chat_id
    }
    
    save_config(new_config)
    bot.edit_message_text("✅ Все лоты успешно удалены. Chat ID и сервисы сохранены.", 
                         call.message.chat.id, 
                         call.message.message_id)

def process_name_change(message: types.Message, lot_key: str):
    new_name = message.text.strip()
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    if lot_key not in lot_map:
        bot.send_message(message.chat.id, f"❌ Лот {lot_key} не найден.")
        return
    lot_map[lot_key]["name"] = new_name
    cfg["lot_mapping"] = lot_map
    save_config(cfg)
    kb_ = InlineKeyboardMarkup()
    kb_.add(InlineKeyboardButton("◀️ К лотам", callback_data="return_to_lots"))
    bot.send_message(message.chat.id, f"✅ Название лота {lot_key} изменено на {new_name}.", reply_markup=kb_)

def process_id_change(message: types.Message, lot_key: str):
    try:
        new_id = int(message.text.strip())
    except ValueError:
        bot.send_message(message.chat.id, "❌ Ошибка: ID услуги должно быть числом.")
        return
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    if lot_key not in lot_map:
        bot.send_message(message.chat.id, f"❌ Лот {lot_key} не найден.")
        return
    lot_map[lot_key]["service_id"] = new_id
    cfg["lot_mapping"] = lot_map
    save_config(cfg)
    kb_ = InlineKeyboardMarkup()
    kb_.add(InlineKeyboardButton("◀️ К лотам", callback_data="return_to_lots"))
    bot.send_message(message.chat.id, f"✅ ID услуги для {lot_key} изменён на {new_id}.", reply_markup=kb_)

def process_quantity_change(message: types.Message, lot_key: str):
    try:
        new_q = int(message.text.strip())
    except ValueError:
        bot.send_message(message.chat.id, "❌ Ошибка: Количество должно быть числом.")
        return
    cfg = load_config()
    lot_map = cfg.get("lot_mapping", {})
    if lot_key not in lot_map:
        bot.send_message(message.chat.id, f"❌ Лот {lot_key} не найден.")
        return
    lot_map[lot_key]["quantity"] = new_q
    cfg["lot_mapping"] = lot_map
    save_config(cfg)
    kb_ = InlineKeyboardMarkup()
    kb_.add(InlineKeyboardButton("◀️ К лотам", callback_data="return_to_lots"))
    bot.send_message(message.chat.id, f"✅ Количество для {lot_key} изменено на {new_q}.", reply_markup=kb_)

def process_service_num_change(message: types.Message, lot_key: str):
    try:
        new_snum = int(message.text.strip())
        cfg = load_config()
        if str(new_snum) not in cfg["services"]:
            bot.send_message(message.chat.id, f"❌ Ошибка: Сервис #{new_snum} не существует.")
            return
        lot_map = cfg.get("lot_mapping", {})
        if lot_key not in lot_map:
            bot.send_message(message.chat.id, f"❌ Лот {lot_key} не найден.")
            return
        lot_map[lot_key]["service_number"] = new_snum
        cfg["lot_mapping"] = lot_map
        save_config(cfg)
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("◀️ К лотам", callback_data="return_to_lots"))
        bot.send_message(message.chat.id, f"✅ Номер сервиса для {lot_key} изменён на {new_snum}.", reply_markup=kb_)
    except ValueError:
        bot.send_message(message.chat.id, "❌ Ошибка: Введите номер сервиса (число).")

def process_new_lot_id_step(message: types.Message):
    # v10.1 FIX: верхний catch-all + явное логирование. Раньше любое
    # исключение в этом обработчике (например NameError, AttributeError на
    # нестандартном LotFields) телебот глотал и пользователь видел тишину.
    logger.info(
        f"process_new_lot_id_step: received text={message.text!r}",
        extra={"event": "add_lot_step", "chat_id": message.chat.id, "raw": message.text},
    )
    try:
        if not message or not message.text:
            bot.send_message(message.chat.id, "❌ Пустое сообщение. Введите ID лота числом.")
            return
        try:
            lot_id = int(message.text.strip())
        except ValueError:
            bot.send_message(message.chat.id, "❌ Ошибка: ID лота должно быть числом.")
            return

        if cardinal_instance is None:
            bot.send_message(message.chat.id, "❌ Плагин ещё не инициализирован, перезапустите FPC.")
            return

        try:
            lot_fields = cardinal_instance.account.get_lot_fields(lot_id)
            fields = lot_fields.fields if lot_fields is not None else {}
            name = fields.get("fields[summary][ru]") or fields.get("fields[summary][en]") or f"Лот #{lot_id}"
        except Exception as e:
            logger.error(
                f"get_lot_fields({lot_id}) failed: {e}",
                extra={"event": "get_lot_fields_fail", "lot_id": lot_id, "error": str(e)},
            )
            bot.send_message(message.chat.id, f"❌ Не удалось получить данные лота {lot_id}: {e}")
            return

        cfg = load_config()
        lot_map = cfg.get("lot_mapping", {})

        # Идемпотентность: если такой lot_id уже есть — не плодим дубли.
        for existing_key, lot_info in lot_map.items():
            if str(lot_info.get("lot_id")) == str(lot_id):
                bot.send_message(message.chat.id, f"⚠ Лот {lot_id} уже добавлен как {existing_key} ({lot_info.get('name','?')}).")
                return

        new_lot_key = _next_lot_key(lot_map)
        lot_map[new_lot_key] = {
            "lot_id": lot_id,
            "name": name,
            "service_id": 1,
            "quantity": 1,
            "service_number": 1,
        }

        cfg["lot_mapping"] = lot_map
        save_config(cfg)

        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам", callback_data="return_to_settings"))
        bot.send_message(message.chat.id, f"✅ Добавлен новый лот {new_lot_key} с названием: {name}", reply_markup=kb_)
    except Exception as e:
        logger.exception(f"process_new_lot_id_step crashed: {e}")
        try:
            bot.send_message(message.chat.id, f"❌ Внутренняя ошибка добавления лота: {e}")
        except Exception:
            pass

def api_settings_menu(call):
        
    cfg = load_config()
    services = cfg["services"]

    text_ = """
<b>⚙️ Настройки API сервисов SMM</b>

Здесь вы можете настроить подключение к различным SMM-сервисам, 
проверить баланс или добавить новые сервисы.
"""

    for srv_num, srv_data in services.items():
        text_ += f"""
<b>📡 Сервис #{srv_num}</b>
• <b>URL:</b> <code>{srv_data['api_url']}</code>
• <b>API KEY:</b> <code>{srv_data['api_key']}</code>
"""

    kb = InlineKeyboardMarkup(row_width=2)
    
    kb.row(InlineKeyboardButton("📡 API URLs (показать все)", callback_data="show_all_api_urls"))
    
    api_buttons = []
    for srv_num in services:
        api_buttons.append(InlineKeyboardButton(f"Сервис #{srv_num}", callback_data=f"edit_apiurl_{srv_num}"))
    kb.add(*api_buttons)
    
    kb.row(InlineKeyboardButton("🔑 API Keys (показать все)", callback_data="show_all_api_keys"))
    
    key_buttons = []
    for srv_num in services:
        key_buttons.append(InlineKeyboardButton(f"Ключ #{srv_num}", callback_data=f"edit_apikey_{srv_num}"))
    kb.add(*key_buttons)
    
    kb.row(InlineKeyboardButton("💰 Балансы всех сервисов", callback_data="check_all_balances"))
    
    balance_buttons = []
    for srv_num in services:
        balance_buttons.append(InlineKeyboardButton(f"Баланс #{srv_num}", callback_data=f"check_balance_{srv_num}"))
    kb.add(*balance_buttons)
    
    kb.row(
        InlineKeyboardButton("➕ Добавить сервис", callback_data="add_service"),
        InlineKeyboardButton("🗑 Удалить сервис", callback_data="delete_service")
    )
    
    kb.add(InlineKeyboardButton("🔙 Вернуться в настройки", callback_data="return_to_settings"))

    bot.edit_message_text(text_, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=kb)

def process_apiurl_change(message: types.Message, service_idx: int):
        
    new_url = message.text.strip()
    
    if not new_url.startswith(("http://", "https://")):
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, "❌ URL должен начинаться с http:// или https://", reply_markup=kb_)
        return
        
    cfg = load_config()
    if str(service_idx) not in cfg["services"]:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, f"❌ Сервис #{service_idx} не найден в конфигурации.", reply_markup=kb_)
        return
        
    old_url = cfg["services"][str(service_idx)]["api_url"]
    cfg["services"][str(service_idx)]["api_url"] = new_url
    save_config(cfg)
    
    kb_ = InlineKeyboardMarkup(row_width=1)
    kb_.add(
        InlineKeyboardButton("✅ Проверить баланс", callback_data=f"check_balance_{service_idx}"),
        InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings")
    )
    
    text_ = f"""
✅ <b>URL сервиса #{service_idx} успешно обновлен!</b>

• <b>Было:</b> <code>{old_url}</code>
• <b>Стало:</b> <code>{new_url}</code>

Вы можете сразу проверить баланс сервиса для проверки работоспособности.
    """.strip()
    
    bot.send_message(message.chat.id, text_, parse_mode="HTML", reply_markup=kb_)

def process_apikey_change(message: types.Message, service_idx: int):
        
    new_key = message.text.strip()
    
    if not new_key:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, "❌ API ключ не может быть пустым", reply_markup=kb_)
        return
        
    cfg = load_config()
    if str(service_idx) not in cfg["services"]:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, f"❌ Сервис #{service_idx} не найден в конфигурации.", reply_markup=kb_)
        return
    
    old_key = cfg["services"][str(service_idx)]["api_key"]
    old_key_masked = f"{old_key[:4]}...{old_key[-4:]}" if len(old_key) > 8 else old_key
    new_key_masked = f"{new_key[:4]}...{new_key[-4:]}" if len(new_key) > 8 else new_key
    
    cfg["services"][str(service_idx)]["api_key"] = new_key
    save_config(cfg)
    
    kb_ = InlineKeyboardMarkup(row_width=1)
    kb_.add(
        InlineKeyboardButton("✅ Проверить баланс", callback_data=f"check_balance_{service_idx}"),
        InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings")
    )
    
    text_ = f"""
✅ <b>API-ключ сервиса #{service_idx} успешно обновлен!</b>

• <b>Было:</b> <code>{old_key_masked}</code>
• <b>Стало:</b> <code>{new_key_masked}</code>

Вы можете сразу проверить баланс сервиса для проверки работоспособности.
    """.strip()
    
    bot.send_message(message.chat.id, text_, parse_mode="HTML", reply_markup=kb_)

def check_balance_func(call: types.CallbackQuery, service_idx: int):
        
    cfg = load_config()
    s_ = cfg["services"].get(str(service_idx))
    if not s_:
        bot.edit_message_text(f"❌ Сервис {service_idx} не найден.", call.message.chat.id, call.message.message_id)
        return
        
    bot.edit_message_text(f"⏳ Проверка баланса сервиса #{service_idx}...", 
                         call.message.chat.id, call.message.message_id)
                         
    url_ = f"{s_['api_url']}?action=balance&key={s_['api_key']}"
    
    try:
        rr = HTTP_SESSION.get(url_, timeout=HTTP_TIMEOUT)
        rr.raise_for_status()
        d_ = rr.json()
        bal_ = d_.get("balance", "0")
        

        text_ = f"""
<b>💰 Баланс сервиса #{service_idx}</b>

• <b>Текущий баланс:</b> <code>{bal_}</code>
• <b>Сервис:</b> <code>{s_['api_url'].split('/')[2]}</code>
• <b>Время запроса:</b> <code>{datetime.now().strftime('%H:%M:%S')}</code>
        """.strip()
        
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        
        bot.edit_message_text(text_, call.message.chat.id, call.message.message_id, 
                             parse_mode="HTML", reply_markup=kb_)
                             
    except requests.exceptions.Timeout:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔄 Повторить", callback_data=f"check_balance_{service_idx}"))
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        
        bot.edit_message_text(f"⚠️ Время ожидания ответа от сервиса #{service_idx} истекло.",
                             call.message.chat.id, call.message.message_id, reply_markup=kb_)
                             
    except Exception as e:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔄 Повторить", callback_data=f"check_balance_{service_idx}"))
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        
        bot.edit_message_text(f"❌ Ошибка при запросе баланса сервиса #{service_idx}:\n<code>{str(e)[:100]}</code>", 
                             call.message.chat.id, call.message.message_id, 
                             parse_mode="HTML", reply_markup=kb_)

def _mask_api_key(key: str) -> str:
    """v11.3: маскирует ключ для отображения (показывает первые 4 + последние 4)."""
    if not key:
        return "—"
    k = str(key)
    if len(k) <= 12:
        return k[:2] + "•" * (len(k) - 2)
    return f"{k[:4]}…{k[-4:]} ({len(k)} симв.)"


def show_all_api_urls_func(call: types.CallbackQuery):
    """v11.3: сводный список всех API-URL'ов сервисов."""
    cfg = load_config()
    services = cfg.get("services", {}) or {}
    lines = ["<b>📡 API URLs всех сервисов</b>", ""]
    if not services:
        lines.append("Сервисов пока не добавлено.")
    else:
        for srv_num in sorted(services.keys(), key=lambda x: int(x) if str(x).isdigit() else 0):
            s = services[srv_num]
            url = s.get("api_url", "—")
            try:
                host = url.split("/")[2] if "://" in url else url
            except Exception:
                host = url
            lines.append(f"• <b>Сервис #{srv_num}</b>: <code>{html.escape(url)}</code> ({html.escape(host)})")
    kb_ = InlineKeyboardMarkup()
    kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
    bot.edit_message_text("\n".join(lines), call.message.chat.id, call.message.message_id,
                          parse_mode="HTML", reply_markup=kb_)


def show_all_api_keys_func(call: types.CallbackQuery):
    """v11.3: сводный список ключей всех сервисов (маскированные)."""
    cfg = load_config()
    services = cfg.get("services", {}) or {}
    lines = ["<b>🔑 API Keys всех сервисов</b>", "<i>(ключи маскированы: первые 4 + последние 4 символа)</i>", ""]
    if not services:
        lines.append("Сервисов пока не добавлено.")
    else:
        for srv_num in sorted(services.keys(), key=lambda x: int(x) if str(x).isdigit() else 0):
            s = services[srv_num]
            key = s.get("api_key", "")
            status = "✅" if key else "❌"
            lines.append(f"• <b>Сервис #{srv_num}</b>: {status} <code>{html.escape(_mask_api_key(key))}</code>")
    kb_ = InlineKeyboardMarkup()
    kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
    bot.edit_message_text("\n".join(lines), call.message.chat.id, call.message.message_id,
                          parse_mode="HTML", reply_markup=kb_)


def check_all_balances_func(call: types.CallbackQuery):
    """v11.3: опрашивает балансы всех сервисов и показывает сводную таблицу."""
    cfg = load_config()
    services = cfg.get("services", {}) or {}
    bot.edit_message_text("⏳ Опрос балансов всех сервисов…",
                          call.message.chat.id, call.message.message_id)

    if not services:
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.edit_message_text("Сервисов пока не добавлено.",
                              call.message.chat.id, call.message.message_id, reply_markup=kb_)
        return

    lines = ["<b>💰 Балансы всех сервисов</b>",
             f"<i>обновлено в {datetime.now().strftime('%H:%M:%S')}</i>", ""]
    total_lines = []
    for srv_num in sorted(services.keys(), key=lambda x: int(x) if str(x).isdigit() else 0):
        s = services[srv_num]
        url_ = f"{s.get('api_url','')}?action=balance&key={s.get('api_key','')}"
        try:
            rr = HTTP_SESSION.get(url_, timeout=HTTP_TIMEOUT, verify=smm_verify())
            if rr.status_code != 200:
                total_lines.append(f"• <b>Сервис #{srv_num}</b>: ❌ HTTP {rr.status_code}")
                continue
            try:
                d_ = rr.json()
            except Exception:
                total_lines.append(f"• <b>Сервис #{srv_num}</b>: ❌ некорректный JSON")
                continue
            bal = d_.get("balance", "—")
            cur = d_.get("currency", "")
            host = s.get("api_url", "").split("/")[2] if "/" in s.get("api_url", "") else "—"
            total_lines.append(f"• <b>Сервис #{srv_num}</b> ({html.escape(host)}): "
                               f"<code>{html.escape(str(bal))} {html.escape(str(cur))}</code>")
        except requests.exceptions.Timeout:
            total_lines.append(f"• <b>Сервис #{srv_num}</b>: ⏰ таймаут")
        except Exception as e:
            total_lines.append(f"• <b>Сервис #{srv_num}</b>: ❌ {html.escape(str(e)[:80])}")

    lines.extend(total_lines)
    kb_ = InlineKeyboardMarkup(row_width=2)
    kb_.add(
        InlineKeyboardButton("🔄 Обновить", callback_data="check_all_balances"),
        InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"),
    )
    bot.edit_message_text("\n".join(lines), call.message.chat.id, call.message.message_id,
                          parse_mode="HTML", reply_markup=kb_)


def init_commands(c_: Cardinal):
    global bot, config, lot_mapping, cardinal_instance
    logger.info("=== init_commands() from auto_smm (2 services) ===")

    logger.info("Плагин активирован.")

    cardinal_instance = c_
    bot = c_.telegram.bot

    # P.32: разводим конфиги и state по подкаталогам аккаунта.
    try:
        account_id = getattr(getattr(c_, "account", None), "id", None)
        if account_id:
            _rebind_paths_for_account(account_id)
    except Exception as e:
        logger.error(f"P.32 rebind failed: {e}")

    # v10: инициализация SQLite + одноразовая миграция из JSON.
    try:
        _db_init()
        _db_migrate_from_json(ORDERS_DATA_PATH)
        _db_migrate_customers_from_json(CUSTOMER_PROFILES_PATH)
    except Exception as e:
        logger.error(f"v10 SQLite init failed: {e}", extra={"event": "db_init_fail"})

    # P.13: единоразовый прогон reconcile_storages приведёт ORDERS_PATH и
    # ORDERS_DATA_PATH к согласованному состоянию (canonical = orders_data).
    try:
        reconcile_storages()
    except Exception as e:
        logger.error(f"reconcile_storages failed: {e}")

    # P.14: запускаем watcher диалогов (напоминание + авто-рефанд по таймауту).
    try:
        _start_dialog_timeout_watcher(c_)
    except Exception as e:
        logger.error(f"start_dialog_timeout_watcher failed: {e}")

    auto_started = auto_start_plugin(c_)
    if auto_started:
        logger.info("Плагин был автоматически запущен при инициализации")

    @bot.message_handler(content_types=['document'])
    def handle_document_upload(message: types.Message):
        user_id = message.from_user.id
        logger.info(f"Получен документ от {user_id}. Проверка ожидания...")
        if user_id not in waiting_for_lots_upload:
            logger.info(f"Пользователь {user_id} не ожидает загрузки JSON")
            bot.send_message(message.chat.id, "❌ Вы не активировали загрузку JSON. Используйте меню настроек.")
            return
        waiting_for_lots_upload.remove(user_id)
        logger.info(f"Пользователь {user_id} удалён из ожидания. Обрабатываю файл...")
        file_id = message.document.file_id
        file_info = bot.get_file(file_id)
        downloaded_file = bot.download_file(file_info.file_path)
        try:
            data = json.loads(downloaded_file.decode('utf-8'))
            if "lot_mapping" not in data:
                bot.send_message(message.chat.id, "❌ Ошибка: в файле нет ключа 'lot_mapping'.")
                logger.error("JSON не содержит 'lot_mapping'")
                return
            save_config(data)
            kb_ = InlineKeyboardMarkup()
            kb_.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
            bot.send_message(message.chat.id, "✅ Новый auto_lots.json успешно загружен и сохранён!", reply_markup=kb_)
            logger.info("JSON успешно загружен и сохранён")
        except json.JSONDecodeError as e:
            bot.send_message(message.chat.id, f"❌ Ошибка: Не удалось считать JSON. Проверьте синтаксис. ({e})")
            logger.error(f"Ошибка декодирования JSON: {e}")
        except Exception as e:
            bot.send_message(message.chat.id, f"❌ Произошла ошибка при загрузке файла: {e}")
            logger.error(f"Неизвестная ошибка при загрузке: {e}")

    cfg = load_config()
    config.update(cfg)
    lot_mapping.clear()
    lot_mapping.update(cfg.get("lot_mapping", {}))
    
    c_.add_telegram_commands(UUID, [
        ("start_smm", "Включить автопродажу", True),
        ("stop_smm", "Выключить автопродажу", True),
        ("auto_smm_settings", "Настройки автопродажи", True),
        ("auto_smm_delete", "Удалить файлы заказов", True)
    ])

    @bot.callback_query_handler(func=lambda call: call.data == "manage_websites")
    def manage_websites(call: types.CallbackQuery):
        valid_links = load_valid_links()
        if valid_links:
            kb_ = InlineKeyboardMarkup(row_width=2)
            for site in valid_links:
                kb_.add(
                    InlineKeyboardButton(site, callback_data=f"delete_website_{site}"),
                    InlineKeyboardButton("Удалить", callback_data=f"delete_website_{site}")
                )
        else:
            kb_ = InlineKeyboardMarkup(row_width=1)
        
        kb_.add(InlineKeyboardButton("➕ Добавить сайт", callback_data="add_website"))
        kb_.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))

        bot.edit_message_text("Список разрешённых сайтов:", call.message.chat.id, call.message.message_id, reply_markup=kb_)

    @bot.callback_query_handler(func=lambda call: call.data == "add_website")
    def add_website_prompt(call: types.CallbackQuery):
        msg_ = bot.edit_message_text("Введите ссылку для добавления (например, example.com):", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_add_website)

    def process_add_website(message: types.Message):
        new_site = message.text.strip()
        add_website(message, new_site)
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 Вернуться в настройки", callback_data="return_to_settings"))
        bot.send_message(message.chat.id, "Вернитесь в настройки для продолжения.", reply_markup=kb_)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("delete_website_"))
    def remove_website_prompt(call: types.CallbackQuery):
        site_to_remove = call.data.split("_", 2)[2]
        valid_links = load_valid_links()
        if site_to_remove in valid_links:
            valid_links.remove(site_to_remove)
            save_valid_links(valid_links)
            bot.edit_message_text(f"✅ Сайт {site_to_remove} удалён из списка.", call.message.chat.id, call.message.message_id)
        else:
            bot.edit_message_text(f"❌ Сайт {site_to_remove} не найден в списке.", call.message.chat.id, call.message.message_id)
        manage_websites(call)

    @bot.callback_query_handler(func=lambda call: call.data == "delete_all_lots")
    def delete_all_lots_prompt(call: types.CallbackQuery):
        kb = InlineKeyboardMarkup()
        kb.add(
            InlineKeyboardButton("Да, удалить", callback_data="confirm_delete_all_lots"),
            InlineKeyboardButton("Нет, отменить", callback_data="return_to_settings")
        )
        bot.edit_message_text("Вы уверены, что хотите удалить все лоты?", call.message.chat.id, call.message.message_id, reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "confirm_delete_all_lots")
    def confirm_delete_all_lots(call: types.CallbackQuery):
        delete_all_lots_func(call)
        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
        bot.edit_message_text("Все лоты удалены.", call.message.chat.id, call.message.message_id, reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "lot_settings")
    def lot_settings(call: types.CallbackQuery):
        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(InlineKeyboardButton("🔍 Поиск лота", callback_data="search_lot"))
        kb.add(InlineKeyboardButton("📋 Список лотов", callback_data="show_lots_list"))
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
        bot.edit_message_text("Управление лотами:", call.message.chat.id, call.message.message_id, reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "show_lots_list")
    def show_lots_list(call: types.CallbackQuery):
        page = _save_lot_page(call.message.chat.id, _get_lot_page(call.message.chat.id))
        bot.edit_message_text("Выберите лот:", call.message.chat.id, call.message.message_id, reply_markup=generate_lots_keyboard(page))

    @bot.callback_query_handler(func=lambda call: call.data == "search_lot")
    def search_lot_prompt(call: types.CallbackQuery):
        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="lot_settings"))
        msg = bot.edit_message_text("Введите название или часть названия лота для поиска:", 
                                    call.message.chat.id, call.message.message_id, reply_markup=kb)
        bot.register_next_step_handler(msg, process_lot_search)

    def process_lot_search(message: types.Message):
        search_term = message.text.strip().lower()
        if not search_term:
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("🔙 К настройкам лотов", callback_data="lot_settings"))
            bot.send_message(message.chat.id, "❌ Поисковый запрос не может быть пустым.", reply_markup=kb)
            return
            
        cfg = load_config()
        lot_map = cfg.get("lot_mapping", {})
        
        found_lots = {}
        for lot_key, lot_data in lot_map.items():
            lot_name = lot_data["name"].lower()
            if search_term in lot_name:
                found_lots[lot_key] = lot_data
                
        if not found_lots:
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("🔍 Новый поиск", callback_data="search_lot"))
            kb.add(InlineKeyboardButton("🔙 К настройкам лотов", callback_data="lot_settings"))
            bot.send_message(message.chat.id, f"❌ Лоты с названием '{search_term}' не найдены.", reply_markup=kb)
            return
            
        kb = InlineKeyboardMarkup(row_width=1)
        for lot_key, lot_data in found_lots.items():
            name_ = lot_data["name"]
            sid_ = lot_data["service_id"]
            qty_ = lot_data["quantity"]
            snum_ = lot_data.get("service_number", 1)
            btn_text = f"{name_} [ID={sid_}, Q={qty_}, S={snum_}]"
            cd_ = f"edit_lot_{lot_key}"
            kb.add(InlineKeyboardButton(btn_text, callback_data=cd_))
            
        kb.add(InlineKeyboardButton("🔍 Новый поиск", callback_data="search_lot"))
        kb.add(InlineKeyboardButton("🔙 К настройкам лотов", callback_data="lot_settings"))
        bot.send_message(message.chat.id, f"🔍 Результаты поиска для '{search_term}':", reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("edit_lot_"))
    def edit_lot_callback(call: types.CallbackQuery):
        lot_key = call.data.split("_", 2)[2]
        edit_lot(call, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("prev_page_") or call.data.startswith("next_page_"))
    def page_navigation(call: types.CallbackQuery):
        try:
            page_ = int(call.data.split("_")[-1])
        except ValueError:
            page_ = 0
        page_ = _save_lot_page(call.message.chat.id, page_)
        bot.edit_message_text("Выберите лот:", call.message.chat.id, call.message.message_id, reply_markup=generate_lots_keyboard(page_))

    @bot.callback_query_handler(func=lambda call: call.data == "show_orders")
    def show_orders(call: types.CallbackQuery):
        stats = get_statistics()
        if not stats:
            kb = InlineKeyboardMarkup()
            kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
            bot.edit_message_text("❌ Нет данных о заказах.", call.message.chat.id, call.message.message_id, reply_markup=kb)
            return

        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))

        text = f"""
📊 <b>Информация о заказах SMM</b>

За 24 часа: {stats['day_orders']} заказов на {stats['day_total']} руб. (чистая прибыль: {stats['day_chistota']} руб.)
За неделю: {stats['week_orders']} заказов на {stats['week_total']} руб. (чистая прибыль: {stats['week_chistota']} руб.)
За месяц: {stats['month_orders']} заказов на {stats['month_total']} руб. (чистая прибыль: {stats['month_chistota']} руб.)
За всё время: {stats['all_time_orders']} заказов на {stats['all_time_total']} руб. (чистая прибыль: {stats['all_time_chistota']} руб.)
        """.strip()

        try:
            bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)
        except Exception as e:
            logger.error(f"Ошибка при редактировании сообщения: {e}")
            bot.send_message(call.message.chat.id, text, parse_mode='HTML', reply_markup=kb)
        
        bot.answer_callback_query(call.id)

    @bot.callback_query_handler(func=lambda call: call.data == "upload_lots_json")
    def upload_lots_json(call: types.CallbackQuery):
        user_id = call.from_user.id
        waiting_for_lots_upload.add(user_id)
        logger.info(f"Добавлен пользователь {user_id} в waiting_for_lots_upload: {waiting_for_lots_upload}")
        bot.edit_message_text("Пришлите файл JSON (можно любым названием).", call.message.chat.id, call.message.message_id)

    @bot.callback_query_handler(func=lambda call: call.data == "export_files")
    def export_files(call: types.CallbackQuery):
        chat_id_ = call.message.chat.id
        # v10.1 FIX: orders_data.json после миграции переименован в .legacy.bak,
        # canonical-хранилище теперь auto_smm.db. Дампим заказы из SQLite в
        # in-memory JSON и шлём как orders_data.json — формат совместимый.
        try:
            orders_dump = json.dumps(load_orders_data(), ensure_ascii=False, indent=2).encode("utf-8")
            bot.send_document(
                chat_id_,
                ("orders_data.json", io.BytesIO(orders_dump)),
                caption="Файл: orders_data.json (выгружен из SQLite)",
            )
        except Exception as e:
            bot.send_message(chat_id_, f"Не удалось выгрузить orders_data из SQLite: {e}")

        # Остальные файлы — конфиг, view, БД, customer profiles.
        files_to_send = [CONFIG_PATH, ORDERS_PATH, DB_PATH, CUSTOMER_PROFILES_PATH]
        for f_ in files_to_send:
            if os.path.exists(f_):
                try:
                    with open(f_, 'rb') as ff:
                        bot.send_document(chat_id_, ff, caption=f"Файл: {os.path.basename(f_)}")
                except Exception as e:
                    bot.send_message(chat_id_, f"Ошибка отправки {os.path.basename(f_)}: {e}")
            # отсутствующие файлы (например customers.json до первого VIP) тихо пропускаем

    @bot.callback_query_handler(func=lambda call: call.data == "export_errors")
    def export_errors(call: types.CallbackQuery):
        chat_id_ = call.message.chat.id
        if os.path.exists(LOG_PATH):
            try:
                with open(LOG_PATH, 'rb') as f:
                    bot.send_document(chat_id_, f, caption="Лог ошибок")
                bot.edit_message_text("Логи выгружены.", chat_id_, call.message.message_id)
            except Exception as e:
                bot.edit_message_text(f"Ошибка отправки лог-файла: {e}", chat_id_, call.message.message_id)
        else:
            bot.edit_message_text("Лог-файл не найден.", chat_id_, call.message.message_id)

    @bot.callback_query_handler(func=lambda call: call.data == "delete_orders")
    def delete_orders(call: types.CallbackQuery):
        if os.path.exists(ORDERS_PATH):
            os.remove(ORDERS_PATH)
        if os.path.exists(ORDERS_DATA_PATH):
            os.remove(ORDERS_DATA_PATH)
        bot.edit_message_text("Файлы заказов удалены.", call.message.chat.id, call.message.message_id)
        files_menu(call)

    @bot.callback_query_handler(func=lambda call: call.data == "toggle_auto_refunds")
    def toggle_auto_refunds(call: types.CallbackQuery):
        cfg = load_config()
        ar_ = cfg.get("auto_refunds", True)
        cfg["auto_refunds"] = not ar_
        save_config(cfg)
        bot.answer_callback_query(call.id, f"✅ Автовозвраты: {'ВКЛ' if cfg['auto_refunds'] else 'ВЫКЛ'}")
        misc_settings(call)

    @bot.callback_query_handler(func=lambda call: call.data == "toggle_confirm_link")
    def toggle_confirm_link(call: types.CallbackQuery):
        cfg = load_config()
        confirm_link = cfg.get("confirm_link", True)
        cfg["confirm_link"] = not confirm_link
        save_config(cfg)
        bot.answer_callback_query(call.id, f"✅ Подтверждение ссылки: {'ВКЛ' if cfg['confirm_link'] else 'ВЫКЛ'}")
        misc_settings(call)

    @bot.callback_query_handler(func=lambda call: call.data == "toggle_send_auto_lots")
    def toggle_send_auto_lots(call: types.CallbackQuery):
        cfg = load_config()
        current_value = cfg.get("send_auto_lots", True)
        cfg["send_auto_lots"] = not current_value
        save_config(cfg)
        bot.answer_callback_query(call.id, f"Отправка auto_lots.json {'отключена' if current_value else 'включена'}!")
        misc_settings(call)
        
    @bot.callback_query_handler(func=lambda call: call.data == "toggle_auto_start")
    def toggle_auto_start(call: types.CallbackQuery):
        cfg = load_config()
        current_value = cfg.get("auto_start", False)
        cfg["auto_start"] = not current_value
        save_config(cfg)
        bot.answer_callback_query(call.id, f"Автозапуск плагина {'отключен' if current_value else 'включен'}!")
        misc_settings(call)

    @bot.callback_query_handler(func=lambda call: call.data == "change_send_interval")
    def change_send_interval(call: types.CallbackQuery):
        cfg = load_config()
        current_interval = cfg.get("send_auto_lots_interval", 30)
        
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 Вернуться назад", callback_data="cancel_interval_change"))
        
        msg_ = bot.edit_message_text(f"Текущий интервал отправки: {current_interval} минут\n\nВведите новый интервал отправки auto_lots.json в минутах (от 5 до 1440):", 
                                call.message.chat.id, call.message.message_id, reply_markup=kb_)
        bot.register_next_step_handler(msg_, process_send_interval_change)

    @bot.callback_query_handler(func=lambda call: call.data == "cancel_interval_change")
    def cancel_interval_change(call: types.CallbackQuery):
        bot.clear_step_handler_by_chat_id(call.message.chat.id)
        misc_settings(call)
    
    def process_send_interval_change(message: types.Message):
        try:
            new_interval = int(message.text.strip())
            if new_interval < 5:
                bot.send_message(message.chat.id, "❌ Интервал не может быть меньше 5 минут")
                return
            if new_interval > 1440:
                bot.send_message(message.chat.id, "❌ Интервал не может быть больше 1440 минут (24 часа)")
                return
                
            cfg = load_config()
            cfg["send_auto_lots_interval"] = new_interval
            save_config(cfg)
            
            kb_ = InlineKeyboardMarkup()
            kb_.add(InlineKeyboardButton("🔙 К настройкам", callback_data="misc_settings"))
            bot.send_message(message.chat.id, f"✅ Интервал отправки auto_lots.json установлен: {new_interval} минут", reply_markup=kb_)
        except ValueError:
            bot.send_message(message.chat.id, "❌ Ошибка: Введите корректное число минут.")
            
    @bot.callback_query_handler(func=lambda call: call.data == "return_to_settings")
    def return_to_settings(call: types.CallbackQuery):
        
        cfg = load_config()
        lmap = cfg.get("lot_mapping", {})
        auto_refunds = cfg.get("auto_refunds", True)
        confirm_link = cfg.get("confirm_link", True)
        notif_chat_id = cfg.get("notification_chat_id", "Не задан")
        send_auto_lots = cfg.get("send_auto_lots", True)
        send_auto_lots_interval = cfg.get("send_auto_lots_interval", 30)
        auto_start = cfg.get("auto_start", False)

        status_text = "✅ АКТИВИРОВАН"

        txt_ = f"""
🚀 <b>AUTOSMM ПАНЕЛЬ УПРАВЛЕНИЯ v{VERSION}</b> 🚀
━━━━━━━━━━━━━━━━━━━━━━━━
👨‍💻 <b>Разработчик:</b> {CREDITS}

📊 <b>СТАТУС:</b> {status_text}

💡 <b>ОСНОВНЫЕ ПАРАМЕТРЫ:</b>
 • Лотов в базе: <code>{len(lmap)}</code>
 • Автовозвраты: {'✅' if auto_refunds else '❌'}
 • Подтверждение ссылки: {'✅' if confirm_link else '❌'}
 • Отправка auto_lots.json: {'✅' if send_auto_lots else '❌'}
 • Интервал отправки: <code>{send_auto_lots_interval} мин</code>
 • Автозапуск: {'✅' if auto_start else '❌'}

📞 <b>УВЕДОМЛЕНИЯ:</b> <code>{notif_chat_id}</code>

📝 <b>О ПЛАГИНЕ:</b> <i>{DESCRIPTION}</i>
━━━━━━━━━━━━━━━━━━━━━━━━
    """.strip()

        kb = InlineKeyboardMarkup(row_width=2)
        
        kb.add(
            InlineKeyboardButton("🛍️ Каталог лотов", callback_data="lot_settings"),
            InlineKeyboardButton("➕ Создать новый лот", callback_data="add_new_lot")
        )
        
        kb.add(
            InlineKeyboardButton("🔌 Интеграция API", callback_data="api_settings"),
        )
        
        kb.add(
            InlineKeyboardButton("🌐 Доверенные сайты", callback_data="manage_websites"),
            InlineKeyboardButton("💬 Шаблоны сообщений", callback_data="edit_messages")
        )
        
        kb.add(
            InlineKeyboardButton("📊 Бэкап и аналитика", callback_data="files_menu"),
            InlineKeyboardButton("⚙️ Тонкая настройка", callback_data="misc_settings")
        )
        
        kb.add(
            InlineKeyboardButton("📚 Полезные ресурсы", callback_data="links_menu")
        )

        bot.edit_message_text(txt_, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "return_to_lots")
    def return_to_lots(call: types.CallbackQuery):
        page = _save_lot_page(call.message.chat.id, _get_lot_page(call.message.chat.id))
        bot.edit_message_text("Выберите лот:", call.message.chat.id, call.message.message_id, reply_markup=generate_lots_keyboard(page))

    @bot.callback_query_handler(func=lambda call: call.data.startswith("change_name_"))
    def change_name(call: types.CallbackQuery):
        lot_key = call.data.split("_", 2)[2]
        msg_ = bot.edit_message_text(f"Введите новое название для {lot_key}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_name_change, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("change_id_"))
    def change_id(call: types.CallbackQuery):
        lot_key = call.data.split("_", 2)[2]
        msg_ = bot.edit_message_text(f"Введите новый ID услуги для {lot_key}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_id_change, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("change_quantity_"))
    def change_quantity(call: types.CallbackQuery):
        lot_key = call.data.split("_", 2)[2]
        msg_ = bot.edit_message_text(f"Введите новое количество для {lot_key}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_quantity_change, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("change_snum_"))
    def change_snum(call: types.CallbackQuery):
        lot_key = call.data.split("_", 2)[2]
        msg_ = bot.edit_message_text(f"Введите номер сервиса для {lot_key}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_service_num_change, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("delete_one_lot_"))
    def delete_one_lot_callback(call: types.CallbackQuery):
        lot_key = call.data.split("_", 3)[3]
        delete_one_lot(call, lot_key)

    @bot.callback_query_handler(func=lambda call: call.data == "api_settings")
    def api_settings_callback(call: types.CallbackQuery):
        api_settings_menu(call)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("edit_apiurl_"))
    def edit_apiurl(call: types.CallbackQuery):
        idx_ = int(call.data.split("_")[-1])
        msg_ = bot.edit_message_text(f"Введите новый URL для сервиса #{idx_}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_apiurl_change, idx_)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("edit_apikey_"))
    def edit_apikey(call: types.CallbackQuery):
        idx_ = int(call.data.split("_")[-1])
        msg_ = bot.edit_message_text(f"Введите новый ключ для сервиса #{idx_}:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_apikey_change, idx_)

    @bot.callback_query_handler(func=lambda call: call.data.startswith("check_balance_"))
    def check_balance(call: types.CallbackQuery):
        idx_ = int(call.data.split("_")[-1])
        check_balance_func(call, idx_)

    @bot.callback_query_handler(func=lambda call: call.data == "add_new_lot")
    def add_new_lot(call: types.CallbackQuery):
        bot.delete_message(call.message.chat.id, call.message.message_id)
        msg_ = bot.send_message(call.message.chat.id, "Введите ID лота для добавления:")
        bot.register_next_step_handler(msg_, process_new_lot_id_step)

    @bot.callback_query_handler(func=lambda call: call.data == "update_lot_ids")
    def update_lot_ids(call: types.CallbackQuery):
        cfg = load_config()
        reindex_lots(cfg)
        bot.answer_callback_query(call.id, "Номера лотов обновлены.")
        misc_settings(call)

    @bot.callback_query_handler(func=lambda call: call.data == "edit_messages")
    def edit_messages_menu(call: types.CallbackQuery):
        cfg = load_config()
        msg_payment = html.escape(cfg["messages"]["after_payment"])
        msg_confirmation = html.escape(cfg["messages"]["after_confirmation"])

        # v10.1 FIX: были f-string с {orderID}/{buyer}/... — Python пытался
        # резолвить их как переменные, NameError, telebot глотал и хендлер
        # молча умирал. Теперь обычная конкатенация.
        vars_line = (
            "Переменные: {orderID}, {buyer}, {amount}, {price}, {service}, {link}"
        )
        text_ = (
            "⚙ <b>Редактирование текстов сообщений</b>\n\n"
            "<b>После оплаты:</b>\n\n"
            f"{vars_line}\n\n"
            f"<code>{msg_payment}</code>\n\n"
            "<b>После подтверждения ссылки:</b>\n\n"
            f"{vars_line}\n\n"
            f"<code>{msg_confirmation}</code>"
        )

        kb = InlineKeyboardMarkup(row_width=1)
        kb.add(
            InlineKeyboardButton("Изменить текст после оплаты", callback_data="edit_msg_payment"),
            InlineKeyboardButton("Изменить текст после подтверждения", callback_data="edit_msg_confirmation")
        )
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))

        bot.edit_message_text(text_, call.message.chat.id, call.message.message_id, parse_mode="HTML", reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "edit_msg_payment")
    def edit_msg_payment(call: types.CallbackQuery):
        msg_ = bot.edit_message_text("Введите новый текст после оплаты:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_message_payment_change)

    @bot.callback_query_handler(func=lambda call: call.data == "edit_msg_confirmation")
    def edit_msg_confirmation(call: types.CallbackQuery):
        msg_ = bot.edit_message_text("Введите новый текст после подтверждения:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_message_confirmation_change)

    def process_message_payment_change(message: types.Message):
        new_text = message.text.strip()
        cfg = load_config()
        cfg["messages"]["after_payment"] = new_text
        save_config(cfg)
        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
        bot.send_message(message.chat.id, "Текст после оплаты обновлен.", reply_markup=kb)

    def process_message_confirmation_change(message: types.Message):
        new_text = message.text.strip()
        cfg = load_config()
        cfg["messages"]["after_confirmation"] = new_text
        save_config(cfg)
        kb = InlineKeyboardMarkup()
        kb.add(InlineKeyboardButton("🔙 Назад", callback_data="return_to_settings"))
        bot.send_message(message.chat.id, "Текст после подтверждения обновлен.", reply_markup=kb)

    @bot.callback_query_handler(func=lambda call: call.data == "add_service")
    def add_service(call: types.CallbackQuery):
        msg_ = bot.edit_message_text("Введите номер нового сервиса (число):", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_add_service)

    @bot.callback_query_handler(func=lambda call: call.data == "delete_service")
    def delete_service(call: types.CallbackQuery):
        msg_ = bot.edit_message_text("Введите номер сервиса для удаления:", call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_delete_service)

    def process_add_service(message: types.Message):
        try:
            srv_num = int(message.text.strip())
            if srv_num < 1:
                raise ValueError
        except ValueError:
            bot.send_message(message.chat.id, "❌ Ошибка: Номер сервиса должен быть положительным числом.")
            return

        cfg = load_config()
        if str(srv_num) in cfg["services"]:
            bot.send_message(message.chat.id, f"❌ Сервис #{srv_num} уже существует.")
            return

        cfg["services"][str(srv_num)] = {
            "api_url": "https://example.com/api/v2",
            "api_key": "YOUR_API_KEY"
        }
        save_config(cfg)
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, f"✅ Сервис #{srv_num} добавлен. Настройте его URL и ключ.", reply_markup=kb_)

    def process_delete_service(message: types.Message):
        try:
            srv_num = int(message.text.strip())
        except ValueError:
            bot.send_message(message.chat.id, "❌ Ошибка: Номер сервиса должен быть числом.")
            return

        cfg = load_config()
        if str(srv_num) not in cfg["services"]:
            bot.send_message(message.chat.id, f"❌ Сервис #{srv_num} не существует.")
            return

        del cfg["services"][str(srv_num)]
        save_config(cfg)
        kb_ = InlineKeyboardMarkup()
        kb_.add(InlineKeyboardButton("🔙 К настройкам API", callback_data="api_settings"))
        bot.send_message(message.chat.id, f"✅ Сервис #{srv_num} удален.", reply_markup=kb_)

    @bot.callback_query_handler(func=lambda call: call.data == "set_notification_chat_id")
    def set_notification_chat_id(call: types.CallbackQuery):
        msg_ = bot.edit_message_text(f"Введите Chat ID для уведомлений (например, -1001234567890 для группы или ваш ID, ваш id: {call.message.chat.id}):", 
                                    call.message.chat.id, call.message.message_id)
        bot.register_next_step_handler(msg_, process_notification_chat_id)

    def process_notification_chat_id(message: types.Message):
        try:
            new_chat_id = int(message.text.strip())
            cfg = load_config()
            cfg["notification_chat_id"] = new_chat_id
            save_config(cfg)
            kb_ = InlineKeyboardMarkup()
            kb_.add(InlineKeyboardButton("🔙 К настройкам", callback_data="return_to_settings"))
            bot.send_message(message.chat.id, f"✅ Chat ID для уведомлений установлен: {new_chat_id}", reply_markup=kb_)
        except ValueError:
            bot.send_message(message.chat.id, "❌ Ошибка: Введите корректный Chat ID (целое число).")

    @bot.callback_query_handler(func=lambda call: call.data == "files_menu")
    def files_menu_callback(call: types.CallbackQuery):
        files_menu(call)

    @bot.callback_query_handler(func=lambda call: call.data == "misc_settings")
    def misc_settings_callback(call: types.CallbackQuery):
        misc_settings(call)

    @bot.callback_query_handler(func=lambda call: call.data == "links_menu")
    def links_menu_callback(call: types.CallbackQuery):
        links_menu(call)

    # v11.3: бывшие inline-заголовки теперь полноценные кнопки.
    @bot.callback_query_handler(func=lambda call: call.data == "show_all_api_urls")
    def show_all_api_urls_callback(call: types.CallbackQuery):
        show_all_api_urls_func(call)

    @bot.callback_query_handler(func=lambda call: call.data == "show_all_api_keys")
    def show_all_api_keys_callback(call: types.CallbackQuery):
        show_all_api_keys_func(call)

    @bot.callback_query_handler(func=lambda call: call.data == "check_all_balances")
    def check_all_balances_callback(call: types.CallbackQuery):
        check_all_balances_func(call)

    # v11.2: бекомпат для старых сообщений с заголовками — тихо проглатываем.
    @bot.callback_query_handler(func=lambda call: call.data == "header_no_action")
    def header_no_action_callback(call: types.CallbackQuery):
        try:
            bot.answer_callback_query(call.id)
        except Exception:
            pass

    # === v11.4 FIX (2026-05): catch-all БОЛЬШЕ НЕТ. ===
    # Раньше здесь висел @bot.callback_query_handler(func=lambda call: True),
    # который перехватывал ВСЕ callback'и в TG-боте FPC, включая колбэки
    # других плагинов (TeamX-воронка, авто-выдача FPC, авто-ответчик FPC) и
    # самого Cardinal. Из-за этого пользователь нажимал «Подать заявку» в
    # сторонней воронке → catch-all отвечал answer_callback_query(call.id) и
    # реальный handler никогда не отрабатывал. Воронка фиксировала «Застрял
    # на кнопке».
    #
    # Если в будущем понадобится логировать «осиротевшие» callback'и нашего
    # плагина — фильтруй ИМЕННО по prefix-ам нашего плагина, не по `True`.
    # Пример:
    #   _MY_PREFIXES = ("lot_settings", "edit_apiurl_", "check_balance_", ...)
    #   @bot.callback_query_handler(
    #       func=lambda call: any(call.data.startswith(p) for p in _MY_PREFIXES)
    #   )
    #   def my_orphan_callback(call): ...

    c_.telegram.msg_handler(start_smm, commands=["start_smm"])
    c_.telegram.msg_handler(stop_smm, commands=["stop_smm"])
    c_.telegram.msg_handler(auto_smm_settings, commands=["auto_smm_settings"])
    c_.telegram.msg_handler(auto_smm_delete, commands=["auto_smm_delete"])

    # === v8: дополнительные команды ===
    c_.telegram.msg_handler(autosmm_pnl_command, commands=["autosmm_pnl"])
    c_.telegram.msg_handler(autosmm_top_command, commands=["autosmm_top"])
    c_.telegram.msg_handler(autosmm_health_command, commands=["autosmm_health"])
    c_.telegram.msg_handler(autosmm_refill_now_command, commands=["autosmm_refill_now"])
    c_.telegram.msg_handler(autosmm_rate_command, commands=["autosmm_rate"])

    # === v9: команды клиентских профилей ===
    c_.telegram.msg_handler(autosmm_customers_command, commands=["autosmm_customers"])

    # === v11: дашборд ошибок ===
    c_.telegram.msg_handler(autosmm_errors_command, commands=["autosmm_errors"])
    c_.telegram.msg_handler(autosmm_pending_command, commands=["autosmm_pending"])

    # Запускаем v8-потоки (refill watcher, balance watcher, webhook).
    _start_refill_watcher(c_)
    _start_balance_watcher(c_)
    _start_webhook_server_if_enabled(c_)
    # === v9: бэкапы state-файлов ===
    _start_backup_watcher(c_)
    # === v11: pending_refunds queue worker + canary heartbeat ===
    _start_pending_refunds_worker(c_)
    _start_canary(c_)


# =====================================================================
# === v8: Currency utils (USD/RUB) ====================================
# =====================================================================

CBR_RATE_URL = "https://www.cbr-xml-daily.ru/daily_json.js"
USD_RUB_REFRESH_INTERVAL_SEC = 6 * 60 * 60
_USD_RUB_CACHE_LOCK = threading.Lock()


def _maybe_refresh_usd_rub_rate(cfg: Optional[Dict] = None) -> float:
    """
    Возвращает актуальный курс USD→RUB. Если в конфиге `usd_rub_auto_refresh=True`
    и кеш старше 6 часов — тянет курс из ЦБР, обновляет конфиг. На любой ошибке
    возвращает текущий cfg['usd_rub_rate'] (никогда не падает).
    """
    if cfg is None:
        cfg = load_config()
    rate = float(cfg.get("usd_rub_rate", 95.0))
    if not cfg.get("usd_rub_auto_refresh", True):
        return rate
    last = float(cfg.get("usd_rub_last_refreshed", 0) or 0)
    if time.time() - last < USD_RUB_REFRESH_INTERVAL_SEC:
        return rate
    with _USD_RUB_CACHE_LOCK:
        # повторная проверка после захвата лока
        cfg = load_config()
        last = float(cfg.get("usd_rub_last_refreshed", 0) or 0)
        if time.time() - last < USD_RUB_REFRESH_INTERVAL_SEC:
            return float(cfg.get("usd_rub_rate", rate))
        try:
            resp = HTTP_SESSION.get(CBR_RATE_URL, timeout=HTTP_TIMEOUT)
            resp.raise_for_status()
            new_rate = float(resp.json()["Valute"]["USD"]["Value"])
            cfg["usd_rub_rate"] = round(new_rate, 4)
            cfg["usd_rub_last_refreshed"] = time.time()
            save_config(cfg)
            logger.info(
                "usd_rub_rate refreshed",
                extra={"event": "usd_rub_refresh", "rate": cfg["usd_rub_rate"]},
            )
            return float(cfg["usd_rub_rate"])
        except Exception as e:
            logger.warning(f"usd_rub refresh failed: {e}; используем кешированный курс {rate}")
            return rate


def convert_to_rub(amount: float, currency: str, *, cfg: Optional[Dict] = None) -> float:
    """
    Приводит сумму к рублям. Поддерживаются 'RUB' (≡ identity) и 'USD'.
    Любая другая валюта — возвращаем как есть с warning'ом (не догадываемся).
    """
    try:
        amt = float(amount)
    except (TypeError, ValueError):
        return 0.0
    cur = (currency or "USD").upper()
    if cur == "RUB":
        return round(amt, 2)
    if cur == "USD":
        rate = _maybe_refresh_usd_rub_rate(cfg)
        return round(amt * rate, 2)
    logger.warning(f"convert_to_rub: неизвестная валюта {cur!r}, возвращаю как есть")
    return round(amt, 2)


# =====================================================================
# === v8: P.20 — Sanitizers ===========================================
# =====================================================================

_USERNAME_BAD_CHARS = re.compile(r"[\u0000-\u001F\u007F]")  # control chars


def _safe_username(s: Optional[str], max_len: int = 64) -> str:
    """
    P.20: чистим имя покупателя для безопасной вставки в TG-сообщение.
    - срезаем control-символы (\\x00..\\x1F, DEL),
    - выкидываем markdown/html-метасимволы, которыми ник мог инжектить ссылку,
    - ограничиваем длину.
    Используется во ВСЕХ админских уведомлениях и логах, где видим buyer_username.
    """
    if not s:
        return "—"
    s = _USERNAME_BAD_CHARS.sub("", str(s))
    s = s.strip()
    # Удаляем символы которые ломают TG-парсер или могут стать активной разметкой.
    s = re.sub(r"[<>`\[\]\(\)*_~]", "", s)
    if len(s) > max_len:
        s = s[: max_len - 1] + "…"
    return s or "—"


# =====================================================================
# === v8: SMM-API helpers (balance / status) для health & refill =======
# =====================================================================

def _smm_query_balance(service_cfg: Dict) -> Tuple[float, str, float]:
    """
    Возвращает (balance, native_currency, latency_sec). Бросает на любой ошибке.
    Выявленную валюту автоматически записывает в service_cfg['currency'] (in-memory).
    """
    api_url = service_cfg["api_url"]
    api_key = service_cfg["api_key"]
    url_ = f"{api_url}?action=balance&key={api_key}"
    t0 = time.time()
    resp = http_request_with_retries(
        "GET", url_,
        log_extra={"stage": "balance"},
        max_retries=2,  # для health-чека долго ждать не имеет смысла
    )
    resp.raise_for_status()
    data = resp.json()
    balance = float(data.get("balance", 0))
    currency = (data.get("currency") or service_cfg.get("currency") or "USD").upper()
    latency = time.time() - t0
    service_cfg["currency"] = currency  # auto-detect
    return balance, currency, latency


def _smm_query_status(service_cfg: Dict, twiboost_id: int) -> Dict:
    """Возвращает raw JSON со статусом заказа из SMM-сервиса. Использует ретраи."""
    api_url = service_cfg["api_url"]
    api_key = service_cfg["api_key"]
    url_ = f"{api_url}?action=status&order={twiboost_id}&key={api_key}"
    resp = http_request_with_retries(
        "GET", url_,
        log_extra={"stage": "status_query", "twiboost_order_id": twiboost_id},
        max_retries=3,
    )
    resp.raise_for_status()
    return resp.json()


def _smm_request_refill(service_cfg: Dict, twiboost_id: int) -> Dict:
    """Запрашивает рефилл у SMM-сервиса. Возвращает raw JSON."""
    api_url = service_cfg["api_url"]
    api_key = service_cfg["api_key"]
    url_ = f"{api_url}?action=refill&order={twiboost_id}&key={api_key}"
    resp = http_request_with_retries(
        "GET", url_,
        log_extra={"stage": "refill_request", "twiboost_order_id": twiboost_id},
        max_retries=3,
    )
    resp.raise_for_status()
    return resp.json()


# =====================================================================
# === v8: Admin auth (мини-проверка, что команда от авторизованного TG) =
# =====================================================================

def _is_admin_message(message) -> bool:
    """
    Возвращает True, если сообщение от админа FPC. Используем встроенный
    helper FPC: если у бота настроен `chat_id` админа в TG, c.telegram.bot
    обычно знает список админов. Тут используем простую проверку: читаем
    notification_chat_id и сравниваем — большинство одно-операторных установок
    закрывают этим. Для расширения — вписывайте список chat_id в
    cfg['admin_chat_ids'].
    """
    cfg = load_config()
    admins = cfg.get("admin_chat_ids") or []
    if cfg.get("notification_chat_id"):
        admins = list(admins) + [cfg["notification_chat_id"]]
    if not admins:
        # Без явного списка пускаем всех — но логируем.
        return True
    try:
        cid = message.chat.id
    except Exception:
        return False
    return cid in [int(a) for a in admins if a is not None]


# =====================================================================
# === v8: П.25 P&L dashboard ==========================================
# =====================================================================

def _orders_in_window(orders: List[Dict], days: Optional[int]) -> List[Dict]:
    if days is None:
        return list(orders)
    cutoff = datetime.now() - timedelta(days=days)
    out = []
    for o in orders:
        d = o.get("date")
        if not d:
            continue
        try:
            dt = datetime.strptime(d, "%Y-%m-%d %H:%M:%S")
        except Exception:
            continue
        if dt >= cutoff:
            out.append(o)
    return out


def _aggregate_pnl(orders: List[Dict], cfg: Dict) -> Dict:
    """
    Для каждого ордера: revenue (RUB) = summa, cost (RUB) = convert(spent, currency).
    margin = revenue - cost. Возвращает агрегат + per-order details (для топ-листа).
    """
    n = len(orders)
    revenue_rub = 0.0
    cost_rub = 0.0
    refunded = 0
    completed = 0
    per_lot: Dict[str, Dict] = {}
    for o in orders:
        rev = float(o.get("summa") or 0)
        cur = (o.get("currency") or "USD").upper()
        spent = float(o.get("spent") or 0)
        cost = convert_to_rub(spent, cur, cfg=cfg)
        revenue_rub += rev
        cost_rub += cost
        if o.get("is_refunded"):
            refunded += 1
        if (o.get("status") or "").lower() == "completed":
            completed += 1
        lot_name = (o.get("service_name") or "—").strip() or "—"
        slot = per_lot.setdefault(lot_name, {"count": 0, "revenue_rub": 0.0, "cost_rub": 0.0})
        slot["count"] += 1
        slot["revenue_rub"] += rev
        slot["cost_rub"] += cost
    margin_rub = revenue_rub - cost_rub
    return {
        "n": n,
        "revenue_rub": round(revenue_rub, 2),
        "cost_rub": round(cost_rub, 2),
        "margin_rub": round(margin_rub, 2),
        "refunded": refunded,
        "completed": completed,
        "refund_pct": round(100.0 * refunded / n, 1) if n else 0.0,
        "avg_check_rub": round(revenue_rub / n, 2) if n else 0.0,
        "per_lot": per_lot,
    }


def autosmm_pnl_command(message):
    if not _is_admin_message(message):
        return
    cfg = load_config()
    orders = load_orders_data()
    rate = _maybe_refresh_usd_rub_rate(cfg)
    windows = [("24ч", 1), ("7д", 7), ("30д", 30), ("All-time", None)]
    lines = [
        f"<b>📊 P&amp;L AutoSMM</b>",
        f"<i>USD→RUB:</i> <code>{rate:.2f}</code>",
        "",
    ]
    for label, days in windows:
        agg = _aggregate_pnl(_orders_in_window(orders, days), cfg)
        if agg["n"] == 0:
            lines.append(f"<b>{label}:</b> 0 заказов")
            continue
        lines.append(
            f"<b>{label}:</b> {agg['n']} зак., "
            f"💰 {agg['revenue_rub']:.0f}₽ / "
            f"💸 {agg['cost_rub']:.0f}₽ / "
            f"✅ <b>{agg['margin_rub']:.0f}₽</b>"
        )
        lines.append(
            f"  ср.чек: {agg['avg_check_rub']:.0f}₽, "
            f"refund: {agg['refunded']} ({agg['refund_pct']}%), "
            f"completed: {agg['completed']}"
        )
    # ARR-проекция
    agg30 = _aggregate_pnl(_orders_in_window(orders, 30), cfg)
    arr = agg30["margin_rub"] * 12
    lines.append("")
    lines.append(f"📈 ARR-проекция (margin30 × 12): <b>{arr:.0f}₽/год</b>")
    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def autosmm_top_command(message):
    if not _is_admin_message(message):
        return
    cfg = load_config()
    orders = load_orders_data()
    agg = _aggregate_pnl(_orders_in_window(orders, 30), cfg)
    if agg["n"] == 0:
        bot.send_message(message.chat.id, "За 30 дней заказов нет.")
        return
    by_volume = sorted(agg["per_lot"].items(), key=lambda kv: kv[1]["count"], reverse=True)[:5]
    by_margin = sorted(
        agg["per_lot"].items(),
        key=lambda kv: kv[1]["revenue_rub"] - kv[1]["cost_rub"],
        reverse=True,
    )[:5]
    lines = ["<b>🏆 Топ-5 лотов за 30 дней</b>", "", "<b>По объёму:</b>"]
    for name, st in by_volume:
        margin = st["revenue_rub"] - st["cost_rub"]
        lines.append(f"• <code>{html.escape(name)}</code>: {st['count']} зак., margin {margin:.0f}₽")
    lines.append("")
    lines.append("<b>По марже:</b>")
    for name, st in by_margin:
        margin = st["revenue_rub"] - st["cost_rub"]
        lines.append(f"• <code>{html.escape(name)}</code>: margin {margin:.0f}₽ ({st['count']} зак.)")
    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def autosmm_rate_command(message):
    """Покажи / принудительно обнови курс."""
    if not _is_admin_message(message):
        return
    cfg = load_config()
    text = (message.text or "").strip()
    if "refresh" in text.lower() or "обнов" in text.lower():
        cfg["usd_rub_last_refreshed"] = 0
        save_config(cfg)
    rate = _maybe_refresh_usd_rub_rate(cfg)
    cfg = load_config()
    last = cfg.get("usd_rub_last_refreshed", 0) or 0
    last_human = (
        datetime.fromtimestamp(last).strftime("%Y-%m-%d %H:%M:%S")
        if last else "never"
    )
    bot.send_message(
        message.chat.id,
        f"<b>USD→RUB</b>: <code>{rate:.4f}</code>\n"
        f"<i>Last refresh:</i> {html.escape(last_human)}\n"
        f"<i>Auto-refresh:</i> {'on' if cfg.get('usd_rub_auto_refresh', True) else 'off'}\n\n"
        f"<i>Команда</i> <code>/autosmm_rate refresh</code> — принудительно обновить.",
        parse_mode="HTML",
    )


# =====================================================================
# === v8: П.27 Health-check ============================================
# =====================================================================

def autosmm_health_command(message):
    if not _is_admin_message(message):
        return
    cfg = load_config()
    rate = _maybe_refresh_usd_rub_rate(cfg)
    orders = load_orders_data()
    pending_total = sum(
        1 for o in orders
        if (o.get("status") or "").lower() not in ("completed", "legacy", "awaiting_link")
        and not o.get("is_refunded")
    )
    lines = ["<b>🏥 AutoSMM health</b>", f"<i>USD→RUB:</i> <code>{rate:.2f}</code>", ""]
    for svc_id, svc in cfg.get("services", {}).items():
        lines.append(f"<b>Сервис #{svc_id}:</b> <code>{html.escape(str(svc.get('api_url', '')))}</code>")
        try:
            balance, currency, latency = _smm_query_balance(svc)
            balance_rub = convert_to_rub(balance, currency, cfg=cfg)
            threshold = float(svc.get("balance_alert_threshold", 10.0))
            warn = "⚠️" if balance < threshold else "✅"
            lines.append(
                f"  {warn} balance: <b>{balance:.2f} {html.escape(currency)}</b> "
                f"(≈{balance_rub:.0f}₽) | latency: {latency*1000:.0f} ms"
            )
            # сохраним детектированную валюту в конфиг
            cfg["services"][svc_id]["currency"] = currency
        except Exception as e:
            lines.append(f"  ❌ balance error: <code>{html.escape(str(e)[:120])}</code>")
        # pending для этого сервиса
        pending_svc = sum(
            1 for o in orders
            if str(o.get("service_number")) == str(svc_id)
            and (o.get("status") or "").lower() not in ("completed", "legacy", "awaiting_link")
            and not o.get("is_refunded")
        )
        lines.append(f"  pending: {pending_svc}")
    save_config(cfg)
    lines.append("")
    lines.append(f"<b>Всего pending:</b> {pending_total}")

    # последние 5 ошибок из лог-файла (ищем JSON-строки с level ERROR/WARNING)
    errs = _tail_log_errors(5)
    if errs:
        lines.append("")
        lines.append("<b>Последние ошибки:</b>")
        for e in errs:
            lines.append(f"• <code>{html.escape(e[:160])}</code>")

    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def _tail_log_errors(n: int = 5) -> List[str]:
    if not os.path.exists(LOG_PATH):
        return []
    try:
        # читаем хвост файла безопасно — последние ~64KB
        with open(LOG_PATH, "rb") as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - 64 * 1024))
            tail = f.read().decode("utf-8", errors="ignore")
        out = []
        for line in tail.splitlines()[::-1]:
            try:
                rec = json.loads(line)
            except Exception:
                continue
            if rec.get("level") in ("ERROR", "WARNING"):
                out.append(f"[{rec.get('level')}] {rec.get('msg','')}")
                if len(out) >= n:
                    break
        return out
    except Exception:
        return []


# =====================================================================
# === v8: Balance watcher (низкий баланс → пуш админу) ================
# =====================================================================

_BALANCE_WATCHER_THREAD: Optional[threading.Thread] = None
# Мапа service_id -> ts последнего алерта (антиспам — не чаще чем раз в 6 ч).
_BALANCE_LAST_ALERT: Dict[str, float] = {}
_BALANCE_ALERT_COOLDOWN_SEC = 6 * 60 * 60


def _balance_watcher_loop(c: "Cardinal"):
    logger.info("balance_watcher started")
    while not _SHUTDOWN_EVENT.is_set():
        cfg = load_config()
        if not cfg.get("balance_watcher_enabled", True):
            if _SHUTDOWN_EVENT.wait(300):
                break
            continue
        interval_sec = max(60, int(cfg.get("balance_watcher_interval_hours", 1)) * 3600)
        notification_chat_id = cfg.get("notification_chat_id")
        for svc_id, svc in cfg.get("services", {}).items():
            try:
                balance, currency, _ = _smm_query_balance(svc)
                threshold = float(svc.get("balance_alert_threshold", 10.0))
                if balance < threshold and notification_chat_id:
                    last = _BALANCE_LAST_ALERT.get(str(svc_id), 0)
                    if time.time() - last > _BALANCE_ALERT_COOLDOWN_SEC:
                        try:
                            c.telegram.bot.send_message(
                                notification_chat_id,
                                f"⚠️ <b>SMM balance low</b>\n"
                                f"Сервис #{svc_id}: <b>{balance:.2f} {html.escape(currency)}</b>\n"
                                f"Порог: {threshold} {html.escape(currency)}\n"
                                f"Пополни до того, как пойдут refund-ы.",
                                parse_mode="HTML",
                            )
                            _BALANCE_LAST_ALERT[str(svc_id)] = time.time()
                            logger.warning(
                                "balance_alert sent",
                                extra={
                                    "event": "balance_alert",
                                    "service_id": str(svc_id),
                                    "balance": balance,
                                    "currency": currency,
                                    "threshold": threshold,
                                },
                            )
                        except Exception as e:
                            logger.error(f"balance_alert send failed: {e}")
            except Exception as e:
                logger.warning(
                    f"balance_watcher: service #{svc_id} ping failed: {e}",
                    extra={"event": "balance_check_fail", "service_id": str(svc_id)},
                )
        if _SHUTDOWN_EVENT.wait(interval_sec):
            break
    logger.info("balance_watcher finished (shutdown).")


def _start_balance_watcher(c: "Cardinal") -> None:
    global _BALANCE_WATCHER_THREAD
    if _BALANCE_WATCHER_THREAD and _BALANCE_WATCHER_THREAD.is_alive():
        return
    _BALANCE_WATCHER_THREAD = threading.Thread(
        target=_balance_watcher_loop, args=(c,),
        daemon=True, name="auto_smm_balance_watcher",
    )
    _BALANCE_WATCHER_THREAD.start()


# =====================================================================
# === v8: П.26 Auto-refill (гарантия) ==================================
# =====================================================================

_REFILL_WATCHER_THREAD: Optional[threading.Thread] = None


def _attempt_refill_for_order(c: "Cardinal", svc_id: str, svc: Dict, order: Dict, cfg: Dict) -> Optional[str]:
    """
    Попытка авторефилла для одного заказа. Возвращает строку-описание
    результата или None, если рефилл не нужен. Не бросает.
    """
    twiboost_id = order.get("id_zakaz")
    if not twiboost_id:
        return None
    quantity = int(order.get("quantity") or 0)
    if quantity <= 0:
        return None
    try:
        st = _smm_query_status(svc, twiboost_id)
    except Exception as e:
        return f"#{order.get('order_id')}: status error: {e}"
    try:
        remains = int(st.get("remains", 0))
    except Exception:
        remains = 0
    pct = 100.0 * remains / quantity if quantity else 0.0
    threshold = float(cfg.get("auto_refill_min_remains_pct", 5))
    if pct < threshold:
        return None
    try:
        rr = _smm_request_refill(svc, twiboost_id)
    except Exception as e:
        return f"#{order.get('order_id')}: refill API error: {e}"

    # Обновляем заказ.
    with _FILES_LOCK:
        all_orders = load_orders_data()
        for o in all_orders:
            if str(o.get("order_id")) == str(order.get("order_id")):
                o["last_refill_at"] = time.time()
                o["refill_count"] = int(o.get("refill_count", 0)) + 1
                o.setdefault("refill_history", []).append({
                    "ts": time.time(),
                    "remains_pct": round(pct, 2),
                    "result": rr,
                })
                break
        save_orders_data(all_orders)

    logger.info(
        f"auto_refill: requested for #{order.get('order_id')} (remains {pct:.1f}%)",
        extra={
            "event": "auto_refill",
            "order_id": str(order.get("order_id")),
            "twiboost_order_id": twiboost_id,
            "remains_pct": round(pct, 2),
            "service_id": str(svc_id),
        },
    )
    return f"#{order.get('order_id')}: refill OK (remains {pct:.1f}%)"


def _refill_watcher_loop(c: "Cardinal"):
    logger.info("refill_watcher started")
    # небольшая задержка на старте чтобы не дёргать API сразу при загрузке
    if _SHUTDOWN_EVENT.wait(60):
        return
    while not _SHUTDOWN_EVENT.is_set():
        cfg = load_config()
        if not cfg.get("auto_refill_enabled", True):
            if _SHUTDOWN_EVENT.wait(600):
                break
            continue
        interval_sec = max(600, int(cfg.get("auto_refill_interval_hours", 6)) * 3600)
        warranty_days = int(cfg.get("auto_refill_warranty_days", 60))
        cutoff = datetime.now() - timedelta(days=warranty_days)
        try:
            orders = load_orders_data()
        except Exception as e:
            logger.error(f"refill_watcher: load_orders_data failed: {e}")
            orders = []

        notification_chat_id = cfg.get("notification_chat_id")
        ran = []
        for o in orders:
            if (o.get("status") or "").lower() != "completed":
                continue
            if o.get("is_refunded"):
                continue
            d = o.get("date")
            if not d:
                continue
            try:
                dt = datetime.strptime(d, "%Y-%m-%d %H:%M:%S")
            except Exception:
                continue
            if dt < cutoff:
                continue
            # Не чаще чем раз в 6 часов на один заказ.
            last_refill = float(o.get("last_refill_at") or 0)
            if last_refill and time.time() - last_refill < 6 * 3600:
                continue
            svc_id = str(o.get("service_number") or "1")
            svc = cfg.get("services", {}).get(svc_id)
            if not svc:
                continue
            res = _attempt_refill_for_order(c, svc_id, svc, o, cfg)
            if res:
                ran.append(res)
            # Не бомбим API.
            if _SHUTDOWN_EVENT.wait(2.0):
                break

        if ran and notification_chat_id:
            try:
                c.telegram.bot.send_message(
                    notification_chat_id,
                    "<b>🔁 Auto-refill отчёт</b>\n" + "\n".join(html.escape(s) for s in ran[:30]),
                    parse_mode="HTML",
                )
            except Exception as e:
                logger.error(f"refill_watcher: notify failed: {e}")
        logger.info(
            "refill_watcher cycle done",
            extra={"event": "auto_refill_cycle", "actions": len(ran)},
        )
        if _SHUTDOWN_EVENT.wait(interval_sec):
            break
    logger.info("refill_watcher finished (shutdown).")


def _start_refill_watcher(c: "Cardinal") -> None:
    global _REFILL_WATCHER_THREAD
    if _REFILL_WATCHER_THREAD and _REFILL_WATCHER_THREAD.is_alive():
        return
    _REFILL_WATCHER_THREAD = threading.Thread(
        target=_refill_watcher_loop, args=(c,),
        daemon=True, name="auto_smm_refill_watcher",
    )
    _REFILL_WATCHER_THREAD.start()


def autosmm_refill_now_command(message):
    """Ручной запуск одного цикла авторефилла (полезно для тестов)."""
    if not _is_admin_message(message):
        return
    bot.send_message(message.chat.id, "🔁 Запускаю один цикл auto-refill в фоне…")
    cfg = load_config()
    cfg["auto_refill_enabled"] = True
    save_config(cfg)
    if cardinal_instance is not None:
        threading.Thread(
            target=lambda: _refill_one_pass(cardinal_instance),
            daemon=True,
        ).start()


def _refill_one_pass(c: "Cardinal"):
    """Один проход авторефилла без цикла (для /autosmm_refill_now)."""
    cfg = load_config()
    warranty_days = int(cfg.get("auto_refill_warranty_days", 60))
    cutoff = datetime.now() - timedelta(days=warranty_days)
    orders = load_orders_data()
    notification_chat_id = cfg.get("notification_chat_id")
    ran = []
    for o in orders:
        if (o.get("status") or "").lower() != "completed" or o.get("is_refunded"):
            continue
        d = o.get("date")
        if not d:
            continue
        try:
            dt = datetime.strptime(d, "%Y-%m-%d %H:%M:%S")
        except Exception:
            continue
        if dt < cutoff:
            continue
        svc_id = str(o.get("service_number") or "1")
        svc = cfg.get("services", {}).get(svc_id)
        if not svc:
            continue
        res = _attempt_refill_for_order(c, svc_id, svc, o, cfg)
        if res:
            ran.append(res)
    if notification_chat_id:
        msg = "🔁 Один цикл auto-refill завершён.\n" + ("\n".join(html.escape(s) for s in ran[:30]) or "Нечего рефиллить.")
        try:
            c.telegram.bot.send_message(notification_chat_id, msg, parse_mode="HTML")
        except Exception as e:
            logger.error(f"manual refill notify failed: {e}")


# =====================================================================
# === v8: П.21 Webhook receiver (опциональный) =========================
# =====================================================================

_WEBHOOK_SERVER = None
_WEBHOOK_THREAD: Optional[threading.Thread] = None


def _make_webhook_handler(c: "Cardinal"):
    from http.server import BaseHTTPRequestHandler

    class AutoSMMWebhookHandler(BaseHTTPRequestHandler):
        # silence default stderr access logs — у нас свой logger
        def log_message(self, format, *args):
            logger.debug("webhook: " + (format % args))

        def do_POST(self):
            if self.path != "/autosmm/callback":
                self.send_response(404); self.end_headers(); return
            cfg = load_config()
            secret = (cfg.get("webhook_secret") or "").encode()
            sig = self.headers.get("X-Signature", "")
            length = int(self.headers.get("Content-Length") or 0)
            body = self.rfile.read(length) if length else b""
            expected = hmac.new(secret, body, hashlib.sha256).hexdigest() if secret else ""
            if not secret or not hmac.compare_digest(sig, expected):
                logger.warning(
                    "webhook: invalid signature",
                    extra={"event": "webhook_bad_sig", "path": self.path},
                )
                self.send_response(401); self.end_headers(); return
            try:
                payload = json.loads(body.decode("utf-8") or "{}")
            except Exception:
                self.send_response(400); self.end_headers(); return
            order_id = str(payload.get("order_id") or "")
            twiboost_id = payload.get("twiboost_id")
            status = (payload.get("status") or "").lower()
            charge = payload.get("charge")
            currency = (payload.get("currency") or "USD").upper()
            remains = payload.get("remains")
            logger.info(
                "webhook received",
                extra={
                    "event": "webhook_in",
                    "order_id": order_id,
                    "twiboost_order_id": twiboost_id,
                    "status": status,
                    "charge": charge,
                    "currency": currency,
                    "remains": remains,
                },
            )
            try:
                # Найдём buyer_chat_id и customer_url по orders_data
                target = None
                with _FILES_LOCK:
                    for o in load_orders_data():
                        if order_id and str(o.get("order_id")) == order_id:
                            target = o; break
                        if twiboost_id and str(o.get("id_zakaz")) == str(twiboost_id):
                            target = o; break
                if target is None:
                    self.send_response(202); self.end_headers(); return
                if charge is not None:
                    try:
                        update_order_charge_and_net(
                            str(target.get("order_id")),
                            float(charge),
                            currency=currency,
                            net_profit=None,
                        )
                    except Exception as e:
                        logger.error(f"webhook: update_order_charge_and_net failed: {e}")
                if status in ("completed", "done", "success", "partial"):
                    # помечаем completed_notification_sent + рассылаем покупателю
                    with _FILES_LOCK:
                        latest = load_orders_data()
                        for rec in latest:
                            if str(rec.get("order_id")) == str(target.get("order_id")):
                                rec["completed_notification_sent"] = True
                                rec["status"] = "completed"
                                break
                        save_orders_data(latest)
                    try:
                        order_link = f"https://funpay.com/orders/{target.get('order_id')}/"
                        c.send_message(
                            target.get("chat_id"),
                            f"🎉 Ваш заказ успешно завершён!\n"
                            f"🔢 Номер заказа: {target.get('id_zakaz')}\n"
                            f"🔗 Подтвердите заказ: {order_link}",
                        )
                    except Exception as e:
                        logger.error(f"webhook: notify buyer failed: {e}")
                elif status in ("failed", "error", "canceled"):
                    try:
                        refund_order(
                            c, str(target.get("order_id")), int(target.get("chat_id")),
                            reason=f"Webhook: статус {status}.",
                            detailed_reason=f"SMM-сервис вернул через webhook статус '{status}'.",
                        )
                    except Exception as e:
                        logger.error(f"webhook: refund failed: {e}")
                self.send_response(200); self.end_headers()
            except Exception as e:
                logger.error(f"webhook: processing failed: {e}")
                self.send_response(500); self.end_headers()

    return AutoSMMWebhookHandler


def _start_webhook_server_if_enabled(c: "Cardinal") -> None:
    global _WEBHOOK_SERVER, _WEBHOOK_THREAD
    cfg = load_config()
    if not cfg.get("webhook_enabled", False):
        return
    if _WEBHOOK_THREAD and _WEBHOOK_THREAD.is_alive():
        return
    if not cfg.get("webhook_secret"):
        cfg["webhook_secret"] = hashlib.sha256(os.urandom(32)).hexdigest()[:32]
        save_config(cfg)
        logger.info("webhook: сгенерирован новый webhook_secret и сохранён в auto_lots.json")
    port = int(cfg.get("webhook_port", 8800))
    # v10: ThreadingHTTPServer вместо HTTPServer — обрабатывает несколько
    # коллбэков параллельно. Раньше запросы стояли в очереди по одному.
    from http.server import ThreadingHTTPServer
    try:
        _WEBHOOK_SERVER = ThreadingHTTPServer(("0.0.0.0", port), _make_webhook_handler(c))
        # daemon-threads, чтобы при выгрузке плагина зависшие коллбэки
        # не задерживали shutdown.
        _WEBHOOK_SERVER.daemon_threads = True
    except OSError as e:
        logger.error(f"webhook: не смог открыть порт {port}: {e}")
        return

    def _serve():
        logger.info(f"webhook: listening on 0.0.0.0:{port} POST /autosmm/callback")
        try:
            _WEBHOOK_SERVER.serve_forever(poll_interval=1.0)
        finally:
            logger.info("webhook: serve_forever завершён")

    _WEBHOOK_THREAD = threading.Thread(target=_serve, daemon=True, name="auto_smm_webhook")
    _WEBHOOK_THREAD.start()


# =====================================================================
# === v9: П.28 — rolling backups of state files =======================
# =====================================================================

_BACKUP_WATCHER_THREAD: Optional[threading.Thread] = None
BACKUP_INTERVAL_SEC = 60 * 60                # 1 раз в час
BACKUP_RETAIN_HOURLY = 24                    # последние 24 часовых
BACKUP_RETAIN_DAILY = 30                     # + 30 ежедневных


def _backup_state_files(reason: str = "scheduled") -> Optional[str]:
    """
    Пакует все актуальные state-файлы в tar.gz внутри BACKUP_DIR. Возвращает путь
    к созданному архиву или None при ошибке. Не бросает.
    """
    try:
        os.makedirs(BACKUP_DIR, exist_ok=True)
        ts = time.strftime("%Y%m%d_%H%M%S")
        archive_path = os.path.join(BACKUP_DIR, f"auto_smm_state_{ts}_{reason}.tar.gz")
        import tarfile
        sources = [CONFIG_PATH, ORDERS_PATH, ORDERS_DATA_PATH, STATE_PATH, CUSTOMER_PROFILES_PATH]
        with _FILES_LOCK:
            with tarfile.open(archive_path, "w:gz") as tar:
                for src in sources:
                    if os.path.exists(src):
                        tar.add(src, arcname=os.path.basename(src))
        logger.info(
            f"backup created: {archive_path}",
            extra={"event": "backup_created", "path": archive_path, "reason": reason},
        )
        return archive_path
    except Exception as e:
        logger.error(f"_backup_state_files failed: {e}", extra={"event": "backup_fail"})
        return None


def _backup_rotate() -> None:
    """
    Чистим старые бэкапы: оставляем последние BACKUP_RETAIN_HOURLY часовых +
    BACKUP_RETAIN_DAILY ежедневных (по одному снимку на день).
    """
    try:
        if not os.path.isdir(BACKUP_DIR):
            return
        files = []
        for fn in os.listdir(BACKUP_DIR):
            if not fn.startswith("auto_smm_state_") or not fn.endswith(".tar.gz"):
                continue
            full = os.path.join(BACKUP_DIR, fn)
            try:
                mtime = os.path.getmtime(full)
            except OSError:
                continue
            files.append((mtime, full, fn))
        files.sort(reverse=True)
        keep_hourly = {f[1] for f in files[:BACKUP_RETAIN_HOURLY]}
        # daily: один файл на день
        keep_daily = set()
        seen_days = set()
        for mtime, full, _ in files:
            day = time.strftime("%Y-%m-%d", time.localtime(mtime))
            if day in seen_days:
                continue
            seen_days.add(day)
            keep_daily.add(full)
            if len(keep_daily) >= BACKUP_RETAIN_DAILY:
                break
        keep = keep_hourly | keep_daily
        removed = 0
        for _, full, _ in files:
            if full not in keep:
                try:
                    os.remove(full)
                    removed += 1
                except OSError:
                    pass
        if removed:
            logger.info(
                f"backup rotation: removed {removed} old backups",
                extra={"event": "backup_rotate", "removed": removed, "kept": len(keep)},
            )
    except Exception as e:
        logger.error(f"_backup_rotate failed: {e}")


def _maybe_upload_backup(archive_path: str, cfg: Dict) -> None:
    """
    Опциональный upload бэкапа на удалённый HTTP/S3-compatible endpoint.
    cfg["backup_remote_url"] — куда POST-ить, cfg["backup_remote_token"] — Bearer.
    Не падает на ошибке.
    """
    url = cfg.get("backup_remote_url") or ""
    if not url or not archive_path or not os.path.exists(archive_path):
        return
    headers = {}
    token = cfg.get("backup_remote_token")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    try:
        with open(archive_path, "rb") as f:
            resp = HTTP_SESSION.put(url, data=f, headers=headers, timeout=(10, 120))
        if resp.status_code >= 400:
            logger.warning(
                f"backup upload failed: HTTP {resp.status_code}",
                extra={"event": "backup_upload_fail", "status": resp.status_code},
            )
        else:
            logger.info(
                f"backup uploaded to remote",
                extra={"event": "backup_uploaded", "path": archive_path, "status": resp.status_code},
            )
    except Exception as e:
        logger.warning(f"backup upload error: {e}", extra={"event": "backup_upload_err"})


def _backup_watcher_loop(c: "Cardinal"):
    logger.info("backup_watcher started")
    # стартовый бэкап сразу
    try:
        cfg = load_config()
        if cfg.get("backup_enabled", True):
            path = _backup_state_files(reason="startup")
            if path:
                _maybe_upload_backup(path, cfg)
            _backup_rotate()
    except Exception as e:
        logger.error(f"backup_watcher startup failed: {e}")
    while not _SHUTDOWN_EVENT.is_set():
        if _SHUTDOWN_EVENT.wait(BACKUP_INTERVAL_SEC):
            break
        try:
            cfg = load_config()
            if not cfg.get("backup_enabled", True):
                continue
            path = _backup_state_files(reason="scheduled")
            if path:
                _maybe_upload_backup(path, cfg)
            _backup_rotate()
        except Exception as e:
            logger.error(f"backup_watcher iteration failed: {e}")
    logger.info("backup_watcher finished (shutdown).")


def _start_backup_watcher(c: "Cardinal") -> None:
    global _BACKUP_WATCHER_THREAD
    if _BACKUP_WATCHER_THREAD and _BACKUP_WATCHER_THREAD.is_alive():
        return
    _BACKUP_WATCHER_THREAD = threading.Thread(
        target=_backup_watcher_loop, args=(c,),
        daemon=True, name="auto_smm_backup_watcher",
    )
    _BACKUP_WATCHER_THREAD.start()


# =====================================================================
# === v9: П.29 — Customer profiles / VIP-логика ========================
# =====================================================================

VIP_WINDOW_DAYS = 30
VIP_MIN_ORDERS = 3


def _load_customer_profiles() -> Dict[str, Dict]:
    """v10: фасад над SQLite. Сигнатура и формат не изменились."""
    try:
        return _db_load_all_customers()
    except Exception as e:
        logger.error(f"_load_customer_profiles (sqlite) failed: {e}")
        return {}


def _save_customer_profiles(profiles: Dict[str, Dict]) -> None:
    """v10: фасад над SQLite (per-row upsert в транзакции)."""
    try:
        _db_upsert_customers(profiles)
    except Exception as e:
        logger.error(f"_save_customer_profiles (sqlite) failed: {e}")


def update_customer_profile(buyer_id, buyer_username: Optional[str], summa_rub: float, currency_summa: str = "RUB") -> Dict:
    """
    Обновляет профиль покупателя по факту нового заказа. Возвращает обновлённую запись.
    summa передаём как есть в RUB (FunPay-цена).
    """
    if not buyer_id:
        return {}
    bid = str(buyer_id)
    with _FILES_LOCK:
        profs = _load_customer_profiles()
        prof = profs.get(bid, {
            "buyer_id": bid,
            "buyer_username": _safe_username(buyer_username),
            "first_order_at": time.time(),
            "orders_count": 0,
            "total_spent_rub": 0.0,
            "last_order_at": 0.0,
            "history_30d": [],  # ts орденов за последние 30 дней (в виде unix-ts)
        })
        prof["buyer_username"] = _safe_username(buyer_username)
        prof["orders_count"] = int(prof.get("orders_count", 0)) + 1
        rub = float(summa_rub or 0)
        if (currency_summa or "RUB").upper() != "RUB":
            rub = convert_to_rub(rub, currency_summa)
        prof["total_spent_rub"] = round(float(prof.get("total_spent_rub", 0)) + rub, 2)
        now = time.time()
        prof["last_order_at"] = now
        # окно 30 дней
        cutoff = now - VIP_WINDOW_DAYS * 86400
        history = [t for t in prof.get("history_30d", []) if t >= cutoff]
        history.append(now)
        prof["history_30d"] = history
        profs[bid] = prof
        _save_customer_profiles(profs)
    return prof


def get_customer_tier(buyer_id) -> Dict:
    """
    Возвращает {"tier": "vip"|"regular", "orders_30d": int, "total_spent_rub": float,
                "skip_confirmation": bool, "bonus_pct": int}
    с учётом cfg["vip_skip_confirmation"], cfg["vip_bonus_pct"].
    """
    cfg = load_config()
    if not buyer_id:
        return {"tier": "regular", "orders_30d": 0, "total_spent_rub": 0.0,
                "skip_confirmation": False, "bonus_pct": 0}
    profs = _load_customer_profiles()
    prof = profs.get(str(buyer_id))
    if not prof:
        return {"tier": "regular", "orders_30d": 0, "total_spent_rub": 0.0,
                "skip_confirmation": False, "bonus_pct": 0}
    cutoff = time.time() - VIP_WINDOW_DAYS * 86400
    orders_30d = sum(1 for t in prof.get("history_30d", []) if t >= cutoff)
    is_vip = orders_30d >= cfg.get("vip_min_orders_30d", VIP_MIN_ORDERS)
    bonus_pct = int(cfg.get("vip_bonus_pct", 5)) if is_vip else 0
    skip_conf = bool(cfg.get("vip_skip_confirmation", True)) if is_vip else False
    return {
        "tier": "vip" if is_vip else "regular",
        "orders_30d": orders_30d,
        "total_spent_rub": float(prof.get("total_spent_rub", 0)),
        "skip_confirmation": skip_conf,
        "bonus_pct": bonus_pct,
    }


def autosmm_customers_command(message):
    if not _is_admin_message(message):
        return
    profs = _load_customer_profiles()
    cfg = load_config()
    cutoff = time.time() - VIP_WINDOW_DAYS * 86400
    rows = []
    for bid, prof in profs.items():
        orders_30d = sum(1 for t in prof.get("history_30d", []) if t >= cutoff)
        rows.append({
            "buyer_id": bid,
            "username": prof.get("buyer_username", "—"),
            "total_rub": float(prof.get("total_spent_rub", 0)),
            "orders_total": int(prof.get("orders_count", 0)),
            "orders_30d": orders_30d,
            "tier": "vip" if orders_30d >= cfg.get("vip_min_orders_30d", VIP_MIN_ORDERS) else "regular",
        })
    rows.sort(key=lambda r: r["total_rub"], reverse=True)
    rows = rows[:10]
    if not rows:
        bot.send_message(message.chat.id, "Покупателей пока нет.")
        return
    lines = [f"<b>👥 Топ покупателей (по выручке)</b>", ""]
    for i, r in enumerate(rows, 1):
        tier_mark = "⭐" if r["tier"] == "vip" else "·"
        lines.append(
            f"{i}. {tier_mark} <code>{html.escape(r['username'])}</code> "
            f"({r['orders_total']} зак., {r['orders_30d']} за 30д) — <b>{r['total_rub']:.0f}₽</b>"
        )
    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def on_plugin_unload(*_args, **_kwargs):
    """
    P.17: graceful shutdown. FPC дёргает BIND_TO_DELETE при выгрузке/перезагрузке
    плагина. Ставим shutdown-флаг, ждём завершения фоновых потоков (с разумным
    таймаутом), сохраняем state на диск ещё раз.
    """
    global RUNNING, IS_STARTED
    logger.info("on_plugin_unload: shutdown sequence started")
    _SHUTDOWN_EVENT.set()
    RUNNING = False
    IS_STARTED = False

    # Останавливаем webhook-сервер (если поднят).
    try:
        if _WEBHOOK_SERVER is not None:
            _WEBHOOK_SERVER.shutdown()
    except Exception as e:
        logger.error(f"on_plugin_unload: webhook shutdown failed: {e}")

    # Ждём ключевые потоки.
    join_targets = [
        ("dialog_timeout_watcher", _DIALOG_WATCHER_THREAD),
        ("order_check", ORDER_CHECK_THREAD),
        ("auto_lots_send", AUTO_LOTS_SEND_THREAD),
        ("refill_watcher", _REFILL_WATCHER_THREAD),
        ("balance_watcher", _BALANCE_WATCHER_THREAD),
        ("webhook", _WEBHOOK_THREAD),
        ("backup_watcher", _BACKUP_WATCHER_THREAD),
    ]
    deadline = time.time() + 15.0  # суммарный лимит
    for name, t in join_targets:
        if t is None or not t.is_alive():
            continue
        remaining = max(0.0, deadline - time.time())
        try:
            t.join(timeout=remaining)
            if t.is_alive():
                logger.warning(f"on_plugin_unload: поток {name} не завершился за timeout")
            else:
                logger.info(f"on_plugin_unload: поток {name} завершён")
        except Exception as e:
            logger.error(f"on_plugin_unload: ошибка join для {name}: {e}")

    # Сохраняем state и orders ещё раз на всякий случай.
    try:
        save_state()
    except Exception as e:
        logger.error(f"on_plugin_unload: save_state failed: {e}")
    logger.info("on_plugin_unload: shutdown sequence complete")


BIND_TO_PRE_INIT = [init_commands]
BIND_TO_NEW_MESSAGE = [auto_smm_handler]
BIND_TO_NEW_ORDER = [auto_smm_handler]
BIND_TO_DELETE = [on_plugin_unload]

def start_order_checking_if_needed(c: Cardinal):
    if RUNNING:  
        start_order_checking(c)

def send_order_started_notification(c: Cardinal, order_id_funpay: str, twiboost_id: int, link: str, api_url: str, api_key: str, lot_price: float, real_amount: int):
    """
    Отправляет уведомление о начале заказа с информацией о чистой прибыли
    """
    cfg = load_config()
    notification_chat_id = cfg.get("notification_chat_id")
    if not notification_chat_id:
        logger.warning("Notification chat_id не задан в конфигурации.")
        return
        
    try:
        status_url = f"{api_url}?action=status&order={twiboost_id}&key={api_key}"
        status_resp = HTTP_SESSION.get(status_url, timeout=HTTP_TIMEOUT)
        status_resp.raise_for_status()
        status_data = status_resp.json()
        
        charge = float(status_data.get("charge", "0"))
        currency = status_data.get("currency", "USD")
        
        net_profit = round(lot_price - charge, 2)

        
        order_data = c.account.get_order(order_id_funpay)
        buyer_username = _safe_username(order_data.buyer_username)  # P.20

        kb_ = InlineKeyboardMarkup()
        order_url = f"https://funpay.com/orders/{order_id_funpay}/"
        kb_.add(InlineKeyboardButton("Перейти к заказу", url=order_url))

        # v8: чистая прибыль теперь в RUB через convert_to_rub
        spent_rub = convert_to_rub(charge, currency)
        net_profit_rub = round(lot_price - spent_rub, 2)

        notification_text = (
            f"🚀 [AUTOSMM] Заказ #{order_id_funpay} начат!\n\n"
            f"👤 Покупатель: {buyer_username}\n"
            f"🔢 ID заказа: {order_id_funpay}\n"
            f"💰 Сумма на FP: {lot_price} ₽\n"
            f"💸 Сумма на сайте: {charge} {currency} (≈{spent_rub:.2f} ₽)\n"
            f"✅ Чистая прибыль: {net_profit_rub} ₽\n"
            f"🔢 Кол-во: {real_amount}\n"
            f"🔗 Ссылка: {link}"
        )
        
        c.telegram.bot.send_message(
            notification_chat_id,
            notification_text,
            reply_markup=kb_
        )
        
    except Exception as ex:
        logger.error(f"Ошибка при отправке уведомления о начале заказа: {ex}")

def _attempt_smm_create(api_url: str, api_key: str, service_id: int,
                        link_: str, real_amount: int, *, log_extra: Dict) -> Tuple[Optional[Dict], Optional[Dict]]:
    """
    v11.P1.1: одна попытка SMM-создания. Возвращает (success_json, error_info).
    Если success_json["order"] есть — успех. Иначе error_info содержит
    {"error_type": ..., "msg": ..., "status_code": ..., "body": ...}.
    """
    encoded_link = quote(link_, safe="")
    url_req = f"{api_url}?action=add&service={service_id}&link={encoded_link}&quantity={real_amount}&key={api_key}"
    try:
        resp_ = http_request_with_retries("GET", url_req, log_extra=log_extra,
                                          verify=smm_verify())  # v11.P3.8
    except requests.exceptions.RequestException as ex:
        et = classify_error(exc=ex)
        if et == ERROR_TYPE_SSL_EXPIRED:
            maybe_enable_ssl_fallback()
        return None, {"error_type": et, "msg": str(ex), "status_code": None, "body": None}

    body = ""
    try:
        body = resp_.text
    except Exception:
        pass

    if resp_.status_code != 200:
        et = classify_error(response=resp_)
        return None, {"error_type": et, "msg": f"HTTP {resp_.status_code}",
                      "status_code": resp_.status_code, "body": body}

    try:
        j_ = resp_.json()
    except Exception as ex:
        et = classify_error(exc=ex, text=body)
        return None, {"error_type": et, "msg": str(ex), "status_code": 200, "body": body}

    if "order" in j_:
        return j_, None

    # 200 OK, но JSON содержит ошибку (типичный случай: {"error":"neworder.error.not_enough_funds"})
    err_str = json.dumps(j_, ensure_ascii=False)
    et = classify_error(text=err_str)
    return None, {"error_type": et, "msg": err_str, "status_code": 200, "body": body, "json": j_}


def _build_attempt_chain(cfg: Dict, primary_service_number: int, primary_service_id: int,
                         link_: str, lot_key: Optional[str] = None) -> List[Tuple[int, int, str, str]]:
    """
    v11.P3.9: возвращает список (service_number, service_id, link_variant, label)
    для попыток создания. Сначала primary + варианты ссылки, потом fallback chain.
    """
    chain: List[Tuple[int, int, str, str]] = []
    # Кандидаты ссылок (нормализация только для primary; для fallback оставляем лучший вариант)
    link_variants = normalize_smm_link(link_)
    if not link_variants:
        link_variants = [link_]

    # Primary service со всеми вариантами ссылки
    for i, lv in enumerate(link_variants):
        label = f"primary svc#{primary_service_number}/{primary_service_id} {'(нормализовано)' if i == 0 and lv != link_ else ''}"
        chain.append((primary_service_number, primary_service_id, lv, label.strip()))

    # Fallback chain: либо из lot_mapping[lot_key].fallback_services, либо из cfg.fallback_services_default
    fallbacks: List[Dict] = []
    if lot_key:
        lot_info = cfg.get("lot_mapping", {}).get(lot_key, {})
        fallbacks = lot_info.get("fallback_services") or []
    if not fallbacks:
        fallbacks = cfg.get("fallback_services_default") or []

    for fb in fallbacks:
        try:
            sn = int(fb.get("service_number"))
            sid = int(fb.get("service_id"))
        except Exception:
            continue
        if (sn, sid) == (primary_service_number, primary_service_id):
            continue
        # Для fallback берём только первую (наиболее каноничную) ссылку.
        chain.append((sn, sid, link_variants[0], f"fallback svc#{sn}/{sid}"))
    return chain


def process_link_without_confirmation(c: Cardinal, data: Dict):
    """
    v11.P1: обрабатывает ссылку с smart-400 и fallback chain.

    Раньше: один запрос → при 400 моментальный refund.
    Теперь:
      1) Идём по chain попыток (нормализация ссылки + fallback services).
      2) При not_enough_funds → ставим в pending_refunds queue, НЕ рефанд.
      3) При bad_link / bad_quantity на ВСЕХ кандидатах → возвращаем покупателя
         в await_link с просьбой прислать другую ссылку, НЕ рефанд.
      4) При network/5xx после исчерпания chain → degraded mode + refund.
      5) При auth (401/403) → алерт админу + refund.
    """
    link_ = data["link"]
    service_id = data["service_id"]
    real_amount = data["real_amount"]
    order_id_funpay = data["order_id_funpay"]
    buyer_chat_id = data["chat_id"]
    service_number = data["service_number"]
    lot_price = data["price"]
    buyer_id = data.get("buyer_id")
    lot_key = data.get("lot_key")

    cfg = load_config()
    service_cfg = cfg["services"].get(str(service_number))
    if not service_cfg:
        logger.error(f"Нет настроек для service_number={service_number}")
        c.send_message(buyer_chat_id, f"❌ Ошибка: нет настроек для service_number={service_number}.")
        refund_order(c, order_id_funpay, buyer_chat_id,
                     reason="Ошибка конфигурации.",
                     detailed_reason=f"Нет настроек для service_number={service_number}.")
        return

    chain = _build_attempt_chain(cfg, service_number, service_id, link_, lot_key=lot_key)
    last_error: Optional[Dict] = None
    success_attempt: Optional[Dict] = None

    for attempt_idx, (sn, sid, lv, label) in enumerate(chain, 1):
        srv_cfg = cfg["services"].get(str(sn))
        if not srv_cfg:
            continue
        log_extra = {
            "order_id": order_id_funpay,
            "service_id": sid,
            "service_number": sn,
            "stage": "smm_order_create",
            "attempt_label": label,
            "attempt_idx": attempt_idx,
        }
        logger.info(f"v11: смм-create попытка {attempt_idx}/{len(chain)}: {label}, link={lv!r}", extra=log_extra)
        j_, err = _attempt_smm_create(srv_cfg["api_url"], srv_cfg["api_key"], sid, lv, real_amount,
                                      log_extra=log_extra)
        if j_ is not None:
            success_attempt = {
                "json": j_, "service_number": sn, "service_id": sid, "link": lv,
                "api_url": srv_cfg["api_url"], "api_key": srv_cfg["api_key"],
                "label": label,
            }
            break
        # err is not None
        last_error = err
        et = err["error_type"]
        record_error(et, service=sn, order_id=order_id_funpay, msg=err.get("msg", ""))
        logger.error(
            f"smm_create attempt {attempt_idx} failed: error_type={et}, msg={err.get('msg','')[:200]}",
            extra={**log_extra, "error_type": et, "status_code": err.get("status_code"),
                   "body_preview": (err.get("body") or "")[:200]},
        )
        # Permanent ошибки на этой попытке — решаем дальше, не ретраим бесконечно chain
        if et == ERROR_TYPE_FUNDS:
            # Останавливаем chain — ставим в очередь, не пробуем fallback (там тоже могут быть funds-проблемы).
            break
        if et == ERROR_TYPE_AUTH:
            break  # ключ протух — fallback скорее всего тоже
        # bad_link / bad_quantity / 5xx / network — пробуем следующий элемент chain

    # === Успех ===
    if success_attempt is not None:
        j_ = success_attempt["json"]
        sn = success_attempt["service_number"]
        sid = success_attempt["service_id"]
        lv = success_attempt["link"]
        api_url = success_attempt["api_url"]
        api_key = success_attempt["api_key"]
        twiboost_id = j_["order"]
        chistota = float(lot_price)

        save_order_data(buyer_chat_id, order_id_funpay, twiboost_id, "pending",
                        chistota, lv, real_amount, sn)
        send_order_started_notification(c, order_id_funpay, twiboost_id, lv,
                                        api_url, api_key, lot_price, real_amount)
        check_order_status(c, twiboost_id, buyer_chat_id, lv, order_id_funpay)

        msg_confirmation = cfg["messages"]["after_confirmation"].format(
            twiboost_id=twiboost_id, link=lv,
        )
        c.send_message(buyer_chat_id, msg_confirmation)
        try:
            update_customer_profile(buyer_id, None, summa_rub=float(lot_price or 0), currency_summa="RUB")
        except Exception as e:
            logger.error(f"update_customer_profile failed: {e}")
        with _FILES_LOCK:
            waiting_for_link.pop(str(order_id_funpay), None)
            save_state()
        # Если этот заказ был в pending — снимаем с очереди.
        try:
            pending_mark_resolved(order_id_funpay)
        except Exception:
            pass
        return

    # === Все попытки провалились ===
    if last_error is None:
        last_error = {"error_type": ERROR_TYPE_UNKNOWN, "msg": "no chain attempts"}
    et = last_error["error_type"]

    # 1) not_enough_funds → очередь повторов, НЕ рефанд.
    if et == ERROR_TYPE_FUNDS:
        try:
            pending_enqueue(
                str(order_id_funpay), buyer_id=buyer_id or 0, buyer_chat_id=buyer_chat_id,
                service_number=service_number, service_id=service_id, link=link_,
                quantity=real_amount, summa=float(lot_price or 0),
                last_error=last_error.get("msg", ""),
            )
            c.send_message(
                buyer_chat_id,
                "⏳ Временные проблемы у провайдера (нехватка баланса). Повторим попытку через 5 минут — "
                "если не получится, в течение часа автоматически вернём средства.",
            )
            _admin_notify(
                f"⚠ <b>not_enough_funds</b> у сервиса #{service_number}.\n"
                f"Заказ <code>{order_id_funpay}</code> поставлен в pending_refunds. "
                f"Текущая очередь: {pending_count()} заказов.\n"
                f"Пополни баланс провайдера — заказы автоматически досоздадутся."
            )
        except Exception as e:
            logger.exception(f"pending_enqueue failed: {e}")
            refund_order(c, order_id_funpay, buyer_chat_id,
                         reason="Сбой постановки в очередь.", detailed_reason=str(e))
        return

    # 2) bad_link / bad_quantity на всех вариантах → возвращаем в await_link.
    if et in (ERROR_TYPE_BAD_LINK, ERROR_TYPE_BAD_QUANTITY):
        with _FILES_LOCK:
            wfl_data = waiting_for_link.get(str(order_id_funpay))
            if wfl_data is not None:
                wfl_data["step"] = "await_link"
                save_state()
        if et == ERROR_TYPE_BAD_LINK:
            c.send_message(
                buyer_chat_id,
                "❌ Провайдер не принял эту ссылку. "
                "Проверьте, что ссылка корректная и сервис накручиваемого типа поддерживает её формат, "
                "затем пришлите её ещё раз. Если ситуация повторится — свяжитесь с продавцом.",
            )
        else:
            c.send_message(
                buyer_chat_id,
                "❌ Провайдер сообщил о неподходящем количестве. "
                "Свяжитесь с продавцом — настройка лота требует корректировки.",
            )
        _admin_notify(
            f"⚠ <b>{et}</b> на заказе <code>{order_id_funpay}</code>.\n"
            f"Buyer chat: <code>{buyer_chat_id}</code>, link: <code>{html.escape(link_[:200])}</code>\n"
            f"Все {len(chain)} попыток chain провалились. Покупатель отправлен на ввод новой ссылки."
        )
        return

    # 3) auth → алерт + refund (другого не остаётся, нашим API-ключом не воспользоваться).
    if et == ERROR_TYPE_AUTH:
        _admin_notify(
            f"🔥 <b>AUTH ERROR</b> на сервисе #{service_number}!\n"
            f"API-ключ протух или забанен. Заказ <code>{order_id_funpay}</code> рефанднут.\n"
            f"Сообщение: {html.escape(str(last_error.get('msg',''))[:200])}"
        )
        refund_order(c, order_id_funpay, buyer_chat_id,
                     reason="Авторизация у провайдера.",
                     detailed_reason=f"Auth error: {last_error.get('msg','')}")
        return

    # 4) network/5xx/json/ssl/unknown — обычная схема: refund (degraded mode уже мог сработать).
    logger.error(
        f"smm_create chain exhausted for #{order_id_funpay}: error_type={et}",
        extra={"event": "smm_create_exhausted", "order_id": order_id_funpay, "error_type": et,
               "attempts": len(chain)},
    )
    refund_order(c, order_id_funpay, buyer_chat_id,
                 reason="Технический сбой на стороне провайдера.",
                 detailed_reason=f"Все {len(chain)} попыток chain провалились. Последняя ошибка: {last_error.get('msg','')[:200]}")


# =====================================================================
# === v11.P1.2 — pending_refunds worker ================================
# =====================================================================

_PENDING_WORKER_THREAD: Optional[threading.Thread] = None


def _pending_refunds_loop(c: "Cardinal"):
    """v11.P1.2: воркер pending_refunds. Раз в минуту проверяет таблицу и
    повторяет попытки создания SMM-заказа для записей с next_retry_at <= now."""
    logger.info("pending_refunds_worker started")
    if _SHUTDOWN_EVENT.wait(30):
        return
    while not _SHUTDOWN_EVENT.is_set():
        try:
            due = pending_due()
        except Exception as e:
            logger.error(f"pending_refunds_worker: pending_due failed: {e}")
            due = []

        for row in due:
            if _SHUTDOWN_EVENT.is_set():
                break
            order_id = row["order_id"]
            try:
                cfg = load_config()
                srv_cfg = cfg["services"].get(str(row["service_number"]))
                if not srv_cfg:
                    pending_mark_attempt_failed(order_id, "service config missing")
                    continue
                log_extra = {"order_id": order_id, "stage": "pending_retry",
                             "attempts": row["attempts"]}
                logger.info(
                    f"pending_refunds: retry #{row['attempts']+1} for order {order_id}",
                    extra=log_extra,
                )
                j_, err = _attempt_smm_create(
                    srv_cfg["api_url"], srv_cfg["api_key"], int(row["service_id"]),
                    row["link"], int(row["quantity"]), log_extra=log_extra,
                )
                if j_ is not None:
                    twiboost_id = j_["order"]
                    save_order_data(
                        int(row["buyer_chat_id"]) if row["buyer_chat_id"] else 0,
                        order_id, twiboost_id, "pending",
                        float(row["summa"] or 0), row["link"],
                        int(row["quantity"]), int(row["service_number"]),
                    )
                    send_order_started_notification(
                        c, order_id, twiboost_id, row["link"],
                        srv_cfg["api_url"], srv_cfg["api_key"],
                        float(row["summa"] or 0), int(row["quantity"]),
                    )
                    check_order_status(c, twiboost_id, int(row["buyer_chat_id"] or 0),
                                       row["link"], order_id)
                    pending_mark_resolved(order_id)
                    try:
                        c.send_message(
                            int(row["buyer_chat_id"] or 0),
                            f"✅ Заказ создан после повторной попытки. ID: {twiboost_id}",
                        )
                    except Exception:
                        pass
                    _admin_notify(
                        f"✅ pending_refunds: заказ <code>{order_id}</code> успешно создан "
                        f"с попытки #{row['attempts']+1}."
                    )
                    continue

                # Снова провал
                err_msg = err.get("msg", "")
                should_refund = pending_mark_attempt_failed(order_id, err_msg)
                if should_refund:
                    logger.warning(
                        f"pending_refunds: order {order_id} исчерпал попытки → refund",
                        extra={"event": "pending_exhausted", "order_id": order_id},
                    )
                    refund_order(
                        c, order_id, int(row["buyer_chat_id"] or 0),
                        reason="Не удалось оформить заказ после повторных попыток.",
                        detailed_reason=f"3 попытки за час провалились. Последняя ошибка: {err_msg[:200]}",
                    )
            except Exception as e:
                logger.exception(f"pending_refunds: order {order_id} loop crashed: {e}")
                try:
                    pending_mark_attempt_failed(order_id, f"worker crash: {e}")
                except Exception:
                    pass

        if _SHUTDOWN_EVENT.wait(60):
            break
    logger.info("pending_refunds_worker finished (shutdown).")


def _start_pending_refunds_worker(c: "Cardinal") -> None:
    global _PENDING_WORKER_THREAD
    if _PENDING_WORKER_THREAD and _PENDING_WORKER_THREAD.is_alive():
        return
    _PENDING_WORKER_THREAD = threading.Thread(
        target=_pending_refunds_loop, args=(c,),
        daemon=True, name="auto_smm_pending_refunds",
    )
    _PENDING_WORKER_THREAD.start()


# =====================================================================
# === v11.P2.7 — canary heartbeat ======================================
# =====================================================================

_CANARY_THREAD: Optional[threading.Thread] = None
_CANARY_FAILS: Dict[int, int] = {}  # service_number → consecutive fails


def _canary_loop(c: "Cardinal"):
    """v11.P2.7: раз в 10 минут проверяет доступность каждого SMM-сервиса.
    3 подряд провала → degraded mode на этот сервис + алерт."""
    logger.info("canary heartbeat started")
    if _SHUTDOWN_EVENT.wait(120):
        return
    while not _SHUTDOWN_EVENT.is_set():
        cfg = load_config()
        if not cfg.get("canary_enabled", True):
            if _SHUTDOWN_EVENT.wait(600):
                break
            continue
        services = cfg.get("services", {}) or {}
        for sn_str, scfg in list(services.items()):
            try:
                sn = int(sn_str)
            except Exception:
                continue
            url = f"{scfg.get('api_url')}?action=balance&key={scfg.get('api_key')}"
            try:
                resp = http_request_with_retries(
                    "GET", url, max_retries=2,
                    log_extra={"stage": "canary", "service_number": sn},
                    verify=smm_verify(),
                )
                if resp.status_code == 200 and resp.text:
                    _CANARY_FAILS[sn] = 0
                    continue
                _CANARY_FAILS[sn] = _CANARY_FAILS.get(sn, 0) + 1
                record_error(classify_error(response=resp), service=sn, msg=f"canary status={resp.status_code}")
            except Exception as ex:
                _CANARY_FAILS[sn] = _CANARY_FAILS.get(sn, 0) + 1
                record_error(classify_error(exc=ex), service=sn, msg=f"canary {ex!r}")
            if _CANARY_FAILS.get(sn, 0) >= 3:
                _DEGRADED.enter(DEGRADED_BACKOFF_SEC, f"canary svc#{sn}: 3 fails")
                _admin_notify(
                    f"⚠ <b>canary</b>: сервис #{sn} недоступен 3 раза подряд. "
                    f"Включён degraded mode на {DEGRADED_BACKOFF_SEC//60} мин."
                )
                _CANARY_FAILS[sn] = 0  # сбрасываем после алерта
        if _SHUTDOWN_EVENT.wait(600):  # 10 мин
            break
    logger.info("canary heartbeat finished (shutdown).")


def _start_canary(c: "Cardinal") -> None:
    global _CANARY_THREAD
    if _CANARY_THREAD and _CANARY_THREAD.is_alive():
        return
    _CANARY_THREAD = threading.Thread(
        target=_canary_loop, args=(c,),
        daemon=True, name="auto_smm_canary",
    )
    _CANARY_THREAD.start()


# =====================================================================
# === v11.P2.5 — /autosmm_errors TG command ============================
# =====================================================================

def autosmm_pending_command(message):
    """v11.P1.2: показывает текущую очередь pending_refunds."""
    if not _is_admin_message(message):
        return
    _db_init_pending_refunds()
    with _DB_LOCK:
        conn = _db_connect()
        try:
            rows = conn.execute(
                "SELECT * FROM pending_refunds WHERE state='pending' ORDER BY first_failed_at"
            ).fetchall()
            rows = [dict(r) for r in rows]
        finally:
            conn.close()
    if not rows:
        bot.send_message(message.chat.id, "✅ Очередь pending_refunds пуста.")
        return
    lines = [f"<b>⏳ Pending refunds ({len(rows)})</b>", ""]
    now = time.time()
    for r in rows[:20]:
        next_in = max(0, int((r["next_retry_at"] or now) - now))
        lines.append(
            f"• <code>{r['order_id']}</code> svc#{r['service_number']} "
            f"att {r['attempts']}/{PENDING_MAX_ATTEMPTS} retry in {next_in//60}m\n"
            f"   err: {html.escape((r['last_error'] or '')[:90])}"
        )
    if len(rows) > 20:
        lines.append(f"... ещё {len(rows)-20}")
    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def autosmm_errors_command(message):
    """Показывает топ ошибок из буфера за выбранное окно (default 24ч).
    Использование: /autosmm_errors [hours]   (например /autosmm_errors 168 = 7д)
    """
    if not _is_admin_message(message):
        return
    try:
        parts = (message.text or "").split()
        hours = float(parts[1]) if len(parts) > 1 else 24.0
    except Exception:
        hours = 24.0

    cutoff = time.time() - hours * 3600
    with _ERROR_LOG_LOCK:
        relevant = [e for e in _ERROR_LOG_BUF if e["ts"] >= cutoff]

    if not relevant:
        bot.send_message(message.chat.id, f"Ошибок за последние {hours:g}ч не зафиксировано.")
        return

    # Группировка по (error_type, service)
    from collections import Counter
    grouped = Counter((e["error_type"], e["service"]) for e in relevant)
    lines = [f"<b>📊 Ошибки за {hours:g}ч</b> (всего {len(relevant)})", ""]
    for (et, svc), cnt in grouped.most_common(15):
        # последний пример
        sample = next((e for e in reversed(relevant) if e["error_type"] == et and e["service"] == svc), None)
        sample_msg = (sample.get("msg", "") or "")[:80] if sample else ""
        sample_msg = html.escape(sample_msg)
        sample_oid = (sample.get("order_id") or "—") if sample else "—"
        svc_str = f"svc#{svc}" if svc is not None else "—"
        lines.append(f"• <code>{et}</code> {svc_str}: <b>{cnt}</b> | last: <code>{sample_oid}</code> — {sample_msg}")

    # Доп. метаданные: degraded / pending / ssl_fallback
    lines.append("")
    if _DEGRADED.is_active():
        lines.append(f"⚠ degraded mode: ещё {_DEGRADED.remaining_sec()}s, причина: {_DEGRADED.reason}")
    if _SSL_FALLBACK_ACTIVE:
        lines.append("⚠ SSL fallback active (verify=False для SMM-API)")
    try:
        pc = pending_count()
    except Exception:
        pc = 0
    lines.append(f"pending_refunds queue: {pc}")

    bot.send_message(message.chat.id, "\n".join(lines), parse_mode="HTML")


def start_auto_lots_sender(c: Cardinal):
    """
    P.15: бэкап auto_lots.json теперь шлётся:
      - сразу при старте (если ещё не было, чтобы у админа всегда был свежий снапшот);
      - при изменении файла (sha256 содержимого отличается от прошлого);
      - принудительно раз в 24 часа (как daily snapshot), если ничего не менялось,
        чтобы поддерживать "регулярный" бэкап.
    Раньше плагин засирал админский чат одинаковым файлом каждые 30 минут — теперь
    в 99% случаев это будет 1 пуш в день максимум.
    """
    global RUNNING
    logger.info("Запуск потока бэкапа auto_lots.json (push-on-change + 24h fallback)")

    last_hash: Optional[str] = None
    last_sent_at: float = 0.0
    DAILY_FALLBACK_SEC = 24 * 60 * 60
    POLL_INTERVAL_SEC = 60  # как часто проверяем хеш файла

    while RUNNING and not _SHUTDOWN_EVENT.is_set():
        try:
            cfg = load_config()
            chat_id = cfg.get("notification_chat_id")
            send_auto_lots = cfg.get("send_auto_lots", True)

            now = time.time()
            should_send = False
            reason = ""

            if chat_id and send_auto_lots and os.path.exists(CONFIG_PATH):
                try:
                    with open(CONFIG_PATH, "rb") as f:
                        body = f.read()
                    cur_hash = hashlib.sha256(body).hexdigest()
                except Exception as e:
                    logger.error(f"auto_lots backup: чтение {CONFIG_PATH} не удалось: {e}")
                    cur_hash = None

                if cur_hash is not None:
                    if last_hash is None:
                        should_send, reason = True, "initial"
                    elif cur_hash != last_hash:
                        should_send, reason = True, "changed"
                    elif now - last_sent_at >= DAILY_FALLBACK_SEC:
                        should_send, reason = True, "daily_fallback"

                if should_send and c.telegram and c.telegram.bot:
                    try:
                        with open(CONFIG_PATH, "rb") as file:
                            c.telegram.bot.send_document(
                                chat_id,
                                file,
                                caption=(
                                    f"📄 Бэкап auto_lots.json ({reason})\n"
                                    f"sha256: {cur_hash[:12]}..."
                                ),
                            )
                        logger.info(
                            "auto_lots backup pushed",
                            extra={"reason": reason, "sha256_prefix": cur_hash[:12]},
                        )
                        last_hash = cur_hash
                        last_sent_at = now
                    except Exception as e:
                        logger.error(f"Ошибка при отправке auto_lots.json: {e}")
        except Exception as e:
            logger.error(f"Ошибка в потоке бэкапа auto_lots.json: {e}")

        # P.17: ждём с уважением к shutdown. wait() вернёт True если флаг поставлен.
        if _SHUTDOWN_EVENT.wait(POLL_INTERVAL_SEC):
            break
    logger.info("auto_lots backup loop finished.")

def auto_start_plugin(c: Cardinal):
    """
    Плагин всегда работает — автоматически запускаем фоновые потоки.
    """
    logger.info("Автоматический запуск плагина SMM (always-on)")
    global RUNNING, IS_STARTED, ORDER_CHECK_THREAD, AUTO_LOTS_SEND_THREAD
    RUNNING = True
    IS_STARTED = True

    if not ORDER_CHECK_THREAD or not ORDER_CHECK_THREAD.is_alive():
        ORDER_CHECK_THREAD = threading.Thread(target=start_order_checking, args=(c,))
        ORDER_CHECK_THREAD.daemon = True
        ORDER_CHECK_THREAD.start()

    if not AUTO_LOTS_SEND_THREAD or not AUTO_LOTS_SEND_THREAD.is_alive():
        AUTO_LOTS_SEND_THREAD = threading.Thread(target=start_auto_lots_sender, args=(c,))
        AUTO_LOTS_SEND_THREAD.daemon = True
        AUTO_LOTS_SEND_THREAD.start()

    logger.info("Плагин SMM запущен.")
    return True
    
    return False