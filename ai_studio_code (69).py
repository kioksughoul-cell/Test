from __future__ import annotations
from typing import TYPE_CHECKING, Dict, Optional, Any, List

if TYPE_CHECKING:
    from cardinal import Cardinal

import os
import json
import sqlite3
import logging
import threading
import asyncio
import time
import re
import sys
import subprocess
import importlib
from urllib.parse import urlparse

# ================== АВТОУСТАНОВЩИК ==================
def _auto_install_dependencies():
    required = {
        "telethon": "telethon", 
        "socks": "pysocks",
        "google.genai": "google-genai",
        "httpx_socks": "httpx[socks]"
    }
    missing = []
    for imp_name, pkg_name in required.items():
        try:
            importlib.import_module(imp_name)
        except ImportError:
            missing.append(pkg_name)

    if missing:
        print(f"[TeamXFarm] Установка библиотек: {missing}...")
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "-U", *missing])
            importlib.invalidate_caches()
            time.sleep(1)
        except Exception as e:
            print(f"[TeamXFarm] Ошибка установки зависимостей: {e}")

_auto_install_dependencies()

# --- Импорты после установки ---
try:
    from telethon.sync import TelegramClient
    from telethon.sessions import StringSession, SQLiteSession
    from telethon import errors
    from telethon.tl.functions.messages import ImportChatInviteRequest
    import socks
    TELETHON_INSTALLED = True
except ImportError:
    TELETHON_INSTALLED = False

try:
    from google import genai
    GEMINI_INSTALLED = True
except ImportError:
    GEMINI_INSTALLED = False

try:
    from telebot import types as bot_types
    from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton
except ImportError:
    pass

# ================== МЕТАДАННЫЕ ==================
NAME = "TeamX Farm Automator"
VERSION = "1.5.0" # Shared DB with Zarub Farm + Runtime Proxy Fallback
DESCRIPTION = "Автоматизация воронки TeamX. Интегрировано с БД Zarub Farm."
CREDITS = "@SeniorArchitect"
UUID = "dfe0db52-b1e7-4715-9bbe-783286fb7d7f"
SETTINGS_PAGE = False

# ================== КОНФИГУРАЦИЯ ==================
API_ID = 25211038
API_HASH = "de5a98ff866f5ea88540c92d84bf1b16"

STORAGE_DIR = "storage"
ZARUB_CACHE_DIR = os.path.join(STORAGE_DIR, "cache")
os.makedirs(ZARUB_CACHE_DIR, exist_ok=True)

# ИСПОЛЬЗУЕМ БД ИЗ ZARUB FARM
DB_PATH = os.path.join(ZARUB_CACHE_DIR, "zarub_farm.db") 

CACHE_DIR = os.path.join(STORAGE_DIR, "cache", "teamx_farm")
os.makedirs(CACHE_DIR, exist_ok=True)
CONFIG_PATH = os.path.join(CACHE_DIR, "config.json")

# ================== ЛОГИРОВАНИЕ ==================
logger = logging.getLogger(f"FPC.{NAME}")
logger.setLevel(logging.INFO)

# ================== ГЛОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ==================
cardinal_instance: Optional[Cardinal] = None
bot = None
temp_data = {} 
config = {}

gemini_sync_lock = threading.Lock()
gemini_call_history = []

# ================== КОНФИГ И БД ==================
def load_config():
    global config
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, 'r', encoding='utf-8') as f:
                config = json.load(f)
        except:
            config = {}
    if "gemini_api_key" not in config: config["gemini_api_key"] = ""
    if "group_proxies" not in config: config["group_proxies"] = {}
    save_config()

def save_config():
    with open(CONFIG_PATH, 'w', encoding='utf-8') as f:
        json.dump(config, f, indent=4, ensure_ascii=False)

def get_db():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with get_db() as conn:
        # 1. Создаем таблицы, если это самый первый запуск (до Zarub)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS groups (
                id INTEGER PRIMARY KEY AUTOINCREMENT, 
                name TEXT UNIQUE NOT NULL,
                created_at INTEGER
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS accounts (
                phone TEXT PRIMARY KEY, 
                session_string TEXT NOT NULL, 
                group_id INTEGER, 
                username TEXT,
                proxy TEXT, 
                status TEXT DEFAULT 'active', 
                FOREIGN KEY(group_id) REFERENCES groups(id) ON DELETE CASCADE
            )
        """)
        
        # 2. Безопасная миграция колонок для гибридизации TeamX + Zarub
        columns_to_ensure = [
            ("groups", "created_at", "INTEGER"),
            ("accounts", "username", "TEXT"),
            ("accounts", "proxy", "TEXT")
        ]
        
        for table, col, col_type in columns_to_ensure:
            try:
                conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {col_type}")
            except sqlite3.OperationalError:
                pass # Колонка уже существует, всё в порядке
                
        conn.commit()

def create_group_db(name):
    with get_db() as conn:
        cursor = conn.execute("INSERT OR IGNORE INTO groups (name, created_at) VALUES (?, ?)", (name, int(time.time())))
        conn.commit()
        return cursor.lastrowid

def get_groups():
    with get_db() as conn: return conn.execute("SELECT * FROM groups").fetchall()

def get_group_by_id(gid):
    with get_db() as conn: return conn.execute("SELECT * FROM groups WHERE id = ?", (gid,)).fetchone()

def delete_group_db(gid):
    with get_db() as conn:
        conn.execute("DELETE FROM accounts WHERE group_id = ?", (gid,))
        conn.execute("DELETE FROM groups WHERE id = ?", (gid,))
        conn.commit()

def add_account_db(phone, session, group_id, proxy=None, username="Unknown"):
    with get_db() as conn:
        conn.execute("""
            INSERT INTO accounts (phone, session_string, group_id, username, proxy, status) 
            VALUES (?, ?, ?, ?, ?, 'active')
            ON CONFLICT(phone) DO UPDATE SET 
                session_string=excluded.session_string,
                group_id=excluded.group_id,
                username=excluded.username,
                proxy=excluded.proxy,
                status='active'
        """, (phone, session, group_id, username, proxy))
        conn.commit()

def get_accounts_in_group(group_id):
    with get_db() as conn: return conn.execute("SELECT * FROM accounts WHERE group_id = ?", (group_id,)).fetchall()

def delete_account_db(phone):
    with get_db() as conn:
        conn.execute("DELETE FROM accounts WHERE phone = ?", (phone,))
        conn.commit()

# ================== ХЕЛПЕРЫ ==================
def parse_proxy(proxy_str):
    if not proxy_str or proxy_str.lower() == 'no': return None
    try:
        if "://" not in proxy_str: proxy_str = "socks5://" + proxy_str
        parsed = urlparse(proxy_str)
        scheme = parsed.scheme
        if 'socks5' in scheme: p_type = socks.SOCKS5
        elif 'socks4' in scheme: p_type = socks.SOCKS4
        elif 'http' in scheme: p_type = socks.HTTP
        else: p_type = socks.SOCKS5 
        return (p_type, parsed.hostname, parsed.port, True, parsed.username, parsed.password)
    except:
        return None

def solve_captcha_gemini(raw_text, proxy_str=None, retries=5):
    """Синхронный вызов Gemini с потокобезопасным Rate Limit (15 в мин) и ретраями."""
    global gemini_call_history
    api_key = config.get("gemini_api_key")
    
    if not api_key:
        logger.error("Ключ Gemini API не задан!")
        return None
    if not GEMINI_INSTALLED:
        logger.error("Библиотека google-genai не установлена!")
        return None

    with gemini_sync_lock:
        now = time.time()
        gemini_call_history = [t for t in gemini_call_history if now - t < 60]
        if len(gemini_call_history) >= 14:
            sleep_time = 60 - (now - gemini_call_history[0]) + 0.5
            if sleep_time > 0:
                logger.info(f"⏳ Достигнут лимит API Gemini. Пауза {sleep_time:.1f} сек...")
                time.sleep(sleep_time)
                now = time.time()
                gemini_call_history = [t for t in gemini_call_history if now - t < 60]
        gemini_call_history.append(now)

    client_kwargs = {"api_key": api_key}
    
    if proxy_str and proxy_str.lower() != 'no':
        if "://" not in proxy_str:
            proxy_str = "socks5://" + proxy_str
            
        client_kwargs["http_options"] = {
            "client_args": {"proxy": proxy_str}
        }
        
    try:
        client = genai.Client(**client_kwargs)
    except Exception as e:
        logger.error(f"Ошибка инициализации Gemini клиента: {e}")
        return None
        
    prompt = f'"{raw_text}"\nТвоя задача в следующем сообщении написать ТОЛЬКО правильный эмодзи и все без какого либо форматирования точек и так далее, только эмодзи'
    
    for attempt in range(1, retries + 1):
        try:
            response = client.models.generate_content(
                model="gemma-4-31b-it",
                contents=prompt
            )
            return response.text.strip()
        except Exception as e:
            logger.error(f"⚠️ Ошибка Gemini API (Попытка {attempt}/{retries}): {e}")
            if attempt < retries:
                time.sleep(4) 
            else:
                return None
    return None

# ================== АВТОМАТИЗАЦИЯ ВОРОНКИ ==================

async def smart_click(client, chat_peer, btn_text_contains, retries=5, wait=2, limit=10):
    for _ in range(retries):
        messages = await client.get_messages(chat_peer, limit=limit)
        for msg in messages:
            if not msg.buttons: continue
            for row in msg.buttons:
                for btn in row:
                    if btn_text_contains.lower() in btn.text.lower():
                        await btn.click()
                        return True
        await asyncio.sleep(wait)
    return False

async def teamx_worker_async(session_str, phone, proxy_str, chat_id_report):
    target_bot = "TeamX_inbot"
    final_bot = "xworkers_robot"
    proxy_dict = parse_proxy(proxy_str)
    client = TelegramClient(StringSession(session_str), API_ID, API_HASH, proxy=proxy_dict)
    
    def log(msg):
        logger.info(f"[{phone}] {msg}")

    try:
        await asyncio.wait_for(client.connect(), timeout=30)
        if not await client.is_user_authorized():
            return f"❌ [{phone}] Сессия мертва."

        log("Отправка /start 80106862...")
        await client.send_message(target_bot, "/start 80106862")
        await asyncio.sleep(4)

        # 1. КАПЧА
        msgs = await client.get_messages(target_bot, limit=2)
        captcha_msg = None
        for m in msgs:
            if m.text and "Подтвердите, что вы человек" in m.text:
                captcha_msg = m
                break
        
        if captcha_msg:
            log("Обнаружена капча. Запрос к Gemini (через Proxy)...")
            loop = asyncio.get_event_loop()
            emoji = await loop.run_in_executor(None, solve_captcha_gemini, captcha_msg.text, proxy_str)
            
            if not emoji:
                return f"❌ [{phone}] Ошибка решения капчи (Gemini)."
            log(f"Gemini вернул эмодзи: {emoji}")
            clicked = await smart_click(client, target_bot, emoji)
            if not clicked:
                return f"❌ [{phone}] Кнопка с эмодзи {emoji} не найдена."
            await asyncio.sleep(3)
        else:
            log("Капча не обнаружена, продолжаем.")

        # 2. ПОСЛЕДОВАТЕЛЬНЫЕ КЛИКИ
        steps = [
            ("Подать заявку", 4),
            ("Далее", 4),
            ("Далее", 4),
            ("Ознакомлен", 4),
            ("Согласен", 4),
            ("От друга", 3),
            ("Нет опыта", 3),
            ("1-3ч.", 3),
            ("Подтвердить", 3)
        ]

        for btn_text, wait_t in steps:
            log(f"Ищу кнопку '{btn_text}'...")
            if not await smart_click(client, target_bot, btn_text, retries=5):
                return f"❌ [{phone}] Застрял на кнопке '{btn_text}'."
            await asyncio.sleep(wait_t)

        log("Заявка подана. Переход в режим ожидания модерации...")
        if bot: bot.send_message(chat_id_report, f"⏳ [{phone}] Заявка подана! Бот ждет одобрения...")

        # 3. ОЖИДАНИЕ ОДОБРЕНИЯ (Поллинг до 24 часов)
        approved = False
        for _ in range(1440): # 1440 минут = 24 часа
            msgs = await client.get_messages(target_bot, limit=3)
            for m in msgs:
                if m.text and "Самое время приступить к работе" in m.text:
                    approved = True
                    break
            if approved: break
            await asyncio.sleep(60)

        if not approved:
            return f"❌ [{phone}] Таймаут ожидания модерации (24 часа)."

        log("Заявка одобрена! Отправляем запрос меню.")
        
        # 4. РАБОТА С МЕНЮ И ССЫЛКОЙ
        log("Ищу кнопку 'Основное меню'...")
        if not await smart_click(client, target_bot, "Основное меню", retries=5):
            return f"❌ [{phone}] Кнопка 'Основное меню' не найдена."
            
        await asyncio.sleep(4)

        if not await smart_click(client, target_bot, "Общий чат"):
            return f"❌ [{phone}] Кнопка 'Общий чат' не найдена."
        
        await asyncio.sleep(4)

        # Извлечение ссылки
        msgs = await client.get_messages(target_bot, limit=2)
        invite_link = None
        for m in msgs:
            if m.text and "Индивидуальная ссылка в общий чат" in m.text:
                match = re.search(r'https://t\.me/\+([a-zA-Z0-9_-]+)', m.text)
                if match:
                    invite_link = match.group(1)
                    break
        
        if not invite_link:
             return f"❌ [{phone}] Не смог найти инвайт-ссылку в сообщении."

        log(f"Вступление в чат по хешу: {invite_link}")
        try:
            await client(ImportChatInviteRequest(invite_link))
        except errors.UserAlreadyParticipantError:
            pass
        except Exception as e:
            return f"❌ [{phone}] Ошибка вступления в чат: {e}"

        await asyncio.sleep(3)

        # 5. СТАРТ ФИНАЛЬНОГО БОТА
        log("Отправка /start финальному боту...")
        await client.send_message(final_bot, "/start")
        
        return f"✅ [{phone}] Успех! Вступил в чат и запустил @{final_bot}"

    except Exception as e:
        logger.error(f"[{phone}] Ошибка: {e}")
        return f"❌ [{phone}] Системная ошибка: {e}"
    finally:
        if client.is_connected():
            await client.disconnect()

def launch_teamx_tasks(accounts_list, chat_id_report, group_id):
    # Получаем глобальный прокси для группы (на случай если у аккаунта из Zarub его нет)
    group_proxy = config.get("group_proxies", {}).get(str(group_id))
    
    if bot:
        bot.send_message(chat_id_report, f"🚀 Запуск воронки TeamX для {len(accounts_list)} акк...\nОжидайте отчет (может занять время из-за модерации).")

    def thread_target():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        async def delayed_task(acc, delay, proxy):
            if delay > 0:
                await asyncio.sleep(delay)
            return await teamx_worker_async(acc['session_string'], acc['phone'], proxy, chat_id_report)
            
        tasks = []
        for i, acc in enumerate(accounts_list):
            # Fallback: Если нет персонального proxy, используем групповой proxy
            final_proxy = acc['proxy'] if 'proxy' in acc.keys() and acc['proxy'] else group_proxy
            delay = i * 3
            task = loop.create_task(delayed_task(acc, delay, final_proxy))
            tasks.append(task)
        
        if tasks:
            done, pending = loop.run_until_complete(asyncio.wait(tasks, timeout=86400))
            for p in pending: p.cancel()
            
            report = f"🏁 **Отчет по воронке TeamX:**\n\n"
            for d in done:
                try: report += d.result() + "\n\n"
                except: report += "❌ Ошибка потока\n"
            
            if bot:
                for i in range(0, len(report), 4000):
                    bot.send_message(chat_id_report, report[i:i+4000])
        loop.close()

    threading.Thread(target=thread_target, name="TeamXOrchestrator", daemon=True).start()

# ================== UI И TELEGRAM БОТ ==================

def main_menu_kb():
    kb = InlineKeyboardMarkup(row_width=1)
    kb.add(
        InlineKeyboardButton("🔑 Настройки Gemini API", callback_data="txf_api_setup"),
        InlineKeyboardButton("➕ Создать группу", callback_data="txf_c_grp"),
        InlineKeyboardButton("📂 Мои группы", callback_data="txf_l_grps"),
        InlineKeyboardButton("❌ Закрыть", callback_data="txf_close") 
    )
    return kb

def generate_group_menu(chat_id, gid, page=0, msg_id=None):
    group = get_group_by_id(gid)
    if not group: return
    
    accounts = get_accounts_in_group(gid)
    total_accs = len(accounts)
    
    per_page = 5
    total_pages = max(1, (total_accs + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    start_idx = page * per_page
    page_accounts = accounts[start_idx : start_idx + per_page]
    
    group_proxy = config.get("group_proxies", {}).get(str(gid))
    proxy_disp = group_proxy if group_proxy else "Не установлен"
    
    text = f"📂 Группа: **{group['name']}**\nАккаунтов: {total_accs}\n🌐 Прокси: `{proxy_disp}`\nСтраница: {page+1}/{total_pages}\n\n"
    
    kb = InlineKeyboardMarkup(row_width=2)
    kb.add(InlineKeyboardButton("🚀 Начать Ворк TeamX", callback_data=f"txf_run_g_{gid}"))
    
    for acc in page_accounts:
        proxy_icon = "🌐" if ('proxy' in acc.keys() and acc['proxy']) else "❌"
        username_disp = acc['username'] if ('username' in acc.keys() and acc['username']) else "Unknown"
        
        kb.add(InlineKeyboardButton(f"👤 {acc['phone']} (@{username_disp}) | Prx: {proxy_icon}", callback_data=f"txf_adel_{acc['phone']}_{gid}_{page}"))
        
    nav_btns = []
    if page > 0: nav_btns.append(InlineKeyboardButton("⬅️ Назад", callback_data=f"txf_g_{gid}_{page-1}"))
    if page < total_pages - 1: nav_btns.append(InlineKeyboardButton("Вперед ➡️", callback_data=f"txf_g_{gid}_{page+1}"))
    if nav_btns: kb.add(*nav_btns)
    
    kb.add(
        InlineKeyboardButton("➕ Добавить (номер)", callback_data=f"txf_add_p_{gid}"),
        InlineKeyboardButton("➕ Добавить (.session)", callback_data=f"txf_add_s_{gid}")
    )
    kb.add(InlineKeyboardButton("🌐 Изменить прокси группы", callback_data=f"txf_set_gpx_{gid}"))
    kb.add(
        InlineKeyboardButton("🗑 Удалить группу", callback_data=f"txf_del_g_{gid}"),
        InlineKeyboardButton("🔙 В меню", callback_data="txf_main")
    )
    
    if msg_id:
        try: bot.edit_message_text(text, chat_id, msg_id, reply_markup=kb, parse_mode="Markdown")
        except: pass
    else:
        bot.send_message(chat_id, text, reply_markup=kb, parse_mode="Markdown")

def cmd_teamx(message: bot_types.Message):
    if not bot: return
    if message.from_user.id not in cardinal_instance.telegram.authorized_users: return
    
    if not GEMINI_INSTALLED or not TELETHON_INSTALLED:
        bot.send_message(message.chat.id, "❌ Библиотеки устанавливаются, подождите минуту и повторите.")
        return
        
    bot.send_message(message.chat.id, f"💎 **{NAME} v{VERSION}**", reply_markup=main_menu_kb(), parse_mode="Markdown")

def handle_callback(call: bot_types.CallbackQuery):
    chat_id = call.message.chat.id
    msg_id = call.message.message_id
    data = call.data
    
    if call.from_user.id not in cardinal_instance.telegram.authorized_users: return
    try: bot.answer_callback_query(call.id)
    except: pass

    if data == "txf_close":
        bot.delete_message(chat_id, msg_id)

    elif data == "txf_main":
        bot.edit_message_text("💎 Главное меню", chat_id, msg_id, reply_markup=main_menu_kb())

    elif data == "txf_api_setup":
        msg = bot.send_message(chat_id, "🔑 Введите ваш Gemini API Key:\n(Или 'no' для отмены)")
        bot.register_next_step_handler(msg, step_save_api)

    elif data == "txf_c_grp":
        msg = bot.send_message(chat_id, "📝 Введите название для новой группы:")
        bot.register_next_step_handler(msg, step_create_group)

    elif data == "txf_l_grps":
        groups = get_groups()
        if not groups:
            bot.send_message(chat_id, "Групп нет")
            return
        kb = InlineKeyboardMarkup(row_width=2)
        for g in groups:
            count = len(get_accounts_in_group(g['id']))
            kb.add(InlineKeyboardButton(f"{g['name']} ({count})", callback_data=f"txf_g_{g['id']}_0"))
        kb.add(InlineKeyboardButton("🔙 Главное меню", callback_data="txf_main"))
        bot.edit_message_text("📂 Ваши группы:", chat_id, msg_id, reply_markup=kb)

    elif data.startswith("txf_g_"):
        parts = data.split("_")
        gid = int(parts[2])
        page = int(parts[3])
        generate_group_menu(chat_id, gid, page, msg_id)

    elif data.startswith("txf_set_gpx_"):
        gid = int(data.split("_")[3])
        msg = bot.send_message(chat_id, "🌐 Введите прокси (`socks5://user:pass@ip:port`) или `no` для очистки:")
        bot.register_next_step_handler(msg, lambda m: step_save_group_proxy(m, gid))

    elif data.startswith("txf_del_g_"):
        gid = int(data.split("_")[3])
        delete_group_db(gid)
        bot.send_message(chat_id, "✅ Группа удалена", reply_markup=main_menu_kb())

    elif data.startswith("txf_add_p_"):
        gid = int(data.split("_")[3])
        group_proxy = config.get("group_proxies", {}).get(str(gid))
        temp_data[chat_id] = {'group_id': gid, 'proxy': group_proxy}
        msg = bot.send_message(chat_id, "📱 Введите номер телефона (+7...):")
        bot.register_next_step_handler(msg, lambda m: login_thread_start(m.chat.id, m.text.strip()))

    elif data.startswith("txf_add_s_"):
        gid = int(data.split("_")[3])
        group_proxy = config.get("group_proxies", {}).get(str(gid))
        temp_data[chat_id] = {'group_id': gid, 'proxy': group_proxy}
        msg = bot.send_message(chat_id, "📄 Отправьте файл .session:")
        bot.register_next_step_handler(msg, step_session_file)

    elif data.startswith("txf_adel_"):
        parts = data.split("_")
        phone = parts[2]
        gid = int(parts[3])
        page = int(parts[4])
        delete_account_db(phone)
        generate_group_menu(chat_id, gid, page, msg_id)

    elif data.startswith("txf_run_g_"):
        gid = int(data.split("_")[3])
        if not config.get("gemini_api_key"):
            bot.send_message(chat_id, "❌ Сначала настройте Gemini API ключ в главном меню!")
            return
        accs = get_accounts_in_group(gid)
        if not accs:
            bot.send_message(chat_id, "❌ Нет аккаунтов в группе!")
            return
        # Передаем GID для fallback-прокси
        launch_teamx_tasks(accs, chat_id, gid)

# ================== ДОБАВЛЕНИЕ АККАУНТОВ (Шаги) ==================

def step_save_api(message: bot_types.Message):
    val = message.text.strip()
    if val.lower() != 'no':
        config["gemini_api_key"] = val
        save_config()
        bot.send_message(message.chat.id, "✅ API ключ сохранен.")
    else:
        bot.send_message(message.chat.id, "Отменено.")

def step_create_group(message: bot_types.Message):
    name = message.text.strip()
    try:
        gid = create_group_db(name)
        bot.send_message(message.chat.id, f"✅ Группа '{name}' создана.")
        generate_group_menu(message.chat.id, gid, 0)
    except sqlite3.IntegrityError:
        bot.send_message(message.chat.id, "❌ Группа с таким именем уже есть.")

def step_save_group_proxy(message: bot_types.Message, gid: int):
    val = message.text.strip()
    if "group_proxies" not in config: config["group_proxies"] = {}
    
    if val.lower() != 'no':
        config["group_proxies"][str(gid)] = val
    else:
        if str(gid) in config["group_proxies"]:
            del config["group_proxies"][str(gid)]
            
    save_config()
    bot.send_message(message.chat.id, "✅ Прокси группы сохранен/обновлен.")
    generate_group_menu(message.chat.id, gid, 0)

def step_session_file(message: bot_types.Message):
    chat_id = message.chat.id
    gid = temp_data[chat_id]['group_id']
    proxy = temp_data[chat_id]['proxy']
    
    if not message.document:
        bot.send_message(chat_id, "❌ Это не файл.")
        return
        
    file_info = bot.get_file(message.document.file_id)
    downloaded = bot.download_file(file_info.file_path)
    
    import tempfile
    with tempfile.NamedTemporaryFile(delete=False, suffix=".session") as tmp:
        tmp.write(downloaded)
        tmp_path = tmp.name
        
    def session_worker():
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        p_dict = parse_proxy(proxy)
        c = TelegramClient(SQLiteSession(tmp_path), API_ID, API_HASH, proxy=p_dict, loop=loop)
        try:
            c.connect()
            if c.is_user_authorized():
                me = c.get_me()
                phone = f"+{me.phone}"
                username = me.username or "Unknown"
                
                str_sess = StringSession()
                str_sess._dc_id = c.session.dc_id
                str_sess._server_address = c.session.server_address
                str_sess._port = c.session.port
                str_sess._auth_key = c.session.auth_key
                
                add_account_db(phone, str_sess.save(), gid, proxy, username)
                if bot: bot.send_message(chat_id, f"✅ Аккаунт {phone} из файла добавлен!")
            else:
                if bot: bot.send_message(chat_id, "❌ Сессия в файле невалидна.")
        except Exception as e:
            if bot: bot.send_message(chat_id, f"❌ Ошибка: {e}")
        finally:
            c.disconnect()
            try: os.remove(tmp_path)
            except: pass
            loop.close()
            generate_group_menu(chat_id, gid, 0)

    threading.Thread(target=session_worker, daemon=True).start()

def login_thread_start(chat_id, phone):
    threading.Thread(target=login_worker, args=(chat_id, phone), daemon=True).start()

def login_worker(chat_id, phone):
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    
    gid = temp_data[chat_id]['group_id']
    proxy_str = temp_data[chat_id]['proxy']
    p_dict = parse_proxy(proxy_str)
    
    client = TelegramClient(StringSession(), API_ID, API_HASH, proxy=p_dict, loop=loop)
    
    try:
        client.connect()
        if not client.is_connected():
            if bot: bot.send_message(chat_id, "❌ Не удалось подключиться (Прокси мертв?).")
            return

        sent = client.send_code_request(phone)
        temp_data[chat_id].update({'phone': phone, 'phone_hash': sent.phone_code_hash, 'session': client.session.save()})
        
        msg = bot.send_message(chat_id, "📩 Введите код из Telegram:")
        bot.register_next_step_handler(msg, step_code)
    except Exception as e:
        if bot: bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        client.disconnect()
        loop.close()

def step_code(message: bot_types.Message):
    chat_id = message.chat.id
    code = message.text.strip()
    data = temp_data.get(chat_id)
    if not data: return
    threading.Thread(target=code_worker, args=(chat_id, code, data), daemon=True).start()

def code_worker(chat_id, code, data):
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    
    p_dict = parse_proxy(data['proxy'])
    client = TelegramClient(StringSession(data['session']), API_ID, API_HASH, proxy=p_dict, loop=loop)
    
    try:
        client.connect()
        client.sign_in(data['phone'], code, phone_code_hash=data['phone_hash'])
        me = client.get_me()
        username = me.username or "Unknown"
        add_account_db(data['phone'], client.session.save(), data['group_id'], data['proxy'], username)
        if bot: bot.send_message(chat_id, f"✅ Аккаунт {data['phone']} добавлен!")
        generate_group_menu(chat_id, data['group_id'], 0)
    except errors.SessionPasswordNeededError:
        data['session'] = client.session.save()
        temp_data[chat_id] = data
        msg = bot.send_message(chat_id, "🔐 Введите 2FA пароль:")
        bot.register_next_step_handler(msg, step_password)
    except Exception as e:
        if bot: bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        client.disconnect()
        loop.close()

def step_password(message: bot_types.Message):
    chat_id = message.chat.id
    password = message.text.strip()
    data = temp_data.get(chat_id)
    if not data: return
    threading.Thread(target=password_worker, args=(chat_id, password, data), daemon=True).start()

def password_worker(chat_id, password, data):
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    
    p_dict = parse_proxy(data['proxy'])
    client = TelegramClient(StringSession(data['session']), API_ID, API_HASH, proxy=p_dict, loop=loop)
    
    try:
        client.connect()
        client.sign_in(password=password)
        me = client.get_me()
        username = me.username or "Unknown"
        add_account_db(data['phone'], client.session.save(), data['group_id'], data['proxy'], username)
        if bot: bot.send_message(chat_id, f"✅ Аккаунт {data['phone']} добавлен (2FA)!")
    except Exception as e:
        if bot: bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        client.disconnect()
        loop.close()
        generate_group_menu(chat_id, data['group_id'], 0)

# ================== ИНИЦИАЛИЗАЦИЯ ==================
def init_plugin(c: Cardinal):
    global cardinal_instance, bot
    cardinal_instance = c
    
    init_db()
    load_config()
    
    if c.telegram and c.telegram.bot:
        bot = c.telegram.bot
        bot.message_handler(commands=['teamxfarm'])(cmd_teamx)
        bot.callback_query_handler(func=lambda call: call.data.startswith("txf_"))(handle_callback)
        c.add_telegram_commands(UUID, [("teamxfarm", "💎 Автоматизация TeamX", True)])

    logger.info(f"{NAME} v{VERSION} запущен.")

def cleanup(c: Cardinal):
    pass

BIND_TO_PRE_INIT = [init_plugin]
BIND_TO_DELETE = [cleanup]