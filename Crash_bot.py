# -*- coding: utf-8 -*-
import datetime
import asyncio
import html
import importlib
import json
import logging
import os
import random
import re
import string
import threading
from functools import wraps
from http.server import BaseHTTPRequestHandler, HTTPServer
from json import JSONDecodeError
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import TelegramError
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# mise a jour
TOKEN = os.getenv("TOKEN")
DATA_FILE = "users.json"
ADMIN_ID_FILE = "admin_id.json"
SECURITY_LOG_FILE = "security_log.json"
SIGNAUX_DEFAUT = 3
ADMIN_USERNAME = os.environ.get("ADMIN_USERNAME", "hacker_ci").lstrip("@")
COOLDOWN_SECONDS = 30
ANALYSE_MIN_SECONDS = 8
ANALYSE_MAX_SECONDS = 15
HISTORIQUE_LIMIT = 100
SIGNAL_MEMORY_LIMIT = 20
OPPORTUNITE_REFUS_PROBABILITY = 0.07
SAFE_DB_IDENTIFIER_RE = re.compile(r"^[a-zA-Z_][a-zA-Z0-9_]*$")
POSTGRES_SCHEMA = os.getenv("CRASH_DB_SCHEMA", "crash")
CRASH_TIMEZONE = os.getenv("CRASH_TIMEZONE", "Africa/Abidjan")

# Configuration du groupe de journalisation (0 = désactivé)
LOG_GROUP_ID = int(os.environ.get("LOG_GROUP_ID", "0"))  # mettre -100... dans l'env pour activer
SALES_LOG_KEY = "sales_log"

# Configuration des prix (modifiable)
PACK_PRICES = {
    100: 2000,
    250: 4000,
    500: 7000,
}
DEFAULT_PRICE_PER_SIGNAL = 20
ABONNEMENT_PRICE = 12000

def admin_username_html():
    return f"@{html.escape(ADMIN_USERNAME)}"

def echapper_html_texte(texte):
    return html.escape(str(texte), quote=True)

def format_fcfa(n):
    try:
        return f"{int(n):,}".replace(",", " ")
    except Exception:
        return str(n)

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=os.environ.get("LOG_LEVEL", "INFO").upper(),
)
logger = logging.getLogger(__name__)
storage_lock = threading.RLock()
storage_cache = {}
db_pool = None
db_initialized = False
db_disabled = False
db_warning_logged = False
Jsonb = None
analyses_lock = threading.Lock()
analyses_en_cours = set()
signal_history_lock = threading.Lock()
derniers_signaux_generes = []

def identifiant_sql_sur(schema):
    if not SAFE_DB_IDENTIFIER_RE.match(schema or ""):
        raise RuntimeError("Nom de schema PostgreSQL invalide.")
    return schema

def schema_postgres():
    return identifiant_sql_sur(POSTGRES_SCHEMA)

def copie_defaut(default):
    if isinstance(default, dict):
        return default.copy()
    if isinstance(default, list):
        return list(default)
    return default

def chemins_migration_json(*noms):
    chemins = []
    for nom in noms:
        if nom and nom not in chemins:
            chemins.append(nom)
    return chemins

def lire_json_migration(path, default):
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return copie_defaut(default)
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (JSONDecodeError, OSError) as exc:
        logger.exception("Impossible d'importer %s vers PostgreSQL.", path, exc_info=exc)
        return copie_defaut(default)

def lire_json_fichier(path, default):
    with storage_lock:
        if path in storage_cache:
            return storage_cache[path]
        if not os.path.exists(path) or os.path.getsize(path) == 0:
            valeur = copie_defaut(default)
            storage_cache[path] = valeur
            return valeur
        try:
            with open(path, "r", encoding="utf-8") as f:
                valeur = json.load(f)
                storage_cache[path] = valeur
                return valeur
        except (JSONDecodeError, OSError) as exc:
            logger.exception("Impossible de lire %s. Valeur par défaut utilisée.", path, exc_info=exc)
            valeur = copie_defaut(default)
            storage_cache[path] = valeur
            return valeur

def ecrire_json_fichier(path, data):
    dossier = os.path.dirname(os.path.abspath(path)) or "."
    os.makedirs(dossier, exist_ok=True)
    tmp_path = os.path.join(dossier, f".{os.path.basename(path)}.{os.getpid()}.tmp")
    with storage_lock:
        storage_cache[path] = data
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, path)

def avertir_stockage_json(message):
    global db_warning_logged
    if not db_warning_logged:
        logger.warning("%s Utilisation du stockage JSON.", message)
        db_warning_logged = True

def get_db_pool():
    global db_pool, db_disabled, Jsonb
    if db_disabled:
        return None
    if db_pool is None:
        database_url = os.getenv("DATABASE_URL")
        if not database_url:
            avertir_stockage_json("DATABASE_URL absente.")
            db_disabled = True
            return None
        try:
            PsycopgConnectionPool = importlib.import_module("psycopg_pool").ConnectionPool
            PsycopgJsonb = importlib.import_module("psycopg.types.json").Jsonb
            Jsonb = PsycopgJsonb
            schema = schema_postgres()
            db_pool = PsycopgConnectionPool(
                database_url,
                min_size=1,
                max_size=int(os.getenv("DB_POOL_MAX_SIZE", "5")),
                kwargs={"options": f"-c search_path={schema}"},
            )
        except Exception as exc:
            logger.warning("PostgreSQL indisponible (%s). Utilisation du stockage JSON.", exc)
            db_disabled = True
            return None
    return db_pool

def initialiser_base_de_donnees():
    """
    Initialise la base et effectue une migration minimale :
    - crée les tables si besoin
    - migre le JSON vers Postgres si tables vides
    - génère des codes pour les utilisateurs existants qui n'en ont pas (SEULEMENT si Postgres disponible)
    """
    global db_initialized, db_disabled
    if db_initialized:
        return not db_disabled

    with storage_lock:
        if db_initialized:
            return not db_disabled

        pool = get_db_pool()
        if pool is None:
            db_initialized = True
            return False
        try:
            with pool.connection() as conn:
                with conn.cursor() as cur:
                    schema = schema_postgres()
                    cur.execute(f'CREATE SCHEMA IF NOT EXISTS "{schema}"')
                    cur.execute(f'SET search_path TO "{schema}"')
                    cur.execute(
                        """
                        CREATE TABLE IF NOT EXISTS users (
                            user_key TEXT PRIMARY KEY,
                            telegram_id BIGINT,
                            username TEXT,
                            code_client TEXT,
                            data JSONB NOT NULL DEFAULT '{}'::jsonb,
                            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                        )
                        """
                    )
                    cur.execute(
                        """
                        CREATE TABLE IF NOT EXISTS statistiques (
                            key TEXT PRIMARY KEY,
                            data JSONB NOT NULL DEFAULT '{}'::jsonb,
                            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                        )
                        """
                    )
                    cur.execute(
                        """
                        CREATE TABLE IF NOT EXISTS administrateurs (
                            key TEXT PRIMARY KEY,
                            data JSONB NOT NULL DEFAULT '{}'::jsonb,
                            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                        )
                        """
                    )
                    cur.execute("CREATE INDEX IF NOT EXISTS idx_users_telegram_id ON users (telegram_id)")
                    cur.execute("CREATE INDEX IF NOT EXISTS idx_users_code_client ON users (code_client)")
                conn.commit()

            migrer_json_vers_postgres_si_vide()

            # Après avoir un pool valide et les utilisateurs chargés, s'assurer que chaque user a un 'code'
            # et que la colonne code_client est synchronisée => utilité pour la nouvelle logique d'invitations.
            try:
                data = lire_json(DATA_FILE, {})
                modifie = False
                for uid, user in data.items():
                    if not isinstance(user, dict):
                        continue
                    if "code" not in user or not user.get("code"):
                        user["code"] = generer_code_unique(data)
                        modifie = True
                if modifie:
                    sauvegarder_users(data)
            except Exception:
                logger.exception("Impossible d'assigner automatiquement des codes aux comptes existants.")
        except Exception as exc:
            logger.warning("Connexion PostgreSQL impossible (%s). Utilisation du stockage JSON.", exc)
            db_disabled = True
            db_initialized = True
            return False
        db_initialized = True
        return True

def migrer_json_vers_postgres_si_vide():
    pool = get_db_pool()
    with pool.connection() as conn:
        with conn.cursor() as cur:
            cur.execute("SELECT COUNT(*) FROM users")
            users_vide = cur.fetchone()[0] == 0
            if users_vide:
                cur.execute("SELECT to_regclass('public.users')")
                public_users_existe = cur.fetchone()[0] is not None
                if public_users_existe:
                    cur.execute(
                        """
                        INSERT INTO users (user_key, telegram_id, username, code_client, data, updated_at)
                        SELECT user_key, telegram_id, username, code_client, data, updated_at
                        FROM public.users
                        ON CONFLICT (user_key) DO NOTHING
                        """
                    )
                    cur.execute("SELECT COUNT(*) FROM users")
                    users_vide = cur.fetchone()[0] == 0
            if users_vide:
                users_importes = {}
                for path in chemins_migration_json(DATA_FILE, "crash_users.json"):
                    donnees = lire_json_migration(path, {})
                    if isinstance(donnees, dict):
                        users_importes.update(donnees)
                if users_importes:
                    sauvegarder_users_postgres(cur, users_importes, supprimer_absents=False)
                    logger.info("%s utilisateur(s) importes depuis JSON vers PostgreSQL.", len(users_importes))

            cur.execute("SELECT COUNT(*) FROM administrateurs")
            admins_vide = cur.fetchone()[0] == 0
            if admins_vide:
                cur.execute("SELECT to_regclass('public.administrateurs')")
                public_admins_existe = cur.fetchone()[0] is not None
                if public_admins_existe:
                    cur.execute(
                        """
                        INSERT INTO administrateurs (key, data, updated_at)
                        SELECT key, data, updated_at
                        FROM public.administrateurs
                        ON CONFLICT (key) DO NOTHING
                        """
                    )
                    cur.execute("SELECT COUNT(*) FROM administrateurs")
                    admins_vide = cur.fetchone()[0] == 0
            if admins_vide:
                admin_data = {}
                for path in chemins_migration_json(ADMIN_ID_FILE, "crash_admin_id.json"):
                    donnees = lire_json_migration(path, {})
                    if isinstance(donnees, dict) and donnees:
                        admin_data = donnees
                        break
                if admin_data:
                    cur.execute(
                        """
                        INSERT INTO administrateurs (key, data, updated_at)
                        VALUES ('main', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(admin_data),),
                    )

            cur.execute("SELECT COUNT(*) FROM statistiques")
            stats_vides = cur.fetchone()[0] == 0
            if stats_vides:
                cur.execute("SELECT to_regclass('public.statistiques')")
                public_stats_existe = cur.fetchone()[0] is not None
                if public_stats_existe:
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        SELECT key, data, updated_at
                        FROM public.statistiques
                        ON CONFLICT (key) DO NOTHING
                        """
                    )
                    cur.execute("SELECT COUNT(*) FROM statistiques")
                    stats_vides = cur.fetchone()[0] == 0
            if stats_vides:
                data_stats = lire_json_migration("data.json", {})
                journal = lire_json_migration(SECURITY_LOG_FILE, [])
                if isinstance(data_stats, dict) and data_stats:
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        VALUES ('main', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(data_stats),),
                    )
                if isinstance(journal, list) and journal:
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        VALUES ('security_log', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(journal[-1000:]),),
                    )
        conn.commit()

def valeur_texte(data, *cles):
    for cle in cles:
        valeur = data.get(cle)
        if valeur is not None:
            return str(valeur)
    return None

def valeur_entier(data, *cles):
    for cle in cles:
        valeur = data.get(cle)
        if valeur is not None:
            try:
                return int(valeur)
            except (TypeError, ValueError):
                return None
    return None

def sauvegarder_users_postgres(cur, data, supprimer_absents=False):
    cles = []
    for uid, user in data.items():
        if not isinstance(user, dict):
            continue
        user_key = str(uid)
        cles.append(user_key)
        cur.execute(
            """
            INSERT INTO users (user_key, telegram_id, username, code_client, data, updated_at)
            VALUES (%s, %s, %s, %s, %s, NOW())
            ON CONFLICT (user_key) DO UPDATE SET
                telegram_id = EXCLUDED.telegram_id,
                username = EXCLUDED.username,
                code_client = EXCLUDED.code_client,
                data = EXCLUDED.data,
                updated_at = NOW()
            """,
            (
                user_key,
                valeur_entier(user, "telegram_id", "user_id"),
                valeur_texte(user, "username"),
                valeur_texte(user, "code_client", "code"),
                Jsonb(user),
            ),
        )

    if supprimer_absents:
        if cles:
            cur.execute("DELETE FROM users WHERE NOT (user_key = ANY(%s))", (cles,))
        else:
            cur.execute("DELETE FROM users")

def lire_json(path, default):
    if not initialiser_base_de_donnees():
        return lire_json_fichier(path, default)
    with storage_lock:
        if path in storage_cache:
            return storage_cache[path]

        pool = get_db_pool()
        with pool.connection() as conn:
            with conn.cursor() as cur:
                if path == DATA_FILE:
                    cur.execute("SELECT user_key, data FROM users")
                    valeur = {str(user_key): data for user_key, data in cur.fetchall()}
                elif path == ADMIN_ID_FILE:
                    cur.execute("SELECT data FROM administrateurs WHERE key = 'main'")
                    ligne = cur.fetchone()
                    valeur = ligne[0] if ligne else copie_defaut(default)
                elif path == SECURITY_LOG_FILE:
                    cur.execute("SELECT data FROM statistiques WHERE key = 'security_log'")
                    ligne = cur.fetchone()
                    valeur = ligne[0] if ligne else copie_defaut(default)
                elif path == "data.json":
                    cur.execute("SELECT data FROM statistiques WHERE key = 'main'")
                    ligne = cur.fetchone()
                    valeur = ligne[0] if ligne else copie_defaut(default)
                else:
                    cur.execute("SELECT data FROM statistiques WHERE key = %s", (path,))
                    ligne = cur.fetchone()
                    valeur = ligne[0] if ligne else copie_defaut(default)

        storage_cache[path] = valeur
        return valeur

def ecrire_json(path, data):
    if not initialiser_base_de_donnees():
        ecrire_json_fichier(path, data)
        return
    with storage_lock:
        storage_cache[path] = data
        pool = get_db_pool()
        with pool.connection() as conn:
            with conn.cursor() as cur:
                if path == DATA_FILE:
                    sauvegarder_users_postgres(cur, data)
                elif path == ADMIN_ID_FILE:
                    cur.execute(
                        """
                        INSERT INTO administrateurs (key, data, updated_at)
                        VALUES ('main', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(data),),
                    )
                elif path == SECURITY_LOG_FILE:
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        VALUES ('security_log', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(data[-1000:] if isinstance(data, list) else data),),
                    )
                elif path == "data.json":
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        VALUES ('main', %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (Jsonb(data),),
                    )
                else:
                    cur.execute(
                        """
                        INSERT INTO statistiques (key, data, updated_at)
                        VALUES (%s, %s, NOW())
                        ON CONFLICT (key) DO UPDATE SET data = EXCLUDED.data, updated_at = NOW()
                        """,
                        (path, Jsonb(data)),
                    )
            conn.commit()

def get_admin_id():
    return lire_json(ADMIN_ID_FILE, {}).get("id")

def sauvegarder_admin_id(user_id):
    ecrire_json(ADMIN_ID_FILE, {"id": user_id})

def charger_users():
    return lire_json(DATA_FILE, {})

def sauvegarder_users(data):
    ecrire_json(DATA_FILE, data)

def safe_sauvegarder_users(data):
    """
    Tente de sauvegarder via la voie normale (Postgres si dispo).
    En cas d'erreur, force la sauvegarde sur fichier JSON local et met à jour le cache.
    Ceci garantit que la création/association marche même si Postgres est down.
    """
    try:
        # sauvegarder_users utilise ecrire_json qui bascule en JSON si Postgres indisponible,
        # mais cette opération peut encore lever une exception dans certains cas -> on capture.
        sauvegarder_users(data)
        return True
    except Exception as exc:
        logger.exception("Erreur en sauvegardant via la voie normale, bascule vers fichier JSON local.", exc_info=exc)
        try:
            # Forcer écriture sur fichier local (atomic)
            ecrire_json_fichier(DATA_FILE, data)
            with storage_lock:
                storage_cache[DATA_FILE] = data
            logger.info("Sauvegarde locale (JSON) réussie.")
            return True
        except Exception as exc2:
            logger.exception("Echec de la sauvegarde locale JSON.", exc_info=exc2)
            return False

def charger_journal_securite():
    journal = lire_json(SECURITY_LOG_FILE, [])
    return journal if isinstance(journal, list) else []

def sauvegarder_journal_securite(journal):
    ecrire_json(SECURITY_LOG_FILE, journal[-1000:])

# --- Journal des ventes (recharges & abonnements) et notifications de groupe ---
def charger_journal_ventes():
    journal = lire_json(SALES_LOG_KEY, [])
    return journal if isinstance(journal, list) else []

def sauvegarder_journal_ventes(journal):
    ecrire_json(SALES_LOG_KEY, journal[-10000:])

def calculer_prix_recharge(nombre):
    try:
        n = int(nombre)
    except Exception:
        return 0
    if n in PACK_PRICES:
        return PACK_PRICES[n]
    return int(n * DEFAULT_PRICE_PER_SIGNAL)

def journaliser_recharge(code_client, nombre, admin_name, price_fcfa=None):
    if price_fcfa is None:
        price_fcfa = calculer_prix_recharge(nombre)
    journal = charger_journal_ventes()
    journal.append(
        {
            "type": "recharge",
            "date": datetime.datetime.now().isoformat(),
            "client": code_client,
            "signals": int(nombre),
            "price": int(price_fcfa),
            "admin": admin_name,
        }
    )
    sauvegarder_journal_ventes(journal)

def journaliser_abonnement(code_client, admin_name, duree_jours=30, price_fcfa=None):
    if price_fcfa is None:
        price_fcfa = ABONNEMENT_PRICE
    journal = charger_journal_ventes()
    journal.append(
        {
            "type": "abonnement",
            "date": datetime.datetime.now().isoformat(),
            "client": code_client,
            "duration_days": int(duree_jours),
            "price": int(price_fcfa),
            "admin": admin_name,
        }
    )
    sauvegarder_journal_ventes(journal)

async def _envoyer_notification_groupe(context: ContextTypes.DEFAULT_TYPE, texte: str):
    if not LOG_GROUP_ID:
        return
    try:
        await context.bot.send_message(chat_id=LOG_GROUP_ID, text=texte, parse_mode=ParseMode.HTML)
    except TelegramError:
        logger.exception("Erreur lors de l'envoi du message au groupe LOG_GROUP_ID.")
    except Exception:
        logger.exception("Erreur inattendue lors de l'envoi du message au groupe LOG_GROUP_ID.")
# --- Fin journal ventes ---

def date_heure_securite():
    return datetime.datetime.now().strftime("%d/%m/%Y %H:%M")

def journaliser_securite(evenement, code, telegram_id, ancien_telegram_id=None):
    journal = charger_journal_securite()
    journal.append(
        {
            "date": date_heure_securite(),
            "evenement": evenement,
            "code": code,
            "telegram_id": telegram_id,
            "ancien_telegram_id": ancien_telegram_id,
        }
    )
    sauvegarder_journal_securite(journal)

def telegram_id_enregistre(user):
    valeur = user.get("telegram_id")
    try:
        return int(valeur) if valeur is not None else None
    except (TypeError, ValueError):
        return None

def entier_positif(valeur, defaut=0, maximum=None):
    try:
        nombre = int(valeur)
    except (TypeError, ValueError):
        nombre = defaut

    nombre = max(0, nombre)
    if maximum is not None:
        nombre = min(nombre, maximum)
    return nombre

def timezone_crash():
    try:
        return ZoneInfo(CRASH_TIMEZONE)
    except ZoneInfoNotFoundError:
        logger.warning("Fuseau horaire CRASH_TIMEZONE invalide (%s). UTC utilise.", CRASH_TIMEZONE)
        return datetime.timezone.utc

def maintenant_crash():
    return datetime.datetime.now(timezone_crash())

def planning_crash(maintenant=None):
    maintenant = maintenant or maintenant_crash()
    if maintenant.weekday() in (2, 6):
        return {
            "actif": False,
            "type": "journee",
            "prochaine_session": "demain",
        }

    heure = maintenant.time()
    if datetime.time(12, 0) <= heure < datetime.time(14, 0):
        return {
            "actif": False,
            "type": "midi",
            "prochaine_session": "14h00",
        }
    if datetime.time(21, 0) <= heure < datetime.time(22, 0):
        return {
            "actif": False,
            "type": "soir",
            "prochaine_session": "22h00",
        }

    return {
        "actif": True,
        "type": "actif",
        "prochaine_session": None,
    }

def bot_crash_actif(maintenant=None):
    return planning_crash(maintenant)["actif"]

def texte_mise_a_jour_crash(etat=None):
    etat = etat or planning_crash()
    if etat.get("type") == "journee":
        return (
            "💥 <b>CRASH</b>\n\n"
            "🔄 <b>MISE À JOUR DU SYSTÈME</b>\n\n"
            "🇷🇺 <b>ОБНОВЛЕНИЕ СИСТЕМЫ</b>\n\n"
            "Le bot est actuellement en mise à jour\n"
            "afin d'améliorer les prochaines analyses.\n\n"
            "🚫 Aucun signal n'est disponible aujourd'hui.\n\n"
            "⏰ Revenez demain pour retrouver les signaux.\n\n"
            "Merci pour votre patience. ❤️"
        )

    if etat.get("type") == "soir":
        return (
            "💥 <b>CRASH</b>\n\n"
            "🔄 <b>MISE À JOUR DU SOIR</b>\n\n"
            "🇷🇺 <b>ВЕЧЕРНЕЕ ОБНОВЛЕНИЕ</b>\n\n"
            "Le système analyse les nouvelles données\n"
            "pour améliorer les prochains signaux.\n\n"
            "⏰ Prochaine session : 22h00\n\n"
            "Vos signaux restent conservés."
        )

    return (
        "💥 <b>CRASH</b>\n\n"
        "🔄 <b>MISE À JOUR</b>\n\n"
        "🇷🇺 <b>ОБНОВЛЕНИЕ</b>\n\n"
        "Le système analyse actuellement les données\n"
        "pour améliorer les prochains signaux.\n\n"
        "⏰ Prochaine session : 14h00\n\n"
        "Vos signaux restent entièrement conservés."
    )

def timestamp_ou_none(valeur):
    try:
        return float(valeur)
    except (TypeError, ValueError):
        return None

def abonnement_actif(user, maintenant=None):
    if not user.get("vip"):
        return False

    fin_ts = timestamp_ou_none(user.get("vip_fin"))
    if not fin_ts:
        return False

    maintenant = maintenant or datetime.datetime.now()
    return fin_ts > maintenant.timestamp()

def abonnement_expire(user, maintenant=None):
    if not user.get("vip") or not user.get("vip_fin"):
        return False

    fin_ts = timestamp_ou_none(user.get("vip_fin"))
    if not fin_ts:
        return False

    maintenant = maintenant or datetime.datetime.now()
    return fin_ts <= maintenant.timestamp()

def normaliser_signaux_gratuits(user):
    restants_actuels = entier_positif(user.get("restants", 0), maximum=SIGNAUX_DEFAUT)

    if "signaux_gratuits_restants" not in user:
        if user.get("vip") and user.get("vip_signals") is not None:
            gratuits = 0
        else:
            gratuits = restants_actuels
        user["signaux_gratuits_restants"] = gratuits

    user["signaux_gratuits_restants"] = entier_positif(
        user.get("signaux_gratuits_restants", 0),
        maximum=SIGNAUX_DEFAUT,
    )
    user["gratuits_deja_donnes"] = True
    return user["signaux_gratuits_restants"]

def normaliser_signaux_vip(user):
    user["vip_signals"] = entier_positif(user.get("vip_signals", 0))
    return user["vip_signals"]

def date_limite_journaliere():
    return maintenant_crash().strftime("%Y-%m-%d")

def normaliser_limite_journaliere(user):
    limite = entier_positif(user.get("daily_limit_max", 0))
    active = bool(user.get("daily_limit_enabled")) and limite > 0
    aujourd_hui = date_limite_journaliere()

    if not active:
        user["daily_limit_enabled"] = False
        user["daily_limit_max"] = 0
        user["daily_used"] = 0
        user["daily_limit_date"] = aujourd_hui
        return 0, 0, False

    if user.get("daily_limit_date") != aujourd_hui:
        user["daily_used"] = 0
        user["daily_limit_date"] = aujourd_hui

    user["daily_limit_enabled"] = True
    user["daily_limit_max"] = limite
    user["daily_used"] = entier_positif(user.get("daily_used", 0), maximum=limite)
    return user["daily_used"], limite, True

def configurer_limite_journaliere(user, limite=None):
    if limite and limite > 0:
        user["daily_limit_enabled"] = True
        user["daily_limit_max"] = int(limite)
        user["daily_used"] = 0
        user["daily_limit_date"] = date_limite_journaliere()
    else:
        user["daily_limit_enabled"] = False
        user["daily_limit_max"] = 0
        user["daily_used"] = 0
        user["daily_limit_date"] = date_limite_journaliere()

def supprimer_limite_journaliere(user):
    user.pop("daily_limit_enabled", None)
    user.pop("daily_limit_max", None)
    user.pop("daily_used", None)
    user.pop("daily_limit_date", None)

def limite_journaliere_atteinte(user):
    utilises, limite, active = normaliser_limite_journaliere(user)
    return active and utilises >= limite

def texte_limite_journaliere(user):
    utilises, limite, active = normaliser_limite_journaliere(user)
    if not active:
        return "📅 Limite quotidienne\nNon activée"
    return f"📅 Limite quotidienne\n<b>{utilises} / {limite}</b> utilisés aujourd'hui"

def texte_limite_atteinte():
    return (
        "⛔ <b>Vous avez atteint votre limite quotidienne.</b>\n\n"
        "Revenez demain pour obtenir de nouveaux signaux."
    )

def normaliser_signaux_restants(user):
    gratuits = normaliser_signaux_gratuits(user)
    vip_signals = normaliser_signaux_vip(user)
    normaliser_limite_journaliere(user)

    if abonnement_actif(user):
        user["vip"] = True
        user["illimite"] = True
        user["restants"] = None
        return vip_signals

    user["illimite"] = False
    if user.get("vip"):
        user["restants"] = vip_signals
    else:
        user["restants"] = gratuits

    return user["restants"]

def remettre_en_mode_gratuit(user):
    gratuits = normaliser_signaux_gratuits(user)
    user["vip"] = False
    user["illimite"] = False
    user["restants"] = gratuits
    user["vip_signals"] = 0
    supprimer_limite_journaliere(user)
    user.pop("vip_debut", None)
    user.pop("vip_fin", None)
    return gratuits

def appliquer_expiration_si_necessaire(user, maintenant=None):
    if not abonnement_expire(user, maintenant=maintenant):
        return False

    remettre_en_mode_gratuit(user)
    return True

def migrer_si_besoin(data):
    modifie = False

    for uid, user in data.items():
        if not isinstance(user, dict):
            continue

        avant = json.dumps(user, sort_keys=True, ensure_ascii=False)

        if "restants" not in user:
            user["restants"] = 0

        if "vip" not in user:
            user["vip"] = False

        if "code" not in user:
            user["code"] = generer_code_unique(data)

        if "telegram_id" not in user:
            user["telegram_id"] = int(uid) if str(uid).isdigit() else None

        if "banned" not in user:
            user["banned"] = False

        normaliser_limite_journaliere(user)

        if "messages" in user and not isinstance(user["messages"], list):
            user["messages"] = []

        historique = user.get("historique_signaux", [])
        if not isinstance(historique, list):
            historique = []
        user["historique_signaux"] = historique[-HISTORIQUE_LIMIT:]

        normaliser_signaux_restants(user)

        apres = json.dumps(user, sort_keys=True, ensure_ascii=False)
        if apres != avant:
            modifie = True

    if modifie:
        sauvegarder_users(data)

    return data

def peut_obtenir_signal(user):
    if limite_journaliere_atteinte(user):
        return False
    if abonnement_actif(user):
        return True
    return normaliser_signaux_restants(user) > 0

def generer_code_unique(data):
    # s'assure d'unicité dans 'data'
    codes_existants = {user.get("code") for user in data.values() if isinstance(user, dict)}
    while True:
        code = "".join(random.choices(string.ascii_uppercase + string.digits, k=6))
        if code not in codes_existants:
            return code

def trouver_uid_par_code(data, code_cible):
    return next(
        (
            uid
            for uid, user in data.items()
            if isinstance(user, dict) and user.get("code") == code_cible
        ),
        None,
    )

# NOTE: Changement principal ici : associer_ou_creer_user ne crée PLUS d'utilisateur "libre" sans code.
# Il ne permet que :
# - l'association d'un code existant à un Telegram ID (première connexion),
# - ou retourne des statuts indiquant 'no_account'/'invalid_code'/'device_locked'/'ok'/'banned'.
def associer_ou_creer_user(user_id, code_cible=None):
    data = migrer_si_besoin(charger_users())
    uid = str(user_id)
    code_cible = code_cible.upper() if code_cible else None

    # Si un code est fourni : tenter d'associer
    if code_cible:
        uid_code = trouver_uid_par_code(data, code_cible)
        # Si le code n'existe pas : invalide
        if uid_code is None:
            return data, uid, "invalid_code", None

        # Si le code correspond déjà au même user numeric (rare), ok
        if uid_code == uid:
            user = data[uid]
            ancien_telegram_id = telegram_id_enregistre(user)
            if ancien_telegram_id and ancien_telegram_id != user_id:
                journaliser_securite("tentative_connexion", code_cible, user_id, ancien_telegram_id)
                return data, uid, "device_locked", ancien_telegram_id
            if user.get("banned", False):
                return data, uid, "banned", None
            # ensure telegram_id set
            if user.get("telegram_id") is None:
                user["telegram_id"] = user_id
                user["first_connection"] = user.get("first_connection") or datetime.datetime.now().isoformat()
                user["invitation_used"] = True
                sauvegarder_users(data)
                journaliser_securite("connexion", user.get("code", code_cible), user_id)
            return data, uid, "ok", None

        # Si code trouvé sous une autre clé (typiquement la clé est le code)
        user_code = data[uid_code]
        ancien_telegram_id = telegram_id_enregistre(user_code)
        if ancien_telegram_id and ancien_telegram_id != user_id:
            journaliser_securite("tentative_connexion", code_cible, user_id, ancien_telegram_id)
            return data, uid_code, "device_locked", ancien_telegram_id

        # Associer désormais le compte au nouvel uid (string of telegram id)
        user_code["telegram_id"] = user_id
        user_code["first_connection"] = user_code.get("first_connection") or datetime.datetime.now().isoformat()
        user_code["invitation_used"] = True
        # Déplacer sous la clé uid numérique
        data[uid] = user_code
        try:
            del data[uid_code]
        except KeyError:
            pass
        sauvegarder_users(data)
        journaliser_securite("connexion", user_code.get("code", code_cible), user_id)
        return data, uid, "ok", None

    # Si aucun code fourni : ne PAS créer d'utilisateur.
    # On vérifie uniquement si le uid existe déjà (compte déjà associé)
    if uid not in data:
        return data, uid, "no_account", None

    # uid existe :
    user = data[uid]
    ancien_telegram_id = telegram_id_enregistre(user)
    if ancien_telegram_id and ancien_telegram_id != user_id:
        journaliser_securite("tentative_connexion", user.get("code", "?"), user_id, ancien_telegram_id)
        return data, uid, "device_locked", ancien_telegram_id

    if ancien_telegram_id is None:
        user["telegram_id"] = user_id
        sauvegarder_users(data)

    if user.get("banned", False):
        return data, uid, "banned", None

    return data, uid, "ok", None

# Après changement : get_ou_creer_user devient simple récupérateur. Les validations d'accès se font
# dans controler_acces_client (via associer_ou_creer_user)
def get_ou_creer_user(user_id, code_cible=None):
    data = migrer_si_besoin(charger_users())  # recharge à chaque appel
    uid = str(user_id)
    return data, uid

def sauvegarder_message_id(user_id, message_id):
    data = charger_users()
    uid = str(user_id)
    if uid in data:
        data[uid].setdefault("messages", []).append(message_id)
        sauvegarder_users(data)

def consommer_signal(user_id, signal_txt=None):
    data = charger_users()
    uid = str(user_id)
    if uid not in data:
        return {"restants": 0, "mode": "inconnu", "illimite": False}

    user = data[uid]
    appliquer_expiration_si_necessaire(user)
    if limite_journaliere_atteinte(user):
        sauvegarder_users(data)
        return {"restants": user.get("restants"), "mode": "limite_journaliere", "illimite": abonnement_actif(user)}

    if abonnement_actif(user):
        user["dernier_signal"] = maintenant_crash().timestamp()
        user["illimite"] = True
        utilises, limite, active = normaliser_limite_journaliere(user)
        if active:
            user["daily_used"] = min(limite, utilises + 1)
        if signal_txt:
            ajouter_historique_signal(user, signal_txt, "abonnement")
        sauvegarder_users(data)
        return {"restants": None, "mode": "abonnement", "illimite": True}

    restants = normaliser_signaux_restants(user)
    if restants <= 0:
        sauvegarder_users(data)
        return {"restants": 0, "mode": "vip" if user.get("vip") else "gratuit", "illimite": False}

    if user.get("vip"):
        vip_signals = max(0, normaliser_signaux_vip(user) - 1)
        user["vip_signals"] = vip_signals
        user["restants"] = vip_signals
        mode = "vip"
        restants_apres = vip_signals
    else:
        gratuits = max(0, normaliser_signaux_gratuits(user) - 1)
        user["signaux_gratuits_restants"] = gratuits
        user["restants"] = gratuits
        mode = "gratuit"
        restants_apres = gratuits

    user["dernier_signal"] = maintenant_crash().timestamp()
    utilises, limite, active = normaliser_limite_journaliere(user)
    if active:
        user["daily_used"] = min(limite, utilises + 1)
    if signal_txt:
        ajouter_historique_signal(user, signal_txt, mode)
    sauvegarder_users(data)
    return {"restants": restants_apres, "mode": mode, "illimite": False}

def get_secondes_restantes(user):
    dernier = timestamp_ou_none(user.get("dernier_signal"))
    if not dernier:
        return 0
    ecoule = maintenant_crash().timestamp() - dernier
    return max(0, int(COOLDOWN_SECONDS - ecoule))

def formater_date(ts):
    ts = timestamp_ou_none(ts) or maintenant_crash().timestamp()
    return datetime.datetime.fromtimestamp(ts, tz=timezone_crash()).strftime("%d/%m/%Y")

def parser_date_expiration(texte):
    try:
        date_expiration = datetime.datetime.strptime((texte or "").strip(), "%d/%m/%Y")
    except ValueError:
        return None
    return date_expiration.replace(hour=23, minute=59, second=59, microsecond=0)

def jours_restants_jusqua(ts, maintenant=None):
    ts = timestamp_ou_none(ts)
    if not ts:
        return 0
    maintenant = maintenant or datetime.datetime.now()
    return max(0, (datetime.datetime.fromtimestamp(ts) - maintenant).days)

def formater_heure_signal(dt):
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone_crash())
    return dt.astimezone(timezone_crash()).strftime("%H:%M")

def niveau_depuis_coefficient(coefficient):
    if coefficient >= 9:
        return "Très élevé"
    if coefficient >= 8:
        return "Élevé"
    return "Premium"

def texte_compteur_compte(user):
    limite = texte_limite_journaliere(user)
    if abonnement_actif(user):
        return (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Compte Premium</b>\n\n"
            "🎟 Signaux restants\n"
            "♾️ Illimité\n\n"
            f"{limite}\n"
            "━━━━━━━━━━━━━━"
        )

    restants = normaliser_signaux_restants(user)
    if user.get("vip"):
        return (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Compte Premium</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{restants}</b>\n\n"
            f"{limite}\n"
            "━━━━━━━━━━━━━━"
        )

    if restants > 0:
        return (
            "━━━━━━━━━━━━━━\n"
            "🆓 <b>Compte gratuit</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{restants}</b>\n"
            "━━━━━━━━━━━━━━"
        )

    return (
        "❌ Vous avez épuisé vos signaux gratuits.\n\n"
        "💎 Contactez l'administrateur pour recharger votre compte."
    )

def texte_expiration(user):
    if normaliser_signaux_gratuits(user) <= 0:
        return (
            "❌ Votre abonnement VIP a expiré.\n\n"
            "Vous avez épuisé vos signaux gratuits.\n\n"
            "💎 Contactez l'administrateur."
        )

    return (
        "❌ Votre abonnement VIP a expiré.\n\n"
        f"⚡ Il vous reste <b>{normaliser_signaux_gratuits(user)}</b> signaux gratuits."
    )

def ajouter_historique_signal(user, signal_txt, statut):
    historique = user.setdefault("historique_signaux", [])
    historique.append(
        {
            "date": datetime.datetime.now().isoformat(timespec="seconds"),
            "statut": statut,
            "signal": signal_txt,
        }
    )
    user["historique_signaux"] = historique[-HISTORIQUE_LIMIT:]

def memoriser_signal_interne(coefficient):
    with signal_history_lock:
        derniers_signaux_generes.append(float(coefficient))
        del derniers_signaux_generes[:-SIGNAL_MEMORY_LIMIT]

def derniers_multiplicateurs(user, limite=SIGNAL_MEMORY_LIMIT):
    valeurs = []
    for entree in user.get("historique_signaux", [])[-limite:]:
        signal = entree.get("signal", "")
        match = re.search(r"Multiplicateur</b>\n<code>([0-9]+(?:\.[0-9]+)?)x</code>", signal)
        if match:
            try:
                valeurs.append(float(match.group(1)))
            except ValueError:
                continue
    with signal_history_lock:
        valeurs.extend(derniers_signaux_generes[-limite:])
    return valeurs

def opportunite_marche_disponible(user):
    historique = user.get("historique_signaux", [])
    maintenant = datetime.datetime.now()
    refus_probability = OPPORTUNITE_REFUS_PROBABILITY
    dernieres_minutes = 0

    for entree in historique[-10:]:
        try:
            date_signal = datetime.datetime.fromisoformat(entree.get("date", ""))
        except (TypeError, ValueError):
            continue
        if (maintenant - date_signal).total_seconds() <= 180:
            dernieres_minutes += 1

    if dernieres_minutes >= 3:
        refus_probability += 0.02
    if maintenant.minute in {0, 1, 29, 30, 31, 58, 59}:
        refus_probability += 0.01

    return random.random() >= min(refus_probability, 0.10)

def barre_progression(pourcentage):
    blocs = max(0, min(10, round(pourcentage / 10)))
    return f"{'\u2588' * blocs}{'\u2591' * (10 - blocs)} {pourcentage}%"

def texte_analyse(etape, pourcentage, titres=None):
    titres = titres or [
        "\U0001f680 Connexion au serveur Crash...",
        "\U0001f4ca Analyse des derniers Crash...",
        "🇷🇺 СИСТЕМА АКТИВНА - Système actif.",
        "\U0001f9e0 Calcul du multiplicateur...",
        "\u2699\ufe0f Validation du signal...",
        "\u2705 🇷🇺 АНАЛИЗ ЗАВЕРШЁН - Analyse termin\u00e9e.",
    ]
    total = len(titres)
    points = "\u25cf" * (etape + 1) + "\u25cb" * max(0, total - etape - 1)
    return (
        "\u2501" * 22 + "\n"
        "\U0001f4a5 <b>ANALYSE CRASH AI</b>\n"
        + "\u2501" * 22 + "\n\n"
        f"{titres[min(etape, total - 1)]}\n\n"
        f"<code>{points}</code>\n\n"
        f"<code>{barre_progression(pourcentage)}</code>"
    )

async def lancer_animation_analyse(query, user_id):
    total = random.uniform(ANALYSE_MIN_SECONDS, ANALYSE_MAX_SECONDS)
    etapes = random.choice(
        [
            [20, 45, 70, 100],
            [30, 60, 90, 100],
            [15, 40, 68, 88, 100],
            [25, 50, 75, 100],
        ]
    )
    titres_disponibles = [
        "\U0001f680 Connexion au serveur Crash...",
        "🇷🇺 ПОДОЖДИТЕ - Veuillez patienter.",
        "\U0001f4e1 Synchronisation des données...",
        "\U0001f4ca Analyse des derniers Crash...",
        "\U0001f9e0 Calcul du multiplicateur...",
        "\u2699\ufe0f Vérification des probabilités...",
        "\U0001f4c8 Analyse des tendances...",
        "\U0001f50d Recherche d'une opportunité...",
    ]
    titres = random.sample(titres_disponibles, k=len(etapes) - 1) + ["\u2705 🇷🇺 СИГНАЛ ГОТОВ - Signal prêt."]
    poids = [1 / (len(etapes) - 1)] * (len(etapes) - 1)
    variations = [random.uniform(0.85, 1.15) for _ in poids]
    delais = [poids[i] * variations[i] for i in range(len(poids))]
    facteur = total / sum(delais)

    message = await query.message.reply_text(
        texte_analyse(0, etapes[0], titres),
        parse_mode=ParseMode.HTML,
    )
    sauvegarder_message_id(user_id, message.message_id)

    for index in range(1, len(etapes)):
        await asyncio.sleep(delais[index - 1] * facteur)
        try:
            await message.edit_text(
                texte_analyse(index, etapes[index], titres),
                parse_mode=ParseMode.HTML,
            )
        except TelegramError:
            logger.info("Impossible de mettre à jour l'animation d'analyse.")

    return message

def generer_multiplicateur_pondere_crash():
    """Distribution : 1.50–2.00x (45%) | 2.00–2.50x (30%) | 2.50–3.50x (17%) | 3.50–5.00x (8%)"""
    plages = [
        (1.50, 2.00, 0.45),
        (2.00, 2.50, 0.30),
        (2.50, 3.50, 0.17),
        (3.50, 5.00, 0.08),
    ]
    poids = [p[2] for p in plages]
    plage_index = random.choices(range(len(plages)), weights=poids, k=1)[0]
    low, high, _ = plages[plage_index]
    return round(random.uniform(low, high), 2)

def generer_assurance_crash(coefficient):
    """Assurance 1.50–4.00x, jamais > coefficient"""
    return round(random.uniform(1.50, min(4.00, coefficient)), 2)

def delai_signal_crash(coefficient):
    """2–5 min selon coefficient"""
    c = float(coefficient) if isinstance(coefficient, (int, float)) else 0
    if c >= 4.00: return 2
    if c >= 3.00: return 3
    if c >= 2.00: return 4
    return 5

def generer_signal(user=None):
    heure_date = maintenant_crash()
    coefficient_number = generer_multiplicateur_pondere_crash()
    assurance = generer_assurance_crash(coefficient_number)
    minutes = delai_signal_crash(coefficient_number)
    heure_date = heure_date + datetime.timedelta(minutes=minutes)

    message = (
        "━━━━━━━━━━━━━━━━━━\n"
        "💥 <b>CRASH AI</b>\n"
        "🇷🇺 <b>СИГНАЛ ГОТОВ</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "🎯 <b>Multiplicateur</b>\n"
        f"<code>{coefficient_number:.2f}x</code>\n\n"
        "🛡 <b>Assurance</b>\n"
        f"<code>{assurance:.2f}x</code>\n\n"
        "🕒 <b>Heure</b>\n"
        f"<code>{formater_heure_signal(heure_date)}</code>\n\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "✅ 🇷🇺 <b>АНАЛИЗ ЗАВЕРШЁН</b>\n"
        "Analyse terminée\n"
        "━━━━━━━━━━━━━━━━━━"
    )
    return message, True

def texte_restant_apres_signal(user, etat):
    if etat.get("illimite"):
        ligne = "👑 Il vous reste ♾️ signaux VIP."
    elif etat.get("mode") == "vip":
        restants = entier_positif(etat.get("restants", 0))
        ligne = f"👑 Il vous reste {restants} signaux VIP."
    else:
        restants = entier_positif(etat.get("restants", 0))
        ligne = f"🎟 Il vous reste {restants} signaux."

    utilises, limite, active = normaliser_limite_journaliere(user)
    if active:
        ligne += f"\n\n📅 Limite quotidienne\n{utilises} / {limite} utilisés aujourd'hui"
    return ligne

# ===== MENUS RESTRUCTURÉS =====

def bouton_signal(restants=None, vip=False, illimite=False):
    if illimite:
        label = "\U0001f4a5 Obtenir un signal (\u221e)"
    elif restants is not None:
        label = f"\U0001f4a5 Obtenir un signal ({restants})"
    else:
        label = "\U0001f4a5 Obtenir un signal"

    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton(label, callback_data="signal")],
            [InlineKeyboardButton("\U0001f464 Mon compte", callback_data="compte_menu")],
            [InlineKeyboardButton("\U0001f48e VIP & Support", callback_data="vip_menu")],
        ]
    )

def bouton_compte():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("\U0001f4ca Mes signaux", callback_data="historique")],
            [InlineKeyboardButton("\U0001f4c5 Mon abonnement", callback_data="abonnement")],
            [InlineKeyboardButton("\U0001f511 Mon code", callback_data="code")],
            [InlineKeyboardButton("\u2b05\ufe0f Retour", callback_data="retour")],
        ]
    )

def bouton_vip_menu():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("\U0001f6d2 Acheter un pack", callback_data="vip")],
            [InlineKeyboardButton("\U0001f4de Support", callback_data="support")],
            [InlineKeyboardButton("\u2b05\ufe0f Retour", callback_data="retour")],
        ]
    )

def bouton_vip():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("💎 Acheter un pack", callback_data="vip")],
            [InlineKeyboardButton("📞 Support", callback_data="support")],
            [InlineKeyboardButton("ℹ️ Mon code", callback_data="code")],
            [InlineKeyboardButton("⬅️ Retour", callback_data="retour")],
        ]
    )

def bouton_vip_pack():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📞 Support", callback_data="support")],
            [InlineKeyboardButton("⬅️ Retour", callback_data="vip_menu")],
        ]
    )

# ===== FONCTION POUR REMPLACER LES MESSAGES =====

async def remplacer_message(query, texte, markup=None):
    try:
        await query.message.delete()
    except TelegramError:
        logger.info("Impossible de supprimer le message précédent.")
    
    return await query.message.chat.send_message(
        text=texte,
        reply_markup=markup,
        parse_mode=ParseMode.HTML,
    )

async def modifier_message(query, texte, markup=None):
    try:
        return await query.message.edit_text(
            text=texte,
            reply_markup=markup,
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.info("Impossible de modifier le message. Envoi d'un nouveau message.")
        return await query.message.chat.send_message(
            text=texte,
            reply_markup=markup,
            parse_mode=ParseMode.HTML,
        )

def handler_securise(func):
    @wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        try:
            if not await controler_acces_client(update, context):
                return None
            return await func(update, context)
        except Exception as exc:
            logger.exception("Erreur dans %s", func.__name__, exc_info=exc)
            try:
                if update.callback_query:
                    await update.callback_query.answer("Une erreur est survenue. Réessaie dans quelques secondes.", show_alert=False)
                elif update.effective_message:
                    await update.effective_message.reply_text("⚠️ Une erreur est survenue. Réessaie dans quelques secondes.")
            except TelegramError:
                logger.exception("Impossible d'envoyer le message d'erreur à l'utilisateur.")
            return None

    return wrapper

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    logger.exception("Erreur Telegram non interceptée.", exc_info=context.error)

def est_admin(update: Update):
    username = update.effective_user.username if update.effective_user else None
    return username == ADMIN_USERNAME

async def refuser_non_admin(update: Update):
    if update.effective_message:
        await update.effective_message.reply_text("❌ Commande réservée à l'administrateur.", parse_mode=ParseMode.HTML)

async def envoyer_message_acces(update: Update, texte):
    if update.callback_query:
        await update.callback_query.answer()
        try:
            await update.callback_query.message.edit_text(texte, parse_mode=ParseMode.HTML)
        except TelegramError:
            await update.callback_query.message.reply_text(texte, parse_mode=ParseMode.HTML)
    elif update.effective_message:
        await update.effective_message.reply_text(texte, parse_mode=ParseMode.HTML)

async def notifier_tentative_connexion(context: ContextTypes.DEFAULT_TYPE, code, ancien_telegram_id, nouveau_telegram_id):
    admin_id = get_admin_id()
    if not admin_id:
        return

    try:
        await context.bot.send_message(
            chat_id=admin_id,
            text=(
                "🚨 <b>Tentative de connexion détectée</b>\n\n"
                f"<b>Code :</b>\n<code>{echapper_html_texte(code)}</code>\n\n"
                f"<b>Ancien Telegram ID :</b>\n<code>{echapper_html_texte(ancien_telegram_id)}</code>\n\n"
                f"<b>Nouveau Telegram ID :</b>\n<code>{echapper_html_texte(nouveau_telegram_id)}</code>\n\n"
                f"<b>Date :</b>\n{echapper_html_texte(date_heure_securite())}"
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier l'administrateur de la tentative de connexion.")

# CONTROL D'ACCES PRINCIPAL
async def controler_acces_client(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    - Si message /start CODE : tenter d'associer le code (même si admin).
    - Sinon : admin => accès (bypass).
    - Si utilisateur déjà associé (telegram_id présent) => accès.
    - Sinon : bloqué et affiche le message d'accès privé.
    """
    # Récupérer code si présent dans /start (on veut traiter l'association en priorité)
    code_start = None
    if update.effective_message and update.effective_message.text:
        morceaux = update.effective_message.text.split()
        if morceaux and morceaux[0].split("@")[0].lower() == "/start" and len(morceaux) > 1:
            code_start = morceaux[1].upper()

    user_id = update.effective_user.id if update.effective_user else None

    # Si on a un code dans le start => tenter d'associer (TOUJOURS, même pour l'admin)
    if code_start and user_id is not None:
        data, uid, statut, ancien = associer_ou_creer_user(user_id, code_cible=code_start)
        if statut == "invalid_code":
            await envoyer_message_acces(
                update,
                "❌ L'invitation fournie est invalide.\n\nVeuillez contacter l'administrateur.",
            )
            return False
        if statut == "device_locked":
            await envoyer_message_acces(
                update,
                "❌ Ce lien d'invitation est déjà utilisé.\n\nVeuillez contacter l'administrateur.",
            )
            await notifier_tentative_connexion(context, code_start, ancien, user_id)
            return False
        if statut == "banned":
            await envoyer_message_acces(
                update,
                "🚫 Votre accès a été suspendu.\n\nVeuillez contacter l'administrateur.",
            )
            return False
        if statut == "ok":
            return True
        # tout autre statut => refuser
        await envoyer_message_acces(
            update,
            "❌ Accès refusé. Veuillez contacter l'administrateur.",
        )
        return False

    # Pas de code fourni : admin bypass (accès immédiat)
    if not update.effective_user or est_admin(update):
        return True

    # Pas de code fourni et pas admin : vérifier si l'utilisateur est déjà associé
    data = migrer_si_besoin(charger_users())
    uid = str(user_id)
    if uid in data:
        user = data[uid]
        if user.get("banned", False):
            await envoyer_message_acces(update, "🚫 Votre accès a été suspendu.\n\nVeuillez contacter l'administrateur.")
            return False
        return True

    # Sinon : accès privé (aucun menu, aucun bouton)
    private_msg = (
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "🔒 ACCÈS PRIVÉ\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "Ce bot est réservé aux clients autorisés.\n\n"
        "Veuillez contacter l'administrateur afin d'obtenir votre invitation.\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━"
    )
    await envoyer_message_acces(update, private_msg)
    return False
@handler_securise
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    # à ce stade controler_acces_client a déjà permis l'accès (admin, user existant, ou association par code)
    data, uid = get_ou_creer_user(user_id)
    # s'il n'existe pas dans data (rare si controler_acces_client a autorisé mais ...)
    if uid not in data:
        # sécurité : refuse
        await update.message.reply_text(
            "❌ Accès introuvable. Contacter l'administrateur.",
            parse_mode=ParseMode.HTML,
        )
        return

    user = data[uid]
    expire = appliquer_expiration_si_necessaire(user)
    normaliser_signaux_restants(user)
    if expire:
        sauvegarder_users(data)

    code = user.get("code", "?")
    journaliser_securite("connexion", code, user_id)
    vip = user.get("vip", False)
    restants = user.get("restants", 0)
    illimite = abonnement_actif(user)

    if expire:
        texte = f"{texte_expiration(user)}\n\n🔑 Code client : <code>{echapper_html_texte(code)}</code>"
        markup = bouton_vip() if restants <= 0 else bouton_signal(restants=restants)
    elif illimite:
        vip_debut = user.get("vip_debut")
        vip_fin = user.get("vip_fin")
        jours_restants = jours_restants_jusqua(vip_fin)
        texte = (
            "━━━━━━━━━━━━━━━━━━\n"
            "👑 <b>ESPACE VIP PREMIUM</b>\n"
            "🇷🇺 <b>СИСТЕМА АКТИВНА</b>\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            f"🔑 Code client : <code>{echapper_html_texte(code)}</code>\n\n"
            f"📅 Début : <b>{echapper_html_texte(formater_date(vip_debut))}</b>\n"
            f"📆 Expire le : <b>{echapper_html_texte(formater_date(vip_fin))}</b>\n"
            f"⏳ Jours restants : <b>{jours_restants} jour{'s' if jours_restants > 1 else ''}</b>\n\n"
            f"{texte_compteur_compte(user)}\n\n"
            "🎰 Lance une analyse pour obtenir le prochain signal."
            "\n🇷🇺 Сигнал будет готов après l'analyse."
        )
        markup = bouton_signal(vip=vip, illimite=True)
    else:
        texte = (
            "━━━━━━━━━━━━━━━━━━\n"
            "💥 <b>CRASH AI PREMIUM</b>\n"
            "🇷🇺 <b>СИСТЕМА АКТИВНА</b>\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            f"🔑 Code client : <code>{echapper_html_texte(code)}</code>\n\n"
            f"{texte_compteur_compte(user)}\n\n"
            "💥 Appuie sur le bouton pour lancer une analyse."
            "\n🇷🇺 Сигнал будет готов après l'analyse."
        )
        markup = bouton_signal(restants=restants, vip=vip) if restants > 0 else bouton_vip()

    msg = await update.message.reply_text(texte, reply_markup=markup, parse_mode=ParseMode.HTML)
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def clean(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    data, uid = get_ou_creer_user(user_id)
    message_ids = data[uid].get("messages", [])

    supprime = 0
    for mid in message_ids:
        try:
            await context.bot.delete_message(chat_id=update.effective_chat.id, message_id=mid)
            supprime += 1
        except TelegramError:
            logger.info("Message déjà supprimé ou inaccessible: %s", mid)

    data[uid]["messages"] = []
    sauvegarder_users(data)

    try:
        await update.message.delete()
    except TelegramError:
        logger.info("Impossible de supprimer la commande /clean.")

    if supprime > 0:
        msg = await context.bot.send_message(
            chat_id=update.effective_chat.id,
            text=f"🧹 {supprime} message{'s' if supprime > 1 else ''} supprimé{'s' if supprime > 1 else ''} !",
            parse_mode=ParseMode.HTML,
        )
        sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def mon_code(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    data, uid = get_ou_creer_user(user_id)
    await update.message.reply_text(
        f"🔑 Ton code client est : <code>{echapper_html_texte(data[uid]['code'])}</code>\n\nDonne ce code à l'admin pour recharger tes signaux.",
        parse_mode=ParseMode.HTML,
    )

def bouton_choix_limite_journaliere():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("❌ Non", callback_data="daily_limit_no")],
            [InlineKeyboardButton("✅ Oui", callback_data="daily_limit_yes")],
        ]
    )

def bouton_type_client_abonnement():
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("Nouveau client", callback_data="subscription_client_new")],
            [InlineKeyboardButton("Ancien client", callback_data="subscription_client_old")],
        ]
    )

def bouton_confirmation_abonnement():
    return InlineKeyboardMarkup(
        [
            [
                InlineKeyboardButton("✅ Confirmer", callback_data="subscription_confirm_yes"),
                InlineKeyboardButton("❌ Annuler", callback_data="subscription_confirm_no"),
            ]
        ]
    )

async def demander_limite_journaliere(update, code_cible, operation, nombre=None):
    details = f"\n\nSignaux : <b>{nombre}</b>" if nombre is not None else ""
    await update.message.reply_text(
        "1️⃣ <b>Limitation quotidienne ?</b>\n\n"
        "📊 Voulez-vous appliquer une limitation quotidienne ?\n\n"
        f"Client : <code>{echapper_html_texte(code_cible)}</code>{details}",
        parse_mode=ParseMode.HTML,
        reply_markup=bouton_choix_limite_journaliere(),
    )

async def appliquer_recharge_admin(context, admin_chat_id, code_cible, nombre, limite_jour=None):
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await context.bot.send_message(
            chat_id=admin_chat_id,
            text=f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.",
            parse_mode=ParseMode.HTML,
        )
        return

    user_cible = data[uid_cible]
    user_cible["restants"] = nombre
    user_cible["vip_signals"] = nombre
    user_cible["illimite"] = False
    user_cible.pop("vip_debut", None)
    user_cible.pop("vip_fin", None)
    configurer_limite_journaliere(user_cible, limite_jour)
    sauvegarder_users(data)

    limite_txt = (
        f"\n📅 Limite quotidienne : <b>{limite_jour}</b> signal{'s' if limite_jour and limite_jour > 1 else ''} / jour"
        if limite_jour
        else "\n📅 Limite quotidienne : <b>Non activée</b>"
    )
    await context.bot.send_message(
        chat_id=admin_chat_id,
        text=(
            f"✅ Client <code>{echapper_html_texte(code_cible)}</code> rechargé avec <b>{nombre}</b> signal{'s' if nombre > 1 else ''} VIP.\n"
            f"👑 Il lui reste maintenant <b>{nombre}</b> signaux VIP."
            f"{limite_txt}"
        ),
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(
                "🎉 Bonne nouvelle !\n\n"
                "Tes signaux VIP ont été rechargés par l'administrateur.\n"
                f"👑 Il vous reste <b>{nombre}</b> signaux VIP."
                f"{limite_txt}\n\n"
                "Appuie sur /start pour continuer."
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)

    try:
        admin_chat = await context.bot.get_chat(admin_chat_id)
        admin_name = getattr(admin_chat, "full_name", None) or getattr(admin_chat, "username", None) or str(admin_chat_id)
    except Exception:
        admin_name = str(admin_chat_id)

    price_fcfa = calculer_prix_recharge(nombre)
    journaliser_recharge(code_cible, nombre, admin_name, price_fcfa=price_fcfa)

    notif = (
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "💰 <b>NOUVELLE RECHARGE</b>\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"👤 Client : {echapper_html_texte(code_cible)}\n\n"
        f"📦 Pack :\n{int(nombre)} signaux\n\n"
        f"💵 Montant :\n{format_fcfa(price_fcfa)} FCFA\n\n"
        f"👨‍💼 Effectuée par :\n{echapper_html_texte(admin_name)}\n\n"
        f"🕒 Heure :\n{echapper_html_texte(datetime.datetime.now().strftime('%H:%M'))}\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━"
    )

    await _envoyer_notification_groupe(context, notif)

async def appliquer_abonnement_admin(context, admin_chat_id, pending):
    code_cible = pending.get("code")
    limite_active = bool(pending.get("limite_active", True))
    limite_jour = entier_positif(pending.get("limite_jour", 0)) if limite_active else None
    type_client = pending.get("type_client", "nouveau")
    debut_ts = timestamp_ou_none(pending.get("debut_ts"))
    fin_ts = timestamp_ou_none(pending.get("fin_ts"))

    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await context.bot.send_message(
            chat_id=admin_chat_id,
            text=f"\u274c Aucun client trouve avec le code <code>{echapper_html_texte(code_cible)}</code>.",
            parse_mode=ParseMode.HTML,
        )
        return

    if limite_active and (not limite_jour or limite_jour <= 0):
        await context.bot.send_message(
            chat_id=admin_chat_id,
            text="Abonnement annule : la limite quotidienne est obligatoire.",
            parse_mode=ParseMode.HTML,
        )
        return

    maintenant = datetime.datetime.now()
    if debut_ts and fin_ts:
        debut = datetime.datetime.fromtimestamp(debut_ts)
        fin = datetime.datetime.fromtimestamp(fin_ts)
    else:
        debut = maintenant
        fin = maintenant + datetime.timedelta(days=30)
        debut_ts = debut.timestamp()
        fin_ts = fin.timestamp()

    jours_restants = max(0, (fin.date() - maintenant.date()).days)
    type_label = "Ancien client" if type_client == "ancien" else "Nouveau client"
    user_cible = data[uid_cible]
    normaliser_signaux_gratuits(user_cible)
    user_cible["vip"] = True
    user_cible["illimite"] = True
    user_cible["vip_debut"] = debut_ts
    user_cible["vip_fin"] = fin_ts
    user_cible["vip_signals"] = 0
    user_cible["restants"] = None
    user_cible["abonnement_type_client"] = type_client
    user_cible["abonnement_jours_restants_activation"] = jours_restants
    historique_abonnements = user_cible.setdefault("historique_abonnements", [])
    historique_abonnements.append(
        {
            "type_client": type_client,
            "date_debut_originale": debut.strftime("%d/%m/%Y"),
            "date_expiration_originale": fin.strftime("%d/%m/%Y"),
            "jours_restants_activation": jours_restants,
            "limite_jour": limite_jour,
            "limite_active": limite_active,
            "enregistre_le": maintenant.isoformat(timespec="seconds"),
        }
    )
    user_cible["historique_abonnements"] = historique_abonnements[-HISTORIQUE_LIMIT:]
    configurer_limite_journaliere(user_cible, limite_jour if limite_active else None)
    sauvegarder_users(data)

    limite_txt = (
        f"\n\U0001f4ca Limite quotidienne : <b>{limite_jour}</b> signal{'s' if limite_jour > 1 else ''} / jour"
        if limite_active
        else "\n\U0001f4ca Limitation : <b>Aucune</b>"
    )
    duree_txt = "30 jours" if type_client == "nouveau" else f"{jours_restants} jours restants"
    titre_admin = "ABONNEMENT RESTAURE" if type_client == "ancien" else "ABONNEMENT ACTIVE"
    type_admin_txt = f"\U0001f451 Type : <b>{type_label}</b>\n" if limite_active else ""
    texte_admin = (
        f"\U0001f451 <b>{titre_admin}</b>\n\n"
        f"\U0001f464 Client : <code>{echapper_html_texte(code_cible)}</code>\n"
        f"{type_admin_txt}"
        f"{limite_txt}\n"
        "\U0001f3af Signaux : <b>Illimites</b>\n"
        f"\U0001f4c5 Duree : <b>{duree_txt}</b>\n\n"
        f"\U0001f4c5 Debut : <b>{debut.strftime('%d/%m/%Y')}</b>\n"
        f"\U0001f4c5 Expiration : <b>{fin.strftime('%d/%m/%Y')}</b>\n"
        f"\u23f3 Jours restants : <b>{jours_restants}</b>\n\n"
        "\u2705 Abonnement active avec succes."
    )
    await context.bot.send_message(
        chat_id=admin_chat_id,
        text=texte_admin,
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(
                "\U0001f389 Ton abonnement <b>VIP</b> est active ! \U0001f451\n\n"
                f"\U0001f4c5 Debut : <b>{debut.strftime('%d/%m/%Y')}</b>\n"
                f"\U0001f4c5 Expiration : <b>{fin.strftime('%d/%m/%Y')}</b>\n"
                f"\u23f3 Jours restants : <b>{jours_restants}</b>\n"
                "\u267e\ufe0f Signaux illimites"
                f"{limite_txt}\n\n"
                "Tape /start pour voir ton abonnement."
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)

    try:
        admin_chat = await context.bot.get_chat(admin_chat_id)
        admin_name = getattr(admin_chat, "full_name", None) or getattr(admin_chat, "username", None) or str(admin_chat_id)
    except Exception:
        admin_name = str(admin_chat_id)

    price_fcfa = ABONNEMENT_PRICE
    journaliser_abonnement(code_cible, admin_name, duree_jours=jours_restants, price_fcfa=price_fcfa)

    notif = (
        "----------------------\n\n"
        "\U0001f451 <b>NOUVEL ABONNEMENT</b>\n\n"
        "----------------------\n\n"
        f"\U0001f464 Client : {echapper_html_texte(code_cible)}\n\n"
        f"Type :\n{type_label}\n\n"
        f"Duree restante :\n{jours_restants} jours\n\n"
        f"Limite :\n{limite_jour if limite_active else 'Aucune'}{(' signaux/jour' if limite_active else '')}\n\n"
        f"\U0001f4b5 Montant :\n{format_fcfa(price_fcfa)} FCFA\n\n"
        f"\U0001f552 Heure :\n{echapper_html_texte(datetime.datetime.now().strftime('%H:%M'))}\n\n"
        "----------------------"
    )

    await _envoyer_notification_groupe(context, notif)

# --- NOUVELLE COMMANDE ADMIN : /createclient ---
@handler_securise
async def createclient_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Génère automatiquement un client (code + enregistrement DB ou JSON fallback) et renvoie le lien d'invitation.
    """
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    # Charger et migrer les users (s'assurer qu'il n'y a pas de doublon)
    data = migrer_si_besoin(charger_users())

    # Générer code unique
    code = generer_code_unique(data)
    maintenant = datetime.datetime.now().isoformat()

    # Créer l'entrée utilisateur associée au code (clé = code). Telegram ID = None
    data[code] = {
        "restants": SIGNAUX_DEFAUT,
        "vip": False,
        "code": code,
        "telegram_id": None,
        "banned": False,
        "gratuits_deja_donnes": True,
        "signaux_gratuits_restants": SIGNAUX_DEFAUT,
        "vip_signals": 0,
        "illimite": False,
        "historique_signaux": [],
        "messages": [],
        "created_at": maintenant,
        "first_connection": None,
        "invitation_used": False,
    }

    ok = safe_sauvegarder_users(data)
    if not ok:
        await update.message.reply_text(
            "❌ Erreur lors de l'enregistrement du client. Vérifiez les logs.",
            parse_mode=ParseMode.HTML,
        )
        return

    # Construction du lien d'invitation en utilisant le nom du bot
    try:
        bot_username = context.bot.username
    except Exception:
        bot_username = None

    if bot_username:
        lien = f"https://t.me/{bot_username}?start={code}"
    else:
        lien = f"https://t.me/YourBotUsername?start={code}"

    texte = (
        "✅ Nouveau client créé\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "👤 Code client\n\n"
        f"{code}\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "🔗 Lien d'invitation\n\n"
        f"{lien}\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━"
    )

    logger.info("Nouveau client créé: code=%s par uid=%s", code, getattr(update.effective_user, "id", None))
    await update.message.reply_text(texte, parse_mode=ParseMode.HTML)
@handler_securise
async def recharger(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)

    if len(context.args) < 2 or not context.args[1].isdigit():
        await update.message.reply_text(
            "Usage : <code>/recharge CODE NOMBRE</code>\nExemple : <code>/recharge ABC123 250</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    code_cible = context.args[0].upper()
    nombre = int(context.args[1])
    if nombre <= 0 or nombre > 100000:
        await update.message.reply_text("❌ Nombre de signaux invalide.", parse_mode=ParseMode.HTML)
        return

    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)

    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    user_cible = data[uid_cible]
    if appliquer_expiration_si_necessaire(user_cible):
        sauvegarder_users(data)
        await update.message.reply_text(
            "⚠️ L'abonnement de ce client était expiré et vient d'être retiré automatiquement.\n\n"
            "Activez d'abord le VIP classique avec :\n\n"
            "<code>/vip CODE</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    if not user_cible.get("vip", False):
        await update.message.reply_text(
            "❌ Ce client n'est pas VIP.\n\n"
            "Activez d'abord le VIP avec :\n\n"
            "<code>/vip CODE</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    if abonnement_actif(user_cible):
        await update.message.reply_text(
            "ℹ️ Ce client possède déjà un abonnement VIP illimité actif.\n\n"
            "La commande /recharge est réservée aux packs VIP classiques.",
            parse_mode=ParseMode.HTML,
        )
        return

    context.user_data["daily_limit_pending"] = {
        "operation": "recharge",
        "code": code_cible,
        "nombre": nombre,
    }
    await demander_limite_journaliere(update, code_cible, "recharge", nombre=nombre)
    return

@handler_securise
async def clients(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    data = migrer_si_besoin(charger_users())
    if not data:
        await update.message.reply_text("Aucun client enregistré.", parse_mode=ParseMode.HTML)
        return

    lignes = ["👥 <b>Liste des clients :</b>\n"]
    for user in data.values():
        if not isinstance(user, dict):
            continue

        normaliser_signaux_restants(user)
        code = user.get("code", "?")
        if abonnement_actif(user):
            vip_debut = user.get("vip_debut")
            vip_fin = user.get("vip_fin")
            jours_restants = jours_restants_jusqua(vip_fin)
            limite = texte_limite_journaliere(user).replace("\n", " : ")
            ligne = (
                f"💎 <code>{echapper_html_texte(code)}</code> — Abonnement VIP illimité\n"
                f"   💳 Début : {echapper_html_texte(formater_date(vip_debut))}\n"
                f"   📆 Expire le : {echapper_html_texte(formater_date(vip_fin))} ({jours_restants}j restants)\n"
                f"   {limite}"
            )
        elif user.get("vip"):
            restants = normaliser_signaux_vip(user)
            limite = texte_limite_journaliere(user).replace("\n", " : ")
            ligne = f"👑 <code>{echapper_html_texte(code)}</code> — VIP classique — {restants} signal{'s' if restants > 1 else ''} VIP — {limite}"
        else:
            restants = normaliser_signaux_gratuits(user)
            ligne = f"🆓 <code>{echapper_html_texte(code)}</code> — Gratuit — {restants} signal{'s' if restants > 1 else ''} gratuit{'s' if restants > 1 else ''}"
        lignes.append(ligne)

    await update.message.reply_text("\n".join(lignes), parse_mode=ParseMode.HTML)

@handler_securise
async def activer_vip_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/vip CODE</code>\nEx: <code>/vip A3K9F2</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)

    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    user_cible = data[uid_cible]
    normaliser_signaux_gratuits(user_cible)
    user_cible["vip"] = True
    user_cible["illimite"] = False
    user_cible["vip_signals"] = normaliser_signaux_vip(user_cible)
    user_cible["restants"] = user_cible["vip_signals"]
    user_cible.pop("vip_debut", None)
    user_cible.pop("vip_fin", None)
    sauvegarder_users(data)
    await update.message.reply_text(
        f"✅ Client <code>{echapper_html_texte(code_cible)}</code> est maintenant VIP classique 👑\nLe client peut maintenant recevoir des recharges de signaux.",
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(
                "🎉 Félicitations !\n\n"
                "👑 Votre compte VIP est maintenant activé.\n"
                "L'administrateur peut maintenant recharger votre compte selon le pack acheté.\n\n"
                "Tapez /start pour continuer."
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)

@handler_securise
async def abonnement_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/abonnement CODE</code>\nEx: <code>/abonnement A3K9F2</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)

    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    context.user_data["daily_limit_pending"] = {
        "operation": "abonnement",
        "code": code_cible,
    }
    await demander_limite_journaliere(update, code_cible, "abonnement")
    return

@handler_securise
async def desactiver_vip_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/devip CODE</code>\nEx: <code>/devip A3K9F2</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)

    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    gratuits = remettre_en_mode_gratuit(data[uid_cible])
    sauvegarder_users(data)
    statut = (
        f"⚡ Il reste <b>{gratuits}</b> signal{'s' if gratuits > 1 else ''} gratuit{'s' if gratuits > 1 else ''}."
        if gratuits > 0
        else "❌ Vous avez épuisé vos signaux gratuits.\n\n💎 Contactez l'administrateur pour recharger votre compte."
    )
    await update.message.reply_text(
        f"✅ Statut VIP retiré au client <code>{echapper_html_texte(code_cible)}</code>.\n\n{statut}",
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=f"⚠️ Votre statut VIP a été retiré.\n\n{statut}",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)

@handler_securise
async def desabonner_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/desabo CODE</code>\nEx: <code>/desabo A3K9F2</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)

    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    gratuits = remettre_en_mode_gratuit(data[uid_cible])
    sauvegarder_users(data)
    statut = (
        f"⚡ Il reste <b>{gratuits}</b> signal{'s' if gratuits > 1 else ''} gratuit{'s' if gratuits > 1 else ''}."
        if gratuits > 0
        else "❌ Vous avez épuisé vos signaux gratuits.\n\n💎 Contactez l'administrateur."
    )
    await update.message.reply_text(
        f"✅ Abonnement mensuel coupé pour <code>{echapper_html_texte(code_cible)}</code>.\n\n{statut}",
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(

                "⚠️ Ton abonnement mensuel VIP a été désactivé.\n\n"
                f"{statut}\n\n"
                f"Pour renouveler, contacte l'admin : {admin_username_html()}"
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)

@handler_securise
async def resetdevice_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/resetdevice CODE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    data[uid_cible].pop("telegram_id", None)
    sauvegarder_users(data)
    await update.message.reply_text(
        f"✅ Appareil réinitialisé pour <code>{echapper_html_texte(code_cible)}</code>.\n\n"
        "Le prochain utilisateur qui lance <code>/start CODE</code> pourra associer ce compte.",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def ban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/ban CODE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    data[uid_cible]["banned"] = True
    sauvegarder_users(data)
    await update.message.reply_text(f"✅ Client <code>{echapper_html_texte(code_cible)}</code> banni.", parse_mode=ParseMode.HTML)
    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text="🚫 Votre accès a été suspendu.\n\nVeuillez contacter l'administrateur.",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client banni %s.", uid_cible)

@handler_securise
async def unban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/unban CODE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    data[uid_cible]["banned"] = False
    sauvegarder_users(data)
    await update.message.reply_text(f"✅ Client <code>{echapper_html_texte(code_cible)}</code> débanni.", parse_mode=ParseMode.HTML)

@handler_securise
async def info_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/info CODE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    user = data[uid_cible]
    appliquer_expiration_si_necessaire(user)
    normaliser_signaux_restants(user)
    sauvegarder_users(data)

    try:
        chat = await context.bot.get_chat(int(uid_cible))
        nom = chat.full_name or chat.username or "Inconnu"
    except TelegramError:
        nom = "Inconnu"

    if abonnement_actif(user):
        statut = "VIP"
        pack = "Abonnement mensuel"
        signaux = "Illimité"
    elif user.get("vip"):
        statut = "VIP"
        pack = "Pack VIP classique"
        signaux = normaliser_signaux_vip(user)
    else:
        statut = "FREE"
        pack = "Gratuit"
        signaux = normaliser_signaux_gratuits(user)

    vip_debut = user.get("vip_debut")
    vip_fin = user.get("vip_fin")
    texte = (
        "━━━━━━━━━━━━━━━━━━\n"
        "👤 <b>CLIENT</b>\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        f"<b>Nom Telegram</b>\n{echapper_html_texte(nom)}\n\n"
        f"<b>Code client</b>\n<code>{echapper_html_texte(code_cible)}</code>\n\n"
        f"<b>Telegram ID</b>\n<code>{echapper_html_texte(user.get('telegram_id') or uid_cible)}</code>\n\n"
        f"<b>Statut</b>\n{statut}\n\n"
        f"<b>Nombre de signaux</b>\n{echapper_html_texte(signaux)}\n\n"
        f"<b>Pack actuel</b>\n{echapper_html_texte(pack)}\n\n"
        f"<b>Limite quotidienne</b>\n{texte_limite_journaliere(user).replace(chr(10), ' : ')}\n\n"
        f"<b>Date de début</b>\n{echapper_html_texte(formater_date(vip_debut) if vip_debut else '-')}\n\n"
        f"<b>Date d'expiration</b>\n{echapper_html_texte(formater_date(vip_fin) if vip_fin else '-')}\n\n"
        f"<b>Jours restants</b>\n{jours_restants_jusqua(vip_fin) if vip_fin else 0}\n\n"
        f"<b>Compte banni</b>\n{'Oui' if user.get('banned', False) else 'Non'}\n\n"
        "━━━━━━━━━━━━━━━━━━"
    )
    await update.message.reply_text(texte, parse_mode=ParseMode.HTML)

@handler_securise
async def addsignal_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if len(context.args) < 2 or not context.args[1].isdigit():
        await update.message.reply_text("Usage : <code>/addsignal CODE NOMBRE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    nombre = int(context.args[1])
    if nombre <= 0 or nombre > 100000:
        await update.message.reply_text("❌ Nombre de signaux invalide.", parse_mode=ParseMode.HTML)
        return

    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    user = data[uid_cible]
    appliquer_expiration_si_necessaire(user)
    actuel = normaliser_signaux_vip(user) if user.get("vip") else 0
    total = actuel + nombre
    normaliser_signaux_gratuits(user)
    user["vip"] = True
    user["illimite"] = False
    user["vip_signals"] = total
    user["restants"] = total
    user.pop("vip_debut", None)
    user.pop("vip_fin", None)
    sauvegarder_users(data)

    await update.message.reply_text(
        f"✅ <b>{nombre}</b> signal{'s' if nombre > 1 else ''} ajouté{'s' if nombre > 1 else ''} au client <code>{echapper_html_texte(code_cible)}</code>.\n"
        f"Il lui reste maintenant <b>{total}</b> signaux.",
        parse_mode=ParseMode.HTML,
    )
    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(

                "━━━━━━━━━━━━━━━━━━\n"
                "🎉 <b>Recharge effectuée</b>\n"
                "━━━━━━━━━━━━━━━━━━\n\n"
                "L'administrateur vient de vous ajouter :\n\n"
                f"🎟 <b>{nombre}</b> signaux.\n\n"
                "Il vous reste :\n\n"
                f"🎟 <b>{total}</b> signaux.\n\n"
                "Bonne utilisation.\n\n"
                "━━━━━━━━━━━━━━━━━━"
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s pour l'ajout de signaux.", uid_cible)

@handler_securise
async def reset_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    if not context.args:
        await update.message.reply_text("Usage : <code>/reset CODE</code>", parse_mode=ParseMode.HTML)
        return

    code_cible = context.args[0].upper()
    data = migrer_si_besoin(charger_users())
    uid_cible = trouver_uid_par_code(data, code_cible)
    if uid_cible is None:
        await update.message.reply_text(f"❌ Aucun client trouvé avec le code <code>{echapper_html_texte(code_cible)}</code>.", parse_mode=ParseMode.HTML)
        return

    data[uid_cible] = {
        "restants": SIGNAUX_DEFAUT,
        "vip": False,
        "code": code_cible,
        "gratuits_deja_donnes": True,
        "signaux_gratuits_restants": SIGNAUX_DEFAUT,
        "vip_signals": 0,
        "illimite": False,
        "historique_signaux": [],
        "messages": [],
        "banned": False,
    }
    sauvegarder_users(data)
    await update.message.reply_text(
        f"✅ Client <code>{echapper_html_texte(code_cible)}</code> réinitialisé complètement.",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def broadcast_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    context.user_data["broadcast_waiting"] = True
    await update.message.reply_text("✍️ Envoyez le message à diffuser.", parse_mode=ParseMode.HTML)

async def finaliser_action_limite_journaliere(context, chat_id, pending, limite_jour=None):
    operation = pending.get("operation")
    code_cible = pending.get("code")
    if operation == "recharge":
        await appliquer_recharge_admin(context, chat_id, code_cible, int(pending.get("nombre", 0)), limite_jour)
    elif operation == "abonnement":
        pending["limite_jour"] = limite_jour
        await demander_type_client_abonnement(context, chat_id, pending)

async def demander_type_client_abonnement(context, chat_id, pending):
    await context.bot.send_message(
        chat_id=chat_id,
        text=(
            "Type de client ?\n\n"
            f"Client : <code>{echapper_html_texte(pending.get('code'))}</code>\n"
            f"Limite : <b>{pending.get('limite_jour')}</b> signaux/jour"
        ),
        parse_mode=ParseMode.HTML,
        reply_markup=bouton_type_client_abonnement(),
    )

def parser_date_abonnement_debut(texte):
    try:
        date_debut = datetime.datetime.strptime((texte or "").strip(), "%d/%m/%Y")
    except ValueError:
        return None
    return date_debut.replace(hour=0, minute=0, second=0, microsecond=0)

def texte_confirmation_abonnement(pending):
    debut = datetime.datetime.fromtimestamp(timestamp_ou_none(pending.get("debut_ts")))
    fin = datetime.datetime.fromtimestamp(timestamp_ou_none(pending.get("fin_ts")))
    jours_restants = max(0, (fin.date() - datetime.datetime.now().date()).days)
    type_label = "Ancien client" if pending.get("type_client") == "ancien" else "Nouveau client"
    return (
        f"\U0001f464 Client : <code>{echapper_html_texte(pending.get('code'))}</code>\n\n"
        f"\U0001f451 Type : <b>{type_label}</b>\n\n"
        f"\U0001f4c5 Debut : <b>{debut.strftime('%d/%m/%Y')}</b>\n\n"
        f"\U0001f4c5 Expiration : <b>{fin.strftime('%d/%m/%Y')}</b>\n\n"
        f"\u23f3 Jours restants : <b>{jours_restants}</b>\n\n"
        f"\U0001f4ca Limite : <b>{pending.get('limite_jour')}</b> signaux/jour\n\n"
        "Confirmer ?"
    )

async def demander_confirmation_abonnement(context, chat_id, pending):
    await context.bot.send_message(
        chat_id=chat_id,
        text=texte_confirmation_abonnement(pending),
        parse_mode=ParseMode.HTML,
        reply_markup=bouton_confirmation_abonnement(),
    )

@handler_securise
async def choix_limite_journaliere_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    query = update.callback_query
    await query.answer()
    pending = context.user_data.get("daily_limit_pending")
    if not pending:
        await query.edit_message_text("Aucune action en attente.", parse_mode=ParseMode.HTML)
        return

    if query.data == "daily_limit_no":
        context.user_data.pop("daily_limit_pending", None)
        if pending.get("operation") == "abonnement":
            maintenant = datetime.datetime.now()
            fin = maintenant + datetime.timedelta(days=30)
            pending.update(
                {
                    "limite_active": False,
                    "limite_jour": None,
                    "type_client": "nouveau",
                    "debut_ts": maintenant.timestamp(),
                    "fin_ts": fin.timestamp(),
                }
            )
            await query.edit_message_text(
                "Limitation quotidienne desactivee. Activation de l'abonnement en cours...",
                parse_mode=ParseMode.HTML,
            )
            await appliquer_abonnement_admin(context, query.message.chat_id, pending)
            return
        await query.edit_message_text("Limitation quotidienne desactivee. Application en cours...", parse_mode=ParseMode.HTML)
        await finaliser_action_limite_journaliere(context, query.message.chat_id, pending, limite_jour=None)
        return

    context.user_data["daily_limit_waiting_number"] = True
    await query.edit_message_text(
        "Combien de signaux maximum par jour ?\n\n"
        "Exemple : <code>5</code>",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def choix_type_client_abonnement_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    query = update.callback_query
    await query.answer()
    pending = context.user_data.get("daily_limit_pending")
    if not pending or pending.get("operation") != "abonnement":
        await query.edit_message_text("Aucun abonnement en attente.", parse_mode=ParseMode.HTML)
        return

    if query.data == "subscription_client_new":
        maintenant = datetime.datetime.now()
        fin = maintenant + datetime.timedelta(days=30)
        pending["type_client"] = "nouveau"
        pending["debut_ts"] = maintenant.timestamp()
        pending["fin_ts"] = fin.timestamp()
        context.user_data["daily_limit_pending"] = pending
        await query.edit_message_text(
            "Nouveau client selectionne. Verification finale...",
            parse_mode=ParseMode.HTML,
        )
        await demander_confirmation_abonnement(context, query.message.chat_id, pending)
        return

    pending["type_client"] = "ancien"
    context.user_data["daily_limit_pending"] = pending
    context.user_data["subscription_old_start_waiting"] = True
    await query.edit_message_text(
        "Envoyez la date de debut de l'ancien abonnement au format <code>JJ/MM/AAAA</code>.\n\n"
        "Exemple : <code>01/08/2026</code>",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def confirmation_abonnement_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    query = update.callback_query
    await query.answer()
    pending = context.user_data.get("daily_limit_pending")
    context.user_data.pop("subscription_old_start_waiting", None)
    context.user_data.pop("subscription_old_end_waiting", None)

    if not pending or pending.get("operation") != "abonnement":
        await query.edit_message_text("Aucun abonnement en attente.", parse_mode=ParseMode.HTML)
        return

    if query.data == "subscription_confirm_no":
        context.user_data.pop("daily_limit_pending", None)
        await query.edit_message_text("Abonnement annule. Aucune donnee enregistree.", parse_mode=ParseMode.HTML)
        return

    context.user_data.pop("daily_limit_pending", None)
    await query.edit_message_text("Confirmation recue. Enregistrement en cours...", parse_mode=ParseMode.HTML)
    await appliquer_abonnement_admin(context, query.message.chat_id, pending)

@handler_securise
async def limite_journaliere_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.user_data.get("daily_limit_waiting_number"):
        return False
    if not est_admin(update):
        await refuser_non_admin(update)
        return True

    texte = (update.message.text or "").strip()
    if not texte.isdigit():
        await update.message.reply_text("Envoyez uniquement un nombre. Exemple : <code>5</code>", parse_mode=ParseMode.HTML)
        return True

    limite_jour = int(texte)
    if limite_jour <= 0 or limite_jour > 100000:
        await update.message.reply_text("Limite quotidienne invalide.", parse_mode=ParseMode.HTML)
        return True

    pending = context.user_data.get("daily_limit_pending")
    context.user_data.pop("daily_limit_waiting_number", None)
    if not pending:
        await update.message.reply_text("Aucune action en attente.", parse_mode=ParseMode.HTML)
        return True

    if pending.get("operation") != "abonnement":
        context.user_data.pop("daily_limit_pending", None)
    await finaliser_action_limite_journaliere(context, update.effective_chat.id, pending, limite_jour=limite_jour)
    return True

@handler_securise
async def date_abonnement_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    waiting_start = context.user_data.get("subscription_old_start_waiting")
    waiting_end = context.user_data.get("subscription_old_end_waiting")
    if not waiting_start and not waiting_end:
        return False
    if not est_admin(update):
        await refuser_non_admin(update)
        return True

    pending = context.user_data.get("daily_limit_pending")
    if not pending or pending.get("operation") != "abonnement":
        context.user_data.pop("subscription_old_start_waiting", None)
        context.user_data.pop("subscription_old_end_waiting", None)
        await update.message.reply_text("Aucun abonnement en attente.", parse_mode=ParseMode.HTML)
        return True

    if waiting_start:
        debut = parser_date_abonnement_debut(update.message.text)
        if debut is None:
            await update.message.reply_text(
                "Date invalide. Envoyez une date au format <code>JJ/MM/AAAA</code>.\n\n"
                "Exemple : <code>01/08/2026</code>",
                parse_mode=ParseMode.HTML,
            )
            return True
        pending["debut_ts"] = debut.timestamp()
        context.user_data["daily_limit_pending"] = pending
        context.user_data.pop("subscription_old_start_waiting", None)
        context.user_data["subscription_old_end_waiting"] = True
        await update.message.reply_text(
            "Envoyez la date d'expiration de l'ancien abonnement au format <code>JJ/MM/AAAA</code>.\n\n"
            "Exemple : <code>05/09/2026</code>",
            parse_mode=ParseMode.HTML,
        )
        return True

    expiration = parser_date_expiration(update.message.text)
    if expiration is None:
        await update.message.reply_text(
            "Date invalide. Envoyez une date au format <code>JJ/MM/AAAA</code>.\n\n"
            "Exemple : <code>05/09/2026</code>",
            parse_mode=ParseMode.HTML,
        )
        return True

    context.user_data.pop("subscription_old_end_waiting", None)
    if timestamp_ou_none(pending.get("debut_ts")) is None:
        await update.message.reply_text("Date de debut manquante. Relancez <code>/abonnement CODE</code>.", parse_mode=ParseMode.HTML)
        context.user_data.pop("daily_limit_pending", None)
        return True

    pending["fin_ts"] = expiration.timestamp()
    context.user_data["daily_limit_pending"] = pending
    await demander_confirmation_abonnement(context, update.effective_chat.id, pending)
    return True

@handler_securise
async def broadcast_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if await limite_journaliere_message(update, context):
        return
    if await date_abonnement_message(update, context):
        return
    if not context.user_data.get("broadcast_waiting"):
        return
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    context.user_data["broadcast_waiting"] = False
    data = migrer_si_besoin(charger_users())
    envoyes = 0
    echecs = 0

    for uid, user in data.items():
        if not isinstance(user, dict) or user.get("banned", False):
            continue
        try:
            await context.bot.send_message(
                chat_id=int(user.get("telegram_id") or uid),
                text=update.message.text,
            )
            envoyes += 1
        except TelegramError:
            echecs += 1
        except (TypeError, ValueError):
            echecs += 1

    await update.message.reply_text(
        "━━━━━━━━━━━━━━━━━━\n"
        "📢 <b>Diffusion terminée</b>\n\n"
        f"Envoyé :\n<b>{envoyes}</b> utilisateurs\n\n"
        f"Échec :\n<b>{echecs}</b> utilisateurs\n"
        "━━━━━━━━━━━━━━━━━━",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    data = migrer_si_besoin(charger_users())
    utilisateurs = [u for u in data.values() if isinstance(u, dict)]
    total = len(utilisateurs)
    abonnements = sum(1 for u in utilisateurs if abonnement_actif(u))
    vip_classiques = sum(1 for u in utilisateurs if u.get("vip") and not abonnement_actif(u))
    gratuits = total - abonnements - vip_classiques
    limites_actives = sum(1 for u in utilisateurs if normaliser_limite_journaliere(u)[2])

    bientot = []
    maintenant = datetime.datetime.now()
    for user in utilisateurs:
        if abonnement_actif(user) and user.get("vip_fin"):
            jours = jours_restants_jusqua(user["vip_fin"], maintenant=maintenant)
            if 0 <= jours <= 3:
                bientot.append((user.get("code", "?"), jours))

    texte = (
        "📊 Statistiques du bot :\n\n"
        f"👥 Total clients : {total}\n"
        f"💎 Abonnements VIP illimités : {abonnements}\n"
        f"👑 VIP classiques : {vip_classiques}\n"
        f"🆓 Membres gratuits : {gratuits}\n"
        f"📅 Limites quotidiennes actives : {limites_actives}"
    )
    if bientot:
        texte += "\n\n⚠️ <b>Abonnements qui expirent bientôt :</b>"
        for code, jours in bientot:
            texte += f"\n• <code>{echapper_html_texte(code)}</code> — expire dans {jours} jour{'s' if jours > 1 else ''}"

    await update.message.reply_text(texte, parse_mode=ParseMode.HTML)

@handler_securise
async def admin_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not est_admin(update):
        await refuser_non_admin(update)
        return

    sauvegarder_admin_id(update.effective_user.id)
    await update.message.reply_text(
        "🛠 Commandes admin disponibles :\n\n"
        "<code>/clients</code> — Liste tous les clients et leur statut\n"
        "<code>/stats</code> — Statistiques générales du bot\n"
        "<code>/recharge CODE NOMBRE</code> — Recharge un VIP classique\n"
        "<code>/vip CODE</code> — Active le VIP classique, sans signaux automatiques\n"
        "<code>/devip CODE</code> — Retire le statut VIP d'un client\n"
        "<code>/abonnement CODE</code> — Abonnement VIP illimité 30j\n"
        "<code>/desabo CODE</code> — Coupe l'abonnement mensuel d'un client\n"
        "<code>/resetdevice CODE</code> — Réinitialise le Telegram ID associé\n"
        "<code>/ban CODE</code> — Bannit définitivement un client\n"
        "<code>/unban CODE</code> — Retire le bannissement\n"
        "<code>/info CODE</code> — Affiche la fiche complète du client\n"
        "<code>/addsignal CODE NOMBRE</code> — Ajoute des signaux au solde\n"
        "<code>/reset CODE</code> — Réinitialise complètement un client\n"
        "<code>/broadcast</code> — Diffuse un message à tous les utilisateurs\n"
        "<code>/createclient</code> — Crée automatiquement un client et génère le lien d'invitation\n"
        "<code>/admin</code> — Affiche ce menu",
        parse_mode=ParseMode.HTML,
    )

@handler_securise
async def bouton_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    uid = str(user_id)

    with analyses_lock:
        if uid in analyses_en_cours:
            deja_en_cours = True
        else:
            analyses_en_cours.add(uid)
            deja_en_cours = False

    if deja_en_cours:
        await query.answer("⏳ Une analyse est déjà en cours.", show_alert=False)
        msg = await query.message.reply_text(
            "⏳ Une analyse est déjà en cours.\n\nPatiente quelques secondes...",
            parse_mode=ParseMode.HTML,
        )
        sauvegarder_message_id(user_id, msg.message_id)
        return

    try:
        await query.answer()
        data, uid = get_ou_creer_user(user_id)
        user = data[uid]

        expire = appliquer_expiration_si_necessaire(user)
        normaliser_signaux_restants(user)
        if expire:
            sauvegarder_users(data)
            msg = await remplacer_message(
                query,
                texte_expiration(user),
                bouton_vip() if user.get("restants", 0) <= 0 else bouton_signal(restants=user.get("restants", 0)),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        etat_planning = planning_crash()
        if not etat_planning["actif"]:
            msg = await remplacer_message(
                query,
                texte_mise_a_jour_crash(etat_planning),
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        attente = get_secondes_restantes(user)
        if attente > 0:
            msg = await remplacer_message(
                query,
                "⏳ <b>Le robot termine l'analyse précédente.</b>\n\n"
                "Temps restant :\n\n"
                f"<b>{attente} seconde{'s' if attente > 1 else ''}.</b>",
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if limite_journaliere_atteinte(user):
            sauvegarder_users(data)
            msg = await remplacer_message(
                query,
                texte_limite_atteinte(),
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if not peut_obtenir_signal(user):
            msg = await remplacer_message(
                query,
                texte_compteur_compte(user),
                bouton_vip(),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if not opportunite_marche_disponible(user):
            msg = await remplacer_message(
                query,
                "⚠️ <b>Analyse du marché en cours...</b>\n\n"
                "Aucune opportunité détectée.\n\n"
                "Réessayez dans quelques minutes.",
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        await lancer_animation_analyse(query, user_id)

        data, uid = get_ou_creer_user(user_id)
        user = data[uid]
        expire = appliquer_expiration_si_necessaire(user)
        normaliser_signaux_restants(user)
        if expire:
            sauvegarder_users(data)
            msg = await remplacer_message(
                query,
                texte_expiration(user),
                bouton_vip() if user.get("restants", 0) <= 0 else bouton_signal(restants=user.get("restants", 0)),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        etat_planning = planning_crash()
        if not etat_planning["actif"]:
            msg = await remplacer_message(
                query,
                texte_mise_a_jour_crash(etat_planning),
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if limite_journaliere_atteinte(user):
            sauvegarder_users(data)
            msg = await remplacer_message(
                query,
                texte_limite_atteinte(),
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if not peut_obtenir_signal(user):
            msg = await remplacer_message(
                query,
                texte_compteur_compte(user),
                bouton_vip(),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        signal_txt, signal_genere = generer_signal(user)
        if not signal_txt:
            msg = await remplacer_message(
                query,
                "⚠️ Impossible de générer une prédiction pour le moment.\n\nRéessaie dans quelques instants.",
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        if not signal_genere:
            msg = await remplacer_message(
                query,
                signal_txt,
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
            )
            sauvegarder_message_id(user_id, msg.message_id)
            return

        etat = consommer_signal(user_id, signal_txt=signal_txt)
        data_apres = charger_users()
        user_apres = data_apres.get(uid, user)
        if etat["illimite"]:
            texte = f"{signal_txt}\n\n{texte_restant_apres_signal(user_apres, etat)}"
            markup = bouton_signal(vip=True, illimite=True)
        elif etat["mode"] == "vip":
            restants_apres = etat["restants"]
            if restants_apres > 0:
                texte = f"{signal_txt}\n\n{texte_restant_apres_signal(user_apres, etat)}"
                markup = bouton_signal(restants=restants_apres, vip=True)
            else:
                texte = (
                    f"{signal_txt}\n\n"
                    "⚠️ <b>Dernier signal VIP utilisé.</b>\n"
                    "💎 Contactez l'administrateur pour recharger votre compte."
                )
                markup = bouton_vip()
        else:
            restants_apres = etat["restants"]
            if restants_apres > 0:
                texte = f"{signal_txt}\n\n{texte_restant_apres_signal(user_apres, etat)}"
                markup = bouton_signal(restants=restants_apres)
            else:
                texte = (
                    f"{signal_txt}\n\n"
                    "❌ Vous avez épuisé vos signaux gratuits.\n\n"
                    "💎 Contactez l'administrateur pour recharger votre compte."
                )
                markup = bouton_vip()

        msg = await remplacer_message(query, texte, markup)
        sauvegarder_message_id(user_id, msg.message_id)
    finally:
        with analyses_lock:
            analyses_en_cours.discard(uid)

@handler_securise
async def compte_menu_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    
    msg = await remplacer_message(
        query,
        "👑 <b>MON COMPTE</b>\n\n"
        "Sélectionne une option :",
        bouton_compte(),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def vip_menu_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    
    msg = await modifier_message(
        query,
        "💎 <b>ESPACE VIP & SUPPORT</b>\n\n"
        "Sélectionne une option :",
        bouton_vip_menu(),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def retour_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    
    data, uid = get_ou_creer_user(user_id)
    user = data[uid]
    restants = user.get("restants", 0)
    
    msg = await remplacer_message(
        query,
        "💥 <b>MENU PRINCIPAL</b>\n\nChoisir une action :",
        bouton_signal(restants=restants, vip=user.get("vip", False), illimite=abonnement_actif(user)),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def vip_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    
    msg = await modifier_message(
        query,
        "💎 <b>PACKS VIP</b>\n\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "🥉 <b>Starter</b>\n"
        "100 signaux → 2 000 FCFA\n\n"
        "🥈 <b>Standard</b>\n"
        "250 signaux → 4 000 FCFA\n\n"
        "🥇 <b>Pro</b>\n"
        "500 signaux → 7 000 FCFA\n\n"
        "👑 <b>VIP Mensuel</b>\n"
        "♾️ Signaux illimités pendant 30 jours\n"
        "12 000 FCFA\n"
        "━━━━━━━━━━━━━━━━━━\n\n"
        "<b>💳 Paiement :</b>\n"
        "Wave / Moov Money\n\n"
        "<b>📞 Contact Admin</b>\n"
        f"{admin_username_html()}",
        bouton_vip_pack(),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def historique_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    data, uid = get_ou_creer_user(user_id)
    historique = data[uid].get("historique_signaux", [])[-4:]

    if not historique:
        texte = "\U0001f4ca <b>Derniers signaux</b>\n\nAucun signal enregistr\u00e9 pour le moment."
    else:
        lignes = ["\U0001f4ca <b>Derniers signaux</b>\n"]
        for entree in reversed(historique):
            signal = entree.get("signal", "")
            match = re.search(r"Multiplicateur</b>\n<code>([0-9]+(?:\.[0-9]+)?)x</code>", signal)
            try:
                date_signal = datetime.datetime.fromisoformat(entree.get("date", ""))
                heure = date_signal.strftime("%H:%M")
            except (TypeError, ValueError):
                heure = "--:--"
            if match:
                lignes.append(f"<code>{heure} \u2022 {echapper_html_texte(match.group(1))}x</code>")
        texte = "\n".join(lignes) if len(lignes) > 1 else "\U0001f4ca <b>Derniers signaux</b>\n\nAucun signal lisible."

    msg = await remplacer_message(query, texte, bouton_compte())
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def abonnement_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    data, uid = get_ou_creer_user(user_id)
    user = data[uid]
    appliquer_expiration_si_necessaire(user)
    normaliser_signaux_restants(user)
    sauvegarder_users(data)

    if abonnement_actif(user):
        limite = texte_limite_journaliere(user)
        texte = (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Mon abonnement</b>\n\n"
            f"📅 Début\n<b>{echapper_html_texte(formater_date(user.get('vip_debut')))}</b>\n\n"
            "🎟 Signaux\n<b>♾️ Illimité</b>\n\n"
            f"{limite}\n\n"
            f"📆 Expiration\n<b>{echapper_html_texte(formater_date(user.get('vip_fin')))}</b>\n"
            "━━━━━━━━━━━━━━"
        )
    elif user.get("vip"):
        limite = texte_limite_journaliere(user)
        texte = (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>VIP classique</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{normaliser_signaux_vip(user)}</b>\n\n"
            f"{limite}\n"
            "━━━━━━━━━━━━━━"
        )
    else:
        texte = (
            "━━━━━━━━━━━━━━\n"
            "🆓 <b>Compte gratuit</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{normaliser_signaux_gratuits(user)}</b>\n"
            "━━━━━━━━━━━━━━"
        )

    msg = await remplacer_message(query, texte, bouton_compte())
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def support_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()

    msg = await remplacer_message(
        query,
        "📞 <b>SUPPORT OFFICIEL</b>\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "<b>Besoin d'aide ?</b>\n\n"
        "Nous sommes disponibles pour :\n\n"
        "💳 Recharge de signaux\n"
        "👑 Activation VIP\n"
        "♾️ Abonnement mensuel\n"
        "❓ Questions sur le bot\n"
        "⚙️ Assistance technique\n"
        "💰 Problème de paiement\n\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
        "<b>👤 Contact de l'administrateur</b>\n\n"
        f"👉 {admin_username_html()}\n\n"
        "⏰ Réponse généralement en quelques minutes.",
        bouton_vip_menu(),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def code_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    data, uid = get_ou_creer_user(user_id)
    
    msg = await remplacer_message(
        query,
        f"ℹ️ <b>Mon code client</b>\n\n<code>{echapper_html_texte(data[uid]['code'])}</code>\n\n"
        "Ce code te permet de recharger tes signaux auprès de l'admin.",
        bouton_compte(),
    )
    sauvegarder_message_id(user_id, msg.message_id)

@handler_securise
async def effacer_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    try:
        await query.message.delete()
    except TelegramError:
        logger.info("Message déjà supprimé ou inaccessible.")

async def verifier_expirations(context: ContextTypes.DEFAULT_TYPE):
    admin_id = get_admin_id()
    data = migrer_si_besoin(charger_users())
    maintenant = datetime.datetime.now()
    expires = []

    for uid, user in data.items():
        if not isinstance(user, dict):
            continue
        if abonnement_expire(user, maintenant=maintenant):
            code = user.get("code", "?")
            date_fin = formater_date(user["vip_fin"])
            remettre_en_mode_gratuit(user)
            expires.append((uid, code, date_fin, texte_expiration(user)))

    if expires:
        sauvegarder_users(data)

    for uid, code, date_fin, message_client in expires:
        try:
            await context.bot.send_message(
                chat_id=int(uid),
                text=message_client,
                parse_mode=ParseMode.HTML,
            )
        except TelegramError:
            logger.exception("Impossible de notifier le client %s pour l'expiration.", uid)

        if admin_id:
            try:
                await context.bot.send_message(
                    chat_id=admin_id,
                    text=(
                        "⚠️ <b>Abonnement VIP expiré automatiquement !</b>\n\n"
                        f"🔑 Code client : <code>{echapper_html_texte(code)}</code>\n"
                        f"📆 Date d'expiration : <b>{echapper_html_texte(date_fin)}</b>\n\n"
                        "Le statut VIP et l'accès illimité ont été retirés."
                    ),
                    parse_mode=ParseMode.HTML,
                )
            except TelegramError:
                logger.exception("Impossible de notifier l'admin pour l'expiration %s.", code)

# --- Rapport quotidien ---
async def envoyer_rapport_journalier(context: ContextTypes.DEFAULT_TYPE):
    try:
        if not LOG_GROUP_ID:
            logger.info("LOG_GROUP_ID non configuré — rapport quotidien non envoyé.")
            return

        aujourd_hui = datetime.date.today()

        nouveaux_clients = 0
        try:
            journal_sec = charger_journal_securite()
            for ev in journal_sec:
                if ev.get("evenement") == "connexion":
                    try:
                        dt = datetime.datetime.strptime(ev.get("date", ""), "%d/%m/%Y %H:%M")
                        if dt.date() == aujourd_hui:
                            nouveaux_clients += 1
                    except Exception:
                        continue
        except Exception:
            logger.exception("Impossible de lire security_log pour le rapport quotidien.")

        recharges_count = 0
        abonnements_count = 0
        total_signaux_recharges = 0
        chiffre_affaires = 0
        try:
            ventes = charger_journal_ventes()
            for e in ventes:
                try:
                    dt = datetime.datetime.fromisoformat(e.get("date"))
                    if dt.date() != aujourd_hui:
                        continue
                except Exception:
                    continue

                if e.get("type") == "recharge":
                    recharges_count += 1
                    try:
                        total_signaux_recharges += int(e.get("signals", 0))
                    except Exception:
                        pass
                    try:
                        chiffre_affaires += int(e.get("price", 0))
                    except Exception:
                        pass
                elif e.get("type") == "abonnement":
                    abonnements_count += 1
                    try:
                        chiffre_affaires += int(e.get("price", 0))
                    except Exception:
                        pass
        except Exception:
            logger.exception("Impossible de lire sales_log pour le rapport quotidien.")

        texte = (
            "━━━━━━━━━━━━━━━━━━━━━━\n\n"
            "📊 <b>RAPPORT DE LA JOURNÉE</b>\n\n"
            "━━━━━━━━━━━━━━━━━━━━━━\n\n"
            f"👥 Nouveaux clients : {nouveaux_clients}\n\n"
            f"💰 Recharges : {recharges_count}\n\n"
            f"👑 Abonnements : {abonnements_count}\n\n"
            f"💵 Chiffre d'affaires : {format_fcfa(chiffre_affaires)} FCFA\n\n"
            "━━━━━━━━━━━━━━━━━━━━━━\n\n"
            "📈 Activité générée automatiquement\n\n"
            "━━━━━━━━━━━━━━━━━━━━━━"
        )

        await _envoyer_notification_groupe(context, texte)
    except Exception:
        logger.exception("Erreur lors de l'envoi du rapport quotidien.")
# --- Fin rapport quotidien ---

class HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.end_headers()
        self.wfile.write(b"Bot en ligne")

    def log_message(self, format, *args):
        return

def lancer_serveur():
    port = int(os.environ.get("PORT", "10000"))
    server = HTTPServer(("0.0.0.0", port), HealthHandler)
    logger.info("Serveur de santé démarré sur le port %s.", port)
    server.serve_forever()

async def supprimer_webhook(application: Application):
    await application.bot.delete_webhook(drop_pending_updates=True)
    logger.info("Webhook supprimé. Démarrage du polling.")

def creer_application():
    if not TOKEN:
        raise RuntimeError("La variable d'environnement TOKEN est obligatoire.")
    
    app = ApplicationBuilder().token(TOKEN).post_init(supprimer_webhook).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("clean", clean))
    app.add_handler(CommandHandler("moncode", mon_code))
    app.add_handler(CommandHandler("recharge", recharger))
    app.add_handler(CommandHandler("clients", clients))
    app.add_handler(CommandHandler("stats", stats))
    app.add_handler(CommandHandler("vip", activer_vip_cmd))
    app.add_handler(CommandHandler("abonnement", abonnement_cmd))
    app.add_handler(CommandHandler("devip", desactiver_vip_cmd))
    app.add_handler(CommandHandler("desabo", desabonner_cmd))
    app.add_handler(CommandHandler("resetdevice", resetdevice_cmd))
    app.add_handler(CommandHandler("ban", ban_cmd))
    app.add_handler(CommandHandler("unban", unban_cmd))
    app.add_handler(CommandHandler("info", info_cmd))
    app.add_handler(CommandHandler("addsignal", addsignal_cmd))
    app.add_handler(CommandHandler("reset", reset_cmd))
    app.add_handler(CommandHandler("broadcast", broadcast_cmd))
    app.add_handler(CommandHandler("admin", admin_help))
    # Nouvelle commande createclient
    app.add_handler(CommandHandler("createclient", createclient_cmd))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, broadcast_message))
    
    # Handlers de callback - Menu principal
    app.add_handler(CallbackQueryHandler(choix_limite_journaliere_callback, pattern="^daily_limit_(yes|no)$"))
    app.add_handler(CallbackQueryHandler(choix_type_client_abonnement_callback, pattern="^subscription_client_(new|old)$"))
    app.add_handler(CallbackQueryHandler(confirmation_abonnement_callback, pattern="^subscription_confirm_(yes|no)$"))
    app.add_handler(CallbackQueryHandler(bouton_callback, pattern="^signal$"))
    app.add_handler(CallbackQueryHandler(compte_menu_callback, pattern="^compte_menu$"))
    app.add_handler(CallbackQueryHandler(vip_menu_callback, pattern="^vip_menu$"))
    app.add_handler(CallbackQueryHandler(retour_callback, pattern="^retour$"))
    
    # Handlers de callback - Sous-menus
    app.add_handler(CallbackQueryHandler(vip_callback, pattern="^vip$"))
    app.add_handler(CallbackQueryHandler(historique_callback, pattern="^historique$"))
    app.add_handler(CallbackQueryHandler(abonnement_callback, pattern="^abonnement$"))
    app.add_handler(CallbackQueryHandler(support_callback, pattern="^support$"))
    app.add_handler(CallbackQueryHandler(code_callback, pattern="^code$"))
    app.add_handler(CallbackQueryHandler(effacer_callback, pattern="^effacer$"))
    
    app.add_error_handler(error_handler)

    if app.job_queue:
        app.job_queue.run_repeating(verifier_expirations, interval=86400, first=60)

        try:
            report_time = datetime.time(23, 59, tzinfo=datetime.timezone.utc)
            app.job_queue.run_daily(envoyer_rapport_journalier, time=report_time, name="daily_report")
            logger.info("Job quotidien d'envoi du rapport enregistré pour 23:59 UTC.")
        except Exception:
            logger.exception("Impossible d'enregistrer le job quotidien pour le rapport.")
    else:
        logger.warning("Job queue indisponible. Vérifie python-telegram-bot[job-queue] dans requirements.txt.")

    return app

def main():
    threading.Thread(target=lancer_serveur, daemon=True).start()
    app = creer_application()
    logger.info("Bot démarré.")
    app.run_polling(
        poll_interval=1.0,
        timeout=30,
        bootstrap_retries=-1,
        drop_pending_updates=True,
        allowed_updates=Update.ALL_TYPES,
    )

if __name__ == "__main__":
    main()
