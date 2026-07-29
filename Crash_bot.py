import datetime
import asyncio
import html
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

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import TelegramError
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
)


TOKEN = "8886184186:AAFYXUJ9ahtYq_V-gRU8GQj6wKrSnfJdKf4"
DATA_FILE = "users.json"
ADMIN_ID_FILE = "admin_id.json"
SIGNAUX_DEFAUT = 3
ADMIN_USERNAME = os.environ.get("ADMIN_USERNAME", "hacker_ci").lstrip("@")
COOLDOWN_SECONDS = 30
ANALYSE_MIN_SECONDS = 8
ANALYSE_MAX_SECONDS = 15
HISTORIQUE_LIMIT = 100
OPPORTUNITE_REFUS_PROBABILITY = 0.12


def admin_username_html():
    return f"@{html.escape(ADMIN_USERNAME)}"


def echapper_html_texte(texte):
    """Échappe les caractères HTML spéciaux pour une utilisation sûre en ParseMode.HTML"""
    return html.escape(str(texte), quote=True)


logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=os.environ.get("LOG_LEVEL", "INFO").upper(),
)
logger = logging.getLogger(__name__)
file_lock = threading.RLock()
json_cache = {}
analyses_lock = threading.Lock()
analyses_en_cours = set()


def lire_json(path, default):
    with file_lock:
        if path in json_cache:
            return json_cache[path]
        if not os.path.exists(path) or os.path.getsize(path) == 0:
            valeur = default.copy() if isinstance(default, dict) else default
            json_cache[path] = valeur
            return valeur
        try:
            with open(path, "r", encoding="utf-8") as f:
                valeur = json.load(f)
                json_cache[path] = valeur
                return valeur
        except (JSONDecodeError, OSError) as exc:
            logger.exception("Impossible de lire %s. Valeur par défaut utilisée.", path, exc_info=exc)
            valeur = default.copy() if isinstance(default, dict) else default
            json_cache[path] = valeur
            return valeur


def ecrire_json(path, data):
    dossier = os.path.dirname(os.path.abspath(path)) or "."
    os.makedirs(dossier, exist_ok=True)
    tmp_path = os.path.join(dossier, f".{os.path.basename(path)}.{os.getpid()}.tmp")
    with file_lock:
        json_cache[path] = data
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, path)


def get_admin_id():
    return lire_json(ADMIN_ID_FILE, {}).get("id")


def sauvegarder_admin_id(user_id):
    ecrire_json(ADMIN_ID_FILE, {"id": user_id})


def charger_users():
    return lire_json(DATA_FILE, {})


def sauvegarder_users(data):
    ecrire_json(DATA_FILE, data)


def entier_positif(valeur, defaut=0, maximum=None):
    try:
        nombre = int(valeur)
    except (TypeError, ValueError):
        nombre = defaut

    nombre = max(0, nombre)
    if maximum is not None:
        nombre = min(nombre, maximum)
    return nombre


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


def normaliser_signaux_restants(user):
    gratuits = normaliser_signaux_gratuits(user)
    vip_signals = normaliser_signaux_vip(user)

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

    for user in data.values():
        if not isinstance(user, dict):
            continue

        avant = json.dumps(user, sort_keys=True, ensure_ascii=False)

        if "restants" not in user:
            user["restants"] = 0

        if "vip" not in user:
            user["vip"] = False

        if "code" not in user:
            user["code"] = generer_code_unique(data)

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
    if abonnement_actif(user):
        return True
    return normaliser_signaux_restants(user) > 0


def generer_code_unique(data):
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


def get_ou_creer_user(user_id):
    data = migrer_si_besoin(charger_users())
    uid = str(user_id)

    if uid not in data:
        data[uid] = {
            "restants": SIGNAUX_DEFAUT,
            "vip": False,
            "code": generer_code_unique(data),
            "gratuits_deja_donnes": True,
            "signaux_gratuits_restants": SIGNAUX_DEFAUT,
            "vip_signals": 0,
            "illimite": False,
            "historique_signaux": [],
        }
        sauvegarder_users(data)

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

    if abonnement_actif(user):
        user["dernier_signal"] = datetime.datetime.now().timestamp()
        user["illimite"] = True
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

    user["dernier_signal"] = datetime.datetime.now().timestamp()
    if signal_txt:
        ajouter_historique_signal(user, signal_txt, mode)
    sauvegarder_users(data)
    return {"restants": restants_apres, "mode": mode, "illimite": False}


def get_secondes_restantes(user):
    dernier = timestamp_ou_none(user.get("dernier_signal"))
    if not dernier:
        return 0
    ecoule = datetime.datetime.now().timestamp() - dernier
    return max(0, int(COOLDOWN_SECONDS - ecoule))


def formater_date(ts):
    ts = timestamp_ou_none(ts) or datetime.datetime.now().timestamp()
    return datetime.datetime.fromtimestamp(ts).strftime("%d/%m/%Y")


def jours_restants_jusqua(ts, maintenant=None):
    ts = timestamp_ou_none(ts)
    if not ts:
        return 0
    maintenant = maintenant or datetime.datetime.now()
    return max(0, (datetime.datetime.fromtimestamp(ts) - maintenant).days)


def formater_heure_signal(dt):
    return dt.strftime("%H:%M")


def niveau_depuis_coefficient(coefficient):
    if coefficient >= 9:
        return "Très élevé"
    if coefficient >= 8:
        return "Élevé"
    return "Premium"


def texte_compteur_compte(user):
    if abonnement_actif(user):
        return (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Compte Premium</b>\n\n"
            "🎟 Signaux restants\n"
            "♾️ Illimité\n"
            "━━━━━━━━━━━━━━"
        )

    restants = normaliser_signaux_restants(user)
    if user.get("vip"):
        return (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Compte Premium</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{restants}</b>\n"
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


def derniers_multiplicateurs(user, limite=8):
    valeurs = set()
    for entree in user.get("historique_signaux", [])[-limite:]:
        signal = entree.get("signal", "")
        match = re.search(r"Multiplicateur</b>\n<code>([0-9]+(?:\.[0-9]+)?)x</code>", signal)
        if match:
            valeurs.add(match.group(1))
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
        refus_probability += 0.03
    if maintenant.minute in {0, 1, 29, 30, 31, 58, 59}:
        refus_probability += 0.02

    return random.random() >= min(refus_probability, 0.15)


def barre_progression(pourcentage):
    blocs = max(0, min(10, round(pourcentage / 10)))
    return f"{'\u2588' * blocs}{'\u2591' * (10 - blocs)} {pourcentage}%"


def texte_analyse(etape, pourcentage):
    titres = [
        "\U0001f680 Connexion au serveur Crash...",
        "\U0001f4ca Analyse des derniers Crash...",
        "\U0001f9e0 Calcul du multiplicateur...",
        "\u2699\ufe0f Validation du signal...",
        "\u2705 Analyse termin\u00e9e.",
    ]
    points = "\u25cf" * (etape + 1) + "\u25cb" * (4 - etape)
    return (
        "\u2501" * 22 + "\n"
        "\U0001f4a5 <b>ANALYSE CRASH AI</b>\n"
        + "\u2501" * 22 + "\n\n"
        f"{titres[etape]}\n\n"
        f"<code>{points}</code>\n\n"
        f"<code>{barre_progression(pourcentage)}</code>"
    )

async def lancer_animation_analyse(query, user_id):
    total = random.uniform(ANALYSE_MIN_SECONDS, ANALYSE_MAX_SECONDS)
    etapes = [10, 30, 60, 85, 100]
    poids = [0.22, 0.27, 0.25, 0.26]
    variations = [random.uniform(0.85, 1.15) for _ in poids]
    delais = [poids[i] * variations[i] for i in range(len(poids))]
    facteur = total / sum(delais)

    message = await query.message.reply_text(
        texte_analyse(0, etapes[0]),
        parse_mode=ParseMode.HTML,
    )
    sauvegarder_message_id(user_id, message.message_id)

    for index in range(1, len(etapes)):
        await asyncio.sleep(delais[index - 1] * facteur)
        try:
            await message.edit_text(
                texte_analyse(index, etapes[index]),
                parse_mode=ParseMode.HTML,
            )
        except TelegramError:
            logger.info("Impossible de mettre à jour l'animation d'analyse.")

    return message


def delai_signal_depuis_coefficient(coefficient):
    if coefficient >= 3.10:
        return 4
    if coefficient >= 2.70:
        return 5
    if coefficient >= 2.30:
        return 6
    return 7


def generer_signal(user=None):
    heure_date = datetime.datetime.now()
    heure_minute = heure_date.minute
    heure_hour = heure_date.hour

    if 16 <= heure_hour < 17:
        return "\u23f3 <b>Analyse en cours...</b>\n\nVeuillez r\u00e9essayer dans une heure.", False
    if 13 <= heure_minute < 14:
        return "\U0001f504 <b>Intervalle de jeu d\u00e9tect\u00e9.</b>\nVeuillez r\u00e9essayer dans une heure.", False

    deja_vus = derniers_multiplicateurs(user or {})
    coefficient_number = round(random.uniform(2.00, 3.50), 2)
    for _ in range(12):
        if f"{coefficient_number:.2f}" not in deja_vus:
            break
        coefficient_number = round(random.uniform(2.00, 3.50), 2)

    assurance = round(random.uniform(1.50, 2.50), 2)
    heure_date = heure_date + datetime.timedelta(minutes=delai_signal_depuis_coefficient(coefficient_number))
    separateur = "\u2501" * 22

    message = (
        f"{separateur}\n"
        "\U0001f4a5 <b>CRASH AI</b>\n"
        f"{separateur}\n\n"
        "\U0001f3af <b>Multiplicateur</b>\n"
        f"<code>{coefficient_number:.2f}x</code>\n\n"
        "\U0001f6e1 <b>Assurance</b>\n"
        f"<code>{assurance:.2f}x</code>\n\n"
        "\U0001f552 <b>Heure</b>\n"
        f"<code>{formater_heure_signal(heure_date)}</code>\n\n"
        f"{separateur}\n"
        "\u2705 <b>Signal pr\u00eat</b>\n"
        f"{separateur}"
    )
    return message, True

# ===== MENUS RESTRUCTURÉS =====

def bouton_signal(restants=None, vip=False, illimite=False):
    """Menu principal - 3 boutons seulement (compact et professionnel)"""
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
    """Sous-menu : Mon compte (3 options + retour)"""
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("\U0001f4ca Mes signaux", callback_data="historique")],
            [InlineKeyboardButton("\U0001f4c5 Mon abonnement", callback_data="abonnement")],
            [InlineKeyboardButton("\U0001f511 Mon code", callback_data="code")],
            [InlineKeyboardButton("\u2b05\ufe0f Retour", callback_data="retour")],
        ]
    )


def bouton_vip_menu():
    """Sous-menu : VIP & Support (2 options + retour)"""
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("\U0001f6d2 Acheter un pack", callback_data="vip")],
            [InlineKeyboardButton("\U0001f4de Support", callback_data="support")],
            [InlineKeyboardButton("\u2b05\ufe0f Retour", callback_data="retour")],
        ]
    )

def bouton_vip():
    """Fallback : Quand l'utilisateur n'a pas de signaux"""
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("💎 Acheter un pack", callback_data="vip")],
            [InlineKeyboardButton("📞 Support", callback_data="support")],
            [InlineKeyboardButton("ℹ️ Mon code", callback_data="code")],
        ]
    )


# ===== FONCTION POUR REMPLACER LES MESSAGES =====

async def remplacer_message(query, texte, markup=None):
    """
    Supprime le message actuel et envoie un nouveau message à sa place.
    Rend le bot très professionnel sans clutter.
    """
    try:
        await query.message.delete()
    except TelegramError:
        logger.info("Impossible de supprimer le message précédent.")
    
    return await query.message.chat.send_message(
        text=texte,
        reply_markup=markup,
        parse_mode=ParseMode.HTML,
    )


def handler_securise(func):
    @wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        try:
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


@handler_securise
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    data, uid = get_ou_creer_user(user_id)
    user = data[uid]
    expire = appliquer_expiration_si_necessaire(user)
    normaliser_signaux_restants(user)
    if expire:
        sauvegarder_users(data)

    code = user.get("code", "?")
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
            "━━━━━━━━━━━━━━━━━━\n\n"
            f"🔑 Code client : <code>{echapper_html_texte(code)}</code>\n\n"
            f"📅 Début : <b>{echapper_html_texte(formater_date(vip_debut))}</b>\n"
            f"📆 Expire le : <b>{echapper_html_texte(formater_date(vip_fin))}</b>\n"
            f"⏳ Jours restants : <b>{jours_restants} jour{'s' if jours_restants > 1 else ''}</b>\n\n"
            f"{texte_compteur_compte(user)}\n\n"
            "🎰 Lance une analyse pour obtenir le prochain signal."
        )
        markup = bouton_signal(vip=vip, illimite=True)
    else:
        texte = (
            "━━━━━━━━━━━━━━━━━━\n"
            "💥 <b>CRASH AI PREMIUM</b>\n"
            "━━━━━━━━━━━━━━━━━━\n\n"
            f"🔑 Code client : <code>{echapper_html_texte(code)}</code>\n\n"
            f"{texte_compteur_compte(user)}\n\n"
            "💥 Appuie sur le bouton pour lancer une analyse."
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

    user_cible["restants"] = nombre
    user_cible["vip_signals"] = nombre
    user_cible["illimite"] = False
    user_cible.pop("vip_debut", None)
    user_cible.pop("vip_fin", None)
    sauvegarder_users(data)

    await update.message.reply_text(
        f"✅ Client <code>{echapper_html_texte(code_cible)}</code> rechargé avec <b>{nombre}</b> signal{'s' if nombre > 1 else ''} VIP.\n"
        f"👑 Il lui reste maintenant <b>{nombre}</b> signaux VIP.",
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(
                "🎉 Bonne nouvelle !\n\n"
                "Tes signaux VIP ont été rechargés par l'administrateur.\n"
                f"👑 Il vous reste <b>{nombre}</b> signaux VIP.\n\n"
                "Appuie sur /start pour continuer."
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)


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
            ligne = (
                f"💎 <code>{echapper_html_texte(code)}</code> — Abonnement VIP illimité\n"
                f"   💳 Début : {echapper_html_texte(formater_date(vip_debut))}\n"
                f"   📆 Expire le : {echapper_html_texte(formater_date(vip_fin))} ({jours_restants}j restants)"
            )
        elif user.get("vip"):
            restants = normaliser_signaux_vip(user)
            ligne = f"👑 <code>{echapper_html_texte(code)}</code> — VIP classique — {restants} signal{'s' if restants > 1 else ''} VIP"
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

    maintenant = datetime.datetime.now()
    fin = maintenant + datetime.timedelta(days=30)
    user_cible = data[uid_cible]
    normaliser_signaux_gratuits(user_cible)
    user_cible["vip"] = True
    user_cible["illimite"] = True
    user_cible["vip_debut"] = maintenant.timestamp()
    user_cible["vip_fin"] = fin.timestamp()
    user_cible["vip_signals"] = 0
    user_cible["restants"] = None
    sauvegarder_users(data)

    await update.message.reply_text(
        f"✅ Abonnement mensuel activé pour <code>{echapper_html_texte(code_cible)}</code> 👑\n\n"
        "♾️ Signaux illimités activés immédiatement.\n\n"
        f"📅 Début : <b>{maintenant.strftime('%d/%m/%Y')}</b>\n"
        f"📆 Fin : <b>{fin.strftime('%d/%m/%Y')}</b>",
        parse_mode=ParseMode.HTML,
    )

    try:
        await context.bot.send_message(
            chat_id=int(uid_cible),
            text=(
                "🎉 Ton abonnement <b>VIP</b> est activé ! 👑\n\n"
                "━━━━━━━━━━━━━━━━━━\n"
                f"📅 Début : <b>{maintenant.strftime('%d/%m/%Y')}</b>\n"
                f"📆 Expire le : <b>{fin.strftime('%d/%m/%Y')}</b>\n"
                "⏳ Durée : <b>30 jours</b>\n"
                "♾️ Signaux illimités\n"
                "━━━━━━━━━━━━━━━━━━\n\n"
                "Tape /start pour voir ton abonnement."
            ),
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        logger.exception("Impossible de notifier le client %s.", uid_cible)


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
        f"🆓 Membres gratuits : {gratuits}"
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

        if not peut_obtenir_signal(user):
            msg = await remplacer_message(
                query,
                texte_compteur_compte(user),
                bouton_vip(),
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
                "⚠️ <b>Analyse du marché en cours.</b>\n\n"
                "Aucune opportunité fiable détectée.\n\n"
                "Réessaie dans 4 minutes.",
                bouton_signal(
                    restants=user.get("restants"),
                    vip=user.get("vip", False),
                    illimite=abonnement_actif(user),
                ),
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
        if etat["illimite"]:
            texte = f"{signal_txt}\n\n{texte_compteur_compte(user)}"
            markup = bouton_signal(vip=True, illimite=True)
        elif etat["mode"] == "vip":
            restants_apres = etat["restants"]
            if restants_apres > 0:
                texte = f"{signal_txt}\n\n{texte_compteur_compte(user)}"
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
                texte = f"{signal_txt}\n\n{texte_compteur_compte(user)}"
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
    """Affiche le sous-menu "Mon compte" """
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
    """Affiche le sous-menu "VIP & Support" """
    query = update.callback_query
    user_id = query.from_user.id
    await query.answer()
    
    msg = await remplacer_message(
        query,
        "💎 <b>ESPACE VIP & SUPPORT</b>\n\n"
        "Sélectionne une option :",
        bouton_vip_menu(),
    )
    sauvegarder_message_id(user_id, msg.message_id)


@handler_securise
async def retour_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Retour au menu principal"""
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
    
    msg = await remplacer_message(
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
        texte = (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>Mon abonnement</b>\n\n"
            f"📅 Début\n<b>{echapper_html_texte(formater_date(user.get('vip_debut')))}</b>\n\n"
            "🎟 Signaux\n<b>♾️ Illimité</b>\n\n"
            f"📆 Expiration\n<b>{echapper_html_texte(formater_date(user.get('vip_fin')))}</b>\n"
            "━━━━━━━━━━━━━━"
        )
    elif user.get("vip"):
        texte = (
            "━━━━━━━━━━━━━━\n"
            "👑 <b>VIP classique</b>\n\n"
            "🎟 Signaux restants\n"
            f"<b>{normaliser_signaux_vip(user)}</b>\n"
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
    """Affiche le message de support officiel premium"""
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
        raise RuntimeError("La variable d'environnement BOT_TOKEN est obligatoire.")
    
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
    app.add_handler(CommandHandler("admin", admin_help))
    
    # Handlers de callback - Menu principal
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
