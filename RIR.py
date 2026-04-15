import sys
import traceback
import os
import time
import threading
import base64
import zlib
import json
import re
import shutil
import ctypes
import glob
import tempfile
import urllib.request
import subprocess
import webbrowser
import tkinter as tk
import tkinter.filedialog as fd
from tkinter import ttk
from collections import deque
import math
from datetime import datetime

APP_VERSION = "13.2.0"
REPO_URL = "https://github.com/Lynamator123/RockyIdleReader"
UPDATE_MANIFEST_URL = "https://raw.githubusercontent.com/Lynamator123/RockyIdleReader/main/version.json"
DEFAULT_UPDATE_DOWNLOAD_URL = "https://raw.githubusercontent.com/Lynamator123/RockyIdleReader/main/Compiled/RockyIdleReader.exe"

# ==========================================
# CRASH HANDLER
# ==========================================
def _safe_pause_before_exit(prompt):
    try:
        if hasattr(sys, "stdin") and sys.stdin and sys.stdin.isatty():
            input(prompt)
    except Exception:
        pass


def _show_error_messagebox(title, message):
    try:
        ctypes.windll.user32.MessageBoxW(0, str(message), str(title), 0x10)
    except Exception:
        pass


def _ask_yes_no_messagebox(title, message):
    try:
        result = ctypes.windll.user32.MessageBoxW(0, str(message), str(title), 0x24)
        return result == 6
    except Exception:
        return False


def global_crash_handler(exc_type, exc_value, exc_traceback):
    error_msg = "".join(traceback.format_exception(exc_type, exc_value, exc_traceback))
    print(f"\n=== FATAL ERROR ===\n{error_msg}")
    try:
        with open("FATAL_CRASH.txt", "w") as f:
            f.write(error_msg)
    except:
        pass
    _show_error_messagebox("Rocky Idle Reader Crash", error_msg)
    _safe_pause_before_exit("\nPress Enter to exit...")
    sys.exit(1)


sys.excepthook = global_crash_handler

try:
    import customtkinter as ctk
    import pygetwindow as gw
except ImportError as e:
    missing_msg = f"Missing libraries: {e}\nRun: pip install customtkinter pygetwindow"
    print(missing_msg)
    _show_error_messagebox("Missing Libraries", missing_msg)
    _safe_pause_before_exit("Press Enter to exit...")
    sys.exit()

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")


class RIR_by_Foot(ctk.CTk):
    def __init__(self):
        super().__init__()

        # --- APP STATE ---
        self.is_closing = False
        self.is_minimized = False
        self.dev_mode = False
        self.initial_load_done = False
        self.last_known_mtime = 0
        self._last_raw_save = None
        self.prev_state = None
        self.current_debug_list = []
        self.selected_profile_id = None
        self.selected_profile_name = None
        self.selected_profile_info = {}
        self.profile_picker_open = False
        self.profile_picker_window = None
        self.last_sync_epoch = 0
        self.last_xp_notify_epoch = 0
        self.no_change_save_count = 0
        self.drift_alert_active = False
        self.event_history = deque(maxlen=200)
        self.last_recovery_signature = None
        self.recent_changed_item_ids = set()
        self.startup_started_at = time.time()
        self.startup_log_lines = []
        self.startup_timeout_ms = 5000
        self.startup_timeout_handled = False
        self.save_scan_limit = 120
        self.scan_diag_lines = deque(maxlen=600)
        self.app_version = APP_VERSION
        self.repo_url = REPO_URL
        self.update_manifest_url = UPDATE_MANIFEST_URL
        self.default_update_download_url = DEFAULT_UPDATE_DOWNLOAD_URL
        self.update_check_in_progress = False

        # --- TRACKING ENGINE ---
        self.xp_history = {}
        self.session_start_xp = {}
        self.session_gp_earned = 0.0
        self.current_levels = {}
        self.active_skills = {}
        self.stale_counts = {}
        self.save_history = deque()
        self.latest_save_data = {}
        self.latest_save_source = None
        self.current_save_source = None
        self.explorer_tree_widget = None
        self.xp_active_scan_streak = 0
        self.xp_inactive_scan_streak = 0
        self.xp_activity_armed = False
        self.xp_inactive_notified = False
        self.skill_diamond_status = {}

        # --- ITEM TRACKING ---
        self.item_history = {}
        self.stale_item_counts = {}

        # --- DISK MONITOR STATE ---
        self.file_states = {}
        self.last_disk_activity = time.time()

        self.feed_widgets = {}
        self.skill_labels = {}
        self.skill_name_labels = {}
        self.open_popouts = []
        self.latest_feed_items = []

        # --- FILES & DATA ---
        self.db_file = "skills_db.json"
        self.monster_db_file = "monster_db.json"
        self.item_db_file = "item_db.json"
        self.mining_db_file = "mining_db.json"
        self.item_meta_file = "item_meta.json"
        self.skill_tier_file = "skill_tiers.json"
        self.diary_boosters_file = "achievement_boosters.json"
        self.multipliers_file = "multipliers_snapshot.json"
        self.fresh_multipliers_file = "fresh_save_multipliers.json"
        self.skill_full_dump_file = "skill_full_dump.json"
        self.config_file = "settings.json"
        self.session_cache_file = ".rir_session_cache.json"
        self.legacy_data_store_file = "rir_data.json"
        self.data_store_file = "app_data.json"

        self.data_store = self.load_data_store()
        self.cleanup_legacy_data_files()

        self.skill_map = self.load_skill_db()
        self.monster_map = self.load_monster_db()
        self.slayer_category_map = self.load_slayer_category_map()
        self.item_map = self.load_item_db()
        self.mining_db = self.load_mining_db()
        self.item_meta = self.load_item_meta()
        self.save_item_meta()
        self.config = self.load_config()
        self.hidden_items = set(self.config.get("hidden_items", []))
        self.sidebar_collapsed = bool(self.config.get("sidebar_collapsed", False))
        self.no_slayer_task_count = 0
        self.no_slayer_task_notified = False

        # --- WINDOW SETUP ---
        self.title(f"Rocky Idle Reader v{self.app_version}")
        self.apply_topmost_setting()
        self.overrideredirect(True)

        try:
            init_x = int(self.config.get("x", 100))
            init_y = int(self.config.get("y", 100))
        except (ValueError, TypeError):
            init_x, init_y = 100, 100

        self.geometry(f"760x720+{init_x}+{init_y}")
        self.configure(fg_color="#0d1117")

        self.container = ctk.CTkFrame(self, corner_radius=14, fg_color="#0f1117", border_width=1, border_color="#21262d")
        self.container.pack(fill="both", expand=True, padx=8, pady=8)

        self.setup_main_ui()

        self.header.bind("<Button-1>", self.start_move)
        self.header.bind("<B1-Motion>", self.do_move)
        self.title_block.bind("<Button-1>", self.start_move)
        self.title_block.bind("<B1-Motion>", self.do_move)

        self.game_title = "Rocky Idle"
        self.save_folder = self.find_save_path()
        self._startup_log(f"Resolved save folder: {self.save_folder or 'None'}")

        self.refresh_tabs()
        self.restore_recent_session()
        preferred_section = self.config.get("last_section", "OVERVIEW")
        self.switch_section(preferred_section if preferred_section in self.section_frames else "OVERVIEW")
        self.toggle_sidebar(force=self.sidebar_collapsed, persist=False)
        self.update_sync_badge()

        self.after(100, self.snap_to_game)
        self.after(500, self.watchdog_loop)
        self.after(1000, self.ui_update_loop)
        self.after(200, self.disk_monitor_loop)
        self.after(self.startup_timeout_ms, self.startup_timeout_guard)
        self.after(2500, self.check_for_updates_silent)

    # --- DATABASE METHODS ---
    def _default_skill_db(self):
        return {
            "1001": "Hitpoints", "1002": "Melee", "1003": "Mining", "1005": "Smithing",
            "1006": "Defence", "1007": "Alchemy", "1008": "Fishing", "1009": "Range",
            "1010": "Thieving", "1011": "Cooking", "1012": "Prayer", "1013": "Crafting",
            "1015": "Magic", "1016": "Fletching", "1017": "Woodcutting", "1018": "Arcanery",
            "1019": "Slayer", "1020": "Farming"
        }

    def load_skill_db(self):
        data = self.get_store_section("skill_db", self._default_skill_db())
        return data if isinstance(data, dict) else self._default_skill_db()

    def _default_config(self):
        return {
            "pos": "Free Flow", "show_skills": False, "show_disk_monitor": False,
            "x": 100, "y": 100, "save_path": "", "webhook_url": "", "webhook_enabled": False,
            "notify_levels": True, "notify_slayer": True, "notify_xp": False,
            "notify_no_slayer_task": False,
            "notify_boost_ready": False,
            "xp_notify_interval_minutes": 1,
            "always_on_top": True,
            "hidden_items": [],
            "sidebar_collapsed": False,
            "last_section": "OVERVIEW",
            "density": "Comfortable",
            "skills_sort": "Rate",
            "items_sort": "GP/h",
            "restore_items_on_restart": False,
            "skills_filter": "",
            "items_filter": "",
        }

    def _resource_path(self, relative_path):
        if getattr(sys, "frozen", False):
            base = getattr(sys, "_MEIPASS", os.path.dirname(sys.executable))
        else:
            base = os.path.dirname(os.path.abspath(__file__))
        return os.path.join(base, relative_path)

    def _startup_log(self, message):
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.startup_log_lines.append(f"[{ts}] {message}")

    def _scan_diag(self, context, file_path, decision, details=""):
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        name = os.path.basename(str(file_path or "")) if file_path else "(none)"
        suffix = f" | {details}" if details else ""
        self.scan_diag_lines.append(f"[{ts}] [{context}] {name} -> {decision}{suffix}")

    def _get_profile_status_text(self):
        name = str(self.selected_profile_name or "").strip()
        profile_id = str(self.selected_profile_id or "").strip()
        if name and profile_id:
            return f"profile={name} [{profile_id}]"
        if profile_id:
            return f"profile=[{profile_id}]"
        if name:
            return f"profile={name}"
        return "profile=none"

    def _get_save_status_text(self):
        source = str(self.current_save_source or self.latest_save_source or "").strip()
        return f"save={source}" if source else "save=none"

    def _set_status_text(self, base_text, text_color="#8ab4f8", include_context=False):
        text = str(base_text or "")
        if include_context:
            text = f"{text} | {self._get_profile_status_text()} | {self._get_save_status_text()}"
        self.safe_ui(self.status_lbl, "configure", text=text, text_color=text_color)

    def _candidate_log_dirs(self):
        candidates = []

        home = os.path.expanduser("~")
        if home:
            candidates.append(os.path.join(home, "Desktop"))

        user_profile = os.environ.get("USERPROFILE", "")
        if user_profile:
            candidates.append(os.path.join(user_profile, "Desktop"))

        one_drive = os.environ.get("OneDrive", "")
        if one_drive:
            candidates.append(os.path.join(one_drive, "Desktop"))

        candidates.append(os.getcwd())
        candidates.append(tempfile.gettempdir())

        out = []
        seen = set()
        for path in candidates:
            key = str(path or "").strip().lower()
            if not key or key in seen:
                continue
            seen.add(key)
            out.append(path)
        return out

    def _write_startup_log_file(self, reason):
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_name = f"RockyIdleReader_startup_log_{stamp}.txt"
        runtime = "EXE" if getattr(sys, "frozen", False) else "PYTHON"
        lines = [
            "Rocky Idle Reader Startup Diagnostic",
            "=" * 40,
            f"Time: {datetime.now().isoformat(timespec='seconds')}",
            f"Runtime: {runtime}",
            f"Reason: {reason}",
            f"CWD: {os.getcwd()}",
            f"Resolved save folder: {self.save_folder or 'None'}",
            "",
            "Timeline:",
        ]
        if self.startup_log_lines:
            lines.extend(self.startup_log_lines)
        else:
            lines.append("(no startup timeline entries)")

        lines.extend([
            "",
            "Recent Scan Diagnostics:",
        ])
        if self.scan_diag_lines:
            lines.extend(list(self.scan_diag_lines)[-180:])
        else:
            lines.append("(no scan diagnostics captured yet)")

        errors = []
        for folder in self._candidate_log_dirs():
            try:
                os.makedirs(folder, exist_ok=True)
                log_path = os.path.join(folder, log_name)
                with open(log_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(lines) + "\n")
                self._startup_log(f"Diagnostic log written: {log_path}")
                return log_path
            except Exception as exc:
                errors.append(f"{folder} -> {exc}")
        return f"<failed to write startup log in any location: {' | '.join(errors)}>"

    def startup_timeout_guard(self):
        if self.startup_timeout_handled or self.is_closing:
            return
        if not getattr(sys, "frozen", False):
            return
        if self.save_folder and os.path.exists(self.save_folder):
            self._startup_log("Startup timeout guard passed: save folder found.")
            return
        self.startup_timeout_handled = True
        self._startup_log("Startup timeout guard triggered: no save folder found within 5 seconds.")
        report = self._write_startup_log_file("No save folder detected within 5 seconds after startup.")
        _show_error_messagebox(
            "Rocky Idle Reader",
            f"No save folder detected within 5 seconds.\nA startup log was written to:\n{report}",
        )
        self.on_closing()

    def _parse_version_tuple(self, version_text):
        text = str(version_text or "").strip().lower().lstrip("v")
        if not text:
            return (0,)
        parts = []
        for raw in text.split("."):
            digits = re.sub(r"[^0-9]", "", raw)
            if digits == "":
                parts.append(0)
            else:
                try:
                    parts.append(int(digits))
                except Exception:
                    parts.append(0)
        return tuple(parts) if parts else (0,)

    def _is_remote_version_newer(self, local_version, remote_version):
        local_tuple = self._parse_version_tuple(local_version)
        remote_tuple = self._parse_version_tuple(remote_version)
        width = max(len(local_tuple), len(remote_tuple))
        local_pad = local_tuple + (0,) * (width - len(local_tuple))
        remote_pad = remote_tuple + (0,) * (width - len(remote_tuple))
        return remote_pad > local_pad

    def _fetch_update_manifest(self):
        request = urllib.request.Request(
            self.update_manifest_url,
            headers={"User-Agent": f"RockyIdleReader/{self.app_version}"},
        )
        with urllib.request.urlopen(request, timeout=10) as response:
            payload = response.read().decode("utf-8", errors="ignore")
        data = json.loads(payload)
        if not isinstance(data, dict):
            raise ValueError("version manifest is not an object")
        remote_version = str(data.get("version") or "").strip()
        if not remote_version:
            raise ValueError("version manifest missing version")
        download_url = str(data.get("download_url") or self.default_update_download_url).strip()
        notes = str(data.get("notes") or "").strip()
        return {
            "version": remote_version,
            "download_url": download_url,
            "notes": notes,
        }

    def check_for_updates_silent(self):
        if self.update_check_in_progress:
            return
        threading.Thread(target=lambda: self.check_for_updates(manual=False), daemon=True).start()

    def check_for_updates(self, manual=True):
        if self.update_check_in_progress:
            return
        self.update_check_in_progress = True
        try:
            manifest = self._fetch_update_manifest()
            remote_version = manifest.get("version")
            download_url = manifest.get("download_url") or self.default_update_download_url
            notes = manifest.get("notes")

            if not self._is_remote_version_newer(self.app_version, remote_version):
                self._startup_log(f"Update check: up to date (local={self.app_version}, remote={remote_version})")
                if manual:
                    self._set_status_text("UP TO DATE", text_color="#3fb950", include_context=False)
                    _show_error_messagebox("Rocky Idle Reader", f"You are up to date.\nCurrent version: {self.app_version}")
                return

            self._startup_log(f"Update available: local={self.app_version}, remote={remote_version}")
            note_line = f"\n\nNotes:\n{notes}" if notes else ""

            if not getattr(sys, "frozen", False):
                if manual:
                    _show_error_messagebox(
                        "Update Available",
                        f"Version {remote_version} is available (local {self.app_version}).{note_line}\n\nOpen repository to pull latest?",
                    )
                try:
                    webbrowser.open(self.repo_url)
                except Exception:
                    pass
                return

            if manual:
                wants_update = _ask_yes_no_messagebox(
                    "Update Available",
                    f"Version {remote_version} is available (local {self.app_version}).{note_line}\n\nDownload and apply now?",
                )
            else:
                wants_update = True
            if wants_update:
                self.download_and_apply_update(download_url, remote_version)
            elif manual:
                self._set_status_text("UPDATE AVAILABLE", text_color="#e8a000", include_context=False)
        except Exception as exc:
            self._startup_log(f"Update check failed: {exc}")
            if manual:
                self._set_status_text("UPDATE CHECK FAILED", text_color="#f0524f", include_context=False)
                _show_error_messagebox("Rocky Idle Reader", f"Update check failed:\n{exc}")
        finally:
            self.update_check_in_progress = False

    def download_and_apply_update(self, download_url, remote_version):
        if not getattr(sys, "frozen", False):
            return
        exe_path = os.path.abspath(sys.executable)
        exe_dir = os.path.dirname(exe_path)
        temp_download = os.path.join(exe_dir, "RockyIdleReader.new.exe")
        try:
            self._set_status_text("DOWNLOADING UPDATE...", text_color="#8ab4f8", include_context=False)
            request = urllib.request.Request(download_url, headers={"User-Agent": f"RockyIdleReader/{self.app_version}"})
            with urllib.request.urlopen(request, timeout=20) as response, open(temp_download, "wb") as handle:
                shutil.copyfileobj(response, handle)
            size = os.path.getsize(temp_download) if os.path.exists(temp_download) else 0
            if size < 5 * 1024 * 1024:
                raise RuntimeError(f"Downloaded update file looks too small ({size} bytes)")

            bat_path = os.path.join(tempfile.gettempdir(), f"rir_update_{int(time.time())}.bat")
            bat_lines = [
                "@echo off",
                "setlocal",
                f"set TARGET_EXE={exe_path}",
                f"set NEW_EXE={temp_download}",
                "ping 127.0.0.1 -n 4 >nul",
                "if exist \"%TARGET_EXE%\" del /F /Q \"%TARGET_EXE%\" >nul 2>nul",
                "if exist \"%TARGET_EXE%\" (",
                "  ping 127.0.0.1 -n 3 >nul",
                "  del /F /Q \"%TARGET_EXE%\" >nul 2>nul",
                ")",
                "if exist \"%TARGET_EXE%\" (",
                "  ping 127.0.0.1 -n 3 >nul",
                "  del /F /Q \"%TARGET_EXE%\" >nul 2>nul",
                ")",
                "if exist \"%TARGET_EXE%\" (",
                "  echo Failed to remove old executable.",
                "  exit /b 1",
                ")",
                "move /Y \"%NEW_EXE%\" \"%TARGET_EXE%\" >nul",
                "if errorlevel 1 (",
                "  copy /Y \"%NEW_EXE%\" \"%TARGET_EXE%\" >nul",
                ")",
                "if exist \"%NEW_EXE%\" del /F /Q \"%NEW_EXE%\" >nul 2>nul",
                "if exist \"%TARGET_EXE%\" start \"\" \"%TARGET_EXE%\"",
            ]
            with open(bat_path, "w", encoding="utf-8") as bat_file:
                bat_file.write("\n".join(bat_lines) + "\n")

            self._startup_log(f"Update downloaded ({remote_version}) to {temp_download}")
            subprocess.Popen(
                ["cmd", "/c", bat_path],
                creationflags=0x00000008,
                close_fds=True,
            )
            self._set_status_text("UPDATING...", text_color="#3fb950", include_context=False)
            _show_error_messagebox("Rocky Idle Reader", f"Update {remote_version} downloaded.\nThe app will restart to finish updating.")
            self.on_closing()
        except Exception as exc:
            self._startup_log(f"Update download/apply failed: {exc}")
            self._set_status_text("UPDATE DOWNLOAD FAILED", text_color="#f0524f", include_context=False)
            _show_error_messagebox(
                "Rocky Idle Reader",
                f"Automatic update failed:\n{exc}\n\nYou can manually download from:\n{self.repo_url}",
            )

    # --- DATABASE METHODS ---
    def _default_skill_db(self):
        return {
            "1001":"Hitpoints", "1002":"Melee", "1003":"Mining", "1005":"Smithing",
            "1006":"Defence", "1007":"Alchemy", "1008":"Fishing", "1009":"Range",
            "1010":"Thieving", "1011":"Cooking", "1012":"Prayer", "1013":"Crafting",
            "1015":"Magic", "1016":"Fletching", "1017":"Woodcutting", "1018":"Arcanery",
            "1019":"Slayer", "1020":"Farming"
        }

    def load_skill_db(self):
        data = self.get_store_section("skill_db", self._default_skill_db())
        return data if isinstance(data, dict) else self._default_skill_db()

    def _default_config(self):
        return {
            "pos": "Free Flow", "show_skills": False, "show_disk_monitor": False,
            "x": 100, "y": 100, "save_path": "", "webhook_url": "", "webhook_enabled": False,
            "notify_levels": True, "notify_slayer": True, "notify_xp": False,
            "notify_no_slayer_task": False,
            "notify_boost_ready": False,
            "xp_notify_interval_minutes": 1,
            "always_on_top": True,
            "hidden_items": [],
            "sidebar_collapsed": False,
            "last_section": "OVERVIEW",
            "density": "Comfortable",
            "skills_sort": "Rate",
            "items_sort": "GP/h",
            "restore_items_on_restart": False,
            "skills_filter": "",
            "items_filter": "",
        }

    def _resource_path(self, relative_path):
        if getattr(sys, "frozen", False):
            base = getattr(sys, "_MEIPASS", os.path.dirname(sys.executable))
        else:
            base = os.path.dirname(os.path.abspath(__file__))
        return os.path.join(base, relative_path)

    def _startup_log(self, message):
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        self.startup_log_lines.append(f"[{ts}] {message}")

    def _candidate_log_dirs(self):
        candidates = []

        home = os.path.expanduser("~")
        if home:
            candidates.append(os.path.join(home, "Desktop"))

        user_profile = os.environ.get("USERPROFILE", "")
        if user_profile:
            candidates.append(os.path.join(user_profile, "Desktop"))

        one_drive = os.environ.get("OneDrive", "")
        if one_drive:
            candidates.append(os.path.join(one_drive, "Desktop"))

        # Fallbacks that should be writable even on heavily locked-down profiles.
        candidates.append(os.getcwd())
        candidates.append(tempfile.gettempdir())

        # De-duplicate while preserving order.
        out = []
        seen = set()
        for path in candidates:
            key = str(path or "").strip().lower()
            if not key or key in seen:
                continue
            seen.add(key)
            out.append(path)
        return out

    def _write_startup_log_file(self, reason):
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_name = f"RockyIdleReader_startup_log_{stamp}.txt"
        runtime = "EXE" if getattr(sys, "frozen", False) else "PYTHON"
        lines = [
            "Rocky Idle Reader Startup Diagnostic",
            "=" * 40,
            f"Time: {datetime.now().isoformat(timespec='seconds')}",
            f"Runtime: {runtime}",
            f"Reason: {reason}",
            f"CWD: {os.getcwd()}",
            f"Resolved save folder: {self.save_folder or 'None'}",
            "",
            "Timeline:",
        ]
        if self.startup_log_lines:
            lines.extend(self.startup_log_lines)
        else:
            lines.append("(no startup timeline entries)")

        errors = []
        for folder in self._candidate_log_dirs():
            try:
                os.makedirs(folder, exist_ok=True)
                log_path = os.path.join(folder, log_name)
                with open(log_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(lines) + "\n")
                self._startup_log(f"Diagnostic log written: {log_path}")
                return log_path
            except Exception as exc:
                errors.append(f"{folder} -> {exc}")
        return f"<failed to write startup log in any location: {' | '.join(errors)}>"

    def startup_timeout_guard(self):
        if self.startup_timeout_handled or self.is_closing:
            return
        if not getattr(sys, "frozen", False):
            return
        if self.save_folder and os.path.exists(self.save_folder):
            self._startup_log("Startup timeout guard passed: save folder found.")
            return
        self.startup_timeout_handled = True
        self._startup_log("Startup timeout guard triggered: no save folder found within 5 seconds.")
        report = self._write_startup_log_file("No save folder detected within 5 seconds after startup.")
        _show_error_messagebox(
            "Rocky Idle Reader",
            f"No save folder detected within 5 seconds.\nA startup log was written to:\n{report}",
        )
        self.on_closing()

    def write_manual_diagnostic_log(self):
        self._startup_log("Manual diagnostic log requested from Settings.")
        save_ok = bool(self.save_folder and os.path.exists(self.save_folder))
        self._startup_log(f"Current save folder exists: {save_ok}")
        self._startup_log(f"Current selected profile id: {self.selected_profile_id or 'None'}")
        self._startup_log(f"Current selected profile name: {self.selected_profile_name or 'None'}")
        try:
            profiles = self.scan_available_profiles(max_files=self.save_scan_limit)
            self._startup_log(f"Profile scan count: {len(profiles)}")
            for idx, profile in enumerate(profiles[:10], start=1):
                name = profile.get("name") or "Unknown"
                pid = profile.get("profileId") or "unknown"
                src = profile.get("latestFileName") or "unknown"
                self._startup_log(f"Profile {idx}: name={name} | id={pid} | file={src}")
        except Exception as exc:
            self._startup_log(f"Manual profile scan failed: {exc}")

        report = self._write_startup_log_file("Manual diagnostic log requested from Settings.")
        self._set_status_text("DESKTOP LOG WRITTEN", text_color="#3fb950", include_context=True)
        _show_error_messagebox("Rocky Idle Reader", f"Diagnostic log written to:\n{report}")

    def rescan_save_and_profiles(self):
        self._startup_log("Manual save/profile rescan requested from Settings.")
        self.save_folder = self.find_save_path()
        if not self.save_folder or not os.path.exists(self.save_folder):
            self._startup_log("Manual rescan failed: no valid save folder found.")
            report = self._write_startup_log_file("Manual rescan failed: no valid save folder found.")
            self._set_status_text("SAVE PATH NOT FOUND", text_color="#f0524f", include_context=True)
            _show_error_messagebox(
                "Rocky Idle Reader",
                f"No valid save folder found.\nA diagnostic log was written to:\n{report}",
            )
            return

        profiles = self.scan_available_profiles(max_files=self.save_scan_limit)
        self._startup_log(f"Manual rescan found save folder: {self.save_folder}")
        self._startup_log(f"Manual rescan profile count: {len(profiles)}")
        if not profiles:
            report = self._write_startup_log_file("Manual rescan found save folder but no profiles.")
            self._set_status_text("NO PROFILES FOUND", text_color="#e67e22", include_context=True)
            _show_error_messagebox(
                "Rocky Idle Reader",
                f"Save folder was found, but no profiles were detected.\nA diagnostic log was written to:\n{report}",
            )
            return

        if len(profiles) == 1:
            self.select_profile(profiles[0])
            self._set_status_text("PROFILE SELECTED", text_color="#8ab4f8", include_context=True)
            return

        self._set_status_text("SELECT A PROFILE", text_color="#f1c40f", include_context=True)
        self.show_profile_picker(profiles)

    def _load_json_file(self, path, default=None, encoding='utf-8'):
        read_path = path
        if not os.path.exists(read_path) and not os.path.isabs(path):
            bundled_path = self._resource_path(path)
            if os.path.exists(bundled_path):
                read_path = bundled_path
        if not os.path.exists(read_path):
            return default
        try:
            with open(read_path, 'r', encoding=encoding) as f:
                return json.load(f)
        except Exception:
            return default

    def _save_json_file(self, path, payload):
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(payload, f, indent=2)
            return True
        except Exception:
            return False

    def save_data_store(self):
        if not hasattr(self, 'data_store') or not isinstance(self.data_store, dict):
            self.data_store = {"version": 1, "sections": {}}
        self.data_store.setdefault("version", 1)
        self.data_store.setdefault("sections", {})
        return self._save_json_file(self.data_store_file, self.data_store)

    def get_store_section(self, section_name, default=None):
        sections = self.data_store.get("sections", {}) if isinstance(getattr(self, 'data_store', None), dict) else {}
        value = sections.get(section_name, default)
        return value if value is not None else default

    def set_store_section(self, section_name, payload, save_now=True):
        if not hasattr(self, 'data_store') or not isinstance(self.data_store, dict):
            self.data_store = {"version": 1, "sections": {}}
        self.data_store.setdefault("sections", {})[section_name] = payload
        if save_now:
            self.save_data_store()

    def load_data_store(self):
        store = {"version": 1, "sections": {}}
        existing = self._load_json_file(self.data_store_file, default=None)
        if not isinstance(existing, dict):
            existing = self._load_json_file(self.legacy_data_store_file, default=None)
        if isinstance(existing, dict):
            if isinstance(existing.get("sections"), dict):
                store["version"] = existing.get("version", 1)
                store["sections"] = existing.get("sections", {})
            else:
                store["sections"] = existing

        sections = store.setdefault("sections", {})
        migrated = False

        if "config" not in sections:
            legacy_config = self._load_json_file(self.config_file, default={})
            config = {**self._default_config(), **(legacy_config if isinstance(legacy_config, dict) else {})}
            config.pop("scale_factor", None)
            sections["config"] = config
            migrated = True

        if "skill_db" not in sections:
            legacy_skills = self._load_json_file(self.db_file, default=self._default_skill_db())
            sections["skill_db"] = legacy_skills if isinstance(legacy_skills, dict) else self._default_skill_db()
            migrated = True

        legacy_sections = {
            "monster_db": (self.monster_db_file, {"1001": "Sea Snake"}),
            "item_db": (self.item_db_file, {}),
            "mining_db": (self.mining_db_file, {}),
            "item_meta": (self.item_meta_file, {}),
            "skill_tiers": (self.skill_tier_file, {}),
            "diary_boosters": (self.diary_boosters_file, {}),
            "multipliers_snapshot": (self.multipliers_file, {}),
            "fresh_save_multipliers": (self.fresh_multipliers_file, {}),
            "skill_full_dump": (self.skill_full_dump_file, {}),
            "session_cache": (self.session_cache_file, {}),
        }

        for section_name, (legacy_path, fallback) in legacy_sections.items():
            if section_name in sections:
                continue
            legacy_value = self._load_json_file(legacy_path, default=fallback)
            sections[section_name] = legacy_value if legacy_value is not None else fallback
            migrated = True

        if migrated:
            self._save_json_file(self.data_store_file, store)
        return store

    def cleanup_legacy_data_files(self):
        if not os.path.exists(self.data_store_file):
            return
        legacy_paths = [
            self.db_file,
            self.monster_db_file,
            self.item_db_file,
            self.mining_db_file,
            self.item_meta_file,
            self.skill_tier_file,
            self.diary_boosters_file,
            self.multipliers_file,
            self.fresh_multipliers_file,
            self.skill_full_dump_file,
            self.config_file,
            self.session_cache_file,
            self.legacy_data_store_file,
        ]
        for legacy_path in legacy_paths:
            try:
                if os.path.exists(legacy_path):
                    os.remove(legacy_path)
            except Exception:
                pass

    def load_monster_db(self):
        data = self.get_store_section("monster_db", {})
        return data if isinstance(data, dict) else {}

    def load_slayer_category_map(self):
        """Return {str(id): display_name} for SlayerCategoriesIds parsed from the game source."""
        result = {}
        map_path = self._resource_path(os.path.join("GameData", "index-B1HmVF50.js.map"))
        if not os.path.exists(map_path):
            map_path = os.path.join("GameData", "index-B1HmVF50.js.map")
        if not os.path.exists(map_path):
            return result
        try:
            src_map = self._load_json_file(map_path, default={})
            if not isinstance(src_map, dict):
                return result
            lookup = dict(zip(src_map.get("sources", []), src_map.get("sourcesContent", [])))
            text = lookup.get("../../src/data/MonsterData/MonsterTypes.ts", "")
            # Extract SlayerCategoriesIds enum block
            blk = re.search(r'SlayerCategoriesIds\s*\{([^}]+)\}', text)
            if blk:
                for m in re.finditer(r'([A-Z][A-Z0-9_]*)\s*=\s*(\d+)', blk.group(1)):
                    name_parts = m.group(1).replace("_", " ").split()
                    display = " ".join(p.capitalize() for p in name_parts)
                    result[m.group(2)] = display
        except Exception:
            pass
        return result


    def load_item_db(self):
        data = self.get_store_section("item_db", {})
        existing = data if isinstance(data, dict) else {}

        # Bootstrap/augment from bundled price table.
        built = {}
        price_arr = self._load_json_file("item_price_array.json", default=[])
        if isinstance(price_arr, list):
            for row in price_arr:
                if not isinstance(row, dict):
                    continue
                item_id = row.get("id")
                name = str(row.get("name") or "").strip()
                if item_id is None or not name:
                    continue
                built[str(item_id)] = name

        # Always enrich with source-map enum names for IDs missing from price table.
        try:
            map_path = self._resource_path(os.path.join("GameData", "index-B1HmVF50.js.map"))
            if not os.path.exists(map_path):
                map_path = os.path.join("GameData", "index-B1HmVF50.js.map")
            src_map = self._load_json_file(map_path, default={})
            if isinstance(src_map, dict):
                lookup = dict(zip(src_map.get("sources", []), src_map.get("sourcesContent", [])))
                enum_text = lookup.get("../../src/data/ItemData/AllItemsIds.ts", "")
                for m in re.finditer(r'([A-Z0-9_]+)\s*=\s*"?(\d+)"?\s*,?', enum_text):
                    item_id = m.group(2)
                    if item_id in built:
                        continue
                    enum_name = m.group(1).strip("_")
                    pretty = " ".join(part.capitalize() for part in enum_name.split("_") if part)
                    if pretty:
                        built[item_id] = pretty
        except Exception:
            pass

        merged = {**built, **existing}
        if merged:
            try:
                self.set_store_section("item_db", merged)
            except Exception:
                pass
            return merged
        return existing

    def _default_mining_db(self):
        return {
            "source": "built_in_fallback",
            "parsed_at": "2026-04-14",
            "nodes": {
                "rock": {"default_output": 1, "base_loot_factor": 2, "default_xp": 30, "default_time_seconds": 8.0, "speed_badge": 3.0, "sell_gp": 4, "thresholds": {"2x": 90, "3x": 110, "4x": 999}},
                "bronze": {"default_output": 1, "base_loot_factor": 2, "default_xp": 50, "default_time_seconds": 10.0, "speed_badge": 3.0, "sell_gp": 16, "thresholds": {"2x": 95, "3x": 115, "4x": 999}},
                "silver": {"default_output": 1, "base_loot_factor": 1, "default_xp": 70, "default_time_seconds": 10.0, "speed_badge": 3.0, "sell_gp": 36, "thresholds": {"2x": 100, "3x": 120, "4x": 999}},
                "jade": {"default_output": 1, "base_loot_factor": 1, "default_xp": 100, "default_time_seconds": 12.0, "speed_badge": 3.0, "sell_gp": 120, "thresholds": {"2x": 105, "3x": 125, "4x": 999}},
                "gold": {"default_output": 1, "base_loot_factor": 1, "default_xp": 130, "default_time_seconds": 12.0, "speed_badge": 3.0, "sell_gp": 240, "thresholds": {"2x": 110, "3x": 999, "4x": 999}},
                "platinum": {"default_output": 1, "base_loot_factor": 1, "default_xp": 170, "default_time_seconds": 14.0, "speed_badge": 3.0, "sell_gp": 400, "thresholds": {"2x": 115, "3x": 999, "4x": 999}},
                "gemrock": {"default_output": 1, "base_loot_factor": 1, "default_xp": 200, "default_time_seconds": 16.0, "speed_badge": 3.0, "sell_gp": None, "thresholds": {"2x": 120, "3x": 999, "4x": 999}},
                "diamond": {"default_output": 1, "base_loot_factor": 1, "default_xp": 300, "default_time_seconds": 18.0, "speed_badge": 3.0, "sell_gp": 1200, "thresholds": {"2x": 125, "3x": 999, "4x": 999}},
                "sunstone": {"default_output": 1, "base_loot_factor": 1, "default_xp": 450, "default_time_seconds": 22.0, "speed_badge": 2.5, "sell_gp": 2200, "thresholds": {"2x": 125, "3x": 999, "4x": 999}},
            },
        }

    def _is_valid_mining_db(self, payload):
        return isinstance(payload, dict) and isinstance(payload.get("nodes"), dict) and bool(payload.get("nodes"))

    def load_mining_db(self):
        data = self.get_store_section("mining_db", {})
        if self._is_valid_mining_db(data):
            return data

        # Recovery path for stale/empty app_data entries in packaged exe runs.
        try:
            bundled_store = self._load_json_file(self._resource_path("app_data.json"), default={})
            sections = bundled_store.get("sections", {}) if isinstance(bundled_store, dict) else {}
            bundled_mining = sections.get("mining_db", {}) if isinstance(sections, dict) else {}
            if self._is_valid_mining_db(bundled_mining):
                self.set_store_section("mining_db", bundled_mining)
                self._startup_log("Mining DB recovered from bundled app_data.json.")
                return bundled_mining
        except Exception as exc:
            self._startup_log(f"Mining DB bundled recovery failed: {exc}")

        fallback = self._default_mining_db()
        try:
            self.set_store_section("mining_db", fallback)
            self._startup_log("Mining DB fallback defaults applied.")
        except Exception:
            pass
        return fallback

    def load_item_meta(self):
        default = {
            "1100": {"sell_gp": 4, "name": "Rock Fragment"}
        }
        data = self.get_store_section("item_meta", {})
        return {**default, **(data if isinstance(data, dict) else {})}

    def load_config(self):
        config = self.get_store_section("config", self._default_config())
        merged = {**self._default_config(), **(config if isinstance(config, dict) else {})}
        if merged.get("pos") == "Top-Right":
            merged["pos"] = "Free Flow"
        merged.pop("scale_factor", None)
        return merged

    def save_config(self):
        try:
            self.config["pos"] = self.pos_menu.get() if hasattr(self, 'pos_menu') else self.config.get("pos", "Free Flow")
            self.config["webhook_url"] = self.webhook_entry.get() if hasattr(self, 'webhook_entry') else self.config.get("webhook_url", "")
            self.config["hidden_items"] = sorted(list(self.hidden_items))
            self.config.pop("scale_factor", None)
            if self.winfo_exists():
                self.config["x"], self.config["y"] = self.winfo_x(), self.winfo_y()
            self.set_store_section("config", self.config)
        except Exception:
            pass

    def save_item_meta(self):
        try:
            self.set_store_section("item_meta", self.item_meta)
        except Exception:
            pass

    def save_skill_tiers(self, payload):
        try:
            self.set_store_section("skill_tiers", payload)
        except Exception:
            pass

    def save_diary_boosters(self, payload):
        try:
            self.set_store_section("diary_boosters", payload)
        except Exception:
            pass

    def save_multipliers_snapshot(self, payload):
        try:
            self.set_store_section("multipliers_snapshot", payload)
        except Exception:
            pass

    def _serialize_history_map(self, history_map):
        payload = {}
        for key, history in history_map.items():
            try:
                payload[str(key)] = [list(entry) for entry in history]
            except Exception:
                payload[str(key)] = []
        return payload

    def _deserialize_history_map(self, payload, time_offset=0):
        restored = {}
        if not isinstance(payload, dict):
            return restored
        for key, entries in payload.items():
            history = deque()
            if not isinstance(entries, list):
                restored[str(key)] = history
                continue
            for entry in entries:
                if not isinstance(entry, (list, tuple)) or len(entry) < 2:
                    continue
                try:
                    history.append((float(entry[0]) + time_offset, entry[1]))
                except (TypeError, ValueError):
                    continue
            restored[str(key)] = history
        return restored

    def save_session_cache(self):
        try:
            payload = {
                "saved_at": time.time(),
                "selected_profile_id": self.selected_profile_id,
                "selected_profile_name": self.selected_profile_name,
                "selected_profile_info": self.selected_profile_info,
                "last_known_mtime": self.last_known_mtime,
                "last_raw_save": self._last_raw_save.decode('utf-8') if isinstance(self._last_raw_save, (bytes, bytearray)) else self._last_raw_save,
                "prev_state": self.prev_state,
                "current_debug_list": self.current_debug_list,
                "xp_history": self._serialize_history_map(self.xp_history),
                "session_start_xp": self.session_start_xp,
                "current_levels": self.current_levels,
                "active_skills": self.active_skills,
                "stale_counts": self.stale_counts,
                "save_history": list(self.save_history),
                "latest_save_data": self.latest_save_data,
                "latest_save_source": self.latest_save_source,
                "current_save_source": self.current_save_source,
                "xp_active_scan_streak": self.xp_active_scan_streak,
                "xp_inactive_scan_streak": self.xp_inactive_scan_streak,
                "xp_activity_armed": self.xp_activity_armed,
                "xp_inactive_notified": self.xp_inactive_notified,
                "skill_diamond_status": self.skill_diamond_status,
                "item_history": self._serialize_history_map(self.item_history),
                "stale_item_counts": self.stale_item_counts,
                "no_slayer_task_count": self.no_slayer_task_count,
                "no_slayer_task_notified": self.no_slayer_task_notified,
                "initial_load_done": self.initial_load_done,
                "session_gp_earned": self.session_gp_earned,
            }
            self.set_store_section("session_cache", payload)
        except Exception:
            pass

    def restore_recent_session(self):
        payload = self.get_store_section("session_cache", {})
        if not isinstance(payload, dict) or not payload:
            return False

        saved_at = payload.get("saved_at", 0)
        try:
            saved_at = float(saved_at)
        except (TypeError, ValueError):
            saved_at = 0
        age = time.time() - saved_at
        if age < 0 or age > 300:
            # Session cache is stale: hard-reset session-only counters.
            self.session_gp_earned = 0.0
            self.session_start_xp = {}
            self.xp_history = {}
            self.active_skills = {}
            self.item_history = {}
            self.stale_item_counts = {}
            try:
                self.set_store_section("session_cache", {})
            except Exception:
                pass
            return False

        self.selected_profile_id = payload.get("selected_profile_id")
        self.selected_profile_name = payload.get("selected_profile_name")
        self.selected_profile_info = payload.get("selected_profile_info", {}) if isinstance(payload.get("selected_profile_info"), dict) else {}
        self.last_known_mtime = payload.get("last_known_mtime", 0) or 0
        last_raw_save = payload.get("last_raw_save")
        self._last_raw_save = last_raw_save.encode('utf-8') if isinstance(last_raw_save, str) else last_raw_save
        self.prev_state = payload.get("prev_state") if isinstance(payload.get("prev_state"), dict) else None
        self.current_debug_list = payload.get("current_debug_list", []) if isinstance(payload.get("current_debug_list"), list) else []
        self.xp_history = self._deserialize_history_map(payload.get("xp_history", {}), time_offset=age)
        self.session_start_xp = payload.get("session_start_xp", {}) if isinstance(payload.get("session_start_xp"), dict) else {}
        self.current_levels = payload.get("current_levels", {}) if isinstance(payload.get("current_levels"), dict) else {}
        self.active_skills = payload.get("active_skills", {}) if isinstance(payload.get("active_skills"), dict) else {}
        self.stale_counts = payload.get("stale_counts", {}) if isinstance(payload.get("stale_counts"), dict) else {}
        self.save_history = deque(payload.get("save_history", []) if isinstance(payload.get("save_history"), list) else [])
        self.latest_save_data = payload.get("latest_save_data", {}) if isinstance(payload.get("latest_save_data"), dict) else {}
        self.latest_save_source = payload.get("latest_save_source")
        self.current_save_source = payload.get("current_save_source")
        self.xp_active_scan_streak = int(payload.get("xp_active_scan_streak", 0) or 0)
        self.xp_inactive_scan_streak = int(payload.get("xp_inactive_scan_streak", 0) or 0)
        self.xp_activity_armed = bool(payload.get("xp_activity_armed", False))
        self.xp_inactive_notified = bool(payload.get("xp_inactive_notified", False))
        self.skill_diamond_status = payload.get("skill_diamond_status", {}) if isinstance(payload.get("skill_diamond_status"), dict) else {}
        if self.config.get("restore_items_on_restart", False):
            self.item_history = self._deserialize_history_map(payload.get("item_history", {}), time_offset=age)
            self.stale_item_counts = payload.get("stale_item_counts", {}) if isinstance(payload.get("stale_item_counts"), dict) else {}
        else:
            self.item_history = {}
            self.stale_item_counts = {}
            self.recent_changed_item_ids = set()
        self.no_slayer_task_count = int(payload.get("no_slayer_task_count", 0) or 0)
        self.no_slayer_task_notified = bool(payload.get("no_slayer_task_notified", False))
        # Always revalidate profile against current save files on startup.
        # This avoids stale cached profile IDs causing no-sync loops.
        self.initial_load_done = False
        self.session_gp_earned = float(payload.get("session_gp_earned", 0.0) or 0.0)

        if self.selected_profile_name and hasattr(self, 'profile_name_lbl') and self.profile_name_lbl.winfo_exists():
            self.profile_name_lbl.configure(text=self.selected_profile_name, text_color=self._C.get("gold", "#e8a000"))

        self.refresh_restored_session_ui(age)
        return True

    def refresh_restored_session_ui(self, cache_age=0):
        state = self.prev_state or {}
        skills = state.get('skills', {}) if isinstance(state, dict) else {}
        xp_map = state.get('skillsXp', {}) if isinstance(state, dict) else {}
        total_lvl, total_xp, sess_xp = 0, 0, 0

        for sid, name in self.skill_map.items():
            sd = skills.get(sid, {}) if isinstance(skills, dict) else {}
            xd = xp_map.get(sid, 0) if isinstance(xp_map, dict) else 0
            lvl = self._coerce_skill_level(sd)
            if lvl is None:
                continue
            xp = xd.get('xp', xd) if isinstance(xd, dict) else xd
            try:
                xp = float(xp or 0)
            except (TypeError, ValueError):
                xp = 0.0
            total_lvl += lvl
            total_xp += xp
            sess_xp += xp - self.session_start_xp.get(name, xp)
            if sid in self.skill_labels:
                self.safe_ui(self.skill_labels[sid], "configure", text=str(lvl))
            if sid in self.skill_name_labels:
                try:
                    speed_mult = float(sd.get('currentSpeedMultiplier', 1) or 1)
                except (TypeError, ValueError):
                    speed_mult = 1.0
                self.safe_ui(self.skill_name_labels[sid], "configure", text=f"{name} ({speed_mult:.2f}/3.00 Diamond)")

        slayer = state.get('slayer', state.get('slayerInfo', {})) if isinstance(state, dict) else {}
        current_task = slayer.get('currentSlayerTask') or {}
        amt = current_task.get('currentAmount', 0)
        total_amt = current_task.get('totalAmount', 0)
        task_id = current_task.get('slayerCategoryId', '')
        pts = int(slayer.get('slayerPoints', 0)) if isinstance(slayer, dict) else 0
        strk = int(slayer.get('slayerStreak', 0)) if isinstance(slayer, dict) else 0

        self.safe_ui(self.total_lvl_lbl, "configure", text=str(total_lvl) if total_lvl else "--")
        self.safe_ui(self.total_xp_lbl, "configure", text=self.format_number(total_xp) if total_xp else "--")
        self.safe_ui(self.session_xp_lbl, "configure", text=self.format_number(sess_xp))
        self.safe_ui(self.session_gp_lbl, "configure", text=self.format_number(self.session_gp_earned))
        self.safe_ui(self.slayer_task_lbl, "configure", text=self.slayer_category_map.get(str(task_id), self.monster_map.get(str(task_id), "None" if not task_id else f"ID {task_id}")))
        self.safe_ui(self.slayer_kills_lbl, "configure", text=f"{amt} / {total_amt}" if total_amt > 0 else "0")
        self.safe_ui(self.slayer_points_lbl, "configure", text=str(pts))
        self.safe_ui(self.slayer_streak_lbl, "configure", text=str(strk))

        restored_items = []
        for name, data in list(self.active_skills.items()):
            restored_items.append((name, data.get('lvl', '--'), data.get('gain', 0), data.get('rate', 0), self.format_ttl(data.get('ttl', 0)), "SKILL"))
        for name, hist in list(self.item_history.items()):
            gain = sum(i[1] for i in hist)
            rate = (gain / (time.time() - hist[0][0])) * 3600 if hist and (time.time() - hist[0][0]) > 0 else 0
            restored_items.append((name, "Item", gain, rate, "ITEM", "ITEM"))
        self.update_ui_feed(restored_items)
        self.refresh_log_view()
        self.refresh_explorer_view()
        self.update_overview_snapshot(state)
        self.update_optimal_snapshot(state)

        age_text = f"RESTORED {int(cache_age // 60)}M AGO" if cache_age >= 60 else "RESTORED"
        self.safe_ui(self.status_lbl, "configure", text=age_text, text_color="#8ab4f8")

    def _is_completed_flag(self, value):
        if isinstance(value, bool):
            return value
        if isinstance(value, (int, float)):
            return value > 0
        if isinstance(value, str):
            return value.strip().lower() in {"completed", "complete", "done", "claimed", "opened", "unlocked", "true", "1"}
        if isinstance(value, dict):
            for key in ("completed", "isCompleted", "done", "claimed", "opened", "unlocked", "status", "state"):
                if key in value and self._is_completed_flag(value.get(key)):
                    return True
        return False

    def _collection_completion(self, obj):
        if isinstance(obj, dict):
            total = len(obj)
            completed = sum(1 for v in obj.values() if self._is_completed_flag(v))
            return completed, total
        if isinstance(obj, (list, tuple, set)):
            rows = list(obj)
            total = len(rows)
            completed = sum(1 for v in rows if self._is_completed_flag(v))
            return completed, total
        return 0, 0

    def _find_first_state_key(self, state_obj, keys):
        for key in keys:
            if key in state_obj:
                return state_obj.get(key)
        return None

    def _parse_collection_log_progress(self, state_obj):
        raw = state_obj.get("collectionLogSlot") if isinstance(state_obj, dict) else None
        if isinstance(raw, str):
            m = re.search(r"(\d+)\s*/\s*(\d+)", raw)
            if m:
                return int(m.group(1)), int(m.group(2))
        if isinstance(raw, (int, float)):
            return int(raw), 800
        if isinstance(raw, dict):
            done = sum(1 for v in raw.values() if self._is_completed_flag(v))
            total = len(raw) if raw else 800
            return done, total
        if isinstance(raw, (list, tuple, set)):
            rows = list(raw)
            done = sum(1 for v in rows if self._is_completed_flag(v))
            total = len(rows) if rows else 800
            return done, total
        return 0, 800

    def _parse_achievement_progress(self, state_obj):
        diary = state_obj.get("completedAchievementDiary", {}) if isinstance(state_obj, dict) else {}
        area_ids = [str(i) for i in range(1001, 1008)]
        # Total requested by user: 35 checkpoints across the 1001-1007 diary areas.
        total = 35
        done = 0
        tiers = ("EASY", "MED", "MEDIUM", "HARD", "EXPERT", "ELITE", "MASTER")
        for area_id in area_ids:
            row = diary.get(area_id, {}) if isinstance(diary, dict) else {}
            if isinstance(row, dict):
                counted_this_area = 0
                for tier in tiers:
                    if tier in row and self._is_completed_flag(row.get(tier)):
                        done += 1
                        counted_this_area += 1
                # Fallback for unexpected formats: count truthy fields, max 5 per area.
                if counted_this_area == 0:
                    done += min(5, sum(1 for v in row.values() if self._is_completed_flag(v)))
            else:
                if self._is_completed_flag(row):
                    done += 1
        return min(done, total), total

    def _parse_chest_progress(self, state_obj):
        opened = state_obj.get("chestsOpened", {}) if isinstance(state_obj, dict) else {}
        area_ids = ["1000", "1001", "1002", "1003", "1004"]
        default_drop_counts = {
            "1000": 20,
            "1001": 20,
            "1002": 5,
            "1003": 45,
            "1004": 2,
        }
        total = 0
        done = 0
        for area_id in area_ids:
            row = opened.get(area_id, {}) if isinstance(opened, dict) else {}
            area_total = int(default_drop_counts.get(area_id, 0))
            if isinstance(row, dict) and isinstance(row.get("drops"), list):
                area_count = len(row.get("drops") or [])
                done += min(area_count, area_total)
                total += area_total
            else:
                total += area_total
        return done, total

    def _parse_quest_points_progress(self, state_obj):
        # Quest completion is displayed as raw quest count out of 60.
        quests_obj = self._find_first_state_key(state_obj, ["quests", "questProgress", "completedQuests", "questLog"])
        q_done_count, _ = self._collection_completion(quests_obj)
        total_quests = 60
        return max(0, min(int(q_done_count or 0), total_quests)), total_quests

    def update_overview_snapshot(self, state=None):
        state_obj = state if isinstance(state, dict) else (self.prev_state if isinstance(self.prev_state, dict) else {})

        q_done, q_total = self._parse_quest_points_progress(state_obj)
        a_done, a_total = self._parse_achievement_progress(state_obj)
        c_done, c_total = self._parse_chest_progress(state_obj)
        l_done, l_total = self._parse_collection_log_progress(state_obj)

        skills = state_obj.get('skills', {}) if isinstance(state_obj, dict) else {}
        xp_map = state_obj.get('skillsXp', {}) if isinstance(state_obj, dict) else {}

        skill_ids = list(self.skill_map.keys())
        skill_total = len(skill_ids)
        lvl126_done = 0
        xp200m_done = 0
        for sid in skill_ids:
            sk = skills.get(sid, {}) if isinstance(skills, dict) else {}
            lvl = int(sk.get('level', 1) or 1) if isinstance(sk, dict) else 1
            if lvl >= 126:
                lvl126_done += 1
            xp_raw = xp_map.get(sid, 0) if isinstance(xp_map, dict) else 0
            xp_val = xp_raw.get('xp', xp_raw) if isinstance(xp_raw, dict) else xp_raw
            try:
                if int(xp_val or 0) >= 200000000:
                    xp200m_done += 1
            except Exception:
                pass

        maxed_done = lvl126_done + xp200m_done
        maxed_total = skill_total * 2

        parts = []
        for done, total in ((q_done, q_total), (a_done, a_total), (c_done, c_total), (l_done, l_total), (maxed_done, maxed_total)):
            if total > 0:
                parts.append((done / total) * 100.0)
        overall_pct = (sum(parts) / len(parts)) if parts else 0.0

        def fmt(done, total):
            if total <= 0:
                return "N/A"
            return f"{done}/{total} ({(done / total) * 100.0:.1f}%)"

        ok_col = "#3fb950"
        bad_col = "#f0524f"

        def render_completion(label_widget, done, total, default_text=None):
            if not label_widget:
                return
            if total <= 0:
                self.safe_ui(label_widget, "configure", text=(default_text or "N/A"), text_color="#8e9db5")
                return
            is_full = done >= total
            star = " ★" if is_full else ""
            text = default_text if default_text is not None else fmt(done, total)
            if default_text is None:
                text = f"{text}{star}"
            else:
                text = f"{text}{star}" if is_full else text
            self.safe_ui(label_widget, "configure", text=text, text_color=(ok_col if is_full else bad_col))

        if hasattr(self, 'ov_completion_total_lbl'):
            total_full = overall_pct >= 99.999
            self.safe_ui(
                self.ov_completion_total_lbl,
                "configure",
                text=f"{overall_pct:.1f}%{' ★' if total_full else ''}",
                text_color=(ok_col if total_full else bad_col),
            )
        if hasattr(self, 'ov_completion_quests_lbl'):
            render_completion(self.ov_completion_quests_lbl, q_done, q_total)
        if hasattr(self, 'ov_completion_achievements_lbl'):
            render_completion(self.ov_completion_achievements_lbl, a_done, a_total)
        if hasattr(self, 'ov_completion_chests_lbl'):
            render_completion(self.ov_completion_chests_lbl, c_done, c_total)
        if hasattr(self, 'ov_completion_logs_lbl'):
            render_completion(self.ov_completion_logs_lbl, l_done, l_total)
        if hasattr(self, 'ov_completion_maxed_lbl'):
            maxed_text = f"{lvl126_done}/{skill_total} L126 | {xp200m_done}/{skill_total} 200M"
            render_completion(self.ov_completion_maxed_lbl, maxed_done, maxed_total, default_text=maxed_text)

    def get_item_name(self, item_id):
        item_id = str(item_id)
        value = self.item_map.get(item_id)
        if isinstance(value, dict):
            return value.get("name", f"Item {item_id}")
        if isinstance(value, str):
            return value
        meta = self.item_meta.get(item_id, {})
        return meta.get("name", f"Item {item_id}")

    def infer_tier_name(self, speed_multiplier):
        tier_map = {
            1.1: "Bronze",
            1.2: "Silver",
            1.4: "Gold",
            1.6: "Platinum",
            1.9: "Sapphire",
            2.2: "Emerald",
            2.5: "Ruby",
            3.0: "Diamond"
        }
        try:
            value = round(float(speed_multiplier), 1)
        except:
            return None
        return tier_map.get(value)

    def get_tool_tier_names(self):
        return ["Rock", "Bronze", "Silver", "Jade", "Gold", "Platinum", "Diamond"]

    def map_tool_ids_to_tiers(self, tool_ids):
        tier_names = self.get_tool_tier_names()
        if not isinstance(tool_ids, list):
            return []
        mapped = []
        for idx, tool_id in enumerate(tool_ids):
            tier_name = tier_names[idx] if idx < len(tier_names) else f"Tier {idx + 1}"
            mapped.append({
                "tier": tier_name,
                "toolId": tool_id
            })
        return mapped

    def get_area_skill_map(self):
        return {
            "1001": ["1017", "1016"],  # Forest: Woodcutting, Fletching
            "1002": ["1003", "1005"],  # Mind/Mine: Mining, Smithing
            "1003": ["1008", "1011"],  # Seas: Fishing, Cooking
            "1004": ["1020", "1007"],  # Fields: Farming, Alchemy
            "1005": ["1012", "1018"],  # Temple: Prayer, Arcanery
            "1006": ["1013", "1010"]   # Market: Crafting, Thieving
        }

    def get_skill_diary_speed_factor(self, state, skill_id):
        completed = state.get('completedAchievementDiary', {})
        factor = 1.0
        for area_id, skill_ids in self.get_area_skill_map().items():
            if str(skill_id) not in skill_ids:
                continue
            row = completed.get(area_id, {}) if isinstance(completed, dict) else {}
            easy_done = str(row.get('EASY', '')).lower() == 'completed'
            expert_done = str(row.get('EXPERT', '')).lower() == 'completed'
            if easy_done:
                factor += 0.15
            if expert_done:
                factor += 1.0
        return factor

    def parse_node_multiplier(self, node_info):
        if not isinstance(node_info, dict):
            return 1.0
        speed_badge = node_info.get('speed_badge')
        try:
            if speed_badge is not None:
                val = float(speed_badge)
                return val if val > 0 else 1.0
        except:
            pass
        label = str(node_info.get('node_multiplier_label', ''))
        m = re.search(r'([0-9]+(?:\.[0-9]+)?)x', label)
        if m:
            try:
                val = float(m.group(1))
                return val if val > 0 else 1.0
            except:
                pass
        return 1.0

    def get_level_gate_multiplier(self, level):
        try:
            value = int(level)
        except:
            value = 1
        if value >= 110:
            return 3.0
        if value >= 90:
            return 2.0
        return 1.0

    def get_node_level_gate_multiplier(self, node_info, level):
        try:
            value = int(level)
        except:
            value = 1
        thresholds = node_info.get("thresholds", {}) if isinstance(node_info, dict) else {}
        try:
            threshold_4x = int(thresholds.get("4x", 999))
        except:
            threshold_4x = 999
        try:
            threshold_3x = int(thresholds.get("3x", 999))
        except:
            threshold_3x = 999
        try:
            threshold_2x = int(thresholds.get("2x", 999))
        except:
            threshold_2x = 999
        if value >= threshold_4x:
            return 4.0
        if value >= threshold_3x:
            return 3.0
        if value >= threshold_2x:
            return 2.0
        return 1.0

    def parse_multiplier_label(self, label):
        m = re.search(r'([0-9]+(?:\.[0-9]+)?)x', str(label or ''))
        if not m:
            return 1.0
        try:
            value = float(m.group(1))
            return value if value > 0 else 1.0
        except:
            return 1.0

    def get_mining_node_catalog(self):
        return [
            {"key": "rock", "display": "Rock", "itemId": "1100", "toolTier": "Rock"},
            {"key": "bronze", "display": "Bronze", "itemId": "1101", "toolTier": "Bronze"},
            {"key": "silver", "display": "Silver", "itemId": "1102", "toolTier": "Silver"},
            {"key": "jade", "display": "Jade", "itemId": "1103", "toolTier": "Jade"},
            {"key": "gold", "display": "Gold", "itemId": "1104", "toolTier": "Gold"},
            {"key": "platinum", "display": "Platinum", "itemId": "1105", "toolTier": "Platinum"},
            {"key": "gemrock", "display": "Gemrock", "itemId": None, "toolTier": None},
            {"key": "diamond", "display": "Diamond", "itemId": "1106", "toolTier": "Diamond"},
            {"key": "sunstone", "display": "Sunstone", "itemId": "1107", "toolTier": None}
        ]

    def get_item_sell_gp(self, item_id):
        if item_id is None:
            return None
        meta = self.item_meta.get(str(item_id), {}) if isinstance(self.item_meta, dict) else {}
        value = meta.get("sell_gp") if isinstance(meta, dict) else None
        try:
            return float(value)
        except:
            return None

    def get_mining_calculator_report(self, state):
        if not isinstance(state, dict) or not state:
            return {"error": "No save data loaded."}

        skills = state.get('skills', {}) if isinstance(state.get('skills', {}), dict) else {}
        mining = skills.get('1003', {}) if isinstance(skills, dict) else {}
        mining_level = int(mining.get('level', 1) or 1)
        boosted_level = int(mining.get('boostedLevel', mining_level) or mining_level)
        speed_mult = float(mining.get('currentSpeedMultiplier', 1) or 1)
        loot_mult = float(mining.get('currentLootMultiplier', 1) or 1)
        xp_mult = float(mining.get('currentXpMultiplier', 1) or 1)
        diary_factor = round(self.get_skill_diary_speed_factor(state, '1003'), 4)
        tool_tiers = {}
        for row in self.map_tool_ids_to_tiers(mining.get('toolIds')):
            tier_name = row.get('tier')
            if tier_name:
                tool_tiers[tier_name] = row.get('toolId')

        nodes = (self.mining_db or {}).get('nodes', {}) if isinstance(self.mining_db, dict) else {}
        report = {
            "capturedAt": datetime.now().isoformat(),
            "saveSource": self.latest_save_source,
            "summary": {
                "miningLevel": mining_level,
                "boostedMiningLevel": boosted_level,
                "skillSpeedMultiplier": speed_mult,
                "skillLootMultiplier": loot_mult,
                "skillXpMultiplier": xp_mult,
                "diarySpeedFactor": diary_factor,
                "toolTiersUnlocked": tool_tiers
            },
            "nodes": []
        }

        for catalog_row in self.get_mining_node_catalog():
            key = catalog_row["key"]
            node = nodes.get(key, {}) if isinstance(nodes, dict) else {}
            node_speed_mult = self.parse_node_multiplier(node)
            level_gate_mult = self.get_node_level_gate_multiplier(node, boosted_level)
            try:
                base_action = float(node.get('default_time_seconds')) if node.get('default_time_seconds') is not None else None
            except:
                base_action = None
            estimated_action = self.estimate_action_time_seconds(base_action, speed_mult, node_speed_mult, diary_factor) if base_action is not None else None

            try:
                base_xp = float(node.get('default_xp')) if node.get('default_xp') is not None else None
            except:
                base_xp = None
            xp_per_action = round(base_xp * xp_mult * level_gate_mult, 4) if base_xp is not None else None

            xp_per_hour = None
            actions_per_hour = None
            if estimated_action and estimated_action > 0:
                actions_per_hour = round(3600.0 / float(estimated_action), 4)
                if xp_per_action is not None:
                    xp_per_hour = round(actions_per_hour * xp_per_action, 4)

            sell_gp = node.get('sell_gp') if isinstance(node, dict) else None
            try:
                sell_gp = float(sell_gp) if sell_gp is not None else self.get_item_sell_gp(catalog_row.get('itemId'))
            except:
                sell_gp = self.get_item_sell_gp(catalog_row.get('itemId'))
            try:
                default_output = float(node.get('default_output')) if node.get('default_output') is not None else None
            except:
                default_output = None
            try:
                base_loot_factor = float(node.get('base_loot_factor')) if node.get('base_loot_factor') is not None else 1.0
            except:
                base_loot_factor = 1.0
            loot_per_action = round(default_output * base_loot_factor * loot_mult * level_gate_mult, 4) if default_output is not None else None
            gp_per_hour = round(actions_per_hour * loot_per_action * sell_gp, 4) if actions_per_hour is not None and sell_gp is not None and loot_per_action is not None else None

            tier_name = catalog_row.get('toolTier')
            report["nodes"].append({
                "key": key,
                "displayName": catalog_row["display"],
                "toolTier": tier_name,
                "toolId": tool_tiers.get(tier_name) if tier_name else None,
                "nodeSpeedMultiplier": node_speed_mult,
                "levelGateMultiplier": level_gate_mult,
                "baseActionSeconds": base_action,
                "actionSeconds": estimated_action,
                "baseXpPerAction": base_xp,
                "xpPerAction": xp_per_action,
                "actionsPerHour": actions_per_hour,
                "xpPerHour": xp_per_hour,
                "itemId": catalog_row.get('itemId'),
                "itemName": self.get_item_name(catalog_row.get('itemId')) if catalog_row.get('itemId') else None,
                "lootPerAction": loot_per_action,
                "sellGpEach": sell_gp,
                "gpPerHour": gp_per_hour,
                "thresholds": node.get('thresholds') if isinstance(node, dict) else None,
                "notes": "Action time uses save speed and diary factors; XP and loot use node defaults, save multipliers, and node-specific level thresholds."
            })
        return report

    def estimate_action_time_seconds(self, base_seconds, speed_multiplier, node_multiplier, diary_factor):
        try:
            base = float(base_seconds)
            speed = float(speed_multiplier)
            node = float(node_multiplier)
            diary = float(diary_factor)
            if base <= 0 or speed <= 0 or node <= 0 or diary <= 0:
                return None
            return round(base / (speed * node * diary), 4)
        except:
            return None

    def extract_skill_tier_data(self, state):
        skills = state.get('skills', {})
        ltp = state.get('currentLongTermProcesses', {})
        by_skill = {}
        for sid, name in self.skill_map.items():
            sd = skills.get(sid, {}) if isinstance(skills, dict) else {}
            speed = sd.get('currentSpeedMultiplier', 1)
            loot = sd.get('currentLootMultiplier', 1)
            xp = sd.get('currentXpMultiplier', 1)
            process_rows = []
            skill_proc = ltp.get(sid, {}) if isinstance(ltp, dict) else {}
            if isinstance(skill_proc, dict):
                for slot, row in skill_proc.items():
                    if isinstance(row, dict):
                        process_rows.append({
                            "slot": str(slot),
                            "resourceId": row.get("resourceId"),
                            "durationMs": row.get("duration"),
                            "status": row.get("status"),
                            "xpMultiplier": row.get("xpMultiplier"),
                            "lootMultiplier": row.get("lootMultiplier")
                        })
            by_skill[sid] = {
                "name": name,
                "speedMultiplier": speed,
                "lootMultiplier": loot,
                "xpMultiplier": xp,
                "inferredTier": self.infer_tier_name(speed),
                "activeProcesses": process_rows
            }
        return {
            "capturedAt": datetime.now().isoformat(),
            "saveSource": self.latest_save_source,
            "skills": by_skill
        }

    def sync_item_meta_from_state(self, item_totals):
        changed = False
        for i_id in item_totals.keys():
            key = str(i_id)
            if key not in self.item_meta:
                self.item_meta[key] = {"name": self.get_item_name(key)}
                changed = True
            elif "name" not in self.item_meta[key]:
                self.item_meta[key]["name"] = self.get_item_name(key)
                changed = True
        if changed:
            self.save_item_meta()

    def extract_diary_booster_data(self, state):
        completed = state.get('completedAchievementDiary', {})
        area_id_map = {
            "1001": "Forest",
            "1002": "Mind",
            "1003": "Seas",
            "1004": "Field",
            "1005": "Temple",
            "1006": "Market"
        }
        area_skill_map = self.get_area_skill_map()
        areas = {}
        for area_id, area_name in area_id_map.items():
            row = completed.get(area_id, {}) if isinstance(completed, dict) else {}
            easy_done = str(row.get('EASY', '')).lower() == 'completed'
            expert_done = str(row.get('EXPERT', '')).lower() == 'completed'
            skill_ids = area_skill_map.get(area_id, [])
            areas[area_id] = {
                "areaName": area_name,
                "easyCompleted": easy_done,
                "expertCompleted": expert_done,
                "easySpeedBonusPct": 15 if easy_done else 0,
                "expertSpeedBonusPct": 100 if expert_done else 0,
                "affectedSkillIds": skill_ids,
                "affectedSkills": [self.skill_map.get(sid, sid) for sid in skill_ids]
            }
        return {
            "capturedAt": datetime.now().isoformat(),
            "saveSource": self.latest_save_source,
            "notes": "Affected skills are based on user-provided area mapping.",
            "areas": areas
        }

    def extract_multiplier_snapshot(self, state):
        skills = state.get('skills', {})
        ltp = state.get('currentLongTermProcesses', {})
        report = {
            "capturedAt": datetime.now().isoformat(),
            "saveSource": self.latest_save_source,
            "skills": {},
            "subskillMultipliers": {}
        }

        for sid, name in self.skill_map.items():
            sk = skills.get(sid, {}) if isinstance(skills, dict) else {}
            tool_ids = sk.get("toolIds")
            report["skills"][sid] = {
                "name": name,
                "currentSpeedMultiplier": sk.get("currentSpeedMultiplier"),
                "currentLootMultiplier": sk.get("currentLootMultiplier"),
                "currentXpMultiplier": sk.get("currentXpMultiplier"),
                "toolIds": tool_ids,
                "toolTiers": self.map_tool_ids_to_tiers(tool_ids),
                "toolTierOrder": self.get_tool_tier_names()
            }

        if isinstance(ltp, dict):
            for sid, slots in ltp.items():
                skill_name = self.skill_map.get(str(sid), f"Skill {sid}")
                rows = []
                if isinstance(slots, dict):
                    for slot, row in slots.items():
                        if isinstance(row, dict):
                            rows.append({
                                "slot": str(slot),
                                "resourceId": row.get("resourceId"),
                                "status": row.get("status"),
                                "xpMultiplier": row.get("xpMultiplier"),
                                "lootMultiplier": row.get("lootMultiplier"),
                                "durationMs": row.get("duration")
                            })
                report["subskillMultipliers"][str(sid)] = {
                    "name": skill_name,
                    "slots": rows
                }

        # Keep true action-time math separate from long-process duration values.
        mining_skill = report["skills"].get("1003", {})
        mining_speed_mult = mining_skill.get("currentSpeedMultiplier") or 1
        mining_diary_factor = self.get_skill_diary_speed_factor(state, "1003")
        mining_nodes = (self.mining_db or {}).get("nodes", {}) if isinstance(self.mining_db, dict) else {}
        rock_node = mining_nodes.get("rock", {}) if isinstance(mining_nodes, dict) else {}
        rock_node_mult = self.parse_node_multiplier(rock_node)
        rock_observed_action = rock_node.get("action_time_seconds") if isinstance(rock_node, dict) else None
        rock_estimated_action = self.estimate_action_time_seconds(8.0, mining_speed_mult, rock_node_mult, mining_diary_factor)

        mining_process_duration_ms = None
        mining_processes = report["subskillMultipliers"].get("1003", {}).get("slots", [])
        if mining_processes:
            mining_process_duration_ms = mining_processes[0].get("durationMs")

        delta = None
        aligned = None
        try:
            if rock_estimated_action is not None and rock_observed_action is not None:
                delta = round(abs(float(rock_estimated_action) - float(rock_observed_action)), 4)
                aligned = delta <= 0.03
        except:
            pass

        report["actionTiming"] = {
            "mining": {
                "baseRockActionSeconds": 8.0,
                "skillSpeedMultiplier": mining_speed_mult,
                "rockNodeMultiplier": rock_node_mult,
                "diarySpeedFactor": round(mining_diary_factor, 4),
                "estimatedRockActionSeconds": rock_estimated_action,
                "observedRockActionSeconds": rock_observed_action,
                "alignmentDeltaSeconds": delta,
                "aligned": aligned,
                "processDurationMs": mining_process_duration_ms,
                "notes": "Action time is calculated separately from process duration."
            }
        }
        report["miningCalculator"] = self.get_mining_calculator_report(state)
        return report

    def get_mining_calculator_dump_text(self):
        if not self.latest_save_data:
            return "No save data loaded."
        try:
            return json.dumps(self.get_mining_calculator_report(self.latest_save_data), indent=2)
        except Exception:
            return "Failed to build mining calculator report."

    def show_mining_calculator_popup(self):
        report = self.get_mining_calculator_report(self.latest_save_data) if self.latest_save_data else {"error": "No save data loaded."}
        pop = ctk.CTkToplevel(self)
        pop.title("Mining Calculator")
        self._set_popup_topmost(pop)
        self._place_popup_near_main(pop, width=980, height=720)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ctk.CTkLabel(container, text="Mining Calculator", font=("Segoe UI", 13, "bold"), text_color="#dfe6ef").pack(anchor="w", pady=(0, 6))

        summary = report.get("summary", {}) if isinstance(report, dict) else {}
        summary_text = (
            f"Level: {summary.get('miningLevel', '--')} | "
            f"Boosted: {summary.get('boostedMiningLevel', '--')} | "
            f"Speed: x{summary.get('skillSpeedMultiplier', '--')} | "
            f"Loot: x{summary.get('skillLootMultiplier', '--')} | "
            f"XP: x{summary.get('skillXpMultiplier', '--')} | "
            f"Diary Speed: x{summary.get('diarySpeedFactor', '--')}"
        ) if summary else report.get("error", "No mining data.")
        ctk.CTkLabel(container, text=summary_text, font=("Segoe UI", 11), text_color="#8e9db5").pack(anchor="w", pady=(0, 8))

        scroll = ctk.CTkScrollableFrame(container, fg_color="#141414", corner_radius=12)
        scroll.pack(fill="both", expand=True, pady=(0, 10))

        for row in report.get("nodes", []):
            card = ctk.CTkFrame(scroll, fg_color="#1f1f1f", corner_radius=10, border_width=1, border_color="#2f2f2f")
            card.pack(fill="x", padx=8, pady=6)

            title = row.get("displayName", "Unknown")
            tool_id = row.get("toolId")
            tool_text = f"{row.get('toolTier')} [{tool_id}]" if row.get('toolTier') and tool_id else (row.get('toolTier') or "No tool tier")
            ctk.CTkLabel(card, text=title, font=("Segoe UI", 12, "bold"), text_color="#dfe6ef").pack(anchor="w", padx=12, pady=(10, 2))
            ctk.CTkLabel(card, text=f"Tool: {tool_text} | Level Gate: x{row.get('levelGateMultiplier', '--')} | Node Speed: x{row.get('nodeSpeedMultiplier', '--')}", font=("Segoe UI", 10), text_color="#8e9db5").pack(anchor="w", padx=12, pady=(0, 6))

            line_one = (
                f"Action: {row.get('actionSeconds', '--')}s | "
                f"XP/Action: {self.format_number(row.get('xpPerAction', 0)) if row.get('xpPerAction') is not None else '--'} | "
                f"XP/h: {self.format_number(row.get('xpPerHour', 0)) if row.get('xpPerHour') is not None else '--'}"
            )
            ctk.CTkLabel(card, text=line_one, font=("Segoe UI", 11), text_color="#dfe6ef").pack(anchor="w", padx=12, pady=(0, 4))

            gp_text = self.format_number(row.get('gpPerHour', 0)) if row.get('gpPerHour') is not None else "N/A"
            sell_text = row.get('sellGpEach') if row.get('sellGpEach') is not None else "N/A"
            line_two = (
                f"Actions/h: {self.format_number(row.get('actionsPerHour', 0)) if row.get('actionsPerHour') is not None else '--'} | "
                f"Loot/Action: {row.get('lootPerAction', 'N/A')} | Sell Each: {sell_text} | "
                f"GP/h: {gp_text}"
            )
            ctk.CTkLabel(card, text=line_two, font=("Segoe UI", 11), text_color="#dfe6ef").pack(anchor="w", padx=12, pady=(0, 10))

        footer = ctk.CTkFrame(container, fg_color="transparent")
        footer.pack(fill="x")

        def copy_text():
            try:
                self.clipboard_clear()
                self.clipboard_append(json.dumps(report, indent=2))
            except:
                pass

        def dump_text():
            try:
                path = fd.asksaveasfilename(defaultextension=".json", filetypes=[("JSON files", "*.json"), ("Text files", "*.txt")])
                if path:
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(json.dumps(report, indent=2))
            except:
                pass

        ctk.CTkButton(footer, text="COPY", width=100, command=copy_text).pack(side="left", padx=(0, 6))
        ctk.CTkButton(footer, text="DUMP", width=100, command=dump_text).pack(side="left")
        ctk.CTkButton(footer, text="CLOSE", width=100, command=pop.destroy).pack(side="right")

    def get_multiplier_dump_text(self):
        if not self.latest_save_data:
            return "No save data loaded."
        try:
            return json.dumps(self.extract_multiplier_snapshot(self.latest_save_data), indent=2)
        except Exception:
            return "Failed to build multiplier snapshot."

    def show_multipliers_popup(self):
        content = self.get_multiplier_dump_text()
        pop = ctk.CTkToplevel(self)
        pop.title("Skill & Subskill Multipliers")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ctk.CTkLabel(container, text="Skill & Subskill Multipliers", font=("Segoe UI", 12, "bold"), text_color="#dfe6ef").pack(anchor="w", pady=(0, 8))

        content_frame = ctk.CTkFrame(container, fg_color="#141414", corner_radius=12)
        content_frame.pack(fill="both", expand=True, pady=(0, 10))
        text_widget = tk.Text(content_frame, wrap="none", bg="#141414", fg="#dfe6ef", insertbackground="#dfe6ef", bd=0, highlightthickness=0)
        text_widget.pack(side="left", fill="both", expand=True, padx=(8, 0), pady=8)
        yscroll = tk.Scrollbar(content_frame, orient="vertical", command=text_widget.yview)
        yscroll.pack(side="right", fill="y")
        text_widget.configure(yscrollcommand=yscroll.set)
        text_widget.insert("1.0", content)
        text_widget.configure(state="disabled")

        footer = ctk.CTkFrame(container, fg_color="transparent")
        footer.pack(fill="x")

        def copy_text():
            try:
                self.clipboard_clear()
                self.clipboard_append(content)
            except:
                pass

        def dump_text():
            try:
                path = fd.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt"), ("JSON files", "*.json")])
                if path:
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(content)
            except:
                pass

        ctk.CTkButton(footer, text="COPY", width=100, command=copy_text).pack(side="left", padx=(0, 6))
        ctk.CTkButton(footer, text="DUMP", width=100, command=dump_text).pack(side="left")
        ctk.CTkButton(footer, text="CLOSE", width=100, command=pop.destroy).pack(side="right")
        self._place_popup_near_main(pop)

    def _eval_num_expr(self, expr, env):
        if expr is None:
            return None
        text = str(expr).strip().replace("Math.floor", "floor").replace("Math.ceil", "ceil").replace("Math.round", "round")
        if not text:
            return None
        try:
            node = __import__("ast").parse(text, mode="eval")
        except Exception:
            return None

        def _ev(n):
            if isinstance(n, __import__("ast").Expression):
                return _ev(n.body)
            if isinstance(n, __import__("ast").Constant) and isinstance(n.value, (int, float)):
                return float(n.value)
            if isinstance(n, __import__("ast").Name):
                if n.id in env:
                    return float(env[n.id])
                raise KeyError(n.id)
            if isinstance(n, __import__("ast").UnaryOp) and isinstance(n.op, (__import__("ast").UAdd, __import__("ast").USub)):
                v = _ev(n.operand)
                return v if isinstance(n.op, __import__("ast").UAdd) else -v
            if isinstance(n, __import__("ast").BinOp) and isinstance(n.op, (__import__("ast").Add, __import__("ast").Sub, __import__("ast").Mult, __import__("ast").Div, __import__("ast").FloorDiv)):
                a = _ev(n.left)
                b = _ev(n.right)
                if isinstance(n.op, __import__("ast").Add):
                    return a + b
                if isinstance(n.op, __import__("ast").Sub):
                    return a - b
                if isinstance(n.op, __import__("ast").Mult):
                    return a * b
                if isinstance(n.op, __import__("ast").Div):
                    return a / b
                return a // b
            if isinstance(n, __import__("ast").Call) and isinstance(n.func, __import__("ast").Name):
                args = [_ev(a) for a in n.args]
                if n.func.id == "floor":
                    return float(math.floor(args[0]))
                if n.func.id == "ceil":
                    return float(math.ceil(args[0]))
                if n.func.id == "round":
                    return float(round(args[0]))
            raise ValueError("Unsupported expression")

        try:
            return float(_ev(node))
        except Exception:
            return None

    def _title_from_enum(self, enum_name):
        parts = str(enum_name or "").replace("_", " ").split()
        return " ".join(p.capitalize() for p in parts) if parts else "Unknown"

    def _item_sell_gp_from_enum(self, enum_name):
        cache = getattr(self, "_skill_optimizer_cache", None)
        if not isinstance(cache, dict):
            return 0.0
        # First: check the static price table built from item_price_array.json
        enum_to_sell_gp = cache.get("enum_to_sell_gp", {})
        if isinstance(enum_to_sell_gp, dict) and enum_name in enum_to_sell_gp:
            return float(enum_to_sell_gp[enum_name])
        # Fallback: check live item_meta (player inventory-derived)
        enum_to_id = cache.get("enum_to_id", {}) if isinstance(cache.get("enum_to_id"), dict) else {}
        item_id = enum_to_id.get(str(enum_name or ""))
        if item_id is None:
            return 0.0
        value = self.get_item_sell_gp(str(item_id))
        return float(value) if value is not None else 0.0

    def _extract_resource_blocks(self, source_text):
        blocks = []
        if not isinstance(source_text, str) or not source_text:
            return blocks
        pos = 0
        while True:
            m = re.search(r'\[ResourceIds\.([A-Z0-9_]+)\]\s*:\s*\{', source_text[pos:])
            if not m:
                break
            key = m.group(1)
            start = pos + m.end() - 1
            depth = 0
            end = start
            while end < len(source_text):
                ch = source_text[end]
                if ch == '{':
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0:
                        break
                end += 1
            block_text = source_text[start:end + 1]
            req_m = re.search(r'skillReq\s*:\s*\{\s*\[SkillsId\.([A-Za-z]+)\]\s*:\s*([^\}]+)\}', block_text)
            time_m = re.search(r'\btime\s*:\s*([^,\n]+)', block_text)
            xp_m = re.search(r'xp\s*:\s*\{\s*\[SkillsId\.([A-Za-z]+)\]\s*:\s*([^\}]+)\}', block_text)
            loot_m = re.search(r'lootMultiplierLevelMap\s*:\s*([A-Za-z0-9_]+)', block_text)
            if req_m and time_m and xp_m and loot_m:
                blocks.append({
                    "resource": key,
                    "skill": req_m.group(1),
                    "skill_req_expr": req_m.group(2).strip().rstrip(','),
                    "time_expr": time_m.group(1).strip().rstrip(','),
                    "xp_expr": xp_m.group(2).strip().rstrip(','),
                    "loot_var": loot_m.group(1).strip(),
                    "block_text": block_text,
                })
            pos = end + 1
        return blocks

    def _parse_item_refs(self, block_text, section_name):
        refs = []
        sec_m = re.search(section_name + r'\s*:\s*\[([\s\S]*?)\]', block_text)
        if not sec_m:
            return refs
        section = sec_m.group(1)
        for m in re.finditer(r'createItemRef\(\s*ItemIds\.([A-Z0-9_]+)(?:\s*,\s*([^,\)]+))?(?:\s*,\s*([^\)]+))?\)', section):
            refs.append({
                "enum": m.group(1),
                "amount_expr": (m.group(2) or "1").strip(),
                "prob_expr": (m.group(3) or "1").strip(),
            })
        return refs

    def _ensure_skill_optimizer_cache(self):
        cache = getattr(self, "_skill_optimizer_cache", None)
        if isinstance(cache, dict) and cache.get("ready"):
            skill_blocks = cache.get("skill_blocks", {}) if isinstance(cache.get("skill_blocks"), dict) else {}
            required_skills = ("woodcutting", "thieving", "smithing", "fishing", "cooking")
            if all(k in skill_blocks for k in required_skills) and isinstance(cache.get("name_to_sell_gp"), dict):
                return cache

        cache = {
            "ready": False,
            "lookup": {},
            "constants": {},
            "loot_maps": {},
            "skill_blocks": {"woodcutting": [], "thieving": [], "smithing": [], "fishing": [], "cooking": []},
            "enum_to_id": {},
        }
        self._skill_optimizer_cache = cache

        map_path = self._resource_path(os.path.join("GameData", "index-B1HmVF50.js.map"))
        if not os.path.exists(map_path):
            map_path = os.path.join("GameData", "index-B1HmVF50.js.map")
        if not os.path.exists(map_path):
            return cache

        src_map = self._load_json_file(map_path, default={})
        if not isinstance(src_map, dict):
            return cache
        sources = src_map.get("sources", [])
        contents = src_map.get("sourcesContent", [])
        if not isinstance(sources, list) or not isinstance(contents, list):
            return cache

        lookup = dict(zip(sources, contents))
        cache["lookup"] = lookup

        item_ids_src = lookup.get("../../src/data/ItemData/AllItemsIds.ts", "")
        for m in re.finditer(r'([A-Z0-9_]+)\s*=\s*"?(\d+)"?\s*,?', item_ids_src):
            cache["enum_to_id"][m.group(1)] = m.group(2)

        loot_src = lookup.get("../../src/data/utilData/LootMultiplierData/LootMultiplierData.ts", "")
        loot_block = re.search(r'LootMultiplierMapTest[\s\S]*?=\s*\{([\s\S]*?)\n\};', loot_src)
        if loot_block:
            body = loot_block.group(1)
            for tier_m in re.finditer(r'(\d+)\s*:\s*\{([\s\S]*?)\}', body):
                tier = int(tier_m.group(1))
                sub = tier_m.group(2)
                table = {}
                for kv in re.finditer(r'(\d+)\s*:\s*(\d+)', sub):
                    table[int(kv.group(1))] = int(kv.group(2))
                cache["loot_maps"][f"lootMultiplierTier{tier}"] = table

        const_files = [
            "../../src/data/utilData/ClueData/ClueDropRate.ts",
            "../../src/data/skillsData/SkillsEnum.ts",
            "../../src/data/utilData/SkillBossData/SkillBossConst.ts",
            "../../src/data/Constants.ts",
            "../../src/data/skillsData/Smithing/smithingConst.ts",
            "../../src/data/skillsData/Smithing/SmithingResourcesBronze.ts",
        ]
        for path in lookup:
            if "/skillsData/Smithing/SmithingResources" in path and path not in const_files:
                const_files.append(path)

        raw_consts = {}
        for path in const_files:
            text = lookup.get(path, "")
            for m in re.finditer(r'(?:export\s+)?const\s+([A-Z0-9_]+)\s*=\s*([^;]+);', text):
                key = m.group(1)
                if key not in raw_consts:
                    raw_consts[key] = m.group(2).strip()

        resolved = {}
        for _ in range(24):
            progressed = False
            for key, expr in raw_consts.items():
                if key in resolved:
                    continue
                val = self._eval_num_expr(expr, resolved)
                if val is not None:
                    resolved[key] = val
                    progressed = True
            if not progressed:
                break
        cache["constants"] = resolved

        wc_src = lookup.get("../../src/data/skillsData/Woodcutting/woodcutting.core.ts", "")
        th_src = lookup.get("../../src/data/skillsData/Thieving/thieving.core.ts", "")
        cache["skill_blocks"]["woodcutting"] = self._extract_resource_blocks(wc_src)
        cache["skill_blocks"]["thieving"] = self._extract_resource_blocks(th_src)

        smith_blocks = []
        for path, text in lookup.items():
            if "/skillsData/Smithing/SmithingResources" in path:
                smith_blocks.extend(self._extract_resource_blocks(text))
        cache["skill_blocks"]["smithing"] = smith_blocks

        fish_src = lookup.get("../../src/data/skillsData/Fishing/fishing.core.ts", "")
        cook_src = lookup.get("../../src/data/skillsData/Cooking/cooking.core.ts", "")
        cache["skill_blocks"]["fishing"] = self._extract_resource_blocks(fish_src)
        cache["skill_blocks"]["cooking"] = self._extract_resource_blocks(cook_src)

        # Build enum -> sell_gp, id -> sell_gp, and name -> sell_gp lookups from item_price_array.json
        price_arr = self._load_json_file("item_price_array.json", default=[])
        enum_to_sell_gp = {}
        id_to_sell_gp = {}
        name_to_sell_gp = {}
        if isinstance(price_arr, list):
            for entry in price_arr:
                if isinstance(entry, dict):
                    try:
                        gp = float(entry.get("sell_gp") or 0)
                    except Exception:
                        gp = 0.0
                    if "enum" in entry:
                        enum_to_sell_gp[entry["enum"]] = gp
                    if "id" in entry:
                        id_to_sell_gp[str(entry["id"])] = gp
                    if "name" in entry:
                        name_to_sell_gp[str(entry["name"])] = gp
        cache["enum_to_sell_gp"] = enum_to_sell_gp
        cache["id_to_sell_gp"] = id_to_sell_gp
        cache["name_to_sell_gp"] = name_to_sell_gp

        cache["ready"] = True
        return cache

    def _loot_level_multiplier(self, loot_var, level):
        cache = self._ensure_skill_optimizer_cache()
        table = cache.get("loot_maps", {}).get(str(loot_var), {})
        if not isinstance(table, dict) or not table:
            return 1.0
        out = 1.0
        for req, mul in sorted(table.items(), key=lambda x: x[0]):
            try:
                if int(level) >= int(req):
                    out = float(mul)
            except Exception:
                continue
        return out

    def _expected_gp_per_action(self, block_text, loot_multiplier, constants):
        gain_total = 0.0
        for section in ("itemGainAlways", "itemGainWithProbability"):
            for row in self._parse_item_refs(block_text, section):
                amount = self._eval_num_expr(row.get("amount_expr"), constants)
                prob = self._eval_num_expr(row.get("prob_expr"), constants)
                if amount is None:
                    amount = 0.0
                if prob is None:
                    prob = 0.0
                gain_total += float(amount) * float(prob) * self._item_sell_gp_from_enum(row.get("enum"))

        cost_total = 0.0
        for row in self._parse_item_refs(block_text, "itemCost"):
            amount = self._eval_num_expr(row.get("amount_expr"), constants)
            prob = self._eval_num_expr(row.get("prob_expr"), constants)
            if amount is None:
                amount = 0.0
            if prob is None:
                prob = 1.0
            cost_total += float(amount) * float(prob) * self._item_sell_gp_from_enum(row.get("enum"))

        return (gain_total * float(loot_multiplier)) - cost_total

    def _compute_source_skill_rows(self, skill_key, skill_id, state):
        cache = self._ensure_skill_optimizer_cache()
        if not cache.get("ready"):
            return []

        skills = state.get("skills", {}) if isinstance(state, dict) else {}
        sk = skills.get(str(skill_id), {}) if isinstance(skills, dict) else {}
        level = int(sk.get("boostedLevel", sk.get("level", 1)) or 1)
        speed_mult = float(sk.get("currentSpeedMultiplier", 1) or 1)
        xp_mult = float(sk.get("currentXpMultiplier", 1) or 1)
        diary_factor = float(self.get_skill_diary_speed_factor(state, str(skill_id)) or 1)

        constants = cache.get("constants", {}) if isinstance(cache.get("constants"), dict) else {}
        rows = []
        for block in cache.get("skill_blocks", {}).get(skill_key, []):
            req = self._eval_num_expr(block.get("skill_req_expr"), constants)
            base_time = self._eval_num_expr(block.get("time_expr"), constants)
            base_xp = self._eval_num_expr(block.get("xp_expr"), constants)
            if req is None or base_time is None or base_xp is None:
                continue
            req_int = int(req)
            if level < req_int:
                continue

            loot_mult = self._loot_level_multiplier(block.get("loot_var"), level)
            action_seconds = self.estimate_action_time_seconds(base_time, speed_mult, 1.0, diary_factor)
            if action_seconds is None or action_seconds <= 0:
                continue
            actions_per_hour = 3600.0 / float(action_seconds)
            xp_per_action = float(base_xp) * xp_mult  # loot tier only affects loot drops, not base XP
            gp_per_action = self._expected_gp_per_action(block.get("block_text", ""), loot_mult, constants)
            rows.append({
                "name": self._title_from_enum(block.get("resource")),
                "levelReq": req_int,
                "xpPerHour": actions_per_hour * xp_per_action,
                "gpPerHour": actions_per_hour * gp_per_action,
            })
        return rows

    def _pick_best_rows(self, rows):
        if not rows:
            return {"xp": None, "gp": None, "balanced": None}
        xp_best = max(rows, key=lambda r: float(r.get("xpPerHour", 0) or 0))
        gp_best = max(rows, key=lambda r: float(r.get("gpPerHour", 0) or 0))
        max_xp = max(float(r.get("xpPerHour", 0) or 0) for r in rows) or 1.0
        max_gp = max(float(r.get("gpPerHour", 0) or 0) for r in rows) or 1.0
        balanced = max(
            rows,
            key=lambda r: 0.5 * ((float(r.get("xpPerHour", 0) or 0) / max_xp) + (float(r.get("gpPerHour", 0) or 0) / max_gp)),
        )
        return {"xp": xp_best, "gp": gp_best, "balanced": balanced}

    def _compute_source_next_unlock(self, skill_key, skill_id, state):
        cache = self._ensure_skill_optimizer_cache()
        if not cache.get("ready"):
            return None

        skills = state.get("skills", {}) if isinstance(state, dict) else {}
        sk = skills.get(str(skill_id), {}) if isinstance(skills, dict) else {}
        level = int(sk.get("boostedLevel", sk.get("level", 1)) or 1)
        constants = cache.get("constants", {}) if isinstance(cache.get("constants"), dict) else {}

        locked = []
        for block in cache.get("skill_blocks", {}).get(skill_key, []):
            req = self._eval_num_expr(block.get("skill_req_expr"), constants)
            if req is None:
                continue
            req_int = int(req)
            if req_int > level:
                locked.append({"name": self._title_from_enum(block.get("resource")), "levelReq": req_int})

        if not locked:
            return None
        next_req = min(int(r.get("levelReq", 9999)) for r in locked)
        candidates = [r for r in locked if int(r.get("levelReq", 0)) == next_req]
        chosen = sorted(candidates, key=lambda r: str(r.get("name", "")))[0] if candidates else locked[0]
        return {
            "name": chosen.get("name", "Unknown"),
            "levelReq": int(chosen.get("levelReq", next_req)),
            "levelsToGo": max(0, int(next_req) - int(level)),
        }

    def _compute_mining_next_unlock(self, state):
        if not isinstance(state, dict):
            return None

        skills = state.get('skills', {}) if isinstance(state.get('skills'), dict) else {}
        mining = skills.get('1003', {}) if isinstance(skills, dict) else {}
        try:
            level = int(mining.get('level', 1) or 1)
        except Exception:
            level = 1

        nodes = (self.mining_db or {}).get('nodes', {}) if isinstance(self.mining_db, dict) else {}
        if not isinstance(nodes, dict) or not nodes:
            return None

        locked = []
        for row in self.get_mining_node_catalog():
            key = row.get('key')
            node = nodes.get(key, {}) if isinstance(nodes, dict) else {}
            thresholds = node.get('thresholds', {}) if isinstance(node, dict) else {}
            if not isinstance(thresholds, dict):
                continue
            for tier in ('2x', '3x', '4x'):
                try:
                    req = int(thresholds.get(tier, 999))
                except Exception:
                    continue
                if req <= level or req >= 999:
                    continue
                name = row.get('display', str(key or 'Unknown'))
                locked.append({
                    'name': f"{name} {tier}",
                    'levelReq': req,
                })

        if not locked:
            return None
        next_req = min(int(item.get('levelReq', 9999)) for item in locked)
        candidates = [item for item in locked if int(item.get('levelReq', 0)) == next_req]
        chosen = sorted(candidates, key=lambda item: str(item.get('name', '')))[0] if candidates else locked[0]
        return {
            'name': chosen.get('name', 'Unknown'),
            'levelReq': int(chosen.get('levelReq', next_req)),
            'levelsToGo': max(0, int(next_req) - int(level)),
        }

    def get_skill_optimizer_report(self, state):
        if not isinstance(state, dict) or not state:
            return {"error": "No save data loaded.", "skills": {}}

        skills = state.get("skills", {}) if isinstance(state.get("skills"), dict) else {}
        out = {"skills": {}}

        mining_rows = []
        mining_report = self.get_mining_calculator_report(state)
        for row in mining_report.get("nodes", []) if isinstance(mining_report, dict) else []:
            xp_h = row.get("xpPerHour")
            gp_h = row.get("gpPerHour")
            if xp_h is None:
                continue
            mining_rows.append({
                "name": row.get("displayName", "Unknown"),
                "xpPerHour": float(xp_h or 0),
                "gpPerHour": float(gp_h or 0),
            })
        out["skills"]["mining"] = {
            "level": int((skills.get("1003", {}) or {}).get("level", 1) or 1),
            "best": self._pick_best_rows(mining_rows),
            "nextUnlock": self._compute_mining_next_unlock(state),
        }

        skill_defs = [
            ("woodcutting", "1017"),
            ("thieving", "1010"),
            ("smithing", "1005"),
            ("fishing", "1008"),
            ("cooking", "1011"),
        ]
        for key, sid in skill_defs:
            rows = self._compute_source_skill_rows(key, sid, state)
            out["skills"][key] = {
                "level": int((skills.get(sid, {}) or {}).get("level", 1) or 1),
                "best": self._pick_best_rows(rows),
                "nextUnlock": self._compute_source_next_unlock(key, sid, state),
            }
        return out

    def _format_best_line(self, row):
        if not isinstance(row, dict):
            return "--"
        name = row.get("name", "Unknown")
        xp_h = float(row.get("xpPerHour", 0) or 0)
        gp_h = float(row.get("gpPerHour", 0) or 0)
        return f"{name} | XP/h {self.format_number(xp_h)} | GP/h {self.format_number(gp_h)}"

    def _format_next_unlock_line(self, row):
        if not isinstance(row, dict):
            return "--"
        name = row.get("name", "Unknown")
        try:
            req = int(row.get("levelReq", 0) or 0)
        except Exception:
            req = 0
        try:
            gap = int(row.get("levelsToGo", 0) or 0)
        except Exception:
            gap = 0
        lvl_word = "lvl" if gap == 1 else "lvls"
        return f"{name} @ {req} ({gap} {lvl_word} to go)" if req > 0 else "--"

    def update_optimal_snapshot(self, state=None):
        cards = getattr(self, "optimal_cards", None)
        if not isinstance(cards, dict) or not cards:
            return

        state_obj = state if isinstance(state, dict) else (self.prev_state if isinstance(self.prev_state, dict) else {})
        report = self.get_skill_optimizer_report(state_obj)
        skills = report.get("skills", {}) if isinstance(report, dict) else {}

        for key in ("mining", "woodcutting", "thieving", "smithing", "fishing", "cooking"):
            card = cards.get(key)
            if not isinstance(card, dict):
                continue
            data = skills.get(key, {}) if isinstance(skills, dict) else {}
            level = data.get("level", "--")
            best = data.get("best", {}) if isinstance(data.get("best"), dict) else {}
            self.safe_ui(card.get("level"), "configure", text=f"Lvl {level}")
            self.safe_ui(card.get("xp"), "configure", text=self._format_best_line(best.get("xp")))
            self.safe_ui(card.get("gp"), "configure", text=self._format_best_line(best.get("gp")))
            self.safe_ui(card.get("balanced"), "configure", text=self._format_best_line(best.get("balanced")))
            self.safe_ui(card.get("next"), "configure", text=self._format_next_unlock_line(data.get("nextUnlock")))

    # --- UI SETUP ---
    # ─────────────────────────────────────────────────────────────────
    # NEW SIDEBAR UI
    # ─────────────────────────────────────────────────────────────────
    def setup_main_ui(self):
        # ── Colour tokens ────────────────────────────────────────────
        self._C = {
            "bg":       "#0f1117",
            "nav":      "#161b22",
            "nav_act":  "#21262d",
            "nav_hvr":  "#1c2128",
            "sep":      "#21262d",
            "card":     "#1a2030",
            "card_bd":  "#2d3748",
            "gold":     "#e8a000",
            "blue":     "#4f8ef7",
            "green":    "#3fb950",
            "red":      "#f0524f",
            "txt":      "#e6edf3",
            "dim":      "#8b949e",
        }
        C = self._C

        # ── Title bar ─────────────────────────────────────────────────
        self.header = ctk.CTkFrame(self.container, fg_color=C["nav"], height=52, corner_radius=0)
        self.header.pack(fill="x")
        self.header.pack_propagate(False)

        self.title_block = ctk.CTkFrame(self.header, fg_color="transparent")
        self.title_block.pack(side="left", fill="y", padx=(14, 0))
        ctk.CTkLabel(self.title_block, text="●", font=("Segoe UI", 11), text_color=C["red"]).pack(side="left", padx=(0, 10))

        _title_texts = ctk.CTkFrame(self.title_block, fg_color="transparent")
        _title_texts.pack(side="left", fill="y", pady=5)
        ctk.CTkLabel(_title_texts, text=f"Rocky Idle Reader v{self.app_version}",
                     font=("Segoe UI", 13, "bold"), text_color=C["txt"]).pack(anchor="w")
        self.profile_name_lbl = ctk.CTkLabel(_title_texts, text="No profile selected",
                     font=("Segoe UI", 9), text_color=C["dim"])
        self.profile_name_lbl.pack(anchor="w")

        self.sync_badge_lbl = ctk.CTkLabel(self.header, text="NO SYNC", width=140,
                           font=("Segoe UI", 10, "bold"), text_color="#f0524f")
        self.sync_badge_lbl.pack(side="right", padx=(0, 8))

        _btn_frame = ctk.CTkFrame(self.header, fg_color="transparent")
        _btn_frame.pack(side="right", padx=12, fill="y", pady=10)
        ctk.CTkButton(_btn_frame, text="×", width=30, height=30, corner_radius=6,
                      fg_color="#5a1e1e", hover_color=C["red"],
                      font=("Segoe UI", 15, "bold"), text_color=C["txt"],
                      command=self.on_closing).pack(side="right", padx=(3, 0))
        self.min_btn = ctk.CTkButton(_btn_frame, text="−", width=30, height=30, corner_radius=6,
                      fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                      font=("Segoe UI", 13, "bold"), text_color=C["txt"],
                      command=self.toggle_minimize)
        self.min_btn.pack(side="right", padx=3)
        ctk.CTkButton(_btn_frame, text="?", width=30, height=30, corner_radius=6,
                      fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                      font=("Segoe UI", 11), text_color=C["dim"],
                      command=self.show_help).pack(side="right", padx=(0, 3))
        ctk.CTkButton(_btn_frame, text="👤", width=30, height=30, corner_radius=6,
                  fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                  font=("Segoe UI", 10), text_color=C["dim"],
                  command=lambda: self.show_profile_picker(self.scan_available_profiles())).pack(side="right", padx=(0, 3))
        ctk.CTkButton(_btn_frame, text="≡", width=30, height=30, corner_radius=6,
                  fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                  font=("Segoe UI", 12, "bold"), text_color=C["dim"],
                  command=self.toggle_sidebar).pack(side="right", padx=(0, 3))

        # ── Header separator ──────────────────────────────────────────
        ctk.CTkFrame(self.container, height=1, fg_color=C["sep"]).pack(fill="x")

        # ── Body: sidebar + content ───────────────────────────────────
        _body = ctk.CTkFrame(self.container, fg_color="transparent")
        _body.pack(fill="both", expand=True)

        self.sidebar = ctk.CTkFrame(_body, fg_color=C["nav"], width=118, corner_radius=0)
        self.sidebar.pack(side="left", fill="y")
        self.sidebar.pack_propagate(False)

        ctk.CTkFrame(_body, width=1, fg_color=C["sep"]).pack(side="left", fill="y")

        self.content_area = ctk.CTkFrame(_body, fg_color=C["bg"], corner_radius=0)
        self.content_area.pack(side="left", fill="both", expand=True)

        # ── Section registry ──────────────────────────────────────────
        self.section_frames = {}
        self.section_nav_btns = {}
        self.current_section = None

        # Build core pages
        self.section_frames["OVERVIEW"] = ctk.CTkFrame(self.content_area, fg_color="transparent")
        self._build_overview_page(self.section_frames["OVERVIEW"])

        self.section_frames["SKILLS"] = ctk.CTkFrame(self.content_area, fg_color="transparent")
        self._build_skills_page(self.section_frames["SKILLS"])

        self.section_frames["ITEMS"] = ctk.CTkFrame(self.content_area, fg_color="transparent")
        self._build_items_page(self.section_frames["ITEMS"])

        self.section_frames["OPTIMAL"] = ctk.CTkFrame(self.content_area, fg_color="transparent")
        self._build_optimal_page(self.section_frames["OPTIMAL"])

        self.section_frames["SETTINGS"] = ctk.CTkFrame(self.content_area, fg_color="transparent")
        self._build_settings_page(self.section_frames["SETTINGS"])

        # ── Core nav buttons ──────────────────────────────────────────
        ctk.CTkFrame(self.sidebar, height=6, fg_color="transparent").pack()
        self._add_nav_btn("OVERVIEW", "◫", "OVERVIEW")
        self._add_nav_btn("SKILLS",   "✦", "SKILLS")
        self._add_nav_btn("ITEMS",    "◈", "ITEMS")
        self._add_nav_btn("OPTIMAL",  "◎", "OPTIMAL")

        self._add_nav_btn("SETTINGS", "✱", "SETTINGS")

        # ── Default section ───────────────────────────────────────────
        self.switch_section("OVERVIEW")

        # ── Footer status bar ─────────────────────────────────────────
        ctk.CTkFrame(self.container, height=1, fg_color=C["sep"]).pack(fill="x")
        _footer = ctk.CTkFrame(self.container, fg_color=C["nav"], height=28)
        _footer.pack(fill="x")
        _footer.pack_propagate(False)
        self.status_lbl = ctk.CTkLabel(_footer, text="READY",
                                       font=("Segoe UI", 9), text_color=C["dim"])
        self.status_lbl.pack(side="left", padx=14)
        ctk.CTkButton(_footer, text="Dev", width=38, height=20, fg_color="transparent",
                      hover_color=C["nav_act"], font=("Segoe UI", 8), text_color="#2d3748",
                      command=self.unlock_dev_mode).pack(side="right", padx=8)
        ctk.CTkLabel(_footer, text=f"v{self.app_version}",
                 font=("Segoe UI", 8), text_color="#2d3748").pack(side="right", padx=4)
        ctk.CTkLabel(_footer, text="© 2026 Rocky Idle Reader",
                     font=("Segoe UI", 8), text_color="#2d3748").pack(side="right", padx=4)

        # ── Legacy compat ─────────────────────────────────────────────
        self.settings_frame = ctk.CTkFrame(self.container, fg_color="#141414",
                                           corner_radius=16, border_width=1, border_color="#2f2f2f")
        self.settings_frame.place_forget()
        self.dash_frame = self.section_frames["OVERVIEW"]  # alias

    # ── Nav helpers ───────────────────────────────────────────────────
    def _add_nav_btn(self, section_id, icon, label):
        C = self._C
        item = ctk.CTkFrame(self.sidebar, fg_color="transparent", corner_radius=0, height=44)
        item.pack(fill="x")
        item.pack_propagate(False)

        accent = ctk.CTkFrame(item, width=4, fg_color="transparent", corner_radius=0)
        accent.pack(side="left", fill="y")

        btn = ctk.CTkButton(
            item,
            text=f"{icon}  {label}",
            width=114, height=44,
            corner_radius=0,
            fg_color="transparent",
            hover_color=C["nav_hvr"],
            text_color=C["gold"],
            font=("Segoe UI", 11, "bold"),
            anchor="w",
            command=lambda s=section_id: self.switch_section(s)
        )
        btn.pack(side="left", fill="both", expand=True)
        self.section_nav_btns[section_id] = {
            "button": btn,
            "accent": accent,
            "container": item,
            "icon": icon,
            "label": label,
        }
        self._refresh_nav_button_text(section_id)
        return btn

    def switch_section(self, section_id):
        C = self._C
        if section_id not in self.section_frames:
            return
        for frame in self.section_frames.values():
            frame.pack_forget()
        for sid, nav in self.section_nav_btns.items():
            btn = nav["button"]
            accent = nav["accent"]
            if sid == section_id:
                btn.configure(fg_color=C["nav_act"], text_color=C["gold"])
                accent.configure(fg_color=C["gold"])
            else:
                btn.configure(fg_color="transparent", text_color=C["gold"])
                accent.configure(fg_color="transparent")
        self.section_frames[section_id].pack(fill="both", expand=True)
        self.current_section = section_id
        self.config["last_section"] = section_id
        self.set_store_section("config", self.config)

    def _refresh_nav_button_text(self, section_id):
        nav = self.section_nav_btns.get(section_id)
        if not nav:
            return
        if self.sidebar_collapsed:
            nav["button"].configure(text=nav["icon"], anchor="center")
        else:
            nav["button"].configure(text=f"{nav['icon']}  {nav['label']}", anchor="w")

    def toggle_sidebar(self, force=None, persist=True):
        self.sidebar_collapsed = (not self.sidebar_collapsed) if force is None else bool(force)
        width = 62 if self.sidebar_collapsed else 118
        btn_width = 58 if self.sidebar_collapsed else 114
        self.sidebar.configure(width=width)
        for sid, nav in self.section_nav_btns.items():
            nav["button"].configure(width=btn_width)
            self._refresh_nav_button_text(sid)
        if persist:
            self.config["sidebar_collapsed"] = self.sidebar_collapsed
            self.set_store_section("config", self.config)

    def update_sync_badge(self):
        if not hasattr(self, 'sync_badge_lbl') or not self.sync_badge_lbl.winfo_exists():
            return
        if self.last_sync_epoch <= 0:
            self.sync_badge_lbl.configure(text="NO SYNC", text_color="#f0524f")
        else:
            age = int(max(0, time.time() - self.last_sync_epoch))
            if age <= 5:
                self.sync_badge_lbl.configure(text="LIVE", text_color="#3fb950")
            elif age <= 75:
                self.sync_badge_lbl.configure(text=f"SYNC {age}s", text_color="#8ab4f8")
            elif age <= 135:
                self.sync_badge_lbl.configure(text=f"STALE {age}s", text_color="#e8a000")
            else:
                self.sync_badge_lbl.configure(text=f"LATE {age}s", text_color="#f0524f")

    def _remove_section(self, section_id):
        if section_id in self.section_frames:
            try:
                self.section_frames[section_id].destroy()
            except Exception:
                pass
            del self.section_frames[section_id]
        if section_id in self.section_nav_btns:
            try:
                self.section_nav_btns[section_id]["container"].destroy()
            except Exception:
                pass
            del self.section_nav_btns[section_id]
        if self.current_section == section_id:
            self.switch_section("OVERVIEW")

    def _reorder_settings_btn(self):
        if "SETTINGS" in self.section_nav_btns:
            self.section_nav_btns["SETTINGS"]["container"].pack_forget()
            self.section_nav_btns["SETTINGS"]["container"].pack(fill="x")

    # ── Page builders ─────────────────────────────────────────────────
    def _build_overview_page(self, parent):
        C = self._C
        scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent", border_width=0)
        scroll.pack(fill="both", expand=True, padx=14, pady=14)

        cards_row = ctk.CTkFrame(scroll, fg_color="transparent")
        cards_row.pack(fill="x", pady=(0, 6))
        self.total_lvl_lbl  = self.create_card(cards_row, "TOTAL LEVEL", "--",  C["gold"])
        self.total_xp_lbl   = self.create_card(cards_row, "TOTAL XP",    "--",  "#9b59b6")
        self.session_xp_lbl = self.create_card(cards_row, "SESSION XP",  "0",   C["blue"])

        gp_row = ctk.CTkFrame(scroll, fg_color="transparent")
        gp_row.pack(fill="x", pady=(0, 14))
        self.gp_rate_lbl    = self.create_card(gp_row, "GP/H",       "--", C["green"])
        self.session_gp_lbl = self.create_card(gp_row, "SESSION GP", "0",  C["gold"])

        slayer_card = ctk.CTkFrame(scroll, fg_color=C["card"], corner_radius=12,
                                   border_width=1, border_color=C["card_bd"])
        slayer_card.pack(fill="x", pady=(0, 8))
        _sh = ctk.CTkFrame(slayer_card, fg_color="transparent")
        _sh.pack(fill="x", padx=16, pady=(14, 4))
        ctk.CTkLabel(_sh, text="⚔  SLAYER", font=("Segoe UI", 11, "bold"),
                     text_color=C["gold"]).pack(side="left")
        self.slayer_task_lbl   = self.create_row(slayer_card, "TASK",       "None", C["gold"])
        self.slayer_kills_lbl  = self.create_row(slayer_card, "KILLS LEFT", "0",    C["blue"])
        self.slayer_points_lbl = self.create_row(slayer_card, "POINTS",     "0",    C["green"])
        self.slayer_streak_lbl = self.create_row(slayer_card, "STREAK",     "0",    C["red"])
        ctk.CTkFrame(slayer_card, height=10, fg_color="transparent").pack()

        completion_card = ctk.CTkFrame(scroll, fg_color=C["card"], corner_radius=12,
                  border_width=1, border_color=C["card_bd"])
        completion_card.pack(fill="x", pady=(0, 8))
        _mh = ctk.CTkFrame(completion_card, fg_color="transparent")
        _mh.pack(fill="x", padx=16, pady=(14, 4))
        ctk.CTkLabel(_mh, text="◈  ACCOUNT COMPLETION", font=("Segoe UI", 11, "bold"),
             text_color=C["gold"]).pack(side="left")
        _acc_help = ctk.CTkLabel(_mh, text="?", width=20, height=20,
                                 fg_color=C["nav_act"], corner_radius=10,
                                 text_color=C["txt"], font=("Segoe UI", 10, "bold"))
        _acc_help.pack(side="right")
        self.attach_tooltip(
            _acc_help,
            "Account Completion is an average of available categories: Quests, Achievements, Chests, Collection Logs, and Maxed (Level 126 plus 200M XP checks). Missing categories are skipped.",
        )
        self.ov_completion_total_lbl = self.create_row(completion_card, "OVERALL", "--", C["gold"])
        self.ov_completion_quests_lbl = self.create_row(completion_card, "QUESTS", "--", C["txt"])
        self.ov_completion_achievements_lbl = self.create_row(completion_card, "ACHIEVEMENTS", "--", C["txt"])
        self.ov_completion_chests_lbl = self.create_row(completion_card, "CHESTS", "--", C["txt"])
        self.ov_completion_logs_lbl = self.create_row(completion_card, "COLLECTION LOGS", "--", C["txt"])
        self.ov_completion_maxed_lbl = self.create_row(completion_card, "MAXED (126/200M)", "--", C["green"])
        ctk.CTkFrame(completion_card, height=10, fg_color="transparent").pack()

    def _build_skills_page(self, parent):
        C = self._C
        _top = ctk.CTkFrame(parent, fg_color="transparent")
        _top.pack(fill="x", padx=14, pady=(14, 6))
        ctk.CTkLabel(_top, text="Active Skill Gains",
                     font=("Segoe UI", 13, "bold"), text_color=C["txt"]).pack(side="left")
        _controls = ctk.CTkFrame(parent, fg_color="transparent")
        _controls.pack(fill="x", padx=14, pady=(0, 6))
        self.skills_filter_var = ctk.StringVar(value=self.config.get("skills_filter", ""))
        _skills_search = ctk.CTkEntry(_controls, textvariable=self.skills_filter_var,
                                      placeholder_text="Filter skills...", height=30,
                                      fg_color=C["nav_act"], border_color=C["card_bd"], text_color=C["txt"])
        _skills_search.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self.skills_sort_menu = ctk.CTkOptionMenu(_controls, values=["Rate", "Gain", "Name"],
                                                   fg_color=C["nav_act"], button_color=C["card"],
                                                   button_hover_color=C["nav_hvr"], text_color=C["txt"],
                                                   dropdown_fg_color=C["nav"], dropdown_text_color=C["txt"],
                                                   command=lambda v: self.update_feed_controls("skills_sort", v))
        self.skills_sort_menu.pack(side="right")
        self.skills_sort_menu.set(self.config.get("skills_sort", "Rate"))
        self.skills_filter_var.trace_add("write", lambda *_: self.update_feed_controls("skills_filter", self.skills_filter_var.get()))
        self.skills_scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent", border_width=0)
        self.skills_scroll.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.skill_feed = ctk.CTkFrame(self.skills_scroll, fg_color="transparent")
        self.skill_feed.pack(fill="both", expand=True)

    def _build_items_page(self, parent):
        C = self._C
        _top = ctk.CTkFrame(parent, fg_color="transparent")
        _top.pack(fill="x", padx=14, pady=(14, 6))
        ctk.CTkLabel(_top, text="Item Drops",
                     font=("Segoe UI", 13, "bold"), text_color=C["txt"]).pack(side="left")
        ctk.CTkButton(_top, text="Clear Items", width=120, height=28,
                      fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                      font=("Segoe UI", 10), text_color=C["dim"],
                      command=self.clear_item_feed).pack(side="right", padx=(8, 0))
        ctk.CTkButton(_top, text="Manage Hidden", width=140, height=28,
                      fg_color=C["nav_act"], hover_color=C["nav_hvr"],
                      font=("Segoe UI", 10), text_color=C["dim"],
                      command=self.show_item_hide_popup).pack(side="right")
        _controls = ctk.CTkFrame(parent, fg_color="transparent")
        _controls.pack(fill="x", padx=14, pady=(0, 6))
        self.items_filter_var = ctk.StringVar(value=self.config.get("items_filter", ""))
        _items_search = ctk.CTkEntry(
            _controls,
            textvariable=self.items_filter_var,
            placeholder_text="Filter items...",
            height=30,
            fg_color=C["nav_act"],
            border_color=C["card_bd"],
            text_color=C["txt"],
        )
        _items_search.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self.items_sort_menu = ctk.CTkOptionMenu(
            _controls,
            values=["GP/h", "Count/h", "Gain", "Name"],
            fg_color=C["nav_act"],
            button_color=C["card"],
            button_hover_color=C["nav_hvr"],
            text_color=C["txt"],
            dropdown_fg_color=C["nav"],
            dropdown_text_color=C["txt"],
            command=lambda v: self.update_feed_controls("items_sort", v),
        )
        self.items_sort_menu.pack(side="right")
        _items_sort = self.config.get("items_sort", "GP/h")
        if _items_sort not in ("GP/h", "Count/h", "Gain", "Name"):
            _items_sort = "GP/h"
        self.items_sort_menu.set(_items_sort)
        self.items_filter_var.trace_add("write", lambda *_: self.update_feed_controls("items_filter", self.items_filter_var.get()))
        self.items_scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent", border_width=0)
        self.items_scroll.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.item_feed = ctk.CTkFrame(self.items_scroll, fg_color="transparent")
        self.item_feed.pack(fill="both", expand=True)

    def _build_optimal_page(self, parent):
        C = self._C
        self.optimal_cards = {}

        scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent", border_width=0)
        scroll.pack(fill="both", expand=True, padx=14, pady=14)

        ctk.CTkLabel(scroll, text="Skill Optimizer", font=("Segoe UI", 13, "bold"), text_color=C["txt"]).pack(anchor="w")
        ctk.CTkLabel(
            scroll,
            text="Best XP/h, GP/h and balanced target from your live save multipliers.",
            font=("Segoe UI", 10),
            text_color=C["dim"],
        ).pack(anchor="w", pady=(2, 10))

        skill_specs = [
            ("mining", "Mining"),
            ("woodcutting", "Woodcutting"),
            ("thieving", "Thieving"),
            ("smithing", "Smithing"),
            ("fishing", "Fishing"),
            ("cooking", "Cooking"),
        ]

        for key, title in skill_specs:
            card = ctk.CTkFrame(scroll, fg_color=C["card"], corner_radius=12, border_width=1, border_color=C["card_bd"])
            card.pack(fill="x", pady=(0, 10))

            header = ctk.CTkFrame(card, fg_color="transparent")
            header.pack(fill="x", padx=14, pady=(10, 4))
            title_lbl = ctk.CTkLabel(header, text=title.upper(), font=("Segoe UI", 11, "bold"), text_color=C["gold"])
            title_lbl.pack(side="left")
            level_lbl = ctk.CTkLabel(header, text="Lvl --", font=("Segoe UI", 10), text_color=C["dim"])
            level_lbl.pack(side="right")

            xp_lbl = self.create_row(card, "BEST XP/H", "--", C["blue"])
            gp_lbl = self.create_row(card, "BEST GP/H", "--", C["green"])
            bal_lbl = self.create_row(card, "BEST BALANCED", "--", C["txt"])
            next_lbl = self.create_row(card, "NEXT UNLOCK", "--", C["gold"])
            ctk.CTkFrame(card, height=8, fg_color="transparent").pack()

            self.optimal_cards[key] = {
                "title": title_lbl,
                "level": level_lbl,
                "xp": xp_lbl,
                "gp": gp_lbl,
                "balanced": bal_lbl,
                "next": next_lbl,
            }

    def _build_settings_page(self, parent):
        C = self._C
        self.settings_container = ctk.CTkScrollableFrame(parent, fg_color="transparent", border_width=0)
        self.settings_container.pack(fill="both", expand=True, padx=18, pady=16)

        ctk.CTkLabel(self.settings_container, text="Settings",
                     font=("Segoe UI", 14, "bold"), text_color=C["txt"]).pack(anchor="w", pady=(0, 2))
        ctk.CTkLabel(self.settings_container, text="Appearance, notifications and storage.",
                     font=("Segoe UI", 10), text_color=C["dim"]).pack(anchor="w", pady=(0, 16))

        _density_row = ctk.CTkFrame(self.settings_container, fg_color="transparent")
        _density_row.pack(fill="x", pady=(0, 12))
        ctk.CTkLabel(_density_row, text="Feed Density",
                 font=("Segoe UI", 11), text_color=C["txt"]).pack(side="left")
        self.density_menu = ctk.CTkOptionMenu(_density_row,
                  values=["Comfortable", "Compact"],
                  command=self.update_density, fg_color=C["nav_act"], button_color=C["card"],
                  button_hover_color=C["nav_hvr"], text_color=C["txt"],
                  dropdown_fg_color=C["nav"], dropdown_text_color=C["txt"])
        self.density_menu.pack(side="right")
        self.density_menu.set(self.config.get("density", "Comfortable"))

        # Choose Profile
        ctk.CTkButton(self.settings_container, text="CHOOSE PROFILE", height=34,
                      fg_color=C["nav_act"], hover_color=C["card"], text_color=C["txt"],
                      font=("Segoe UI", 11, "bold"),
                      command=lambda: self.show_profile_picker(self.scan_available_profiles())
                      ).pack(fill="x", pady=(0, 14))

        ctk.CTkButton(self.settings_container, text="RESCAN SAVE + PROFILES", height=34,
                  fg_color=C["nav_act"], hover_color=C["card"], text_color=C["txt"],
                  font=("Segoe UI", 11, "bold"),
                  command=self.rescan_save_and_profiles).pack(fill="x", pady=(0, 14))

        # Sticky Position
        _pos_row = ctk.CTkFrame(self.settings_container, fg_color="transparent")
        _pos_row.pack(fill="x", pady=(0, 12))
        ctk.CTkLabel(_pos_row, text="Sticky Position",
                     font=("Segoe UI", 11), text_color=C["txt"]).pack(side="left")
        self.pos_menu = ctk.CTkOptionMenu(_pos_row,
                      values=["Top-Right", "Top-Left", "Bottom-Right", "Bottom-Left", "Free Flow"],
                      command=self.update_pos, fg_color=C["nav_act"], button_color=C["card"],
                      button_hover_color=C["nav_hvr"], text_color=C["txt"],
                      dropdown_fg_color=C["nav"], dropdown_text_color=C["txt"])
        self.pos_menu.pack(side="right")
        self.pos_menu.set(self.config.get("pos", "Free Flow"))

        self.always_on_top_toggle = ctk.CTkSwitch(
            self.settings_container,
            text="Always On Top",
            text_color=C["txt"],
            command=self.toggle_always_on_top,
            progress_color=C["blue"],
        )
        self.always_on_top_toggle.pack(anchor="w", pady=(0, 8))
        if self.config.get("always_on_top", True):
            self.always_on_top_toggle.select()

        # Show All Skills
        self.skills_toggle = ctk.CTkSwitch(self.settings_container, text="Show All Skills",
                                           text_color=C["txt"], command=self.toggle_skills_tab,
                                           progress_color=C["blue"])
        self.skills_toggle.pack(anchor="w", pady=(0, 8))
        if self.config.get("show_skills"): self.skills_toggle.select()

        self.restore_items_toggle = ctk.CTkSwitch(
            self.settings_container,
            text="Keep Items Across Restart",
            text_color=C["txt"],
            command=self.toggle_restore_items_on_restart,
            progress_color=C["blue"],
        )
        self.restore_items_toggle.pack(anchor="w", pady=(0, 8))
        if self.config.get("restore_items_on_restart", False):
            self.restore_items_toggle.select()

        # Enable Webhook
        self.webhook_toggle = ctk.CTkSwitch(self.settings_container, text="Enable Webhook",
                                            text_color=C["txt"], command=self.toggle_webhook_master,
                                            progress_color=C["blue"])
        self.webhook_toggle.pack(anchor="w", pady=(0, 10))
        if self.config.get("webhook_enabled"): self.webhook_toggle.select()

        ctk.CTkButton(self.settings_container, text="Discord Webhook Test", height=32,
                  fg_color=C["blue"], hover_color="#3a75d4", text_color=C["txt"],
                  command=self.send_test_webhook).pack(anchor="w", pady=(0, 12))

        # Discord URL
        ctk.CTkLabel(self.settings_container, text="Discord Webhook URL",
                     font=("Segoe UI", 10), text_color=C["dim"]).pack(anchor="w", pady=(0, 2))
        self.webhook_entry = ctk.CTkEntry(self.settings_container, height=34,
                                          placeholder_text="https://discord.com/api/webhooks/...",
                                          fg_color=C["nav_act"], border_color=C["card_bd"],
                                          text_color=C["txt"])
        self.webhook_entry.pack(fill="x", pady=(0, 16))
        self.webhook_entry.insert(0, self.config.get("webhook_url", ""))
        self.webhook_entry.bind("<FocusOut>", lambda e: self.on_webhook_url_change())

        _tools_row = ctk.CTkFrame(self.settings_container, fg_color="transparent")
        _tools_row.pack(fill="x", pady=(0, 10))
        ctk.CTkButton(_tools_row, text="EXPORT DATA", height=34,
                  fg_color=C["nav_act"], hover_color=C["card"], text_color=C["txt"],
                  font=("Segoe UI", 10, "bold"), command=self.export_app_data).pack(side="left", fill="x", expand=True, padx=(0, 6))
        ctk.CTkButton(_tools_row, text="IMPORT DATA", height=34,
                  fg_color=C["nav_act"], hover_color=C["card"], text_color=C["txt"],
                  font=("Segoe UI", 10, "bold"), command=self.import_app_data).pack(side="left", fill="x", expand=True, padx=(6, 0))

        ctk.CTkButton(self.settings_container, text="OPEN HEALTH CHECKS", height=34,
                  fg_color=C["nav_act"], hover_color=C["card"], text_color=C["txt"],
                  font=("Segoe UI", 11, "bold"), command=self.show_health_popup).pack(fill="x", pady=(0, 12))

        ctk.CTkButton(
            self.settings_container,
            text="WRITE DESKTOP LOG",
            height=34,
            fg_color=C["nav_act"],
            hover_color=C["card"],
            text_color=C["txt"],
            font=("Segoe UI", 11, "bold"),
            command=self.write_manual_diagnostic_log,
        ).pack(fill="x", pady=(0, 12))

        ctk.CTkButton(
            self.settings_container,
            text="CHECK FOR UPDATES",
            height=34,
            fg_color=C["nav_act"],
            hover_color=C["card"],
            text_color=C["txt"],
            font=("Segoe UI", 11, "bold"),
            command=lambda: threading.Thread(target=lambda: self.check_for_updates(manual=True), daemon=True).start(),
        ).pack(fill="x", pady=(0, 12))

        ctk.CTkButton(
            self.settings_container,
            text="SAVE SETTINGS",
            height=36,
            fg_color=C["blue"],
            hover_color="#3a75d4",
            font=("Segoe UI", 11, "bold"),
            command=self.save_config,
        ).pack(fill="x")

    def setup_settings_ui(self):
        pass  # legacy stub

    # --- MONITORING ENGINE ---
    def process_state(self, state, source_label=None):
        now = time.time()
        trackable_reason = self._state_trackable_reason(state)
        if trackable_reason:
            self._startup_log(f"Ignored state with insufficient skill data from {source_label or self.current_save_source or 'unknown source'} ({trackable_reason}).")
            self._scan_diag("process-state", source_label or self.current_save_source, "skip-untrackable", trackable_reason)
            return
        self.last_sync_epoch = now
        self.latest_save_data = state or {}
        self.latest_save_source = source_label or self.current_save_source or datetime.now().strftime('%H:%M:%S')
        if source_label:
            self.current_save_source = source_label
        skills = state.get('skills', {}); xp_map = state.get('skillsXp', {})
        total_lvl, total_xp, sess_xp = 0, 0, 0
        
        slayer = state.get('slayer', state.get('slayerInfo', {}))
        current_task = slayer.get('currentSlayerTask') or {}
        amt, total_amt = current_task.get('currentAmount', 0), current_task.get('totalAmount', 0)
        task_id, pts, strk = current_task.get('slayerCategoryId', ''), int(slayer.get('slayerPoints', 0)), int(slayer.get('slayerStreak', 0))
        
        curr_items = self.get_all_items(state)
        self.sync_item_meta_from_state(curr_items)
        prev_items = self.get_all_items(self.prev_state) if self.prev_state else {}
        visible_curr_items = {i_id: amt for i_id, amt in curr_items.items() if i_id not in self.hidden_items}
        visible_prev_items = {i_id: amt for i_id, amt in prev_items.items() if i_id not in self.hidden_items}
        changed_skill_names = set()
        changed_item_ids_scan = set()

        diff_list = []
        event_markers = []
        if self.prev_state:
            hidden_names = {self.get_item_name(i_id) for i_id in self.hidden_items}
            for name in list(self.item_history):
                if name in hidden_names:
                    del self.item_history[name]

            all_ids = set(visible_curr_items.keys()).union(set(visible_prev_items.keys()))
            for i_id in all_ids:
                diff = visible_curr_items.get(i_id, 0) - visible_prev_items.get(i_id, 0)
                name = self.get_item_name(i_id)
                if diff != 0:
                    if name not in self.item_history: self.item_history[name] = deque()
                    self.item_history[name].append((now, diff))
                    self.stale_item_counts[name] = 0
                    changed_item_ids_scan.add(str(i_id))
                    if diff > 0:
                        _cache = getattr(self, '_skill_optimizer_cache', None)
                        _id_gp = _cache.get('id_to_sell_gp', {}) if isinstance(_cache, dict) else {}
                        _sell = _id_gp.get(str(i_id), 0.0)
                        self.session_gp_earned += diff * _sell
                elif name in self.item_history:
                    self.stale_item_counts[name] = self.stale_item_counts.get(name, 0) + 1
                    if self.stale_item_counts[name] >= 3:
                        del self.item_history[name]
                        self.stale_item_counts.pop(name, 0)

            diff_list = self.deep_diff(self.prev_state, state)
            if diff_list:
                if self.drift_alert_active:
                    event_markers.append("Save drift recovered")
                self.no_change_save_count = 0
                self.drift_alert_active = False
            else:
                self.no_change_save_count += 1
                if self.no_change_save_count >= 5 and not self.drift_alert_active:
                    self.drift_alert_active = True
                    msg = f"No meaningful save changes across {self.no_change_save_count} consecutive saves"
                    event_markers.append(f"Save drift detected: {msg}")
                    if self.config.get("webhook_enabled"):
                        self.send_webhook("⚠️ Your Idle", msg)

            ts = datetime.now().strftime('%H:%M:%S')
            for entry in diff_list: self.current_debug_list.append(f"[{ts}] {entry}")
            if len(self.current_debug_list) > 100: self.current_debug_list = self.current_debug_list[-100:]
            self.after(0, lambda: self.update_debug_feed(diff_list))

            event_markers.extend(self.extract_event_markers(self.prev_state, state))
            self._check_boost_ready_alerts(self.prev_state, state, event_markers)

            prev_slayer = self.prev_state.get('slayer', self.prev_state.get('slayerInfo', {}))
            p_amt = (prev_slayer.get('currentSlayerTask') or {}).get('currentAmount', 0)
            if amt == 0 and p_amt > 0:
                self.send_webhook("⚔️ Slayer Finished!", "Task complete!")
                event_markers.append("Slayer task completed")
        else:
            self.no_change_save_count = 0
            self.drift_alert_active = False

        if changed_item_ids_scan:
            self.recent_changed_item_ids.update(changed_item_ids_scan)

        if total_amt == 0:
            self.no_slayer_task_count += 1
        else:
            self.no_slayer_task_count = 0
            self.no_slayer_task_notified = False

        if self.no_slayer_task_count >= 3 and self.config.get("notify_no_slayer_task") and not self.no_slayer_task_notified:
            self.send_webhook("⚠️ No Slayer Task", "No slayer task was detected for 3 consecutive scans.")
            self.no_slayer_task_notified = True
            event_markers.append("No Slayer Task streak reached 3 scans")

        self.add_log_entry(self.latest_save_source or datetime.now().strftime('%H:%M:%S'), diff_list, event_markers)

        for sid, name in self.skill_map.items():
            sd, xd = skills.get(sid, {}), xp_map.get(sid, 0)
            lvl = self._coerce_skill_level(sd)
            if lvl is None:
                continue
            xp = (xd.get('xp', xd) if isinstance(xd, dict) else xd)
            try:
                xp = float(xp or 0)
            except (TypeError, ValueError):
                xp = 0.0
            try:
                speed_mult = float(sd.get('currentSpeedMultiplier', 1) or 1)
            except (TypeError, ValueError):
                speed_mult = 1.0
            is_diamond = speed_mult >= 3.0
            diamond_text = f"{speed_mult:.2f}/3.00"
            total_xp += xp; total_lvl += lvl
            if name not in self.session_start_xp: self.session_start_xp[name] = xp
            sess_xp += (xp - self.session_start_xp[name])
            if sid in self.skill_labels:
                self.safe_ui(self.skill_labels[sid], "configure", text=str(lvl))
            if sid in self.skill_name_labels:
                self.safe_ui(self.skill_name_labels[sid], "configure", text=f"{name} ({diamond_text} Diamond)")
            prev_lvl = self.current_levels.get(name, lvl)
            if self.prev_state and lvl > prev_lvl and self.config.get("notify_levels"):
                self.send_webhook("✨ Level Up!", f"You leveled {name} to {lvl}!")
            was_diamond = self.skill_diamond_status.get(name, is_diamond)
            if self.prev_state and (not was_diamond) and is_diamond and self.config.get("notify_levels"):
                self.send_webhook("💎 Diamond Tier!", f"{name} reached Diamond tier.")
            if self.prev_state:
                px = self.prev_state.get('skillsXp', {}).get(sid, 0)
                px = px.get('xp', px) if isinstance(px, dict) else px
                if xp > px:
                    changed_skill_names.add(name)
                    if name not in self.xp_history: self.xp_history[name] = deque()
                    self.xp_history[name].append((now, xp - px))
                    self.stale_counts[name] = 0
                    history = self.xp_history[name]
                    while history and now - history[0][0] > 600: history.popleft()
                    if len(history) >= 2:
                        gain = sum(i[1] for i in history)
                        rate = (gain / (now - history[0][0])) * 3600
                        ttl = (self.get_xp_for_level(lvl + 1) - xp) / (rate / 3600) if rate > 0 else 0
                        self.active_skills[name] = {'lvl': lvl, 'gain': gain, 'rate': rate, 'ttl': ttl}
                else:
                    self.stale_counts[name] = self.stale_counts.get(name, 0) + 1
                    if self.stale_counts[name] >= 5 and name in self.active_skills:
                        del self.active_skills[name]
            self.skill_diamond_status[name] = is_diamond
            self.current_levels[name] = lvl

        xp_items = sorted(self.active_skills.items(), key=lambda x: x[1]['rate'], reverse=True)
        has_active_xp = bool(xp_items)
        if has_active_xp:
            self.xp_active_scan_streak += 1
            self.xp_inactive_scan_streak = 0
            self.xp_inactive_notified = False
            if self.xp_active_scan_streak >= 3:
                self.xp_activity_armed = True
        else:
            self.xp_inactive_scan_streak += 1
            self.xp_active_scan_streak = 0

        if self.prev_state and self.config.get("notify_xp"):
            interval_min = float(self.config.get("xp_notify_interval_minutes", 0) or 0)
            if interval_min <= 0:
                interval_min = 1
            interval_seconds = max(0, int(interval_min * 60))
            cooldown_ok = (interval_seconds == 0) or ((now - self.last_xp_notify_epoch) >= interval_seconds)
            changed_xp_items = [(name, data) for name, data in xp_items if name in changed_skill_names]
            if changed_xp_items and cooldown_ok:
                lines = [f"{name}: +{self.format_number(data['gain'])} ({self.format_number(data['rate'])}/h)" for name, data in changed_xp_items[:5]]
                self.send_webhook("📈 XP Rates", "\n".join(lines))
                self.last_xp_notify_epoch = now
            elif self.xp_activity_armed and self.xp_inactive_scan_streak >= 3 and not self.xp_inactive_notified:
                self.send_webhook("📉 XP Rates", "No active XP gains detected for 3 consecutive scans.")
                self.xp_inactive_notified = True
                self.xp_activity_armed = False

        self.safe_ui(self.total_lvl_lbl, "configure", text=str(total_lvl))
        self.safe_ui(self.total_xp_lbl, "configure", text=self.format_number(total_xp))
        self.safe_ui(self.session_xp_lbl, "configure", text=self.format_number(sess_xp))
        self.safe_ui(self.session_gp_lbl, "configure", text=self.format_number(self.session_gp_earned))
        self.safe_ui(self.slayer_task_lbl, "configure", text=self.slayer_category_map.get(str(task_id), self.monster_map.get(str(task_id), "None" if not task_id else f"ID {task_id}")))
        self.safe_ui(self.slayer_kills_lbl, "configure", text=f"{amt} / {total_amt}" if total_amt > 0 else "0")
        self.safe_ui(self.slayer_points_lbl, "configure", text=str(pts)); self.safe_ui(self.slayer_streak_lbl, "configure", text=str(strk))
        self.save_skill_tiers(self.extract_skill_tier_data(state))
        self.save_diary_boosters(self.extract_diary_booster_data(state))
        self.save_multipliers_snapshot(self.extract_multiplier_snapshot(state))
        self.update_overview_snapshot(state)
        self.update_optimal_snapshot(state)
        self.prev_state = state
        self.save_session_cache()
        self._set_status_text("SYNCED", text_color="#2ecc71", include_context=True)
        self.update_sync_badge()

    # --- UI LOOPS ---
    def ui_update_loop(self):
        if self.is_closing: return
        now, items = time.time(), []
        for name, data in list(self.active_skills.items()):
            if data['ttl'] > 0: data['ttl'] -= 1
            items.append((name, data['lvl'], data['gain'], data['rate'], self.format_ttl(data['ttl']), "SKILL"))
        for name, hist in list(self.item_history.items()):
            gain = sum(i[1] for i in hist)
            rate = (gain / (now - hist[0][0])) * 3600 if (now - hist[0][0]) > 0 else 0
            items.append((name, "Item", gain, rate, "ITEM", "ITEM"))
        self.latest_feed_items = items
        self.update_ui_feed(items)
        if hasattr(self, 'gp_rate_lbl'):
            _cache = getattr(self, '_skill_optimizer_cache', None)
            if isinstance(_cache, dict) and _cache.get('ready'):
                _name_to_gp = _cache.get('name_to_sell_gp', {})
                _gp_rate = 0.0
                for _nm, _hist in list(self.item_history.items()):
                    if _hist:
                        _span = now - _hist[0][0]
                        if _span > 0:
                            _gain = sum(i[1] for i in _hist if i[1] > 0)
                            if _gain > 0:
                                _gp_rate += (_gain / _span) * 3600 * _name_to_gp.get(_nm, 0.0)
                self.safe_ui(self.gp_rate_lbl, "configure", text=(self.format_number(_gp_rate) if _gp_rate > 0 else "--"))
        self.after(1000, self.ui_update_loop)

    def update_ui_feed(self, items):
        skills = [i for i in items if i[5] == "SKILL"]
        item_rows = [i for i in items if i[5] == "ITEM"]

        skills = self._apply_feed_controls(skills, "skills")
        item_rows = self._apply_feed_controls(item_rows, "items")
        visible_items = skills + item_rows

        active = [f"{i[5]}:{i[0]}" for i in visible_items]
        for key in list(self.feed_widgets.keys()):
            if key not in active:
                self.feed_widgets[key]['frame'].destroy()
                del self.feed_widgets[key]

        compact = self.config.get("density", "Comfortable") == "Compact"
        row_pad_y = 2 if compact else 4
        row_inner_y = 6 if compact else 10
        label_font = ("Segoe UI", 10, "bold") if compact else ("Segoe UI", 11, "bold")
        stat_font = ("Segoe UI", 9) if compact else ("Segoe UI", 10)

        _cache = getattr(self, '_skill_optimizer_cache', None)
        _n2gp = _cache.get('name_to_sell_gp', {}) if isinstance(_cache, dict) and _cache.get('ready') else {}
        _items_mode = self.config.get("items_sort", "GP/h")

        for n, l, g, r, t, cat in visible_items:
            feed_key = f"{cat}:{n}"
            frame = self.item_feed if cat == "ITEM" else self.skill_feed
            if cat == "ITEM":
                _sell = _n2gp.get(n, 0.0)
                _gp_h = r * _sell
                if _items_mode == "Count/h":
                    txt = f"{'+' if g > 0 else ''}{self.format_number(g)} ({self.format_number(r)}/h)"
                elif _gp_h > 0:
                    txt = f"{'+' if g > 0 else ''}{self.format_number(g)} | {self.format_number(_gp_h)} GP/h"
                else:
                    txt = f"{'+' if g > 0 else ''}{self.format_number(g)}"
            else:
                txt = f"+{self.format_number(g)} ({self.format_number(r)}/h) | TTL: {t}"
            col = "#2ecc71" if g >= 0 else "#e74c3c"
            lvl_text = n.upper() if cat == "ITEM" else f"{n.upper()} ({l})"
            info = (n, l, g, r, t, cat)

            if feed_key in self.feed_widgets:
                self.feed_widgets[feed_key]['lvl'].configure(text=lvl_text)
                self.feed_widgets[feed_key]['stats'].configure(text=txt, text_color=col)
                self.feed_widgets[feed_key]['info'] = info
            else:
                row = ctk.CTkFrame(frame, fg_color="#1a2030", corner_radius=10,
                                   border_width=1, border_color="#2d3748")
                row.pack(fill="x", pady=row_pad_y, padx=8)
                label = ctk.CTkLabel(row, text=lvl_text, font=label_font,
                                     text_color="#e6edf3")
                label.pack(side="left", padx=(14, 8), pady=row_inner_y)
                sta = ctk.CTkLabel(row, text=txt, font=stat_font, text_color=col)
                sta.pack(side="right", padx=(8, 14), pady=row_inner_y)
                for widget in (row, label, sta):
                    widget.bind("<Button-3>", lambda e, info=info: self.create_popout(info))
                    widget.bind("<Button-2>", lambda e, info=info: self.create_popout(info))
                self.feed_widgets[feed_key] = {'frame': row, 'lvl': label, 'stats': sta, 'info': info}

        self.refresh_open_popouts()

    def refresh_open_popouts(self):
        _cache = getattr(self, '_skill_optimizer_cache', None)
        _n2gp = _cache.get('name_to_sell_gp', {}) if isinstance(_cache, dict) and _cache.get('ready') else {}
        _items_mode = self.config.get("items_sort", "GP/h")
        for popout in list(self.open_popouts):
            key = popout.get('key')
            if not key or key not in self.feed_widgets:
                continue
            info = self.feed_widgets[key].get('info')
            if not info:
                continue
            name, lvl, gain, rate, ttl, category = info
            if category == "ITEM":
                _sell = _n2gp.get(name, 0.0)
                _gp_h = rate * _sell
                if _items_mode == "Count/h":
                    info_text = f"{name} | Gain: +{self.format_number(gain)} | Rate: {self.format_number(rate)}/h"
                elif _gp_h > 0:
                    info_text = f"{name} | Gain: +{self.format_number(gain)} | {self.format_number(_gp_h)} GP/h"
                else:
                    info_text = f"{name} | Gain: +{self.format_number(gain)}"
            else:
                info_text = f"{name} | Level: {lvl} | XP Gain: +{self.format_number(gain)} | Rate: {self.format_number(rate)}/h | TTL: {ttl}"
            try:
                popout['label'].configure(text=info_text)
            except: pass

    def create_popout(self, info):
        name, lvl, gain, rate, ttl, category = info
        feed_key = f"{category}:{name}"
        pop = ctk.CTkToplevel(self)
        pop.title(f"{name} Details")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)

        content_frame = ctk.CTkFrame(pop, fg_color="transparent")
        content_frame.pack(fill="both", expand=True, padx=12, pady=10)

        if category == "ITEM":
            _cache = getattr(self, '_skill_optimizer_cache', None)
            _n2gp = _cache.get('name_to_sell_gp', {}) if isinstance(_cache, dict) and _cache.get('ready') else {}
            _sell = _n2gp.get(name, 0.0)
            _gp_h = rate * _sell
            if self.config.get("items_sort", "GP/h") == "Count/h":
                info_text = f"{name} | Gain: +{self.format_number(gain)} | Rate: {self.format_number(rate)}/h"
            elif _gp_h > 0:
                info_text = f"{name} | Gain: +{self.format_number(gain)} | {self.format_number(_gp_h)} GP/h | {self.format_number(_sell)} GP each"
            else:
                info_text = f"{name} | Gain: +{self.format_number(gain)}"
        else:
            info_text = f"{name} | Level: {lvl} | XP Gain: +{self.format_number(gain)} | Rate: {self.format_number(rate)}/h | TTL: {ttl}"

        label = ctk.CTkLabel(content_frame, text=info_text, font=("Segoe UI", 12), text_color="#dfe6ef", anchor="w")
        label.pack(side="left", fill="both", expand=True)

        close_btn = ctk.CTkButton(content_frame, text="×", width=30, height=30, fg_color="transparent", hover_color="#2f2f2f", command=lambda: self.close_popout(pop))
        close_btn.pack(side="right", padx=(8, 0))

        pop.update_idletasks()
        req_w = pop.winfo_reqwidth() + 8
        req_h = pop.winfo_reqheight() + 8
        width = max(req_w, 320)
        height = req_h
        x = self.winfo_x() + self.winfo_width() + 16
        y = self.winfo_y() + 20 + (len(self.open_popouts) * (height + 6))
        pop.geometry(f"{width}x{height}+{x}+{y}")

        pop.protocol("WM_DELETE_WINDOW", lambda: self.close_popout(pop))
        self.open_popouts.append({'window': pop, 'key': feed_key, 'label': label})

    def close_popout(self, pop):
        for idx, popout in enumerate(list(self.open_popouts)):
            if popout.get('window') is pop:
                self.open_popouts.pop(idx)
                break
        try:
            pop.destroy()
        except: pass
        for index, popout in enumerate(self.open_popouts):
            try:
                open_window = popout.get('window')
                open_window.update_idletasks()
                height = open_window.winfo_height()
                x = self.winfo_x() + self.winfo_width() + 16
                y = self.winfo_y() + 20 + (index * (height + 6))
                open_window.geometry(f"+{x}+{y}")
            except: pass

    # --- DISK WORKERS ---
    def watchdog_loop(self):
        if self.is_closing: return
        if not self.initial_load_done:
            if not self.ensure_profile_selected():
                self.after(500, self.watchdog_loop)
                return
            if not self.initial_load_done:
                self.force_initial_load()
                self.initial_load_done = True
        if self.save_folder and os.path.exists(self.save_folder):
            try:
                files = [os.path.join(self.save_folder, f) for f in os.listdir(self.save_folder) if os.path.isfile(os.path.join(self.save_folder, f))]
                files.sort(key=os.path.getmtime, reverse=True)
                latest_bad = files[0] if files else None
                found_candidate = False
                for index, file_path in enumerate(files[:self.save_scan_limit]):
                    payload, raw_save, read_error = self.read_save_payload_from_file(file_path, f"sync_{index}.tmp", include_error=True)
                    if not payload or not raw_save:
                        self._scan_diag("watchdog", file_path, "skip-read", read_error or "unknown")
                        continue
                    state = payload.get('state', {}) if isinstance(payload, dict) else {}
                    if not isinstance(state, dict):
                        self._scan_diag("watchdog", file_path, "skip-state", "state-not-dict")
                        continue
                    trackable_reason = self._state_trackable_reason(state)
                    if trackable_reason:
                        self._scan_diag("watchdog", file_path, "skip-untrackable", trackable_reason)
                        continue
                    if not self.is_selected_profile(state):
                        profile = self.get_profile_info_from_state(state)
                        self._scan_diag("watchdog", file_path, "skip-profile", f"id={profile.get('profileId') or 'unknown'}")
                        continue
                    found_candidate = True
                    mtime = os.path.getmtime(file_path)
                    if raw_save != self._last_raw_save:
                        self.last_known_mtime = max(self.last_known_mtime, mtime)
                        self._last_raw_save = raw_save
                        self.current_save_source = os.path.basename(file_path)
                        self.process_state(state, source_label=self.current_save_source)
                        self._scan_diag("watchdog", file_path, "processed", f"mtime={int(mtime)}")
                    else:
                        self._scan_diag("watchdog", file_path, "skip-unchanged", "raw-save-unchanged")
                    break
                if files and not found_candidate and latest_bad:
                    self.try_recover_from_bad_save(latest_bad, "no-valid-profile-save")
            except Exception as exc:
                self._startup_log(f"watchdog_loop error: {exc}")
        self.update_sync_badge()
        self.after(500, self.watchdog_loop)

    def disk_monitor_loop(self):
        if self.is_closing: return
        if self.save_folder and os.path.exists(self.save_folder):
            try:
                curr = {f: (os.stat(os.path.join(self.save_folder, f)).st_mtime, os.stat(os.path.join(self.save_folder, f)).st_size) for f in os.listdir(self.save_folder)}
                now = datetime.now().strftime('%H:%M:%S')
                for f, (m, s) in curr.items():
                    if f not in self.file_states: self.log_disk_event(f"[{now}] 🟢 NEW: {f}", "#2ecc71")
                    elif self.file_states[f] != (m, s): self.log_disk_event(f"[{now}] 🟡 MOD: {f}", "#f1c40f")
                for f in self.file_states.keys():
                    if f not in curr: self.log_disk_event(f"[{now}] 🔴 DEL: {f}", "#e74c3c")
                self.file_states = curr
            except: pass
        self.after(200, self.disk_monitor_loop)

    # --- SHARED UTILS ---
    def force_initial_load(self):
        if not self.save_folder: return
        try:
            files = [os.path.join(self.save_folder, f) for f in os.listdir(self.save_folder) if os.path.isfile(os.path.join(self.save_folder, f))]
            files.sort(key=os.path.getmtime, reverse=True)
            for file_path in files[:self.save_scan_limit]:
                payload, raw_save, read_error = self.read_save_payload_from_file(file_path, "init.tmp", include_error=True)
                if not payload or not raw_save:
                    self._scan_diag("initial-load", file_path, "skip-read", read_error or "unknown")
                    continue
                state = payload.get('state', {}) if isinstance(payload, dict) else {}
                if not isinstance(state, dict):
                    self._scan_diag("initial-load", file_path, "skip-state", "state-not-dict")
                    continue
                trackable_reason = self._state_trackable_reason(state)
                if trackable_reason:
                    self._scan_diag("initial-load", file_path, "skip-untrackable", trackable_reason)
                    continue
                if not self.is_selected_profile(state):
                    profile = self.get_profile_info_from_state(state)
                    self._scan_diag("initial-load", file_path, "skip-profile", f"id={profile.get('profileId') or 'unknown'}")
                    continue
                self._last_raw_save = raw_save
                self.current_save_source = os.path.basename(file_path)
                self.process_state(state, source_label=self.current_save_source)
                self._scan_diag("initial-load", file_path, "processed", "selected-for-initial-load")
                return
            self._set_status_text("NO SAVE FOR SELECTED PROFILE", text_color="#e67e22", include_context=True)
        except: pass

    def get_all_items(self, state_obj):
        totals = {}
        for bag in state_obj.get('items', {}).values():
            if isinstance(bag, list):
                for item in bag:
                    if item and 'id' in item: totals[str(item['id'])] = totals.get(str(item['id']), 0) + item.get('amount', 0)
        return totals

    def deep_diff(self, o, n, p=""):
        res = []
        if any(x in p for x in ["inGameTime", "accountStart", "lastSeen", "ticks", "stats", "playTime"]): return res
        if isinstance(o, dict) and isinstance(n, dict):
            for k in n:
                np = f"{p}.{k}" if p else k
                if k not in o: res.append(f"NEW {np}")
                else: res.extend(self.deep_diff(o[k], n[k], np))
        elif o != n: res.append(f"{p}: {o}->{n}")
        return res

    def _count_completed_diary(self, state):
        diary = state.get("completedAchievementDiary", {}) if isinstance(state, dict) else {}
        if isinstance(diary, dict):
            return sum(1 for v in diary.values() if bool(v))
        if isinstance(diary, list):
            return len([v for v in diary if bool(v)])
        return 0

    def extract_event_markers(self, prev_state, state):
        markers = []
        try:
            prev_diary = self._count_completed_diary(prev_state)
            curr_diary = self._count_completed_diary(state)
            if curr_diary > prev_diary:
                markers.append(f"Achievement diary progress: +{curr_diary - prev_diary}")

            prev_skills = prev_state.get("skills", {}) if isinstance(prev_state, dict) else {}
            curr_skills = state.get("skills", {}) if isinstance(state, dict) else {}
            for sid, name in self.skill_map.items():
                p = prev_skills.get(sid, {}) if isinstance(prev_skills, dict) else {}
                c = curr_skills.get(sid, {}) if isinstance(curr_skills, dict) else {}
                for key, label in (("currentSpeedMultiplier", "speed"), ("currentXpMultiplier", "xp"), ("currentLootMultiplier", "loot")):
                    pv = p.get(key, 1)
                    cv = c.get(key, 1)
                    try:
                        pvf = float(pv or 1)
                        cvf = float(cv or 1)
                    except (TypeError, ValueError):
                        continue
                    if cvf - pvf >= 0.25:
                        markers.append(f"{name} {label} multiplier jump: {pvf:.2f} -> {cvf:.2f}")
                        break
                prev_tool = p.get("tool") if isinstance(p, dict) else None
                curr_tool = c.get("tool") if isinstance(c, dict) else None
                if prev_tool not in (None, "") and curr_tool not in (None, "") and prev_tool != curr_tool:
                    markers.append(f"{name} tool tier changed: {prev_tool} -> {curr_tool}")
            if len(markers) > 12:
                markers = markers[:12]
        except Exception:
            pass
        return markers

    def _get_boost_cooldown_ms(self, state, boost_key):
        if not isinstance(state, dict):
            return None
        boosts = state.get("activeBoosts", {}) if isinstance(state.get("activeBoosts"), dict) else {}
        row = boosts.get(boost_key, {}) if isinstance(boosts, dict) else {}
        if not isinstance(row, dict):
            return None
        try:
            return int(row.get("coolDown"))
        except (TypeError, ValueError):
            return None

    def _check_boost_ready_alerts(self, prev_state, state, event_markers):
        if not isinstance(prev_state, dict) or not isinstance(state, dict):
            return
        now_ms = int(time.time() * 1000)
        for boost_key, label in (("combat", "Combat"), ("skilling", "Skilling")):
            prev_cd = self._get_boost_cooldown_ms(prev_state, boost_key)
            curr_cd = self._get_boost_cooldown_ms(state, boost_key)
            if prev_cd is None or curr_cd is None:
                continue
            if curr_cd <= now_ms and prev_cd > now_ms:
                msg = f"{label} boost is ready to activate."
                event_markers.append(msg)
                if self.config.get("notify_boost_ready", False):
                    self.send_webhook("⚡ Boost Ready", msg)

    def try_recover_from_bad_save(self, bad_file_path, reason):
        if not self.save_folder or not os.path.exists(self.save_folder):
            return False
        try:
            bad_mtime = os.path.getmtime(bad_file_path)
            signature = f"{os.path.basename(bad_file_path)}:{bad_mtime}:{reason}"
            if self.last_recovery_signature == signature:
                return False
            self.last_recovery_signature = signature

            files = [os.path.join(self.save_folder, f) for f in os.listdir(self.save_folder) if os.path.isfile(os.path.join(self.save_folder, f))]
            files.sort(key=os.path.getmtime, reverse=True)
            for index, file_path in enumerate(files):
                if file_path == bad_file_path:
                    continue
                payload, raw_save, read_error = self.read_save_payload_from_file(file_path, f"recovery_{index}.tmp", include_error=True)
                if not payload or not raw_save:
                    self._scan_diag("recovery", file_path, "skip-read", read_error or "unknown")
                    continue
                state = payload.get('state', {}) if isinstance(payload, dict) else {}
                if not isinstance(state, dict):
                    self._scan_diag("recovery", file_path, "skip-state", "state-not-dict")
                    continue
                trackable_reason = self._state_trackable_reason(state)
                if trackable_reason:
                    self._scan_diag("recovery", file_path, "skip-untrackable", trackable_reason)
                    continue
                if not self.is_selected_profile(state):
                    profile = self.get_profile_info_from_state(state)
                    self._scan_diag("recovery", file_path, "skip-profile", f"id={profile.get('profileId') or 'unknown'}")
                    continue
                marker = f"Recovered from bad save ({reason}): {os.path.basename(bad_file_path)}"
                if raw_save != self._last_raw_save:
                    self._last_raw_save = raw_save
                    self.current_save_source = f"{os.path.basename(file_path)} [RECOVERY]"
                    self.process_state(state, source_label=self.current_save_source)
                    self.add_log_entry(self.current_save_source, [], [marker])
                else:
                    self.add_log_entry(os.path.basename(bad_file_path), [], [marker])
                self.safe_ui(self.status_lbl, "configure", text="RECOVERED", text_color="#e8a000")
                self._scan_diag("recovery", file_path, "processed", marker)
                return True

            self.add_log_entry(os.path.basename(bad_file_path), [], [f"Bad save detected ({reason}) but no recovery candidate found"])
            self.safe_ui(self.status_lbl, "configure", text="SAVE ERROR", text_color="#f0524f")
        except Exception:
            pass
        return False

    def log_disk_event(self, t, c):
        if not hasattr(self, 'disk_feed_frame') or not self.disk_feed_frame.winfo_exists(): return
        if len(self.disk_feed_frame.winfo_children()) > 20: self.disk_feed_frame.winfo_children()[0].destroy()
        ctk.CTkLabel(self.disk_feed_frame, text=t, font=("Consolas", 11), text_color=c, anchor="w").pack(fill="x", padx=5)

    def update_pos(self, c): self.config["pos"] = c; self.save_config()
    def toggle_skills_tab(self): self.config["show_skills"] = self.skills_toggle.get(); self.refresh_tabs(); self.save_config()
    def toggle_restore_items_on_restart(self): self.config["restore_items_on_restart"] = self.restore_items_toggle.get(); self.save_config()
    def toggle_disk_tab(self): self.config["show_disk_monitor"] = self.disk_toggle.get(); self.refresh_tabs(); self.save_config()
    def toggle_webhook_master(self): self.config["webhook_url"], self.config["webhook_enabled"] = self.webhook_entry.get().strip(), self.webhook_toggle.get(); self.refresh_tabs(); self.save_config()
    def toggle_always_on_top(self):
        self.config["always_on_top"] = self.always_on_top_toggle.get() if hasattr(self, 'always_on_top_toggle') else self.config.get("always_on_top", True)
        self.apply_topmost_setting()
        self.save_config()

    def save_notif_settings(self):
        self.config["notify_levels"] = self.sw_lvl.get()
        self.config["notify_slayer"] = self.sw_slayer.get()
        self.config["notify_xp"] = self.sw_xp.get()
        self.config["notify_no_slayer_task"] = self.sw_no_slayer_task.get() if hasattr(self, 'sw_no_slayer_task') else self.config.get("notify_no_slayer_task", False)
        self.config["notify_boost_ready"] = self.sw_boost_ready.get() if hasattr(self, 'sw_boost_ready') else self.config.get("notify_boost_ready", False)
        if hasattr(self, 'xp_interval_menu') and self.xp_interval_menu and self.xp_interval_menu.winfo_exists():
            try:
                self.config["xp_notify_interval_minutes"] = int(self.xp_interval_menu.get())
            except Exception:
                self.config["xp_notify_interval_minutes"] = 1
        self.save_config()

    def set_hidden_items(self, ids):
        self.hidden_items = set(str(i) for i in ids)
        self.config["hidden_items"] = sorted(list(self.hidden_items))
        self.save_config()
        self.apply_hidden_items()

    def apply_hidden_items(self):
        hidden_names = {self.get_item_name(i_id) for i_id in self.hidden_items}
        for name in list(self.item_history):
            if name in hidden_names:
                del self.item_history[name]
        self.update_ui_feed([
            (name, data['lvl'], data['gain'], data['rate'], self.format_ttl(data['ttl']), "SKILL")
            for name, data in self.active_skills.items()
        ] + [
            (name, "Item", sum(i[1] for i in hist), (sum(i[1] for i in hist) / (time.time() - hist[0][0])) * 3600 if hist and (time.time() - hist[0][0]) > 0 else 0, "ITEM", "ITEM")
            for name, hist in self.item_history.items()
        ])

    def clear_item_feed(self):
        self.item_history = {}
        self.stale_item_counts = {}
        self.recent_changed_item_ids = set()
        self.latest_feed_items = [row for row in self.latest_feed_items if len(row) >= 6 and row[5] != "ITEM"]
        self.update_ui_feed(self.latest_feed_items)
        self.save_session_cache()
        self.safe_ui(self.status_lbl, "configure", text="ITEM FEED CLEARED", text_color="#8ab4f8")

    def show_item_hide_popup(self):
        pop = ctk.CTkToplevel(self)
        pop.title("Hide Item IDs")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ctk.CTkLabel(container, text="Hide item IDs from the drop list", font=("Segoe UI", 12, "bold"), text_color="#dfe6ef").pack(anchor="w", pady=(0, 8))
        ctk.CTkLabel(container, text="Check the items you do NOT want to see again.", font=("Segoe UI", 10), text_color="#8e9db5").pack(anchor="w", pady=(0, 10))

        changed_ids = set(str(i) for i in self.recent_changed_item_ids)
        all_ids = sorted(changed_ids.union(set(self.hidden_items)), key=lambda x: (self.get_item_name(x), x))
        self._hide_item_vars = {}

        if not all_ids:
            ctk.CTkLabel(container, text="No recently changing items yet.", font=("Segoe UI", 11), text_color="#dfe6ef").pack(pady=16)
        else:
            search_frame = ctk.CTkFrame(container, fg_color="transparent")
            search_frame.pack(fill="x", pady=(0, 8))
            ctk.CTkLabel(search_frame, text="Search", font=("Segoe UI", 10), text_color="#8e9db5").pack(side="left", padx=(2, 8))
            search_var = ctk.StringVar(value="")
            search_entry = ctk.CTkEntry(search_frame, textvariable=search_var, placeholder_text="Type item name or ID...")
            search_entry.pack(side="left", fill="x", expand=True)

            scroll = ctk.CTkScrollableFrame(container, fg_color="#141414", border_width=0, height=260)
            scroll.pack(fill="both", expand=True, pady=(0, 10))
            for i_id in all_ids:
                self._hide_item_vars[i_id] = ctk.BooleanVar(value=(i_id in self.hidden_items))

            def render_filtered_list(*_):
                query = search_var.get().strip().lower()
                for child in scroll.winfo_children():
                    child.destroy()
                visible = 0
                for i_id in all_ids:
                    label = self.get_item_name(i_id)
                    haystack = f"{label} {i_id}".lower()
                    if query and query not in haystack:
                        continue
                    ctk.CTkCheckBox(scroll, text=f"{label} [{i_id}]", variable=self._hide_item_vars[i_id]).pack(anchor="w", pady=4, padx=10)
                    visible += 1
                if visible == 0:
                    ctk.CTkLabel(scroll, text="No matching items.", font=("Segoe UI", 10), text_color="#8e9db5").pack(anchor="w", pady=8, padx=10)

            search_var.trace_add("write", render_filtered_list)
            render_filtered_list()

        def save_hidden():
            new_hidden = [i_id for i_id, var in self._hide_item_vars.items() if var.get()]
            self.set_hidden_items(new_hidden)
            pop.destroy()

        ctk.CTkButton(container, text="SAVE HIDDEN ITEMS", fg_color="#2ecc71", hover_color="#27ae60", command=save_hidden).pack(fill="x")
        self._place_popup_near_main(pop)

    def on_webhook_url_change(self):
        self.config["webhook_url"] = self.webhook_entry.get().strip()
        self.save_config()
    def manual_dump(self): 
        with open("debug_dump.txt", "w") as f: 
            for line in self.current_debug_list: f.write(f"{line}\n")
    def format_ttl(self, s): return f"{int(s//3600)}h {int((s%3600)//60)}m {int(s%60)}s" if s > 0 else "MAX"
    def format_number(self, n):
        n = abs(float(n)); res = ""
        if n >= 1e9: res = f"{n/1e9:.2f}B"
        elif n >= 1e6: res = f"{n/1e6:.2f}M"
        elif n >= 1e3: res = f"{n/1e3:.1f}K"
        else: res = str(int(n))
        return f"-{res}" if float(n) < 0 else res
    def get_xp_for_level(self, l):
        xp = 0
        for i in range(1, l): xp += math.floor(i + 300 * (2 ** (i / 7.0)))
        return math.floor(xp / 4)
    def find_save_path(self):
        def _is_valid_leveldb(path):
            if not path or not os.path.isdir(path):
                return False
            try:
                entries = os.listdir(path)
            except Exception:
                return False
            return any(name.endswith((".ldb", ".log", ".sst")) for name in entries)

        def _latest_file_mtime(path):
            try:
                mt = 0.0
                for name in os.listdir(path):
                    fp = os.path.join(path, name)
                    if os.path.isfile(fp):
                        mt = max(mt, os.path.getmtime(fp))
                return mt
            except Exception:
                return 0.0

        found_candidates = set()
        self._startup_log("Starting save-path detection.")

        remembered = str(self.config.get("save_path", "")).strip() if isinstance(getattr(self, "config", None), dict) else ""
        if _is_valid_leveldb(remembered):
            found_candidates.add(remembered)
            self._startup_log(f"Valid remembered save path found: {remembered}")
        elif remembered:
            self._startup_log(f"Remembered save path is invalid: {remembered}")

        explicit_roaming = os.path.join(os.path.expanduser("~"), "AppData", "Roaming", "rocky-idle")
        explicit_candidates = [
            os.path.join(explicit_roaming, "Local Storage", "leveldb"),
            os.path.join(explicit_roaming, "leveldb"),
        ]
        for path in explicit_candidates:
            if _is_valid_leveldb(path):
                found_candidates.add(path)
                self._startup_log(f"Found explicit candidate: {path}")

        # Electron local profile paths.
        for root in [os.environ.get('APPDATA'), os.environ.get('LOCALAPPDATA')]:
            if not root:
                continue
            for name in ["Rocky Idle 3852250", "rocky-idle", "rocky_idle", "Rocky Idle", "Rocky_Idle", "rockyidle"]:
                path_candidates = [
                    os.path.join(root, name, "Local Storage", "leveldb"),
                    os.path.join(root, name, "leveldb"),
                ]
                for path in path_candidates:
                    if _is_valid_leveldb(path):
                        found_candidates.add(path)
                        self._startup_log(f"Found APPDATA/LOCALAPPDATA candidate: {path}")
                # Fallback: some installs nest leveldb differently; search shallowly for it.
                nested_pattern = os.path.join(root, name, "**", "leveldb")
                for path in glob.glob(nested_pattern, recursive=True):
                    if _is_valid_leveldb(path):
                        found_candidates.add(path)
                        self._startup_log(f"Found nested candidate: {path}")

        # Steam userdata cloud-style locations (works across different install drives).
        steam_roots = [
            os.environ.get("STEAM_PATH"),
            r"C:\Program Files (x86)\Steam",
            r"C:\Program Files\Steam",
        ]
        for steam_root in steam_roots:
            if not steam_root or not os.path.isdir(steam_root):
                continue
            patterns = [
                os.path.join(steam_root, "userdata", "*", "3852250", "remote", "Local Storage", "leveldb"),
                os.path.join(steam_root, "userdata", "*", "3852250", "remote", "leveldb"),
            ]
            for pattern in patterns:
                for path in glob.glob(pattern):
                    if _is_valid_leveldb(path):
                        found_candidates.add(path)
                        self._startup_log(f"Found Steam candidate: {path}")

        if not found_candidates:
            self._startup_log("Save-path detection finished: no valid candidates found.")
            return None

        # Pick the freshest valid leveldb to avoid stale/stock character data.
        best = max(found_candidates, key=_latest_file_mtime)
        self.config["save_path"] = best
        self._startup_log(f"Save-path detection selected freshest path: {best}")
        return best

    def read_save_payload_from_file(self, file_path, temp_name, include_error=False):
        error_reason = None
        def _to_float(value):
            try:
                return float(value or 0)
            except (TypeError, ValueError):
                return 0.0

        def _score_payload(payload, ordinal):
            state = payload.get('state', {}) if isinstance(payload, dict) else {}
            if not isinstance(state, dict):
                return (0, 0, 0.0, 0.0, 0, ordinal)

            trackable = 1 if self._state_trackable_reason(state) is None else 0

            account = state.get('accountInfo', {}) if isinstance(state.get('accountInfo'), dict) else {}
            account_hint = 1 if any(account.get(k) for k in ('inGameName', 'accountId', 'accountStart', 'profileId', 'characterId')) else 0

            time_hint = max(
                _to_float(state.get('inGameTime')),
                _to_float(state.get('playTime')),
                _to_float(state.get('ticks')),
                _to_float(state.get('totalGameTicks')),
            )

            skills = state.get('skills', {}) if isinstance(state.get('skills'), dict) else {}
            xp_map = state.get('skillsXp', {}) if isinstance(state.get('skillsXp'), dict) else {}

            total_level = 0
            total_xp = 0.0
            parsed_count = 0
            for sid in self.skill_map.keys():
                sid_str = str(sid)
                lvl = self._coerce_skill_level(skills.get(sid_str, {}))
                if lvl is None:
                    continue
                parsed_count += 1
                total_level += int(lvl)
                xd = xp_map.get(sid_str, 0)
                xp = xd.get('xp', xd) if isinstance(xd, dict) else xd
                total_xp += _to_float(xp)

            return (trackable, account_hint, time_hint, total_xp, total_level, parsed_count, ordinal)

        try:
            shutil.copy2(file_path, temp_name)
            with open(temp_name, 'rb') as f:
                matches = re.findall(rb'"(eJz[a-zA-Z0-9+/=]+)"', f.read())
            if not matches:
                error_reason = "no-compressed-save-blob"
                return (None, None, error_reason) if include_error else (None, None)

            best_payload = None
            best_raw = None
            best_score = None
            decode_failures = 0
            json_failures = 0

            for ordinal, raw_save in enumerate(matches):
                try:
                    decoded = zlib.decompress(base64.b64decode(raw_save.decode('utf-8'))).decode('utf-8')
                except Exception:
                    decode_failures += 1
                    continue
                try:
                    payload = json.loads(decoded)
                except Exception:
                    json_failures += 1
                    continue
                score = _score_payload(payload, ordinal)
                if best_score is None or score > best_score:
                    best_score = score
                    best_payload = payload
                    best_raw = raw_save

            if best_payload is None or best_raw is None:
                if decode_failures and not json_failures:
                    error_reason = "decode-failed:all-candidates"
                elif json_failures and not decode_failures:
                    error_reason = "json-failed:all-candidates"
                else:
                    error_reason = "decode-json-failed:all-candidates"
                return (None, None, error_reason) if include_error else (None, None)

            return (best_payload, best_raw, None) if include_error else (best_payload, best_raw)
        except Exception as exc:
            error_reason = f"read-failed:{type(exc).__name__}"
            return (None, None, error_reason) if include_error else (None, None)
        finally:
            try:
                if os.path.exists(temp_name):
                    os.remove(temp_name)
            except Exception:
                pass

    def get_profile_info_from_state(self, state):
        account = state.get('accountInfo', {}) if isinstance(state, dict) else {}
        name = str(account.get('inGameName') or 'Unknown').strip() or 'Unknown'
        account_id = str(account.get('accountId') or '').strip()
        account_start = str(account.get('accountStart') or '').strip()
        image_id = str(account.get('accountImgId') or '').strip()
        # accountId is account-level for many users, not character-level.
        # Prefer character-specific identity to avoid mixing stats between characters.
        explicit_profile_id = str(account.get('profileId') or '').strip()
        character_id = str(account.get('characterId') or '').strip()
        save_slot = str(account.get('saveSlot') or state.get('saveSlot') or '').strip() if isinstance(state, dict) else ''
        profile_parts = []
        if explicit_profile_id:
            profile_parts.append(f"profile:{explicit_profile_id}")
        if character_id:
            profile_parts.append(f"char:{character_id}")
        if save_slot:
            profile_parts.append(f"slot:{save_slot}")
        if name and image_id:
            profile_parts.append(f"nameimg:{name}:{image_id}")
        elif name and account_start:
            profile_parts.append(f"namestart:{name}:{account_start}")
        elif name and account_id:
            profile_parts.append(f"nameacct:{name}:{account_id}")
        elif name:
            profile_parts.append(f"name:{name}")
        elif account_id:
            profile_parts.append(f"acct:{account_id}")
        profile_id = "|".join(profile_parts) if profile_parts else "unknown"
        return {
            "profileId": profile_id,
            "accountId": account_id,
            "accountStart": account_start,
            "name": name,
            "imageId": image_id
        }

    def _profiles_match(self, selected_profile, current_profile):
        if not isinstance(selected_profile, dict) or not selected_profile:
            return True
        if not isinstance(current_profile, dict) or not current_profile:
            return False

        selected_id = str(selected_profile.get('profileId') or '').strip()
        current_id = str(current_profile.get('profileId') or '').strip()
        if selected_id and current_id and selected_id == current_id:
            return True

        # Strong account keys when present on both sides.
        for key in ('accountStart', 'accountId'):
            selected_value = str(selected_profile.get(key) or '').strip()
            current_value = str(current_profile.get(key) or '').strip()
            if selected_value and current_value and selected_value == current_value:
                selected_name = str(selected_profile.get('name') or '').strip().lower()
                current_name = str(current_profile.get('name') or '').strip().lower()
                return (not selected_name or not current_name or selected_name == current_name)

        # Fallback for profiles that only expose display-name + image variants.
        selected_name = str(selected_profile.get('name') or '').strip().lower()
        current_name = str(current_profile.get('name') or '').strip().lower()
        if selected_name and current_name and selected_name == current_name:
            return True

        return False

    def _coerce_skill_level(self, skill_entry):
        if not isinstance(skill_entry, dict):
            return None
        raw = skill_entry.get('level')
        try:
            lvl = int(raw)
        except (TypeError, ValueError):
            return None
        if lvl < 0 or lvl > 400:
            return None
        return lvl

    def _state_trackable_reason(self, state):
        if not isinstance(state, dict):
            return "state-not-dict"
        skills = state.get('skills', {}) if isinstance(state.get('skills'), dict) else {}
        if not skills:
            return "skills-missing"
        xp_map = state.get('skillsXp', {}) if isinstance(state.get('skillsXp'), dict) else {}

        parsed_levels = []
        has_xp = False
        for sid in self.skill_map.keys():
            lvl = self._coerce_skill_level(skills.get(str(sid), {}))
            if lvl is None:
                continue
            parsed_levels.append(lvl)
            xd = xp_map.get(str(sid), 0)
            xp = xd.get('xp', xd) if isinstance(xd, dict) else xd
            try:
                if float(xp or 0) > 0:
                    has_xp = True
            except (TypeError, ValueError):
                pass

        if len(parsed_levels) < 3:
            return f"too-few-skill-levels:{len(parsed_levels)}"
        if has_xp:
            return None
        if max(parsed_levels) <= 1:
            return "all-levels-default"
        return None

    def _state_has_trackable_skills(self, state):
        return self._state_trackable_reason(state) is None

    def scan_available_profiles(self, max_files=None):
        profiles = {}
        if not self.save_folder or not os.path.exists(self.save_folder):
            return []
        file_limit = int(max_files or self.save_scan_limit or 120)
        try:
            files = [os.path.join(self.save_folder, f) for f in os.listdir(self.save_folder) if os.path.isfile(os.path.join(self.save_folder, f))]
            files.sort(key=os.path.getmtime, reverse=True)
            for index, file_path in enumerate(files[:file_limit]):
                payload, _, read_error = self.read_save_payload_from_file(file_path, f"profile_scan_{index}.tmp", include_error=True)
                if not payload:
                    self._scan_diag("profile-scan", file_path, "skip-read", read_error or "unknown")
                    continue
                state = payload.get('state', {}) if isinstance(payload, dict) else {}
                if not isinstance(state, dict) or not state:
                    self._scan_diag("profile-scan", file_path, "skip-state", "missing-or-invalid-state")
                    continue
                trackable_reason = self._state_trackable_reason(state)
                if trackable_reason:
                    self._scan_diag("profile-scan", file_path, "skip-untrackable", trackable_reason)
                    continue
                profile = self.get_profile_info_from_state(state)
                profile_id = profile.get('profileId')
                if not profile_id:
                    self._scan_diag("profile-scan", file_path, "skip-profile", "missing-profile-id")
                    continue
                mtime = os.path.getmtime(file_path)
                existing = profiles.get(profile_id)
                if existing and existing.get('mtime', 0) >= mtime:
                    continue
                profiles[profile_id] = {
                    **profile,
                    "mtime": mtime,
                    "latestFile": file_path,
                    "latestFileName": os.path.basename(file_path)
                }
                self._scan_diag("profile-scan", file_path, "profile-candidate", f"name={profile.get('name') or 'Unknown'} | id={profile_id}")
        except Exception:
            return []
        return sorted(profiles.values(), key=lambda x: x.get('mtime', 0), reverse=True)

    def is_selected_profile(self, state):
        if not self.selected_profile_id and not self.selected_profile_info:
            return True
        current_profile = self.get_profile_info_from_state(state)
        selected_profile = self.selected_profile_info if isinstance(self.selected_profile_info, dict) and self.selected_profile_info else {
            'profileId': self.selected_profile_id,
            'name': self.selected_profile_name,
        }
        return self._profiles_match(selected_profile, current_profile)

    def reset_tracking_state(self):
        for popout in list(self.open_popouts):
            try:
                popout.get('window').destroy()
            except:
                pass
        # Clear existing feed rows before resetting widget tracking.
        for container_name in ("skill_feed", "item_feed"):
            container = getattr(self, container_name, None)
            if container and container.winfo_exists():
                try:
                    for child in container.winfo_children():
                        child.destroy()
                except Exception:
                    pass
        self.last_known_mtime = 0
        self._last_raw_save = None
        self.prev_state = None
        self.current_debug_list = []
        self.xp_history = {}
        self.session_start_xp = {}
        self.session_gp_earned = 0.0
        self.current_levels = {}
        self.active_skills = {}
        self.stale_counts = {}
        self.save_history = deque()
        self.latest_save_data = {}
        self.latest_save_source = None
        self.current_save_source = None
        self.xp_active_scan_streak = 0
        self.xp_inactive_scan_streak = 0
        self.xp_activity_armed = False
        self.xp_inactive_notified = False
        self.skill_diamond_status = {}
        self.item_history = {}
        self.stale_item_counts = {}
        self.no_slayer_task_count = 0
        self.no_slayer_task_notified = False
        self.no_change_save_count = 0
        self.drift_alert_active = False
        self.last_recovery_signature = None
        self.feed_widgets = {}
        self.latest_feed_items = []
        self.open_popouts = []
        self.update_ui_feed([])
        self.safe_ui(self.total_lvl_lbl, "configure", text="--")
        self.safe_ui(self.total_xp_lbl, "configure", text="--")
        self.safe_ui(self.session_xp_lbl, "configure", text="0")
        self.safe_ui(self.session_gp_lbl, "configure", text="0")
        self.safe_ui(self.slayer_task_lbl, "configure", text="None")
        self.safe_ui(self.slayer_kills_lbl, "configure", text="0")
        self.safe_ui(self.slayer_points_lbl, "configure", text="0")
        self.safe_ui(self.slayer_streak_lbl, "configure", text="0")

    def select_profile(self, profile):
        self.selected_profile_id = profile.get('profileId')
        self.selected_profile_name = profile.get('name')
        self.selected_profile_info = dict(profile) if isinstance(profile, dict) else {}
        self.reset_tracking_state()
        self.add_log_entry(profile.get('name', 'PROFILE'), [], [f"Profile switched to {profile.get('name', 'Unknown')}"])
        if hasattr(self, 'profile_name_lbl') and self.profile_name_lbl.winfo_exists():
            self.profile_name_lbl.configure(text=f"{self.selected_profile_name}",
                                            text_color=self._C.get("gold", "#e8a000"))
        self.update_overview_snapshot(self.prev_state)
        self._set_status_text("PROFILE SELECTED", text_color="#8ab4f8", include_context=True)
        self.force_initial_load()
        self.initial_load_done = True

    def show_profile_picker(self, profiles):
        if not profiles:
            self.safe_ui(self.status_lbl, "configure", text="NO PROFILES FOUND", text_color="#e67e22")
            return False
        if self.profile_picker_open:
            try:
                self.profile_picker_window.lift()
                self.profile_picker_window.focus_force()
            except:
                pass
            return False
        self.profile_picker_open = True
        pop = ctk.CTkToplevel(self)
        self.profile_picker_window = pop
        pop.title("Choose Profile")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)
        self._place_popup_near_main(pop, width=360, height=420)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)
        ctk.CTkLabel(container, text="Choose Character", font=("Segoe UI", 14, "bold"), text_color="#dfe6ef").pack(anchor="center", pady=(12, 4))
        ctk.CTkLabel(container, text="Select which save profile Rocky Idle Reader should follow.", font=("Segoe UI", 10), text_color="#8e9db5").pack(anchor="center", pady=(0, 10))

        scroll = ctk.CTkScrollableFrame(container, fg_color="#141414", corner_radius=12)
        scroll.pack(fill="both", expand=True, padx=4, pady=(0, 10))

        def close_picker():
            try:
                pop.destroy()
            except:
                pass
            self.profile_picker_open = False
            self.profile_picker_window = None

        def choose(profile):
            close_picker()
            self.select_profile(profile)

        for profile in profiles:
            label = profile.get('name', 'Unknown')
            ctk.CTkButton(scroll, text=label, height=42, anchor="w", fg_color="#2f2f2f", hover_color="#383838", command=lambda p=profile: choose(p)).pack(fill="x", padx=10, pady=6)

        pop.protocol("WM_DELETE_WINDOW", close_picker)
        return False

    def ensure_profile_selected(self):
        profiles = self.scan_available_profiles()
        if not profiles:
            self._set_status_text("NO PROFILES FOUND", text_color="#e67e22", include_context=True)
            return False
        # On startup, always ask when multiple profiles are present.
        if not self.initial_load_done and len(profiles) > 1:
            self.selected_profile_id = None
            self.selected_profile_name = None
            self.selected_profile_info = {}
            if hasattr(self, 'profile_name_lbl') and self.profile_name_lbl.winfo_exists():
                self.profile_name_lbl.configure(text="Choose profile", text_color=self._C.get("txt", "#dfe6ef"))
            self._set_status_text("SELECT A PROFILE", text_color="#f1c40f", include_context=True)
            return self.show_profile_picker(profiles)
        if self.selected_profile_id:
            selected_profile = self.selected_profile_info if isinstance(self.selected_profile_info, dict) and self.selected_profile_info else {
                'profileId': self.selected_profile_id,
                'name': self.selected_profile_name,
            }
            for profile in profiles:
                if self._profiles_match(selected_profile, profile):
                    self.selected_profile_id = profile.get('profileId') or self.selected_profile_id
                    self.selected_profile_name = profile.get('name') or self.selected_profile_name
                    self.selected_profile_info = dict(profile)
                    if hasattr(self, 'profile_name_lbl') and self.profile_name_lbl.winfo_exists() and self.selected_profile_name:
                        self.profile_name_lbl.configure(text=self.selected_profile_name, text_color=self._C.get("gold", "#e8a000"))
                    return True
            self.selected_profile_id = None
            self.selected_profile_name = None
            self.selected_profile_info = {}
        if len(profiles) == 1:
            self.select_profile(profiles[0])
            return True
        return self.show_profile_picker(profiles)
    def _post_webhook_payload(self, url, payload):
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode('utf-8'),
            headers={
                'Content-Type': 'application/json',
                'User-Agent': f'RockyIdleReader/{self.app_version}',
            },
            method='POST',
        )
        with urllib.request.urlopen(req, timeout=10) as response:
            status = int(getattr(response, 'status', 0) or 0)
            if status and not (200 <= status < 300):
                raise RuntimeError(f"HTTP {status}")

    def send_webhook(self, t, m, force=False, on_complete=None):
        url = str(self.config.get("webhook_url", "") or "").strip()
        if not url:
            if callable(on_complete):
                self.after(0, lambda: on_complete(False, "Webhook URL is empty."))
            return
        if (not force) and (not self.config.get("webhook_enabled")):
            if callable(on_complete):
                self.after(0, lambda: on_complete(False, "Webhook is disabled in settings."))
            return

        def _f():
            try:
                payload = {
                    "embeds": [{
                        "title": t,
                        "description": m,
                        "color": 3915872,
                        "timestamp": time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                    }]
                }
                self._post_webhook_payload(url, payload)
                self._startup_log("Webhook delivered successfully.")
                if callable(on_complete):
                    self.after(0, lambda: on_complete(True, "Webhook sent."))
            except Exception as exc:
                self._startup_log(f"Webhook delivery failed: {exc}")
                if callable(on_complete):
                    self.after(0, lambda: on_complete(False, str(exc)))

        threading.Thread(target=_f, daemon=True).start()
    def update_debug_feed(self, c):
        if not hasattr(self, 'debug_scroll') or not self.debug_scroll.winfo_exists(): return
        self.refresh_log_view()

    def add_log_entry(self, label, diffs, markers=None):
        entry = {
            'label': label,
            'time': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'diffs': diffs or [],
            'markers': markers or []
        }
        self.save_history.append(entry)
        for marker in entry['markers']:
            self.event_history.append(f"[{entry['time']}] {marker}")
        self.refresh_log_view()

    def refresh_log_view(self):
        if not hasattr(self, 'debug_scroll') or not self.debug_scroll.winfo_exists(): return
        for w in self.debug_scroll.winfo_children():
            w.destroy()
        ctk.CTkLabel(self.debug_scroll, text="Save Files", font=("Segoe UI", 12, "bold"), text_color="#dfe6ef", anchor="w").pack(fill="x", pady=(8, 4), padx=10)
        if not self.save_history:
            ctk.CTkLabel(self.debug_scroll, text="No save logs yet.", font=("Segoe UI", 11), text_color="#cccccc", anchor="w").pack(fill="x", pady=10, padx=10)
            return
        for entry in reversed(self.save_history):
            text = f"{entry['label']} — {len(entry['diffs'])} change(s)"
            if entry.get('markers'):
                text += f" | {len(entry['markers'])} event(s)"
            btn = ctk.CTkButton(self.debug_scroll, text=text, fg_color="#2f2f2f", hover_color="#383838", command=lambda e=entry: self.show_log_entry_popup(e))
            btn.pack(fill="x", padx=10, pady=4)

    def show_log_entry_popup(self, entry):
        pop = ctk.CTkToplevel(self)
        pop.title(f"Log: {entry['label']}")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        header = ctk.CTkLabel(container, text=f"{entry['label']} — {entry['time']}", font=("Segoe UI", 12, "bold"), text_color="#dfe6ef")
        header.pack(anchor="w", pady=(0, 8))

        content_frame = ctk.CTkFrame(container, fg_color="#141414", corner_radius=12)
        content_frame.pack(fill="both", expand=True, padx=0, pady=(0, 10))

        text_widget = tk.Text(content_frame, wrap="none", bg="#141414", fg="#dfe6ef", insertbackground="#dfe6ef", bd=0, highlightthickness=0)
        text_widget.pack(side="left", fill="both", expand=True, padx=(8, 0), pady=8)
        yscroll = tk.Scrollbar(content_frame, orient="vertical", command=text_widget.yview)
        yscroll.pack(side="right", fill="y")
        text_widget.configure(yscrollcommand=yscroll.set)

        marker_lines = [f"[EVENT] {m}" for m in entry.get('markers', [])]
        parts = []
        if marker_lines:
            parts.append("\n".join(marker_lines))
        if entry['diffs']:
            parts.append("\n".join(entry['diffs']))
        content = "\n\n".join(parts) if parts else "No changes captured for this entry."
        text_widget.insert("1.0", content)
        text_widget.configure(state="disabled")

        footer = ctk.CTkFrame(container, fg_color="transparent")
        footer.pack(fill="x")

        def copy_text():
            try:
                self.clipboard_clear()
                self.clipboard_append(content)
            except: pass

        def dump_text():
            try:
                path = fd.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
                if path:
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(content)
            except: pass

        ctk.CTkButton(footer, text="COPY", width=100, command=copy_text).pack(side="left", padx=(0, 6))
        ctk.CTkButton(footer, text="DUMP TXT", width=100, command=dump_text).pack(side="left")
        ctk.CTkButton(footer, text="CLOSE", width=100, command=pop.destroy).pack(side="right")
        self._place_popup_near_main(pop)

    def refresh_explorer_view(self):
        if not self.explorer_tree_widget:
            return
        for item in self.explorer_tree_widget.get_children():
            self.explorer_tree_widget.delete(item)
        if not self.latest_save_data:
            self.explorer_tree_widget.insert("", "end", text="No save data loaded.", values=("",))
            return
        self.insert_tree_node("", "state", self.latest_save_data)

    def insert_tree_node(self, parent, key, value):
        if isinstance(value, dict):
            node = self.explorer_tree_widget.insert(parent, "end", text=str(key), values=(f"dict ({len(value)})",), open=False)
            for child_key, child_value in value.items():
                self.insert_tree_node(node, child_key, child_value)
        elif isinstance(value, list):
            node = self.explorer_tree_widget.insert(parent, "end", text=str(key), values=(f"list ({len(value)})",), open=False)
            for index, child_value in enumerate(value):
                self.insert_tree_node(node, f"[{index}]", child_value)
        else:
            display = "None" if value is None else str(value)
            self.explorer_tree_widget.insert(parent, "end", text=str(key), values=(display,))

    def set_tree_open_state(self, item_id, is_open):
        self.explorer_tree_widget.item(item_id, open=is_open)
        for child in self.explorer_tree_widget.get_children(item_id):
            self.set_tree_open_state(child, is_open)

    def expand_explorer_tree(self):
        if not self.explorer_tree_widget:
            return
        for root in self.explorer_tree_widget.get_children(""):
            self.set_tree_open_state(root, True)

    def collapse_explorer_tree(self):
        if not self.explorer_tree_widget:
            return
        for root in self.explorer_tree_widget.get_children(""):
            self.set_tree_open_state(root, False)

    def get_explorer_dump_text(self):
        if not self.latest_save_data:
            return "No save data loaded."
        try:
            return json.dumps(self.latest_save_data, indent=2)
        except Exception:
            return str(self.latest_save_data)

    def pull_explorer_save(self):
        if not self.save_folder or not os.path.exists(self.save_folder):
            return
        try:
            files = [os.path.join(self.save_folder, f) for f in os.listdir(self.save_folder) if os.path.isfile(os.path.join(self.save_folder, f))]
            if not files:
                return
            latest = max(files, key=os.path.getmtime)
            with open(latest, 'rb') as f:
                matches = re.findall(rb'"(eJz[a-zA-Z0-9+/=]+)"', f.read())
                if not matches:
                    return
                decoded = zlib.decompress(base64.b64decode(matches[-1].decode('utf-8'))).decode('utf-8')
                self.latest_save_data = json.loads(decoded).get('state', {})
                self.latest_save_source = os.path.basename(latest)
                self.refresh_explorer_view()
                if hasattr(self, 'explorer_status_lbl'):
                    self.explorer_status_lbl.configure(text=f"Loaded: {self.latest_save_source}")
        except: pass

    def clear_explorer_view(self):
        self.latest_save_data = {}
        if self.explorer_tree_widget:
            for item in self.explorer_tree_widget.get_children():
                self.explorer_tree_widget.delete(item)
            self.explorer_tree_widget.insert("", "end", text="No save data loaded.", values=("",))
        if hasattr(self, 'explorer_status_lbl'):
            self.explorer_status_lbl.configure(text="Explorer cleared")

    def copy_explorer_text(self):
        if not self.explorer_tree_widget:
            return
        try:
            text = self.get_explorer_dump_text()
            self.clipboard_clear()
            self.clipboard_append(text)
        except: pass

    def dump_explorer_text(self):
        if not self.explorer_tree_widget:
            return
        try:
            path = fd.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
            if path:
                text = self.get_explorer_dump_text()
                with open(path, "w", encoding="utf-8") as f:
                    f.write(text)
        except: pass
    def create_card(self, parent, title, value, color):
        C = self._C
        compact = self.config.get("density", "Comfortable") == "Compact"
        title_font = ("Segoe UI", 8) if compact else ("Segoe UI", 9)
        value_font = ("Segoe UI", 18, "bold") if compact else ("Segoe UI", 22, "bold")
        top_pad = 8 if compact else 12
        bottom_pad = 8 if compact else 12
        card = ctk.CTkFrame(parent, fg_color=C["card"], corner_radius=10,
                            border_width=1, border_color=C["card_bd"])
        card.pack(side="left", fill="both", expand=True, padx=4, pady=4)
        ctk.CTkLabel(card, text=title, font=title_font,
                     text_color=C["dim"]).pack(anchor="center", padx=12, pady=(top_pad, 0))
        lbl = ctk.CTkLabel(card, text=value, font=value_font, text_color=color)
        lbl.pack(anchor="center", padx=12, pady=(4, bottom_pad))
        return lbl

    def create_row(self, parent, label, value, color):
        C = self._C
        compact = self.config.get("density", "Comfortable") == "Compact"
        row_pad = 1 if compact else 3
        label_font = ("Segoe UI", 9) if compact else ("Segoe UI", 10)
        value_font = ("Segoe UI", 10, "bold") if compact else ("Segoe UI", 11, "bold")
        r = ctk.CTkFrame(parent, fg_color="transparent")
        r.pack(fill="x", pady=row_pad, padx=16)
        ctk.CTkLabel(r, text=label, font=label_font,
                     text_color=C["dim"]).pack(side="left")
        lbl = ctk.CTkLabel(r, text=value, font=value_font, text_color=color)
        lbl.pack(side="right")
        return lbl

    def attach_tooltip(self, widget, text, delay_ms=250):
        state = {"job": None, "tip": None}

        def hide_tip(_event=None):
            if state["job"] is not None:
                try:
                    self.after_cancel(state["job"])
                except Exception:
                    pass
                state["job"] = None
            if state["tip"] is not None:
                try:
                    state["tip"].destroy()
                except Exception:
                    pass
                state["tip"] = None

        def show_tip():
            hide_tip()
            try:
                tip = ctk.CTkToplevel(widget)
                tip.overrideredirect(True)
                tip.attributes("-topmost", bool(self.config.get("always_on_top", True)))
                x = widget.winfo_rootx() + 18
                y = widget.winfo_rooty() + 24
                tip.geometry(f"+{x}+{y}")
                frame = ctk.CTkFrame(tip, fg_color="#101620", corner_radius=8, border_width=1, border_color="#2b3b52")
                frame.pack(fill="both", expand=True)
                ctk.CTkLabel(
                    frame,
                    text=text,
                    font=("Segoe UI", 10),
                    text_color="#dfe6ef",
                    justify="left",
                    wraplength=320,
                ).pack(padx=10, pady=8)
                state["tip"] = tip
            except Exception:
                state["tip"] = None

        def queue_tip(_event=None):
            hide_tip()
            state["job"] = self.after(delay_ms, show_tip)

        widget.bind("<Enter>", queue_tip)
        widget.bind("<Leave>", hide_tip)
        widget.bind("<ButtonPress>", hide_tip)

    def _apply_feed_controls(self, rows, prefix):
        q = str(self.config.get(f"{prefix}_filter", "")).strip().lower()
        sort_mode = self.config.get(f"{prefix}_sort", "Rate")
        if q:
            rows = [r for r in rows if q in str(r[0]).lower()]
        if sort_mode == "Name":
            return sorted(rows, key=lambda r: str(r[0]).lower())
        if sort_mode == "Gain":
            return sorted(rows, key=lambda r: abs(float(r[2])), reverse=True)
        if prefix == "items":
            if sort_mode == "Count/h":
                return sorted(rows, key=lambda r: abs(float(r[3])), reverse=True)
            if sort_mode in ("Rate", "GP/h"):
                cache = getattr(self, "_skill_optimizer_cache", None)
                name_to_gp = cache.get("name_to_sell_gp", {}) if isinstance(cache, dict) and cache.get("ready") else {}
                return sorted(rows, key=lambda r: abs(float(r[3])) * float(name_to_gp.get(str(r[0]), 0.0)), reverse=True)
        return sorted(rows, key=lambda r: abs(float(r[3])), reverse=True)

    def update_feed_controls(self, key, value):
        self.config[key] = value
        self.save_config()
        self.update_ui_feed(self.latest_feed_items)

    def update_density(self, value):
        self.config["density"] = value
        self.save_config()
        self.refresh_tabs()
        self.update_ui_feed(self.latest_feed_items)

    def send_test_webhook(self):
        test_url = self.webhook_entry.get().strip() if hasattr(self, 'webhook_entry') and self.webhook_entry else ""
        if not test_url:
            self.safe_ui(self.status_lbl, "configure", text="WEBHOOK URL MISSING", text_color="#f0524f")
            _show_error_messagebox("Rocky Idle Reader", "Please paste a Discord webhook URL first.")
            return

        self.config["webhook_url"] = test_url
        self.save_config()
        self.safe_ui(self.status_lbl, "configure", text="TESTING WEBHOOK...", text_color="#8ab4f8")

        def _on_done(ok, info):
            if ok:
                self.safe_ui(self.status_lbl, "configure", text="WEBHOOK TEST OK", text_color="#3fb950")
                _show_error_messagebox("Rocky Idle Reader", "Discord webhook test sent successfully.")
            else:
                self.safe_ui(self.status_lbl, "configure", text="WEBHOOK TEST FAILED", text_color="#f0524f")
                _show_error_messagebox("Rocky Idle Reader", f"Discord webhook test failed:\n{info}")

        self.send_webhook("🔔 Discord Test", "Rocky Idle Reader webhook is connected.", force=True, on_complete=_on_done)

    def export_app_data(self):
        try:
            path = fd.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
            if not path:
                return
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.data_store, f, indent=2)
            self.safe_ui(self.status_lbl, "configure", text="DATA EXPORTED", text_color="#3fb950")
        except Exception:
            self.safe_ui(self.status_lbl, "configure", text="EXPORT FAILED", text_color="#f0524f")

    def import_app_data(self):
        try:
            path = fd.askopenfilename(filetypes=[("JSON", "*.json")])
            if not path:
                return
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f)
            sections = payload.get("sections", payload if isinstance(payload, dict) else {})
            if not isinstance(sections, dict):
                raise ValueError("Invalid data file")
            self.data_store = {"version": payload.get("version", 1), "sections": sections}
            self.save_data_store()
            self.skill_map = self.load_skill_db()
            self.monster_map = self.load_monster_db()
            self.slayer_category_map = self.load_slayer_category_map()
            self.item_map = self.load_item_db()
            self.mining_db = self.load_mining_db()
            self.item_meta = self.load_item_meta()
            self.config = self.load_config()
            self.hidden_items = set(self.config.get("hidden_items", []))
            self.refresh_tabs()
            self.switch_section(self.config.get("last_section", "OVERVIEW") if self.config.get("last_section") in self.section_frames else "OVERVIEW")
            self.toggle_sidebar(force=bool(self.config.get("sidebar_collapsed", False)), persist=False)
            self.update_ui_feed(self.latest_feed_items)
            self.safe_ui(self.status_lbl, "configure", text="DATA IMPORTED", text_color="#3fb950")
        except Exception:
            self.safe_ui(self.status_lbl, "configure", text="IMPORT FAILED", text_color="#f0524f")

    def get_health_report(self):
        save_ok = bool(self.save_folder and os.path.exists(self.save_folder))
        profile_ok = bool(self.selected_profile_id or self.selected_profile_name)
        webhook_ok = bool(str(self.config.get("webhook_url", "")).strip())
        try:
            self.save_data_store()
            store_ok = os.path.exists(self.data_store_file)
        except Exception:
            store_ok = False
        sync_age = int(time.time() - self.last_sync_epoch) if self.last_sync_epoch > 0 else None
        return {
            "Save Path": "OK" if save_ok else "Missing",
            "Profile": self.selected_profile_name or ("Selected" if profile_ok else "Not selected"),
            "Discord Webhook": "Configured" if webhook_ok else "Not configured",
            "Data Store": "Writable" if store_ok else "Write failed",
            "Last Sync": f"{sync_age}s ago" if sync_age is not None else "No sync yet",
        }

    def show_health_popup(self):
        pop = ctk.CTkToplevel(self)
        pop.title("Health Checks")
        self._set_popup_topmost(pop)
        pop.resizable(False, False)
        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)
        ctk.CTkLabel(container, text="Startup Health Checks", font=("Segoe UI", 13, "bold"), text_color="#dfe6ef").pack(anchor="w", pady=(0, 8))
        report = self.get_health_report()
        for key, value in report.items():
            row = ctk.CTkFrame(container, fg_color="transparent")
            row.pack(fill="x", pady=3)
            ctk.CTkLabel(row, text=key, font=("Segoe UI", 10), text_color="#8e9db5").pack(side="left")
            ctk.CTkLabel(row, text=str(value), font=("Segoe UI", 10, "bold"), text_color="#e6edf3").pack(side="right")
        ctk.CTkButton(container, text="Close", width=100, command=pop.destroy).pack(pady=(10, 0))
        self._place_popup_near_main(pop)
    def snap_to_game(self):
        if self.is_closing:
            return
        try:
            if self.config.get("pos") != "Free Flow":
                game = None

                # Prefer the currently active game window and only snap to it when visible.
                try:
                    active = gw.getActiveWindow()
                    active_title = (active.title or "").strip() if active else ""
                    if active and not active.isMinimized and self.game_title.lower() in active_title.lower():
                        game = active
                except Exception:
                    game = None

                # Fallback: look up Rocky Idle windows and require active + not minimized.
                if not game:
                    wins = gw.getWindowsWithTitle(self.game_title)
                    game = next(
                        (
                            w for w in wins
                            if not w.isMinimized
                            and self.game_title.lower() in (w.title or "").lower()
                            and getattr(w, "isActive", False)
                        ),
                        None,
                    )

                if game:
                    w, h = self.winfo_width(), self.winfo_height()
                    if self.config.get("pos") == "Top-Right": x, y = game.left + game.width - w - 20, game.top + 45
                    elif self.config.get("pos") == "Top-Left": x, y = game.left + 20, game.top + 45
                    elif self.config.get("pos") == "Bottom-Right": x, y = game.left + game.width - w - 20, game.top + game.height - h - 20
                    elif self.config.get("pos") == "Bottom-Left": x, y = game.left + 20, game.top + game.height - h - 20
                    else: x, y = self.winfo_x(), self.winfo_y()
                    self.geometry(f"+{int(x)}+{int(y)}")
        except Exception:
            pass
        self.after(1000, self.snap_to_game)

    def setup_settings_tab(self):
        pass  # replaced by _build_settings_page in setup_main_ui

    def refresh_tabs(self):
        C = self._C
        try:
            # ── NOTIFY section ────────────────────────────────────────
            if self.config.get("webhook_enabled") and "NOTIFY" not in self.section_frames:
                frm = ctk.CTkFrame(self.content_area, fg_color="transparent")
                self.section_frames["NOTIFY"] = frm
                _f = ctk.CTkScrollableFrame(frm, fg_color="transparent")
                _f.pack(fill="both", expand=True, padx=14, pady=14)
                ctk.CTkLabel(_f, text="Discord Alerts", font=("Segoe UI", 13, "bold"),
                             text_color=C["txt"]).pack(anchor="w", pady=(0, 12))
                self.sw_lvl = ctk.CTkSwitch(_f, text="Level-up Alerts",
                    command=self.save_notif_settings, text_color=C["txt"])
                self.sw_lvl.pack(anchor="w", pady=4)
                self.sw_slayer = ctk.CTkSwitch(_f, text="Slayer Completion Alerts",
                    command=self.save_notif_settings, text_color=C["txt"])
                self.sw_slayer.pack(anchor="w", pady=4)
                _xp_alert_row = ctk.CTkFrame(_f, fg_color="transparent")
                _xp_alert_row.pack(fill="x", pady=4)
                self.sw_xp = ctk.CTkSwitch(_xp_alert_row, text="XP Activity Alerts",
                    command=self.save_notif_settings, text_color=C["txt"])
                self.sw_xp.pack(side="left")
                self.xp_interval_menu = ctk.CTkOptionMenu(
                    _xp_alert_row,
                    values=["1", "3", "5"],
                    command=lambda _v: self.save_notif_settings(),
                    width=96,
                    fg_color=C["nav_act"],
                    button_color=C["card"],
                    button_hover_color=C["nav_hvr"],
                    text_color=C["txt"],
                    dropdown_fg_color=C["nav"],
                    dropdown_text_color=C["txt"],
                )
                self.xp_interval_menu.pack(side="right")
                raw_interval = int(self.config.get("xp_notify_interval_minutes", 1) or 1)
                interval_value = str(raw_interval if raw_interval in (1, 3, 5) else 1)
                self.xp_interval_menu.set(interval_value)
                self.sw_no_slayer_task = ctk.CTkSwitch(_f, text="No Slayer Task Alerts",
                    command=self.save_notif_settings, text_color=C["txt"])
                self.sw_no_slayer_task.pack(anchor="w", pady=4)
                self.sw_boost_ready = ctk.CTkSwitch(_f, text="Boost Ready Alerts",
                    command=self.save_notif_settings, text_color=C["txt"])
                self.sw_boost_ready.pack(anchor="w", pady=4)
                if self.config.get("notify_levels"):         self.sw_lvl.select()
                if self.config.get("notify_slayer"):         self.sw_slayer.select()
                if self.config.get("notify_xp"):             self.sw_xp.select()
                if self.config.get("notify_no_slayer_task"): self.sw_no_slayer_task.select()
                if self.config.get("notify_boost_ready"):    self.sw_boost_ready.select()
                self._add_nav_btn("NOTIFY", "◌", "DISCORD")
                self._reorder_settings_btn()
            elif not self.config.get("webhook_enabled") and "NOTIFY" in self.section_frames:
                self._remove_section("NOTIFY")

            # ── ALL SKILLS section ────────────────────────────────────
            if self.config.get("show_skills") and "ALL SKILLS" not in self.section_frames:
                frm = ctk.CTkFrame(self.content_area, fg_color="transparent")
                self.section_frames["ALL SKILLS"] = frm
                _s = ctk.CTkScrollableFrame(frm, fg_color="transparent")
                _s.pack(fill="both", expand=True, padx=8, pady=8)
                ctk.CTkLabel(_s, text="All Skills", font=("Segoe UI", 13, "bold"),
                             text_color=C["txt"]).pack(anchor="w", padx=6, pady=(0, 10))
                self.skill_labels = {}
                self.skill_name_labels = {}
                for sid, name in sorted(self.skill_map.items()):
                    _row = ctk.CTkFrame(_s, fg_color=C["card"], corner_radius=8,
                                        border_width=1, border_color=C["card_bd"])
                    _row.pack(fill="x", padx=4, pady=3)
                    name_lbl = ctk.CTkLabel(_row, text=f"{name} (0.00/3.00 Diamond)",
                                            font=("Segoe UI", 11), text_color=C["txt"])
                    name_lbl.pack(side="left", padx=12, pady=8)
                    self.skill_name_labels[sid] = name_lbl
                    lvl_lbl = ctk.CTkLabel(_row, text="--",
                                           font=("Segoe UI", 11, "bold"), text_color=C["gold"])
                    lvl_lbl.pack(side="right", padx=12)
                    self.skill_labels[sid] = lvl_lbl
                self._add_nav_btn("ALL SKILLS", "☰", "ALL SKILLS")
                self._reorder_settings_btn()
            elif not self.config.get("show_skills") and "ALL SKILLS" in self.section_frames:
                self._remove_section("ALL SKILLS")

            # ── DISK section (dev) ────────────────────────────────────
            if self.dev_mode and self.config.get("show_disk_monitor") and "DISK" not in self.section_frames:
                frm = ctk.CTkFrame(self.content_area, fg_color="transparent")
                self.section_frames["DISK"] = frm
                self.disk_feed_frame = ctk.CTkScrollableFrame(frm, fg_color="transparent")
                self.disk_feed_frame.pack(fill="both", expand=True, padx=5, pady=5)
                self._add_nav_btn("DISK", "⬡", "DISK")
                self._reorder_settings_btn()
            elif (not self.dev_mode or not self.config.get("show_disk_monitor")) and "DISK" in self.section_frames:
                self._remove_section("DISK")

            # ── LOGS section (dev) ────────────────────────────────────
            if self.dev_mode and "LOGS" not in self.section_frames:
                frm = ctk.CTkFrame(self.content_area, fg_color="transparent")
                self.section_frames["LOGS"] = frm
                self.tab_debug = frm
                _dtop = ctk.CTkFrame(frm, fg_color="transparent")
                _dtop.pack(fill="x", padx=10, pady=(10, 0))
                ctk.CTkLabel(_dtop, text="DEBUG LOG", font=("Segoe UI", 12, "bold"),
                             text_color=C["blue"]).pack(side="left")
                ctk.CTkButton(_dtop, text="DUMP LOG", width=110, height=32,
                              fg_color=C["blue"], hover_color="#3a75d4",
                              command=self.manual_dump).pack(side="right")
                self.debug_scroll = ctk.CTkScrollableFrame(frm, fg_color=C["card"],
                                                           border_width=1, border_color=C["card_bd"])
                self.debug_scroll.pack(fill="both", expand=True, padx=10, pady=10)
                self.refresh_log_view()
                self._add_nav_btn("LOGS", "▤", "LOGS")
                self._reorder_settings_btn()
            elif not self.dev_mode and "LOGS" in self.section_frames:
                self._remove_section("LOGS")

            # ── EXPLORER section (dev) ────────────────────────────────
            if self.dev_mode and "EXPLORER" not in self.section_frames:
                frm = ctk.CTkFrame(self.content_area, fg_color="transparent")
                self.section_frames["EXPLORER"] = frm
                _etop = ctk.CTkFrame(frm, fg_color="transparent")
                _etop.pack(fill="x", padx=10, pady=(10, 0))
                ctk.CTkButton(_etop, text="PULL",    width=72, height=32, fg_color=C["blue"],     hover_color="#3a75d4", command=self.pull_explorer_save).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="CLOSE",   width=72, height=32, fg_color=C["nav_act"],  hover_color=C["nav_hvr"], command=self.clear_explorer_view).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="EXPAND",  width=72, height=32, fg_color="#6f42c1",     hover_color="#5a32a3", command=self.expand_explorer_tree).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="COLLAPSE",width=80, height=32, fg_color=C["nav_act"],  hover_color=C["nav_hvr"], command=self.collapse_explorer_tree).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="MULT",    width=65, height=32, fg_color="#138d75",     hover_color="#0e7a64", command=self.show_multipliers_popup).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="MINING",  width=70, height=32, fg_color="#c0392b",     hover_color="#a93226", command=self.show_mining_calculator_popup).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="COPY",    width=65, height=32, fg_color=C["green"],    hover_color="#2ea043", command=self.copy_explorer_text).pack(side="left", padx=(0, 4))
                ctk.CTkButton(_etop, text="DUMP",    width=65, height=32, fg_color=C["gold"],     hover_color="#c98b00", command=self.dump_explorer_text).pack(side="left")
                self.explorer_status_lbl = ctk.CTkLabel(_etop, text="Explorer: no save loaded",
                                                        font=("Segoe UI", 10), text_color=C["dim"])
                self.explorer_status_lbl.pack(side="right")
                _ebody = ctk.CTkFrame(frm, fg_color=C["card"], corner_radius=10)
                _ebody.pack(fill="both", expand=True, padx=10, pady=10)
                _tree_frame = tk.Frame(_ebody, bg=C["card"])
                _tree_frame.pack(fill="both", expand=True, padx=8, pady=8)
                self.explorer_tree_widget = ttk.Treeview(_tree_frame, columns=("value",), show="tree headings")
                self.explorer_tree_widget.heading("#0", text="Key")
                self.explorer_tree_widget.heading("value", text="Value")
                self.explorer_tree_widget.column("#0", width=300, stretch=True)
                self.explorer_tree_widget.column("value", width=420, stretch=True)
                yscroll = ttk.Scrollbar(_tree_frame, orient="vertical", command=self.explorer_tree_widget.yview)
                xscroll = ttk.Scrollbar(_tree_frame, orient="horizontal", command=self.explorer_tree_widget.xview)
                self.explorer_tree_widget.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
                self.explorer_tree_widget.grid(row=0, column=0, sticky="nsew")
                yscroll.grid(row=0, column=1, sticky="ns")
                xscroll.grid(row=1, column=0, sticky="ew")
                _tree_frame.grid_rowconfigure(0, weight=1)
                _tree_frame.grid_columnconfigure(0, weight=1)
                self.refresh_explorer_view()
                self._add_nav_btn("EXPLORER", "⌕", "EXPLORER")
                self._reorder_settings_btn()
            elif not self.dev_mode and "EXPLORER" in self.section_frames:
                self._remove_section("EXPLORER")
        except Exception:
            pass

    def unlock_dev_mode(self):
        if self.dev_mode:
            self.dev_mode = False
            if hasattr(self, 'disk_toggle') and self.disk_toggle and self.disk_toggle.winfo_exists():
                try:
                    self.disk_toggle.destroy()
                except:
                    pass
            self.refresh_tabs()
            return

        pop = ctk.CTkToplevel(self)
        pop.title("Unlock Dev Mode")
        self._set_popup_topmost(pop)
        self._place_popup_near_main(pop, width=300, height=150)
        pop.resizable(False, False)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ctk.CTkLabel(container, text="Enter 4-digit code:", font=("Segoe UI", 12)).pack(pady=(16, 8))
        code_entry = ctk.CTkEntry(container, width=100, justify="center", show="*")
        code_entry.pack(pady=(0, 12))

        def check_code():
            if code_entry.get().strip() == chr(49) + chr(57) + chr(57) + chr(49):
                ctk.CTkLabel(container, text="Dev Mode Unlocked!", font=("Segoe UI", 12, "bold"), text_color="#2ecc71").pack(pady=(8, 0))
                code_entry.pack_forget()
                btn.pack_forget()
                self.dev_mode = True
                self.refresh_tabs()
                C = self._C
                self.disk_toggle = ctk.CTkSwitch(self.settings_container, text="Show Disk Monitor",
                                                  command=self.toggle_disk_tab, text_color=C["txt"],
                                                  progress_color=C["blue"])
                self.disk_toggle.pack(anchor="w", pady=(8, 0))
                if self.config.get("show_disk_monitor"): self.disk_toggle.select()
            else:
                pop.destroy()

        btn = ctk.CTkButton(container, text="Unlock", command=check_code)
        btn.pack()

    def safe_ui(self, w, f, *a, **k):
        if not self.is_closing and w and w.winfo_exists():
            try: getattr(w, f)(*a, **k)
            except: pass

    def _is_topmost_enabled(self):
        return bool(self.config.get("always_on_top", True))

    def apply_topmost_setting(self):
        try:
            self.attributes("-topmost", self._is_topmost_enabled())
        except Exception:
            pass

    def _set_popup_topmost(self, window):
        try:
            window.transient(self)
        except Exception:
            pass
        try:
            window.attributes("-topmost", self._is_topmost_enabled())
        except Exception:
            pass

    def _place_popup_near_main(self, window, width=None, height=None, x_offset=24, y_offset=24):
        try:
            window.update_idletasks()
            w = int(width if width is not None else max(window.winfo_reqwidth(), 320))
            h = int(height if height is not None else max(window.winfo_reqheight(), 180))
            x = int(self.winfo_x() + x_offset)
            y = int(self.winfo_y() + y_offset)
            window.geometry(f"{w}x{h}+{x}+{y}")
        except Exception:
            pass

    def start_move(self, e):
        self.x, self.y = e.x, e.y

    def do_move(self, e):
        # Manual drag implies free positioning; disable sticky snapping immediately.
        if self.config.get("pos") != "Free Flow":
            self.config["pos"] = "Free Flow"
            if hasattr(self, "pos_menu"):
                self.pos_menu.set("Free Flow")
            self.save_config()
        self.geometry(f"+{self.winfo_x() + (e.x - self.x)}+{self.winfo_y() + (e.y - self.y)}")
    def on_closing(self): 
        self.is_closing = True
        self.config["x"], self.config["y"] = self.winfo_x(), self.winfo_y()
        self.save_session_cache()
        self.save_config()
        self.destroy()
    def toggle_minimize(self):
        if not self.is_minimized: self.geometry(f"{self.winfo_width()}x50"); self.min_btn.configure(text="+"); self.is_minimized = True
        else: self.geometry("760x720"); self.min_btn.configure(text="−"); self.is_minimized = False
    def toggle_settings(self):
        if self.settings_frame.winfo_ismapped(): self.settings_frame.place_forget(); self.save_config()
        else: self.settings_frame.place(relx=0.5, rely=0.5, anchor="center", relwidth=0.8, relheight=0.8)

    def show_help(self):
        pop = ctk.CTkToplevel(self)
        pop.title("Rocky Idle Reader Help")
        self._set_popup_topmost(pop)
        self._place_popup_near_main(pop, width=620, height=560)
        pop.resizable(False, False)

        container = ctk.CTkFrame(pop, fg_color="#1c1c1c", corner_radius=14, border_width=1, border_color="#2f2f2f")
        container.pack(fill="both", expand=True, padx=12, pady=12)

        ctk.CTkLabel(container, text="Rocky Idle Reader", font=("Segoe UI", 17, "bold"), text_color="#ffffff").pack(pady=(14, 2))
        ctk.CTkLabel(container, text="How This App Works", font=("Segoe UI", 12, "bold"), text_color="#8ab4f8").pack(pady=(0, 10))

        body = ctk.CTkScrollableFrame(container, fg_color="#141922", corner_radius=10, border_width=1, border_color="#2f3a4a")
        body.pack(fill="both", expand=True, padx=12, pady=(0, 12))

        sections = [
            (
                "Live Sync",
                "The app scans your Rocky Idle save folder, decodes the newest save, and only processes data for your selected profile."
            ),
            (
                "Overview",
                "Shows total level, total XP, session XP, Slayer task status, and Account Completion. Account Completion blends progress across quests, achievements, chests, collection logs, and maxed checks."
            ),
            (
                "Skills and Items",
                "Skills track XP gains, hourly rates, and TTL. Items track only changing item IDs for faster lists and cleaner hidden-item management."
            ),
            (
                "Discord Alerts",
                "You can enable level, Slayer, XP activity, and no-task alerts. XP alerts include only skills that changed on that scan and respect your selected minute interval."
            ),
            (
                "Logs and Recovery",
                "Every scan writes change markers to logs. If a bad save is detected, the app attempts automatic recovery using the latest valid save for your profile."
            ),
            (
                "Quick Tips",
                "Right-click any Skills or Items row to open a popout. Use Settings to test your Discord webhook and switch profiles without restarting."
            ),
        ]

        for title, text in sections:
            card = ctk.CTkFrame(body, fg_color="#1b2230", corner_radius=10, border_width=1, border_color="#2e384d")
            card.pack(fill="x", padx=8, pady=6)
            ctk.CTkLabel(card, text=title, font=("Segoe UI", 11, "bold"), text_color="#e6edf3").pack(anchor="w", padx=12, pady=(10, 2))
            desc_lbl = ctk.CTkLabel(card, text=text, font=("Segoe UI", 10), text_color="#b9c4d0", justify="left", anchor="w")
            desc_lbl.pack(fill="x", padx=12, pady=(0, 10))
            card.bind("<Configure>", lambda e, lbl=desc_lbl: lbl.configure(wraplength=max(220, e.width - 24)))

        footer = ctk.CTkFrame(container, fg_color="transparent")
        footer.pack(fill="x", padx=12, pady=(0, 10))
        ctk.CTkLabel(footer, text="© 2026 Rocky Idle Reader", font=("Segoe UI", 9), text_color="#5d6d7e").pack(side="left")
        ctk.CTkButton(footer, text="Close", width=120, height=34, fg_color="#3b8ed0", hover_color="#397acb", command=pop.destroy).pack(side="right")

if __name__ == "__main__":
    # Hide console window on Windows
    try:
        ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(), 0)
    except:
        pass
    RIR_by_Foot().mainloop()