import ast
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RIR = ROOT / "RIR.py"
DATA = ROOT / "app_data.json"

REQUIRED_SECTIONS = [
    "config",
    "skill_db",
    "monster_db",
    "item_db",
    "mining_db",
    "item_meta",
    "skill_tiers",
    "diary_boosters",
    "multipliers_snapshot",
    "session_cache",
]


def check_python_syntax() -> None:
    ast.parse(RIR.read_text(encoding="utf-8"))


def check_data_store() -> None:
    if not DATA.exists():
        raise FileNotFoundError("app_data.json not found")
    payload = json.loads(DATA.read_text(encoding="utf-8"))
    sections = payload.get("sections") if isinstance(payload, dict) else None
    if not isinstance(sections, dict):
        raise ValueError("app_data.json missing top-level 'sections' object")
    missing = [name for name in REQUIRED_SECTIONS if name not in sections]
    if missing:
        raise ValueError(f"Missing required sections: {', '.join(missing)}")


if __name__ == "__main__":
    check_python_syntax()
    check_data_store()
    print("SELF CHECK OK")
