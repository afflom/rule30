"""The frontier register: the claims the research program is currently about,
with their status, Lean name and lexeme. `frontier.toml` is the machine-readable
counterpart of the prose in STRATEGY.md."""

from datetime import date
import tomllib

from . import repo

STATUSES = ("open", "proved", "refuted", "retired")


def load():
    if not repo.FRONTIER.exists():
        return {"claim": []}
    return tomllib.loads(repo.FRONTIER.read_text())


def _toml_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def save(data):
    lines = ["# The research frontier. Edit with `r30 frontier`; see STRATEGY.md for the prose.", ""]
    for c in data["claim"]:
        lines.append("[[claim]]")
        for key in ("id", "status", "statement", "lean", "lexeme", "since", "note"):
            if c.get(key):
                lines.append(f"{key} = {_toml_str(str(c[key]))}")
        lines.append("")
    repo.FRONTIER.write_text("\n".join(lines))


def list_claims(status=None):
    claims = load()["claim"]
    if status:
        claims = [c for c in claims if c["status"] == status]
    return claims


def add(id_, statement, status="open", lean=None, lexeme=None, note=None):
    if status not in STATUSES:
        raise ValueError(f"status must be one of {STATUSES}")
    data = load()
    if any(c["id"] == id_ for c in data["claim"]):
        raise ValueError(f"claim {id_} exists")
    data["claim"].append({k: v for k, v in dict(
        id=id_, status=status, statement=statement, lean=lean, lexeme=lexeme,
        since=date.today().isoformat(), note=note).items() if v})
    save(data)
    return data["claim"][-1]


def update(id_, **fields):
    data = load()
    for c in data["claim"]:
        if c["id"] == id_:
            for k, v in fields.items():
                if v is None:
                    continue
                if k == "status" and v not in STATUSES:
                    raise ValueError(f"status must be one of {STATUSES}")
                c[k] = v
            save(data)
            return c
    raise ValueError(f"no claim {id_}")


def summary():
    claims = load()["claim"]
    counts = {s: sum(1 for c in claims if c["status"] == s) for s in STATUSES}
    return {"counts": counts, "open": [c["id"] for c in claims if c["status"] == "open"]}
