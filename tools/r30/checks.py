"""LexLean check (seconds), verify (minutes) and lock, with compact results."""

import json

from . import repo


def _lexlean(project, args, timeout):
    root = repo.PROJECTS[project]
    cmd = [repo.lexlean_bin(), "--project", str(root / "lexlean.toml"), *args,
           "--diagnostic-format", "json"]
    code, out, err = repo.run(cmd, cwd=root, timeout=timeout)
    try:
        data = json.loads(out.strip().splitlines()[-1]) if out.strip() else {}
    except json.JSONDecodeError:
        data = {}
    diags = []
    for d in data.get("diagnostics", []):
        where = d.get("primary") or {}
        loc = f"{where.get('path', '?')}:{where.get('line_start', '?')}"
        notes = "; ".join(n.get("message", "")[:200] for n in d.get("notes", [])[:2])
        diags.append(f"{d.get('code')} {loc}: {d.get('message', '')[:400]}" + (f" [{notes}]" if notes else ""))
    if code != 0 and not diags:
        diags.append((err or out).strip()[-800:])
    return {"ok": code == 0 and data.get("success", code == 0), "project": project,
            "diagnostics": diags, "attestation": data.get("attestation_id")}


def lock(project):
    root = repo.PROJECTS[project]
    code, out, err = repo.run([repo.lexlean_bin(), "--project", str(root / "lexlean.toml"), "lock"],
                              cwd=root, timeout=600)
    return {"ok": code == 0, "project": project, "output": (out + err).strip()[-300:]}


def check(project="paper", modules=None):
    args = ["check", *(modules or ["--all"])]
    return _lexlean(project, args, timeout=900)


def verify(project="paper", modules=None):
    """Verify the whole project (the commit gate's view) or a module selection
    (seconds; the inner loop)."""
    lock(project)
    return _lexlean(project, ["verify", *(modules or [])], timeout=3600)


def check_all():
    return [check(p) for p in repo.PROJECTS]
