"""Rust emission of the API module through `lexlean production` (SPEC §24.7).

The production roots are the executable definitions of `Api.lex.tex` that
`apimodel.PRODUCTION_ROOTS` declares (`commands`, `commandCount`) and those of
`Rule30Core.lex.tex` that `coremodel.PRODUCTION_ROOTS` declares (the rows,
the center, the right diagonals, the tower words, the ruler background and
the vectors of centers and ruler values), each with the effects and targets
of the closed registry `language/production-1.2.toml`.
From that table this module generates, and `bin/r30 api sync` writes:

- `rule30-api/production/request.json`, the `lexlean/production-request/1`
  document: one crate per root, the target ids with the descriptor digests
  pinned from `lexlean production targets`;
- `rule30-api/model/runtime-roots.toml` (`prismpm/runtime-roots/1`): the
  same roots as the register PrismPM keeps of what its runtime exports.

`bin/r30 api production` runs `lexlean lock`, then `production build` with
the request, replays the published bundle with `verify-artifact`, and reports
the bundle (content-addressed under `rule30-api/.lexlean/production/`, never
committed), each package with its certification and effects, and the number
of outputs that need an input-sized stack. The emitted crate of `commands`
compiles with cargo and its `run()` returns the command list; `engine_rust.py`
and `discover_rust.py` run the engine's roots, and they have no other runtime."""

import json

from . import repo

API = repo.ROOT / "rule30-api"
REQUEST = API / "production" / "request.json"
RUNTIME_ROOTS = API / "model" / "runtime-roots.toml"
MODULE = "Rule30Api.Api"

# The pinned compiler (`.local/bin/lexlean --version`) and its
# `lexlean production targets`: the request pins these digests, and `build`
# refuses another compiler's descriptor (LLC0203), so a toolchain change is
# visible here; the tests compare both with the binary when it is present.
LEXLEAN_VERSION = "0.4.0"
TARGET_DIGESTS = {
    "rust-core": "5b666826370127b074c82e5a9bf6ae77e0465d21e387900e957d8e3777869186",
    "rust-std": "0f5802ea18121b6a7a0d03e999589ce4e5ae812dc2a358432c1bf024a8e53f9f",
}
PACKAGE_VERSION = "0.1.0"
USED = set()  # the bundles whose certified roots this process ran (`engine.tick` reads it per stage)


def crate_name(definition, group=None):
    """`commandCount` -> `rule30_api_command_count` (the §17.16 package form);
    a group names the module's family: `rows` of the core -> `rule30_api_core_rows`."""
    snake = "".join("_" + c.lower() if c.isupper() else c for c in definition)
    return f"rule30_api_{group + '_' if group else ''}{snake}"


def roots():
    """The production roots, strictly ascending by name as the request requires."""
    from .apimodel import PRODUCTION_ROOTS
    from . import coremodel
    rows = [{"root": f"{MODULE}.{name}", "package": crate_name(name), "targets": sorted(spec["targets"]),
             "effects": sorted(spec["effects"])} for name, spec in PRODUCTION_ROOTS.items()]
    rows += [{"root": f"{coremodel.LEAN_MODULE}.{name}", "package": crate_name(name, "core"), "targets": sorted(spec["targets"]),
              "effects": sorted(spec["effects"])} for name, spec in coremodel.PRODUCTION_ROOTS.items()]
    from . import discoverymodel
    rows += [{"root": f"{discoverymodel.LEAN_MODULE}.{name}", "package": crate_name(name, "discovery"), "targets": sorted(spec["targets"]),
              "effects": sorted(spec["effects"])} for name, spec in discoverymodel.PRODUCTION_ROOTS.items()]
    from . import enginemodel
    rows += [{"root": f"{enginemodel.LEAN_MODULE}.{name}", "package": crate_name(name, "engine"), "targets": sorted(spec["targets"]),
              "effects": sorted(spec["effects"])} for name, spec in enginemodel.PRODUCTION_ROOTS.items()]
    rows += [{"root": f"{enginemodel.HYPOTHESES_MODULE}.{name}", "package": crate_name(name, "hypotheses"), "targets": sorted(spec["targets"]),
              "effects": sorted(spec["effects"])} for name, spec in enginemodel.HYPOTHESES_ROOTS.items()]
    return sorted(rows, key=lambda r: r["root"])


def request():
    return {
        "roots": [{"package": {"name": r["package"], "version": PACKAGE_VERSION}, "root": r["root"],
                   "targets": [{"digest": TARGET_DIGESTS[t], "id": t} for t in r["targets"]]} for r in roots()],
        "spec": "lexlean/production-request/1",
    }


def request_json():
    return json.dumps(request(), indent=2, sort_keys=True) + "\n"


def runtime_roots_toml():
    from . import coremodel
    from . import discoverymodel, enginemodel
    lines = ['spec = "prismpm/runtime-roots/1"',
             f'lean_modules = ["{MODULE}", "{coremodel.LEAN_MODULE}", "{discoverymodel.LEAN_MODULE}", "{enginemodel.LEAN_MODULE}", "{enginemodel.HYPOTHESES_MODULE}"]',
             'ir_module = "Rule30Api"', "roots = ["]
    lines += [f'  "{r["root"]}",' for r in roots()]
    lines += ["]", ""]
    for r in roots():
        lines += ["[[root]]", f'name = "{r["root"]}"', f'package = "{r["package"]}"',
                  "targets = [" + ", ".join(f'"{t}"' for t in r["targets"]) + "]",
                  "effects = [" + ", ".join(f'"{e}"' for e in r["effects"]) + "]", ""]
    return "\n".join(lines)


def files():
    return {REQUEST: request_json(), RUNTIME_ROOTS: runtime_roots_toml()}


def _lexlean(args, timeout):
    cmd = [repo.lexlean_bin(), "--project", str(API / "lexlean.toml"), *args, "--diagnostic-format", "json"]
    code, out, err = repo.run(cmd, cwd=API, timeout=timeout)
    try:
        data = json.loads(out.strip().splitlines()[-1]) if out.strip() else {}
    except json.JSONDecodeError:
        data = {}
    diags = []
    for d in data.get("diagnostics", []):
        where = d.get("primary") or {}
        diags.append(f"{d.get('code')} {where.get('path', '?')}:{where.get('line_start', '?')}: {d.get('message', '')[:400]}")
    if code != 0 and not diags:
        diags.append((err or out).strip()[-800:])
    return {"ok": code == 0 and data.get("success", code == 0), "diagnostics": diags, "data": data}


def targets(timeout=120):
    """The compiler's target descriptors (`lexlean production targets`)."""
    r = _lexlean(["production", "targets"], timeout)
    doc = r["data"] if r["data"].get("spec") == "lexlean/target-descriptors/1" else {}
    return {"ok": r["ok"] and bool(doc), "targets": {t["id"]: t["digest"] for t in doc.get("targets", [])},
            "diagnostics": r["diagnostics"]}


def summarize(result):
    """The compact report of a `lexlean/production-result/2` document."""
    outputs = []
    for root in result.get("roots", []):
        for o in root.get("outputs", []):
            outputs.append({"root": root["root"], "target": o["target"]["id"], "package": o["package"]["directory"],
                            "crate": o["crate"]["path"], "certification": o["certification"]["status"],
                            "axioms": o["certification"]["axioms"], "effects": o["effects"],
                            "optimality": root.get("optimality", {}).get("status")})
    return {"result_id": result.get("result_id"), "compiler": result.get("compiler", {}),
            "semantic_id": result.get("source", {}).get("semantic_id"), "outputs": outputs,
            "needs_stack": sum(1 for o in outputs if "recursion" in o["effects"])}


def build(timeout=3600, replay=True):
    """Lock, export, and (by default) replay the bundle. The report is `ok`
    only when every stage is, and names the stage that was not."""
    lock = repo.run([repo.lexlean_bin(), "--project", str(API / "lexlean.toml"), "lock"], cwd=API, timeout=600)
    if lock[0] != 0:
        return {"ok": False, "stage": "lock", "diagnostics": [(lock[2] or lock[1]).strip()[-800:]]}
    r = _lexlean(["production", "build", "--request", str(REQUEST.relative_to(API))], timeout)
    if not r["ok"]:
        return {"ok": False, "stage": "build", "diagnostics": r["diagnostics"]}
    bundles = r["data"].get("artifacts", [])
    if len(bundles) != 1:
        return {"ok": False, "stage": "build", "diagnostics": [f"expected one bundle, got {bundles}"]}
    bundle = API / bundles[0]
    report = {"ok": True, "stage": "build", "bundle": str(bundle.relative_to(repo.ROOT)),
              **summarize(json.loads((bundle / "result.json").read_text())), "diagnostics": []}
    if replay:
        v = _lexlean(["production", "verify-artifact", str(bundle)], 600)
        report["replay"] = "bindings-verified" if v["ok"] else "failed"
        if not v["ok"]:
            report.update(ok=False, stage="replay", diagnostics=v["diagnostics"])
    return report


def render(report):
    if not report["ok"]:
        return f"production {report['stage']} FAILED:\n  " + "\n  ".join(report["diagnostics"])
    lines = [f"bundle {report['bundle']} (result {report['result_id'][:12]}; "
             f"lexlean {report['compiler'].get('version')}, {report['compiler'].get('lean_toolchain')})"]
    for o in report["outputs"]:
        lines.append(f"  {o['root']} -> {o['package']} [{o['target']}]: {o['certification']}, "
                     f"effects {', '.join(o['effects']) or 'none'}, optimality {o['optimality']}")
    lines.append(f"outputs needing an input-sized stack: {report['needs_stack']}"
                 + (f"; replay {report['replay']}" if "replay" in report else ""))
    return "\n".join(lines)
