#!/usr/bin/env python3
"""Publish PDFs from the acceptance gate and check their source provenance."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from datetime import datetime, timezone


DOCUMENTS = {
    "Core": ("Rule30-Core.pdf", "rule30-lexlean/Core.pdf", "rule30-lexlean/pdf/Core.pdf"),
    "Paper": ("Rule30-Paper.pdf", "rule30-paper/Paper.pdf", "rule30-paper/pdf/Paper.pdf"),
    "Observations": ("Rule30-Observations.pdf", "rule30-paper/Observations.pdf",
                     "rule30-paper/pdf/Observations.pdf"),
}
MANIFEST = "pdf-manifest.json"
TEX_PATHS = {name: str(Path(paths[-1]).with_suffix(".tex"))
             for name, paths in DOCUMENTS.items()}
GENERATED = (*[p for paths in DOCUMENTS.values() for p in paths],
             *TEX_PATHS.values(), MANIFEST)


def source_digest(root, tree):
    """Hash every captured Git input except the outputs we generate ourselves."""
    entries = subprocess.check_output(
        ["git", "ls-tree", "-rz", "--full-tree", tree], cwd=root).split(b"\0")
    digest = hashlib.sha256()
    for entry in entries:
        if entry and entry.split(b"\t", 1)[1].decode() not in GENERATED:
            digest.update(entry + b"\0")
    return digest.hexdigest()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sync(root, refresh=False):
    expected_source = os.environ.get("RULE30_SOURCE_DIGEST")
    if not expected_source:
        tree = subprocess.check_output(["git", "write-tree"], cwd=root, text=True).strip()
        expected_source = source_digest(root, tree)
    if refresh:
        manifest = {"source_digest": expected_source,
                    "generated_at_utc": datetime.now(timezone.utc).isoformat(), "documents": {}}
        for name, paths in DOCUMENTS.items():
            pdf, tex = root / "dist" / (name + ".pdf"), root / "dist" / (name + ".tex")
            if not pdf.read_bytes().startswith(b"%PDF-"):
                raise ValueError(f"Invalid generated PDF: {pdf}")
            for relative in (*paths, TEX_PATHS[name]):
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(tex if relative.endswith(".tex") else pdf, target)
            manifest["documents"][name] = {"pdf_sha256": sha256(pdf), "tex_sha256": sha256(tex)}
        (root / MANIFEST).write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    manifest = json.loads((root / MANIFEST).read_text())
    if manifest["source_digest"] != expected_source:
        raise ValueError("Tracked PDFs belong to different sources; commit with the installed hooks")
    for name, paths in DOCUMENTS.items():
        record = manifest["documents"][name]
        if record["tex_sha256"] != sha256(root / "dist" / (name + ".tex")):
            raise ValueError(f"{name}: tracked PDF does not match the verified TeX")
        for relative in (*paths, TEX_PATHS[name]):
            key = "tex_sha256" if relative.endswith(".tex") else "pdf_sha256"
            if sha256(root / relative) != record[key]:
                raise ValueError(f"Stale or modified generated artifact: {relative}")
    print("Tracked PDFs and TeX mirrors match the verified sources.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true")
    args = parser.parse_args()
    sync(Path(__file__).resolve().parents[1], args.refresh)
