#!/usr/bin/env python3
"""Fetch pinned research sources only; no build, search, or large truth tables."""
import hashlib
import json
from pathlib import Path
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / ".cache"
REV = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
PREPRINT = "preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026"


def get(url):
    req = urllib.request.Request(url, headers={"User-Agent": "sensitivity-research-source-audit"})
    with urllib.request.urlopen(req, timeout=40) as response:
        return response.read()


def main():
    records = []
    manifest = ROOT / "sources" / "manifest.json"
    expected = {item["path"]: item["sha256"] for item in
                (json.loads(manifest.read_text()) if manifest.exists() else [])}

    def save(repo, revision, path):
        url = f"https://raw.githubusercontent.com/{repo}/{revision}/{path}"
        out = CACHE / repo.replace("/", "_") / path
        data = out.read_bytes() if out.exists() else get(url)
        digest = hashlib.sha256(data).hexdigest()
        if path in expected and digest != expected[path]:
            raise ValueError(f"Pinned source hash mismatch: {path}")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(data)
        records.append({"repository": repo, "revision": revision, "path": path,
                        "url": url, "sha256": digest, "bytes": len(data)})

    for path in (ROOT / "sources" / "files.txt").read_text().splitlines():
        save("openai/math", REV, path)
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(records, indent=2) + "\n")
    print(f"Cached {len(records)} pinned files; manifest: {manifest}")


if __name__ == "__main__":
    main()
