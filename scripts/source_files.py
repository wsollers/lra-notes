"""Write SOURCE.md at the root of each book track from the lra-source-profiles manifest.

Each track root (`Author/Topic/`) has a SOURCE.md whose first lines name the
book's source record:

    source_id: SRC-000367

Everything below that header is regenerated from
`lra-source-profiles/data/source-manifest.csv`, so the local PDF path, the
Markdown extract, and the Google Drive folder stay in sync with the manifest.
A track whose book is not in the manifest keeps `source_id: none` and says so.

Usage:
    python scripts/source_files.py [--profiles PATH] [--set Author/Topic=SRC-000123 ...]

lra-source-profiles is resolved from --profiles, LRA_SOURCE_PROFILES_ROOT, or the
sibling ../lra-source-profiles.
"""
from __future__ import annotations

import argparse
import csv
import os
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
HEADER = re.compile(r"^source_id:\s*(\S+)", re.M)


def profiles_root(explicit: str | None) -> pathlib.Path:
    for c in (explicit, os.environ.get("LRA_SOURCE_PROFILES_ROOT"), str(REPO.parent / "lra-source-profiles")):
        if c and (pathlib.Path(c) / "data" / "source-manifest.csv").is_file():
            return pathlib.Path(c)
    sys.exit("source_files: lra-source-profiles is not present (set LRA_SOURCE_PROFILES_ROOT)")


def track_roots() -> list[pathlib.Path]:
    """`Author/Topic` directories: a topic folder holding Chapter/Section units."""
    roots = []
    for author in sorted(p for p in REPO.iterdir() if p.is_dir() and (REPO / f"{p.name}.lean").is_file()):
        for topic in sorted(p for p in author.iterdir() if p.is_dir()):
            if any(c.is_dir() and re.match(r"(Chapter|Section)\d+", c.name) for c in topic.iterdir()):
                roots.append(topic)
    return roots


def drive_folder(pdf: str) -> str:
    """The Drive tree `Readings/Sources/...` mirrors `D:\\Readings\\Sources\\...`."""
    m = re.match(r"^[A-Za-z]:\\Readings\\Sources\\(.+)\\[^\\]+$", pdf)
    return "Readings/Sources/" + m.group(1).replace("\\", "/") + "/" if m else ""


def render(track: str, sid: str, row: dict | None) -> str:
    lines = [f"source_id: {sid}", "", f"# Source — `{track}`", ""]
    if row is None:
        lines += [
            "This book is not yet in the `lra-source-profiles` manifest, so its location",
            "is not recorded. Add it there, set `source_id` above, and rerun",
            "`python scripts/source_files.py`.",
        ]
        return "\n".join(lines) + "\n"
    pdf = row["local_pdf_path"] or row["canonical_pdf_path"]
    title = row["canonical_title"].strip()
    by = row["author"].strip()
    ed = row["edition"].strip()
    lines += [
        "| | |",
        "| --- | --- |",
        f"| Title (manifest) | {title} |",
        f"| Author (manifest) | {by} |",
    ]
    if ed:
        lines.append(f"| Edition | {ed} |")
    lines += [
        f"| Source record | `{sid}` |",
        f"| Local PDF | `{pdf}` |",
        f"| Markdown extract | `{row['markdown_extract_path']}` |",
    ]
    folder = drive_folder(pdf)
    if folder:
        lines.append(f"| Google Drive folder | `{folder}` |")
    lines += [
        "",
        "Generated from `lra-source-profiles/data/source-manifest.csv` by",
        "`scripts/source_files.py`; fix the manifest, not this table. The PDF and",
        "extract are local references: read them, never commit or upload them.",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--profiles")
    ap.add_argument("--set", nargs="*", default=[], help="Author/Topic=SRC-000123 or Author/Topic=none")
    args = ap.parse_args()
    manifest = profiles_root(args.profiles) / "data" / "source-manifest.csv"
    rows = {r["source_id"]: r for r in csv.DictReader(manifest.open(encoding="utf-8"))}
    overrides = dict(s.split("=", 1) for s in args.set)

    missing_header = []
    for root in track_roots():
        track = root.relative_to(REPO).as_posix()
        f = root / "SOURCE.md"
        sid = overrides.get(track)
        if sid is None and f.exists():
            m = HEADER.search(f.read_text(encoding="utf-8"))
            sid = m.group(1) if m else None
        if sid is None:
            missing_header.append(track)
            continue
        row = rows.get(sid) if sid != "none" else None
        if sid != "none" and row is None:
            sys.exit(f"source_files: {track}: {sid} is not in the manifest")
        f.write_text(render(track, sid, row), encoding="utf-8", newline="\n")
    if missing_header:
        sys.exit("source_files: no source_id for " + ", ".join(missing_header) + " (use --set)")
    print(f"source_files: wrote SOURCE.md for {len(track_roots())} tracks")


if __name__ == "__main__":
    main()
