"""The ledger (spec 09.1, 09.2): the files of the source and the chapters that explain them.

    ghb ledger            print the coverage
    ghb ledger --write    write ledger/files.yaml, ledger/decls.yaml and ledger/coverage.md
    ghb ledger --diff A B the files and declarations of grh/src that changed from commit A to commit B, and the
                          changed names that a section lists in `decls:`

A file belongs to the chapter whose `source:` prefix in volume.yaml is the longest that matches its path. When two
chapters have the same prefix, the first is the chapter and the others are under `also`.
"""

from __future__ import annotations

import os
import subprocess

import yaml

from .source import edition_at


def _matches(path: str, prefix: str) -> bool:
    return path == prefix + ".lean" or path.startswith(prefix)


def chapter_of(book) -> dict[str, tuple[str | None, list[str]]]:
    """Each file of grh/src → (its chapter "NN/id", the other chapters with a prefix of the same length)."""
    prefixes = []
    for v in book.volumes:
        for c in v.chapters:
            for p in c.source:
                prefixes.append((p, f"{v.number:02d}/{c.id}"))
    out = {}
    for f in book.source.grh.files:
        best, tie = -1, []
        for p, ch in prefixes:
            if _matches(f, p):
                if len(p) > best:
                    best, tie = len(p), [ch]
                elif len(p) == best and ch not in tie:
                    tie.append(ch)
        out[f] = (tie[0], tie[1:]) if tie else (None, [])
    return out


def files_yaml(book) -> list[dict]:
    rows = []
    owner = chapter_of(book)
    for f, lf in sorted(book.source.grh.files.items()):
        ch, also = owner[f]
        row = {"path": f, "lines": lf.lines, "folder": os.path.dirname(f) or ".", "chapter": ch}
        if also:
            row["also"] = also
        rows.append(row)
    return rows


def decls_yaml(book) -> list[dict]:
    rows = []
    for v in book.volumes:
        for c in v.chapters:
            for s in c.sections:
                for d in s.fm.get("decls") or []:
                    d = str(d)
                    dc = book.source.grh.decls.get(d)
                    row = {"name": d, "chapter": f"{v.number:02d}/{c.id}",
                           "section": os.path.relpath(s.path, book.root)}
                    places = book.labels.by_decl.get(d)
                    if places:
                        row["number"] = f"{places[0].kind} {places[0].number}"
                    if dc:
                        row.update({"file": dc.file, "line": dc.line, "kind": dc.kind, "digest": dc.digest})
                    else:
                        row["missing"] = True
                    rows.append(row)
    return sorted(rows, key=lambda r: r["name"])


def coverage_md(book, files: list[dict]) -> str:
    lines_of = {r["path"]: r["lines"] for r in files}
    by_ch: dict[str, list[str]] = {}
    for r in files:
        if r["chapter"]:
            by_ch.setdefault(r["chapter"], []).append(r["path"])
    out = ["# Coverage", "",
           f"Made by `ghb ledger --write` from lsernau/grh-lean at `{book.pin[:12]}`. A file of grh/src belongs to the "
           "chapter whose source prefix in volume.yaml is the longest that matches it.", "",
           "| Vol. | Ch. | Chapter | Files | Lines | Sections | Words | Status |", "|---|---|---|---|---|---|---|---|"]
    tw = tf = tl = 0
    for v in book.volumes:
        for c in v.chapters:
            key = f"{v.number:02d}/{c.id}"
            fs = by_ch.get(key, [])
            ln = sum(lines_of[f] for f in fs)
            out.append(f"| {v.number} | {c.num} | {c.title} | {len(fs)} | {ln:,} | {len(c.sections)} | "
                       f"{c.words:,} | {c.status} |")
            tw += c.words
            tf += len(fs)
            tl += ln
    rest = [r for r in files if not r["chapter"]]
    out += ["", f"Files with a chapter: {tf} of {len(files)} ({tl:,} of {sum(lines_of.values()):,} lines). "
            f"Words written: {tw:,} of about {sum(v.words for v in book.volumes):,}.", ""]
    if rest:
        out += ["## Files with no chapter", ""]
        folders: dict[str, list[int]] = {}
        for r in rest:
            folders.setdefault(r["folder"], []).append(r["lines"])
        out += ["| Folder | Files | Lines |", "|---|---|---|"]
        for f, ls in sorted(folders.items()):
            out.append(f"| {f} | {len(ls)} | {sum(ls):,} |")
        out.append("")
    return "\n".join(out)


def diff(book, a: str, b: str) -> int:
    root = book.source.root
    r = subprocess.run(["git", "-C", root, "diff", "--name-status", a, b, "--", "grh/src"],
                       capture_output=True, text=True)
    if r.returncode:
        print(r.stderr.strip())
        return 1
    changed = [ln.split("\t") for ln in r.stdout.splitlines() if ln.strip()]
    print(f"{len(changed)} files of grh/src changed from {a[:12]} to {b[:12]}")
    for row in changed:
        print("  " + " ".join(row))
    if not changed:
        return 0
    ea, eb = edition_at(root, a), edition_at(root, b)
    gone = sorted(set(ea.decls) - set(eb.decls))
    new = sorted(set(eb.decls) - set(ea.decls))
    moved = sorted(n for n in set(ea.decls) & set(eb.decls) if ea.decls[n].digest != eb.decls[n].digest)
    print(f"declarations: {len(gone)} removed, {len(new)} added, {len(moved)} changed")
    listed = {}
    for v in book.volumes:
        for c in v.chapters:
            for s in c.sections:
                for d in s.fm.get("decls") or []:
                    listed.setdefault(str(d), os.path.relpath(s.path, book.root))
    hit = [(n, "removed") for n in gone if n in listed] + [(n, "changed") for n in moved if n in listed]
    for n, how in sorted(hit):
        print(f"  check: {n} ({how}), in {listed[n]}")
    if not hit:
        print("no name in decls: changed")
    return 0


def run(book, args) -> int:
    if not book.source.present:
        print(f"no source at {book.source.root}")
        return 1
    if args.diff:
        return diff(book, args.diff[0], args.diff[1])
    files = files_yaml(book)
    cov = coverage_md(book, files)
    if args.write:
        d = os.path.join(book.root, "ledger")
        os.makedirs(d, exist_ok=True)
        head = f"# Made by `ghb ledger --write` from lsernau/grh-lean at {book.pin}. Do not edit by hand.\n"
        with open(os.path.join(d, "files.yaml"), "w", encoding="utf-8") as f:
            f.write(head + yaml.safe_dump(files, sort_keys=False, allow_unicode=True, width=120))
        with open(os.path.join(d, "decls.yaml"), "w", encoding="utf-8") as f:
            f.write(head + yaml.safe_dump(decls_yaml(book), sort_keys=False, allow_unicode=True, width=120))
        with open(os.path.join(d, "coverage.md"), "w", encoding="utf-8") as f:
            f.write(cov)
        print(f"wrote ledger/files.yaml ({len(files)} files), ledger/decls.yaml and ledger/coverage.md")
    else:
        print(cov)
    return 0
