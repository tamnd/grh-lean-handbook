"""ghb: build The GRH Lean Handbook from content/ and the pinned clone of lsernau/grh-lean.

    python3 -m ghb [--source ../grh-lean] survey
    python3 -m ghb [--source ../grh-lean] check  [--volume N|N,M|all]
    python3 -m ghb [--source ../grh-lean] build  [--volume N|N,M|all|front] [--formats tex,pdf,epub] [--out DIR]
    python3 -m ghb [--source ../grh-lean] ledger [--write] [--diff A B]
    python3 -m ghb join --in DIR [--out FILE]

The source is a clone of lsernau/grh-lean. The pin is the line "grh <commit>" of EDITION. The builder reads the
source as text and does not build Lean.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import shutil
import sys
import time

from .book import Book
from .source import Source

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NAME = "grh-lean-handbook"


def edition() -> dict:
    """The file EDITION: 'version 0.1.0' and 'grh <commit>'."""
    out = {"version": "0.1.0", "grh": ""}
    p = os.path.join(ROOT, "EDITION")
    if os.path.exists(p):
        for line in open(p):
            k, _, v = line.strip().partition(" ")
            if k:
                out[k] = v.strip()
    return out


def load(args) -> Book:
    t = time.time()
    pin = edition().get("grh", "")
    src = Source(os.path.abspath(args.source), pin)
    book = Book(os.path.join(ROOT, "content"), src, pin or src.commit or "main")
    w = src.warning()
    if w:
        print(f"warning: {w}", file=sys.stderr)
    print(f"grh-lean {src.commit[:12] or 'absent'}: {len(src.grh.files)} files and {len(src.grh.decls):,} names in "
          f"grh, {len(src.compact.decls):,} in grh-compact; {len(book.volumes)} volumes in the plan, "
          f"{len(book.built)} with text; loaded in {time.time() - t:.1f}s", file=sys.stderr)
    return book


def pick(book: Book, which: str):
    if which == "all":
        return list(book.volumes)
    nums = {int(x) for x in which.split(",") if x.strip().isdigit()}
    return [v for v in book.volumes if v.number in nums]


def cmd_survey(args):
    book = load(args)
    from .ledger import chapter_of
    owner = chapter_of(book) if book.source.present else {}
    lines = {f: lf.lines for f, lf in book.source.grh.files.items()}
    print(f"{'vol':>3}  {'title':<62} {'chapters':>8} {'written':>7} {'words':>8} {'target':>8} "
          f"{'files':>5} {'lines':>8}")
    for v in book.volumes:
        fs = [f for f, (ch, _) in owner.items() if ch and ch.startswith(f"{v.number:02d}/")]
        print(f"{v.number:>3}  {v.title[:62]:<62} {len(v.chapters):>8} {len(v.written):>7} "
              f"{sum(c.words for c in v.chapters):>8,} {v.words:>8,} {len(fs):>5} {sum(lines[f] for f in fs):>8,}")
    rest = [f for f, (ch, _) in owner.items() if not ch]
    print(f"files of grh/src with no chapter: {len(rest)} ({sum(lines[f] for f in rest):,} lines)")


def cmd_check(args):
    from . import check
    book = load(args)
    vols = pick(book, args.volume)
    probs, warns = check.run(book, vols)
    for v in vols:
        if v not in book.built:
            continue
        md, st = book.markdown(v)
        said = "\n".join(probs)
        for u in st["unresolved"]:
            if u.startswith("lean:") and f" {u[5:].split('#')[0]} is not a file" in said:
                continue
            probs.append(f"volume {v.number}: the link {u} does not resolve")
        for u in st["pending"]:
            warns.append(f"volume {v.number}: the link {u} is pending (not written yet)")
    for name in ("title", "copyright", "edition"):
        conv = book.converter(-1)
        fm, body = book.front.get(name, ({}, ""))
        conv.page(body, shift=0, prefix=f"front-{name}")
        probs += [f"content/front/{name}.md: the link {u} does not resolve" for u in conv.unresolved]
    if not book.source.present:
        probs.append(f"no source at {book.source.root}: the names and paths were not checked (use --source PATH)")
    for w in warns:
        print(f"warning: {w}")
    for p in probs:
        print(p)
    written = sum(len(v.written) for v in vols)
    print(f"{len(probs)} problems, {len(warns)} warnings in {len(vols)} volumes ({written} written chapters)",
          file=sys.stderr)
    return 1 if probs else 0


def cmd_build(args):
    from . import epub, latex
    book = load(args)
    ed = edition()
    version = ed["version"]
    date = args.date or datetime.date.today().isoformat()
    fmts = set(args.formats.split(","))
    os.makedirs(args.out, exist_ok=True)
    report = {}
    jobs = []
    if args.volume in ("front", "all"):
        jobs.append(("front", None))
    if args.volume != "front":
        for v in pick(book, args.volume):
            if v in book.built:
                jobs.append((f"{v.number:02d}-{v.id}", v))
            else:
                print(f"volume {v.number} {v.title}: no written chapter, skipped", file=sys.stderr)
    for key, v in jobs:
        d = os.path.join(args.out, key)
        os.makedirs(d, exist_ok=True)
        if v is None:
            md, st = "", {"words": 0, "unresolved": [], "pending": []}
        else:
            md, st = book.markdown(v)
        info = {"words": st["words"], "unresolved": len(st["unresolved"]), "pending": len(st["pending"])}
        if fmts & {"tex", "pdf"}:
            info.update(latex.build(book, v, md, d, version, date, pdf="pdf" in fmts))
        if "epub" in fmts:
            e = epub.build(book, v, md, d, version, date)
            if "error" in e:
                e["epub_error"] = e.pop("error")
            info.update(e)
        name = f"{NAME}-{key}-{version}"
        for ext in ("pdf", "epub"):
            src = os.path.join(d, f"main.{ext}")
            if ext in fmts and os.path.exists(src):
                dst = os.path.join(args.out, f"{name}.{ext}")
                os.replace(src, dst) if args.move else shutil.copy(src, dst)
                info[ext] = dst
        report[key] = info
        errs = [info.pop(k) for k in ("error", "epub_error") if k in info]
        over = info.get("overfull") or []
        info["overfull"] = len(over)
        print(f"volume {key}: " + json.dumps(info), file=sys.stderr)
        for o in over:
            print(f"  overfull box: {o}", file=sys.stderr)
        for err in errs:
            print(err, file=sys.stderr)
    json.dump(report, open(os.path.join(args.out, "report.json"), "w"), indent=1)
    bad = [k for k, i in report.items() if i.get("ok") is False or i.get("epub_ok") is False]
    return 1 if bad else 0


def cmd_ledger(args):
    from . import ledger
    return ledger.run(load(args), args)


def cmd_join(args):
    from . import join
    version = edition()["version"]
    out = args.out or os.path.join(args.inp, f"{NAME}-{version}.pdf")
    info = join.join(args.inp, out, version, os.path.join(ROOT, "content"))
    print(f"{out}: " + json.dumps(info), file=sys.stderr)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(prog="ghb", description="Build The GRH Lean Handbook.")
    ap.add_argument("--source", default=os.path.join(ROOT, "..", "grh-lean"),
                    help="a clone of lsernau/grh-lean at the pin of EDITION (default ../grh-lean)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("survey", help="the volumes, their words and their source files")
    c = sub.add_parser("check", help="the check of spec 09.4")
    c.add_argument("--volume", default="all")
    b = sub.add_parser("build", help="PDF and EPUB of the volumes")
    b.add_argument("--volume", default="all", help="N, N,M, all, or front")
    b.add_argument("--formats", default="pdf,epub")
    b.add_argument("--out", default=os.path.join(ROOT, "build"))
    b.add_argument("--date", default="")
    b.add_argument("--move", action="store_true")
    lg = sub.add_parser("ledger", help="ledger/files.yaml, decls.yaml and coverage.md")
    lg.add_argument("--write", action="store_true")
    lg.add_argument("--diff", nargs=2, metavar=("A", "B"))
    j = sub.add_parser("join", help="the PDF of all volumes, from the volume PDFs of the version in EDITION")
    j.add_argument("--in", dest="inp", required=True, help="the folder of the volume PDFs")
    j.add_argument("--out", default="", help="default DIR/grh-lean-handbook-<version>.pdf")
    args = ap.parse_args(argv)
    return {"survey": cmd_survey, "check": cmd_check, "build": cmd_build, "ledger": cmd_ledger,
            "join": cmd_join}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main() or 0)
