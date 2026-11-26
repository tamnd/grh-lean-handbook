#!/usr/bin/env python3
"""Rebuild the generated sections of Volume 0, chapter "Glossary and index of Lean names" (spec 07.3, 10.4).

    python3 scripts/lean_index.py [--source ../grh-lean] [--check]

The script reads every written chapter of content/NN-*/<id>/, collects the names on its `Lean:` lines and in the
`decls:` of its sections, finds the file and the line of each name at the pin of EDITION, and writes three
sections of content/00-guide/lean-index/:

    02-the-status-of-the-chapters.md   the status and the words of each chapter of the plan
    03-names-of-the-data.md            the names in the namespace New.Data
    04-other-names-a-to-l.md           the names outside New, and New.A... to New.L... outside New.Data
    05-other-names-m-to-z.md           the other names of New outside New.Data

The glossary (01-glossary.md) and the notes (06-notes-and-references.md) are written by hand, and the script does
not touch them. With --check, the script writes nothing and exits with 1 if a section is out of date. Run it from
the root of the handbook, at each release, after the chapters of the release are merged.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from ghb.__main__ import edition  # noqa: E402
from ghb.content import load_volumes  # noqa: E402
from ghb.md import LEAN_LINE, lean_names  # noqa: E402
from ghb.source import Source  # noqa: E402

CHAPTER = "lean-index"
FOLDER = os.path.join(ROOT, "content", "00-guide", CHAPTER)
FENCE = re.compile(r"^(`{3,}|~{3,})")


def front(title: str) -> str:
    return (f"---\ntitle: {title}\nlean: []\ndecls: []\nstatus: drafted\n"
            "drafted_by: writer@claude-opus-5-5\ngenerated_by: scripts/lean_index.py\n---\n")


def citations(volumes) -> dict[str, dict]:
    """Each cited name → its edition and the chapters (volume, number, id) that cite it."""
    out: dict[str, dict] = {}

    def add(name: str, ed: str, key: tuple[int, int, str]):
        row = out.setdefault(name, {"edition": ed, "chapters": set()})
        if ed != "grh":
            row["edition"] = ed
        row["chapters"].add(key)

    for v in volumes:
        for c in v.chapters:
            if c.id == CHAPTER:
                continue
            key = (v.number, c.num, c.id)
            for s in c.sections:
                for d in s.fm.get("decls") or []:
                    add(str(d), "grh", key)
                fence = False
                for ln in s.body.split("\n"):
                    if FENCE.match(ln):
                        fence = not fence
                        continue
                    m = None if fence else LEAN_LINE.match(ln)
                    if m:
                        for name, ed in lean_names(m.group(1)):
                            add(name, ed, key)
    return out


def entry(name: str, row: dict, src: Source) -> str:
    ed = row["edition"]
    if ed == "Mathlib":
        where = "a name of Mathlib"
    else:
        e = src.compact if ed == "grh-compact" else src.grh
        d = e.decls.get(name)
        if d is None:
            where = f"not a declaration of {e.name} at the pin"
        elif ed == "grh-compact":
            where = f"`grh-compact/src/{d.file}`, line {d.line} (grh-compact)"
        else:
            where = f"`{d.file}`, [line {d.line}](lean:{d.file}#L{d.line})"
    cites = ", ".join(f"[Chapter](/chapter/{cid}/)" for _v, _n, cid in sorted(row["chapters"]))
    return f"- `{name}`: {where}. Cited in {cites}."


def status_section(volumes) -> str:
    out = [front("The status of the chapters"), "## The status of the chapters", "",
           "This table gives each chapter of the plan with its status and its words, as `wc -w` counts the text "
           "of its sections. A chapter with the status planned has no text yet. The status drafted means that a "
           "model wrote the chapter and that the check of the build passes. The status checked needs a named "
           "person who compared each statement with its Lean type, and the status reviewed needs a named person "
           "who works in the field. This chapter is not in the table, because the script that writes the table "
           "also writes this chapter.", "",
           "| Vol. | Ch. | Title | Status | Words |", "|---|---|---|---|---|"]
    for v in volumes:
        for c in v.chapters:
            if c.id == CHAPTER:
                continue
            title = c.title.replace("|", "\\|")
            out.append(f"| {v.number} | {c.num} | {title} | {c.status} | {c.words:,} |")
    return "\n".join(out) + "\n"


def names_section(title: str, intro: str, names: list[str], cit: dict, src: Source) -> str:
    out = [front(title), f"## {title}", "", intro, ""]
    out += [entry(n, cit[n], src) for n in names]
    return "\n".join(out) + "\n"


def build(src: Source, pin: str) -> dict[str, str]:
    volumes = load_volumes(os.path.join(ROOT, "content"))
    cit = citations(volumes)
    names = sorted(cit, key=lambda n: (n.lower(), n))
    data = [n for n in names if n.startswith("New.Data.")]
    rest = [n for n in names if not n.startswith("New.Data.")]
    first = [n for n in rest if not n.startswith("New.") or "a" <= n[4:5].lower() <= "l"]
    second = [n for n in rest if n not in first]
    n_ch = len({k for r in cit.values() for k in r["chapters"]})
    head = (f"The lines are those of the readable edition `grh/src` at the commit `{pin[:12]}`. A link on a line "
            "number opens the file at that line on GitHub. ")
    return {
        "02-the-status-of-the-chapters.md": status_section(volumes),
        "03-names-of-the-data.md": names_section(
            "Names of the data",
            f"The index lists {len(names)} Lean names that the {n_ch} written chapters cite, on a `Lean:` line or "
            "in the list of declarations of a section. For each name it gives the file and the line of the "
            "declaration, and the chapters that cite it. " + head + "This section has the "
            f"{len(data)} names in the namespace `New.Data`, the namespace of the admissible data. The next "
            "section has the other names.", data, cit, src),
        "04-other-names-a-to-l.md": names_section(
            "Other names, A to L",
            f"This section and the next have the {len(rest)} cited names outside the namespace `New.Data`. This "
            f"section has {len(first)} of them: the names outside the namespace `New`, which are the statements "
            "of the source and the names of Mathlib that the chapters cite, and the names `New.X` with `X` from "
            "A to L. " + head + "A name of Mathlib has no file of the source.", first, cit, src),
        "05-other-names-m-to-z.md": names_section(
            "Other names, M to Z",
            f"This section has the {len(second)} cited names `New.X` outside the namespace `New.Data` with `X` "
            "from M to Z, and the names whose first letter after `New.` is not a Latin letter. " + head,
            second, cit, src),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--source", default=os.path.join(ROOT, "..", "grh-lean"))
    ap.add_argument("--check", action="store_true", help="exit 1 if a section is out of date; write nothing")
    args = ap.parse_args(argv)
    pin = edition().get("grh", "")
    src = Source(os.path.abspath(args.source), pin)
    if not src.present:
        print(f"no source at {args.source}", file=sys.stderr)
        return 1
    if src.commit and pin and src.commit != pin:
        print(f"the clone is at {src.commit[:12]}, the pin is {pin[:12]}", file=sys.stderr)
        return 1
    stale = 0
    for name, text in build(src, pin).items():
        p = os.path.join(FOLDER, name)
        old = open(p, encoding="utf-8").read() if os.path.exists(p) else ""
        if old == text:
            continue
        stale += 1
        if args.check:
            print(f"out of date: {os.path.relpath(p, ROOT)}")
        else:
            os.makedirs(FOLDER, exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                f.write(text)
            print(f"wrote {os.path.relpath(p, ROOT)}")
    return 1 if (args.check and stale) else 0


if __name__ == "__main__":
    sys.exit(main())
