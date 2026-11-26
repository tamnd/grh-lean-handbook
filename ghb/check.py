"""The check of the content (spec 09.4).

A problem fails the check:

1. a `decls:` name or a `Lean:` name is not a declaration at the pin;
2. a `lean:` path is not a file at the pin;
3. a link /decl/, /chapter/ or lean: does not resolve;
4. a file has an em or en dash, or a line break inside a sentence (and the words of the banned list);
5. front matter is missing a field, or `status` is above `drafted` with no named person in `checked_by` or
   `reviewed_by`.

The check also tests the plans (volume.yaml). A warning does not fail the check: a pending link (to a chapter of
the plan that is not written, or to a name of the source with no statement yet), a `decls:` name with no `Lean:`
line in its section, and a statement with no `Lean:` line.
"""

from __future__ import annotations

import os
import re

from .content import STATUSES, Section, Volume
from .md import LEAN_LINE, STMT, lean_names, lean_paths, src_path

FIELDS = ("title", "lean", "decls", "status", "drafted_by")
BANNED = (r"\b(leverag(?:e|es|ed|ing)|showcas(?:e|es|ed|ing)|powerful|elegant(?:ly)?|seamless(?:ly)?|crucial(?:ly)?|"
          r"delv(?:e|es|ed|ing)|journey|landscape|tapestry|realm|intricate|pivotal|robust|underscores?|"
          r"notably|furthermore|moreover|it is worth noting)\b")
# a name that a model gives itself: "writer@model", "claude", "an agent"
_MODEL = re.compile(r"@|\b(claude|gpt|gemini|llama|model|agent|writer|bot|ai)\b", re.I)


def named_person(v) -> bool:
    vals = v if isinstance(v, list) else [v]
    return any(isinstance(x, str) and x.strip() and not _MODEL.search(x) for x in vals)


def _prose(text: str) -> str:
    """The prose of a file: no code, no mathematics, no link targets."""
    t = re.sub(r"```.*?```|~~~.*?~~~", " ", text, flags=re.S)
    t = re.sub(r"\$\$.*?\$\$|\$[^$\n]*\$|`[^`\n]*`", " ", t, flags=re.S)
    return re.sub(r"\]\([^)]*\)", "]", t)


_ITEM = re.compile(r"^\s*(?:[-*+]|[0-9]+[.)])\s+")
_END = re.compile(r"""[.?!:](?:[*_)\]"'’”`]|\$)*\s*$|\$\\square\$\s*$|\\square\$\s*$""")


def line_breaks(body: str, offset: int = 0) -> list[int]:
    """The lines of the body after which a sentence goes on to the next line. Two prose lines in a row are one
    paragraph; the first must end a sentence, and the second must not start with a small letter. Code, display
    mathematics, tables, headings, fenced divs and HTML comments are not prose."""
    lines = body.split("\n")
    kinds = []
    fence = None
    math = comment = False
    for ln in lines:
        s = ln.strip()
        f = re.match(r"^(`{3,}|~{3,})", s)
        if fence:
            kinds.append("x")
            if f and f.group(1)[0] == fence:
                fence = None
            continue
        if f:
            fence = f.group(1)[0]
            kinds.append("x")
            continue
        if math:
            kinds.append("x")
            if "$$" in s:
                math = False
            continue
        if comment:
            kinds.append("x")
            if "-->" in s:
                comment = False
            continue
        if s.startswith("$$"):
            kinds.append("x")
            if s == "$$" or s.count("$$") == 1:
                math = True
            continue
        if s.startswith("<!--"):
            kinds.append("x")
            comment = "-->" not in s
            continue
        if not s:
            kinds.append("")
        elif s.startswith(("#", "|", ":::", "\\begin", "\\end", "<")) or (ln.startswith("    ") and not kinds[-1:] == ["p"]):
            kinds.append("x")
        elif _ITEM.match(ln):
            kinds.append("i")
        else:
            kinds.append("p")
    out = []
    for i in range(len(lines) - 1):
        if kinds[i] not in ("p", "i") or kinds[i + 1] != "p":
            continue
        a, b = lines[i].rstrip(), lines[i + 1].strip()
        if not _END.search(a):
            out.append(i + 1 + offset)
        elif re.match(r"^[*_]*[a-z]", b) and not a.endswith(":"):
            out.append(i + 1 + offset)
    return out


def check_text(rel: str, text: str, body_start: int = 0) -> list[str]:
    """The style rules of 08.7 for one file."""
    probs = []
    for no, ln in enumerate(text.split("\n"), 1):
        if re.search("[–—]", ln):
            probs.append(f"{rel}:{no}: style: an en or em dash")
    for w in sorted({w.lower() for w in re.findall(BANNED, _prose(text), flags=re.I)}):
        probs.append(f"{rel}: style: '{w}'")
    body = "\n".join(text.split("\n")[body_start:])
    for no in line_breaks(body, body_start):
        probs.append(f"{rel}:{no}: style: a line break inside a sentence")
    return probs


def _body_start(text: str) -> int:
    """The line where the body starts, after the front matter."""
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end > 0:
            return text[:end + 5].count("\n")
    return 0


def check_section(rel: str, s: Section, source) -> tuple[list[str], list[str]]:
    probs, warns = [], []
    if s.error:
        return [f"{rel}: {s.error}"], []
    fm = s.fm
    for k in FIELDS:
        if k not in fm or fm[k] is None or fm[k] == "":
            probs.append(f"{rel}: front matter has no {k}")
    for k in ("lean", "decls"):
        if k in fm and fm[k] is not None and not isinstance(fm[k], list):
            probs.append(f"{rel}: front matter: {k} must be a list")
    st = fm.get("status")
    if st is not None and st not in STATUSES:
        probs.append(f"{rel}: status '{st}' is not one of {', '.join(STATUSES)}")
    if st in ("checked", "reviewed") and not named_person(fm.get("checked_by")):
        probs.append(f"{rel}: status is {st}, but checked_by names no person")
    if st == "reviewed" and not named_person(fm.get("reviewed_by")):
        probs.append(f"{rel}: status is reviewed, but reviewed_by names no person")
    if not re.match(r"\s*## ", s.body):
        probs.append(f"{rel}: a section must open with a ## heading")
    have = source is not None and source.present
    decls = [str(d) for d in (fm.get("decls") or []) if d] if isinstance(fm.get("decls"), list) else []
    for p in (fm.get("lean") or []) if isinstance(fm.get("lean"), list) else []:
        if have and not source.grh.has_file(src_path(str(p))):
            probs.append(f"{rel}: lean: {p} is not a file of grh/src at the pin")
    for d in decls:
        if have and d not in source.grh.decls:
            sug = source.grh.suggest(d)
            probs.append(f"{rel}: decls: {d} is not a declaration at the pin"
                         + (f" (did you mean {', '.join(sug)}?)" if sug else ""))
    # the Lean lines
    on_lines: set[str] = set()
    stmt_open = None
    fence = False
    body_lines = s.body.split("\n")
    for i, ln in enumerate(body_lines):
        if re.match(r"^(`{3,}|~{3,})", ln):
            fence = not fence
            continue
        if fence:
            continue
        sm = STMT.match(ln)
        if sm or ln.startswith("## "):
            if stmt_open:
                warns.append(f"{rel}: {stmt_open} has no Lean: line")
            stmt_open = None
            if sm and sm.group(1) not in ("Remark", "Example", "Conjecture"):
                stmt_open = sm.group(1) + (sm.group(3) or "")
            continue
        if re.match(r"^\*?Mathlib:\*? ", ln):   # the statement is a definition or theorem of Mathlib
            stmt_open = None
            continue
        lm = LEAN_LINE.match(ln)
        if not lm:
            continue
        stmt_open = None
        for name, ed in lean_names(lm.group(1)):
            on_lines.add(name)
            if not have or ed == "Mathlib":
                continue
            edition = source.compact if ed == "grh-compact" else source.grh
            if name not in edition.decls:
                sug = edition.suggest(name)
                probs.append(f"{rel}: Lean: {name} is not a declaration of {edition.name} at the pin"
                             + (f" (did you mean {', '.join(sug)}?)" if sug else
                                "; a name of Mathlib needs (Mathlib) after it"))
        for p in lean_paths(lm.group(1)):
            if have and not source.grh.has_file(src_path(p)):
                probs.append(f"{rel}: Lean: {p} is not a file of grh/src at the pin")
    if stmt_open:
        warns.append(f"{rel}: {stmt_open} has no Lean: line")
    for d in decls:
        if d not in on_lines:
            warns.append(f"{rel}: decls: {d} has no Lean: line in the section")
    # the lean: links in the text are tested by the build of the volume (cmd_check)
    return probs, warns


def check_plan(v: Volume, source, root: str) -> list[str]:
    probs = []
    rel = os.path.relpath(os.path.join(v.dir, "volume.yaml"), root)
    for k in ("number", "title", "summary", "words", "chapters"):
        val = v.plan.get(k)
        if val is None or val == "" or (k != "number" and not val):
            probs.append(f"{rel}: no {k}")
    if v.plan.get("number") is not None and int(v.plan["number"]) != int(os.path.basename(v.dir)[:2]):
        probs.append(f"{rel}: number {v.plan['number']} does not match the folder")
    have = source is not None and source.present
    for c in v.chapters:
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", c.id):
            probs.append(f"{rel}: chapter id '{c.id}' is not a slug")
        if have:
            for p in c.source:
                if not any(f == p + ".lean" or f.startswith(p) for f in source.grh.files):
                    probs.append(f"{rel}: chapter {c.id}: source {p} matches no file of grh/src")
    return probs


def check_ids(volumes: list[Volume], root: str) -> list[str]:
    seen: dict[str, str] = {}
    probs = []
    for v in volumes:
        for c in v.chapters:
            if c.id in seen:
                probs.append(f"content/{os.path.basename(v.dir)}/volume.yaml: chapter id '{c.id}' is also in "
                             f"{seen[c.id]}: ids must be unique in the book")
            seen.setdefault(c.id, f"content/{os.path.basename(v.dir)}")
    return probs


def run(book, volumes: list[Volume]) -> tuple[list[str], list[str]]:
    """The problems and the warnings of the chosen volumes, of the front pages and of the plans."""
    probs, warns = [], []
    root = book.root
    src = book.source if book.source.present else None
    probs += check_ids(book.volumes, root)
    files = []
    for name in ("title", "copyright", "edition"):
        p = os.path.join(book.content, "front", name + ".md")
        if os.path.exists(p):
            files.append(p)
        else:
            probs.append(f"content/front/{name}.md is missing")
    for v in volumes:
        probs += check_plan(v, src, root)
        for c in v.chapters:
            for s in c.sections:
                rel = os.path.relpath(s.path, root)
                text = open(s.path, encoding="utf-8").read()
                probs += check_text(rel, text, _body_start(text))
                p, w = check_section(rel, s, src)
                probs += p
                warns += w
    for f in files + [os.path.join(root, n) for n in ("README.md",)]:
        if os.path.exists(f):
            text = open(f, encoding="utf-8").read()
            probs += check_text(os.path.relpath(f, root), text, _body_start(text))
    return probs, warns
