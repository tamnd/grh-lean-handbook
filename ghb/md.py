"""The conversion of the Markdown of the sections into the Markdown of a volume.

The sections write three kinds of link (spec 08.6):

- `[Theorem](/decl/<Lean name>/)`: the statement whose `Lean:` line has the name. If the text is only a kind
  word (Theorem, Lemma, ...), the build gives the number: "Theorem 4.2.3", or "Theorem 4.2.3 of Volume 9".
- `[text](/chapter/<id>/)` and `[text](/chapter/<id>/#<anchor>)`: a chapter, or a section of a chapter.
- `[text](lean:Path.lean#L40)`: a line of the source on GitHub, at the pinned commit.

A link to a target in the same volume stays in the book. A link to another volume goes to the section file on
GitHub, with the volume and the number after it. A link to a chapter of the plan that is not written yet, or to a
declaration of the source with no statement yet, is pending: its text stays, and the check gives a warning.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable

from .content import anchor

REPO = "https://github.com/tamnd/grh-lean-handbook"
LEAN = "https://github.com/lsernau/grh-lean/blob/{pin}/grh/src/{file}"
KIND_WORDS = ("Definition", "Theorem", "Proposition", "Lemma", "Corollary", "Example", "Remark", "Conjecture")


@dataclass
class Target:
    volume: int
    number: str      # "3", "3.4" or "3.4.2"
    label: str       # the identifier in the book
    web: str = ""    # the page of the target on GitHub, for a link from another volume
    written: bool = True


@dataclass
class Place:
    volume: int
    number: str
    label: str
    kind: str        # "Theorem", or "Chapter" for a name that a chapter covers with no statement of its own
    title: str
    web: str = ""


@dataclass
class Labels:
    """Every place a link can point to."""
    chapters: dict[str, Target] = field(default_factory=dict)            # chapter id → its target
    anchors: dict[tuple[str, str], Target] = field(default_factory=dict)  # (chapter id, anchor) → a section
    by_decl: dict[str, list[Place]] = field(default_factory=dict)         # Lean name → its statements


def label_id(*parts: str) -> str:
    return "-".join(p for p in parts if p).replace("_", "-")


_FENCE = re.compile(r"^(`{3,}|~{3,})")
_MATH = re.compile(r"\$\$.*?\$\$|(?<![\\$])\$[^$\n]+\$", re.S)
LINK = re.compile(r"(?<!!)\[((?:[^\[\]]|\[[^\]]*\])*)\]\(([^)\s]+)\)")
STMT = re.compile(r"^\*\*(Definition|Theorem|Proposition|Lemma|Corollary|Example|Remark|Conjecture)"
                  r"((?: [a-z]+)?)(?: [0-9]+(?:\.[0-9]+)*)?((?: \((?:[^()]|\([^()]*\))*\))?)\.\*\*")
LEAN_LINE = re.compile(r"^\*?Lean:\*? (.*)$")
_NUMBERED = re.compile(r"\b[0-9]+\.[0-9]+(?:\.[0-9]+)*(?: of Volume [0-9]+)?$")


def lean_names(line: str) -> list[tuple[str, str]]:
    """The names on a `Lean:` line, each with its edition: "grh", "grh-compact" or "Mathlib". A name followed by
    `(Mathlib)` is a name of Mathlib, and a name followed by `(grh-compact)` is a name of the compact edition."""
    out = []
    for m in re.finditer(r"`([^`]+)`(\s*\((?:in )?(Mathlib|grh-compact)\b[^)]*\))?", line):
        name = m.group(1).strip()
        if not re.fullmatch(r"[^\s()]+", name) or name.endswith(".lean"):
            continue   # an expression or a path, not a name
        out.append((name, m.group(3) or "grh"))
    return out


def lean_paths(line: str) -> list[str]:
    """The paths of source files on a `Lean:` line, as in `(New/Main.lean)` or `(New/Main.lean, Lib/X.lean)`."""
    out = []
    for m in re.finditer(r"([A-Za-z0-9_./-]+\.lean)\b", re.sub(r"`[^`]*`", " ", line)):
        out.append(m.group(1))
    return out


def src_path(p: str) -> str:
    """A path of the source relative to grh/src."""
    p = p.split("#", 1)[0].strip()
    for pre in ("grh/src/", "src/"):
        if p.startswith(pre):
            p = p[len(pre):]
    return p.lstrip("/")


class Converter:
    """Converts the Markdown of one chapter, or of the front pages, for one volume."""

    def __init__(self, labels: Labels, volume: int, pin: str, known: Callable[[str], bool] | None = None,
                 has_file: Callable[[str], bool] | None = None):
        self.labels = labels
        self.volume = volume
        self.pin = pin
        self.known = known          # is a name a declaration at the pin? None if there is no source
        self.has_file = has_file    # is a path a file at the pin?
        self.unresolved: list[str] = []
        self.pending: list[str] = []

    # -- links
    def _cite(self, t: Target | Place, text: str, kind_word: bool) -> str:
        num = t.number
        if t.volume == self.volume:
            if kind_word:
                return f"[{text} {num}](#{t.label})"
            if _NUMBERED.search(text):
                return f"[{text}](#{t.label})"
            return f"[{text}](#{t.label}) [{num}]{{.ref}}"
        url = t.web or REPO
        if kind_word:
            return f"[{text} {num} of Volume {t.volume}]({url})"
        return f"[{text}]({url}) [Vol. {t.volume}, {num}]{{.ref}}"

    def resolve(self, dest: str, text: str) -> str:
        if dest.startswith("lean:"):
            path, _, frag = dest[5:].partition("#")
            path = src_path(path)
            if self.has_file and not self.has_file(path):
                self.unresolved.append(dest)
            url = LEAN.format(pin=self.pin, file=path) + (f"#{frag}" if frag else "")
            return f"[{text}]({url})"
        if dest.startswith("/decl/"):
            name = dest[len("/decl/"):].strip("/")
            places = self.labels.by_decl.get(name)
            kind_word = text.strip().capitalize() in KIND_WORDS or text.strip() == "Chapter"
            if places:
                p = next((p for p in places if p.volume == self.volume), places[0])
                word = text.strip()
                if kind_word and p.kind == "Chapter":
                    word = "Chapter"
                return self._cite(p, word if kind_word else text, kind_word)
            if self.known is None or self.known(name):
                self.pending.append(dest)   # a name of the source that has no statement yet: the text stays
                return f"{text} `{name}`" if kind_word else text
            self.unresolved.append(dest)
            return text
        if dest.startswith("/chapter/"):
            rest = dest[len("/chapter/"):]
            cid, _, frag = rest.partition("#")
            cid = cid.strip("/")
            t = self.labels.chapters.get(cid)
            if t is None:
                self.unresolved.append(dest)
                return text
            if not t.written:
                self.pending.append(dest)
                return text
            if frag:
                s = self.labels.anchors.get((cid, frag))
                if s is None:
                    self.unresolved.append(dest)
                    return self._cite(t, text, False)
                return self._cite(s, text, False)
            return self._cite(t, text, text.strip() == "Chapter")
        if dest.startswith("/") or dest.startswith("#"):
            self.unresolved.append(dest)   # the book has no site: every inner link is /decl/ or /chapter/
            return text
        return f"[{text}]({dest})"

    def inline(self, s: str) -> str:
        """The links in one line of prose, outside code and mathematics."""
        keep: list[str] = []

        def hold(m: re.Match) -> str:
            keep.append(m.group(0))
            return f"\x00{len(keep) - 1}\x00"

        s = re.sub(r"`[^`\n]*`", hold, s)
        s = _MATH.sub(hold, s)
        s = LINK.sub(lambda m: self.resolve(m[2], m[1]), s)
        while "\x00" in s:
            s = re.sub(r"\x00(\d+)\x00", lambda m: keep[int(m[1])], s)
        return s

    # -- headings and statements
    def page(self, md: str, *, shift: int, prefix: str, numbering: str | None = None) -> str:
        """Convert the text of a chapter. `shift` moves every heading down. Headings get the identifier
        `prefix-<anchor>`. With `numbering` ("3"), each ## heading gets a number 3.1, 3.2, ... and each bold
        statement head the number of its section and its place there: Theorem 3.2.1."""
        out, fence = [], None
        sec = stmt = 0
        for ln in md.split("\n"):
            f = _FENCE.match(ln)
            if f:
                fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
                out.append(ln)
                continue
            if fence:
                out.append(ln)
                continue
            m = re.match(r"^(#{1,6}) +(.*?)\s*$", ln)
            if m:
                level = len(m.group(1))
                title = m.group(2)
                lab = label_id(prefix, anchor(title))
                head = "#" * min(6, level + shift)
                if numbering and level == 2:
                    sec += 1
                    stmt = 0
                    out.append(f"{head} {self.inline(title)} {{#{lab} num=\"{numbering}.{sec}\"}}")
                else:
                    out.append(f"{head} {self.inline(title)} {{#{lab}}}")
                continue
            m = STMT.match(ln)
            if m and numbering:
                stmt += 1
                kind, more, name = m.group(1), m.group(2), m.group(3)
                num = f"{numbering}.{sec}.{stmt}"
                rest = ln[m.end():]
                lab = label_id(prefix, "st", str(sec), str(stmt))
                head = f"[{kind}{more} {num}{self.inline(name)}.]{{latex-cmd=\"hbsthead\"}}"
                if not out or not out[-1].strip():   # a paragraph of its own: a little space above it
                    out.append("```{=latex}\n\\hbstskip\\hbnoindentnext\n```\n")
                out.append(f"[]{{#{lab}}}{head}{self.inline(rest)}")
                continue
            lm = LEAN_LINE.match(ln)
            if lm and numbering:   # the source line under a statement
                for p in lean_paths(lm.group(1)):
                    if self.has_file and not self.has_file(src_path(p)):
                        self.unresolved.append(f"lean:{p}")
                out.append(f"[Lean: {self.inline(lm.group(1))}]{{latex-cmd=\"hblean\"}}")
                continue
            out.append(self.inline(ln))
        return "\n".join(out)


def strip_title(md: str) -> str:
    """Drop a leading # title line: the volume makes its own chapter heading."""
    lines = md.lstrip("\n").split("\n")
    if lines and lines[0].startswith("# "):
        lines = lines[1:]
    return "\n".join(lines)
