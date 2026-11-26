"""The volumes of the handbook and the Markdown of each.

The volumes come from content/NN-*/volume.yaml (spec 07.3 and 07.4). The number of a chapter is its place in the
plan of its volume. A chapter of the plan with no section files is not in the build, and a volume with no written
chapter is not built. The numbers of the other chapters do not change when a chapter is missing.
"""

from __future__ import annotations

import os
import re

from .content import Chapter, Volume, anchor, fill, front_pages, load_volumes
from .md import REPO, STMT, LEAN_LINE, Converter, Labels, Place, Target, label_id, lean_names
from .source import Source


class Book:
    def __init__(self, content_dir: str, source: Source, pin: str):
        self.content = content_dir
        self.root = os.path.dirname(os.path.abspath(content_dir))
        self.source = source
        self.pin = pin
        self.volumes: list[Volume] = load_volumes(content_dir)
        self.front = front_pages(content_dir)
        self.labels = Labels()
        self._register()

    # ------------------------------------------------------------------ structure
    @property
    def built(self) -> list[Volume]:
        """The volumes with at least one written chapter."""
        return [v for v in self.volumes if self._chapters(v)]

    def volume(self, n: int) -> Volume:
        return next(v for v in self.volumes if v.number == n)

    def _chapters(self, v: Volume) -> list[Chapter]:
        """The chapters of a volume that go into its build. The generated index goes in only if the volume has
        other written chapters."""
        written = v.written
        out = []
        for c in v.chapters:
            if c.written:
                out.append(c)
            elif c.generated and written:
                out.append(c)
        return out

    def web(self, path: str) -> str:
        rel = os.path.relpath(path, self.root)
        return f"{REPO}/blob/main/{rel}" if path.endswith(".md") else f"{REPO}/tree/main/{rel}"

    def known(self, name: str) -> bool:
        return name in self.source.grh.decls

    def _register(self):
        L = self.labels
        for v in self.volumes:
            for c in v.chapters:
                lab = f"ch-{c.id}"
                live = c.written or bool(c.generated and v.written)
                L.chapters.setdefault(c.id, Target(v.number, str(c.num), lab, self.web(c.dir), live))
                if c.written:
                    self._chapter_labels(v, c)

    def _chapter_labels(self, v: Volume, c: Chapter) -> None:
        """The numbers of the sections and statements of a chapter. A line `Lean: `Name`` under a statement ties
        the name to that statement, so that a link /decl/Name/ goes to its number."""
        L = self.labels
        prefix = f"ch-{c.id}"
        sec = stmt = 0
        cur = None
        for s in c.sections:
            fence = False
            for ln in s.body.split("\n"):
                if re.match(r"^(`{3,}|~{3,})", ln):
                    fence = not fence
                    continue
                if fence:
                    continue
                m = re.match(r"^## +(.*?)\s*$", ln)
                if m:
                    sec += 1
                    stmt = 0
                    cur = None
                    L.anchors.setdefault((c.id, anchor(m.group(1))),
                                         Target(v.number, f"{c.num}.{sec}", label_id(prefix, anchor(m.group(1))),
                                                self.web(s.path)))
                    continue
                sm = STMT.match(ln)
                if sm:
                    stmt += 1
                    cur = (f"{c.num}.{sec}.{stmt}", label_id(prefix, "st", str(sec), str(stmt)), sm.group(1))
                    continue
                lm = LEAN_LINE.match(ln)
                if lm and cur:
                    for name, _ed in lean_names(lm.group(1)):
                        L.by_decl.setdefault(name, []).append(
                            Place(v.number, cur[0], cur[1], cur[2], c.title, self.web(s.path)))
        for name in c.decls:   # names that the chapter covers with no statement of their own
            if name not in L.by_decl:
                L.by_decl[name] = [Place(v.number, str(c.num), prefix, "Chapter", c.title, self.web(c.dir))]

    # ------------------------------------------------------------------ Markdown
    def converter(self, number: int) -> Converter:
        src = self.source if self.source.present else None
        return Converter(self.labels, number, self.pin, self.known if src else None,
                         src.grh.has_file if src else None)

    def markdown(self, v: Volume) -> tuple[str, dict]:
        conv = self.converter(v.number)
        out = []
        for c in self._chapters(v):
            out.append(f"# {conv.inline(c.title)} {{#ch-{c.id} num=\"{c.num}\"}}\n")
            if c.written:
                out.append(self._status(c))
                out.append(conv.page(c.text, shift=0, prefix=f"ch-{c.id}", numbering=str(c.num)))
            elif c.generated == "lean-index":
                out.append(self._lean_index(conv))
        md = "\n\n".join(out)
        stats = {"unresolved": sorted(set(conv.unresolved)), "pending": sorted(set(conv.pending)),
                 "words": sum(c.words for c in v.chapters), "chapters": len(self._chapters(v))}
        return md, stats

    def _status(self, c: Chapter) -> str:
        bits = [f"Status: {c.status}."]
        d = c.people("drafted_by")
        if d:
            bits.append("Drafted by " + ", ".join(d) + ".")
        k = c.people("checked_by")
        bits.append(("Checked by " + ", ".join(k) + ".") if k else "Not yet checked against the Lean source by a person.")
        r = c.people("reviewed_by")
        if r:
            bits.append("Reviewed by " + ", ".join(r) + ".")
        return "::: {latex-env=\"hbstatus\"}\n" + " ".join(bits) + "\n:::\n"

    def _lean_index(self, conv: Converter) -> str:
        out = ["## The status of the chapters {#ch-lean-index-status}\n",
               "Each chapter of the plan, with its status. A chapter that is planned has no text yet.\n",
               "| Vol. | Ch. | Title | Status | Words |", "|---|---|---|---|---|"]
        for v in self.volumes:
            for c in v.chapters:
                if c.generated:
                    continue
                out.append(f"| {v.number} | {c.num} | {c.title} | {c.status} | {c.words:,} |")
        out += ["\n## The index of Lean names {#ch-lean-index-names}\n",
                "Each Lean declaration that a statement of the handbook gives, with the volume and the number of "
                "the statement.\n"]
        for name in sorted(self.labels.by_decl, key=str.lower):
            places = "; ".join(f"Vol. {p.volume}, {p.kind} {p.number}" for p in self.labels.by_decl[name])
            out.append(f"- `{name}`: {places}.")
        return "\n".join(out) + "\n"

    # ------------------------------------------------------------------ front pages
    def front_values(self, v: Volume | None, version: str, date: str) -> dict[str, str]:
        return {"version": version, "date": date, "pin": self.pin,
                "volume": f"Volume {v.number}: {v.title}" if v else "The front pages"}

    def front_md(self, name: str, values: dict[str, str]) -> tuple[dict, str]:
        """A front page with its placeholders filled and its links converted."""
        fm, body = self.front.get(name, ({}, ""))
        conv = self.converter(-1)
        return fm, conv.page(fill(body, values), shift=0, prefix=f"front-{name}")
