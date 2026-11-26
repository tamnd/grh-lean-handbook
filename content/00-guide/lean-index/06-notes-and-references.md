---
title: Notes and references
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Notes and references

### How this chapter is rebuilt

The glossary of the first section and these notes are written by hand. The other three parts of the chapter are made by the script `scripts/lean_index.py` of the handbook: the table of the status of the chapters, and the index of Lean names in its three sections. A person must not edit these sections by hand, because the next run of the script writes over them. Spec 10.4 of the plan of the book says that this chapter is rebuilt at each release. So the script runs at each release, after the chapters of the release are merged and before the release is tagged.

The command is `python3 scripts/lean_index.py --source ../grh-lean`, run from the root of the handbook. The option gives the path of the clone of the source. The clone must be at the pin of the file `EDITION`, and the script stops if it is not. The script reads the plan of each volume and every written chapter. For each section it collects the names on the `Lean:` lines, outside code blocks, and the names in the list `decls:` of its front matter. It finds the file and the line of each name in the readable edition at the pin, with the same reader of the source that the build of the book uses. Then it writes the files `02-the-status-of-the-chapters.md`, `03-names-of-the-data.md`, `04-other-names-a-to-l.md` and `05-other-names-m-to-z.md` of this chapter. The command `python3 scripts/lean_index.py --source ../grh-lean --check` writes nothing, and it fails if a section is out of date. After a run, `python3 -m ghb --source ../grh-lean check --volume 0` must report no problem, and the changed sections are committed with the release.

A new glossary term needs a hand edit of the first section. A term goes into the glossary when a written chapter defines it and later chapters use it. Its link goes to the chapter, or the section, that has the definition.

### What the index contains

The index lists a name once, with every chapter that cites it. A citation is a `Lean:` line under a statement, a `Lean:` line in a remark, or an entry of `decls:`. The index does not record which statement of a chapter gives the name. The link `/decl/<name>/` of the book does that: it resolves to the number of the statement whose `Lean:` line has the name. The line of a declaration is the line of its keyword, such as `theorem` or `def`, in the file of the source. A name of Mathlib has no line in the index, because the source does not contain it and the book does not pin a version of Mathlib apart from the one that the source uses.

The line numbers hold at the pin only. A new pin can move every line. The command `python3 -m ghb ledger --diff A B` of the build lists the declarations that change from commit A to commit B, and the names of `decls:` among them. After a new pin, that list says which statements of the book to read again, and a run of the script then gives the new lines.

### Where to read further

The chapter [reading the Lean](/chapter/reading-the-lean/) explains how to find a declaration and its proof in the source, from a name of this index. The chapter [the two editions](/chapter/two-editions/) gives the map from the names of the compact edition to the names of the readable edition. The file `grh/GUIDE.md` of the source gives a map of its folders. The ledger of the handbook, made by `python3 -m ghb ledger --write`, gives for each file of the source the chapter of the plan that explains it, and for each name of `decls:` its section, its kind and a digest of its text.
