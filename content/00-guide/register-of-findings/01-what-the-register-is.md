---
title: What the register is
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The register of findings

This chapter is a list. It gives each point about the source that a careful reader must know before trusting a statement of it. The source is the readable edition `grh` of lsernau/grh-lean, at the pinned commit 72fead1. A point of the register is called a finding. A finding can be a docstring that says more or less than the Lean text, a definition that takes a junk value, an object that `choose` or `Classical.epsilon` picks, a constant that may be $0$, a hypothesis that is never used or never discharged, a threshold that differs between two files, a citation that no person has checked, or a claim about a check that the repository gives no evidence for.

The register does not judge the proof. The source claims a proof of five theorems, and Lean accepts it, if the reported checks hold. A finding says where a reader of a statement must be careful. It does not say that a statement is false. Most findings are of a mild kind: a junk value that a later lemma removes, or a docstring that uses a word in a loose sense. A few findings are open questions that only a person can settle.

### Where the findings come from

The writers of this book read the source in eight research notes. The notes gave a list of candidate findings, and the plan of the book collected them in one register, with the numbers F-001 to F-136 and the open questions Q-01 to Q-69. For this chapter each candidate was checked again against the source at the pin, by its file, its line and its claim. A row of this chapter is a finding that the check confirmed. Where the file or the line in the plan was wrong, the row gives the correct place. Where the claim was wrong in part, the row states only the part that holds. One candidate, F-129, was dropped, because the check could not confirm it. The numbers are kept, so a number that is missing from the tables is a dropped or an excluded candidate.

Some candidates of the plan are not about the source. They are errors that the writers found in their own notes, such as a wrong path for a file or a wrong value of a constant in a note. These are the candidates F-123 to F-128 and F-131 to F-136. They are corrections of the book, not facts about the source, so this chapter does not list them. The chapters that use the corrected facts state them in their correct form.

### How to read a row

The findings are grouped by kind. Each group has its own section and one table or more. Every table has the same five columns.

| Column | Content |
|---|---|
| ID | The number of the finding, and its status. |
| File and line | The place in the source. A link opens the line on GitHub at the pin. |
| Finding | What the source does, in one or two sentences. |
| Effect on the meaning | What a reader of a statement must change in their reading because of it. |
| Chapter | The chapter of this book that treats it. |

A path in the second column is relative to `grh/src` when it is a link. A path that starts with `grh/` is a document or a file of the edition outside `src`, such as `grh/README.md` or `grh/Challenge.lean`. A path that starts with `grh-compact/` is a file of the compact edition. A path written as root `README.md` is the file at the top of the repository. When a finding has more than one place, the link goes to the first, and the other lines follow in plain text.

The fifth column names chapters by their identifiers in the plans of the volumes. A link to a chapter that is not written yet prints its title only. Some findings belong to two chapters, for example a junk value of a definition in Volume 4 that a theorem of Volume 10 must avoid. Then the column names both.

### The two statuses

A row has one of two statuses.

- **explained.** The source shows the point as the row states it. The chapter in the last column explains it, or will explain it when it is written. A reader needs nothing more than that chapter.
- **open.** A person must still verify or decide the point. The row states what the source shows and what is not known. A chapter of the book may cite an open row, but it must not state the open part as a fact.

Four of the open questions are checks that need a person with a machine, or a person who can ask the authors of the source. They are open as issues of the repository of this book.

| Issue | What a person must do | Rows |
|---|---|---|
| [issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15) | Rerun the build and the axiom check at the pin. | F-004 |
| [issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16) | Get the logs of the independent kernels and of Comparator, and the stand-in sandbox. | F-004, F-005 |
| [issue 17](https://github.com/tamnd/grh-lean-handbook/issues/17) | Check that `Lib/Speed` can be emptied on Lean 4.35.0. | F-019 |
| [issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18) | Find the public form of the original proof. | F-003 |

The other open rows have no issue of their own yet. A person who takes one of them opens an issue and writes its number into the row. Section 9 lists the open questions of the notes, each with the findings it concerns.

### The groups

The sections of this chapter follow the kinds of finding.

1. Checks, trust and the two editions (Section 2): what the repository claims about its checks, what the trusted statements say, and how the two editions differ.
2. Settings and instances (Section 3): the global options, the changes to instances and to `simp`, sealed and irreducible definitions.
3. Junk values and chosen objects (Section 4): definitions that take a conventional value, and objects that `choose` or `Classical.epsilon` picks.
4. Definitions weaker than the textbook (Section 5): names of standard objects whose definitions in the source ask less.
5. Constants that may vanish (Section 6): identities $X = cY$ that can hold with both sides $0$, and the places where nonvanishing comes back.
6. Hypotheses and sizes (Section 7): standing, bundled and unused hypotheses, and thresholds that differ between files.
7. Citations and docstrings (Section 8): unchecked or doubtful citations, and documents that disagree with the code.

Section 9 gives the open questions. Section 10 has exercises and the notes.

### How the register grows

The book is rebuilt at each release, and this chapter with it. When a writer of a later chapter finds a new point, or when a person closes an open row, the register changes. The rules for a change are these.

- A new finding takes the next free number, after the largest number used. It goes into the table of its kind as a new last row. The order of a table is the order of the numbers, so a new row is always appended, and no other row moves.
- A number is never used twice. A dropped finding keeps its number, and the number is not given again.
- When a person settles an open row, the status becomes explained, and the row keeps its number and its place. The row then names the issue that settled it.
- When a later release of the source moves a line, the row gets the new line. The number stays.
- A row cites one chapter or more by identifier. If no chapter treats the point yet, the row names the planned chapter that will treat it.

A row has one line of the Markdown source, with the five cells between bars. A new row is a copy of an old row with new contents. So a writer can add a finding without changing anything else in the chapter.

### What a reader should take from this chapter

A reader does not need to read the register from top to bottom. The chapters of the book cite a finding by its number where it matters, and a reader can follow the number back to its row. A referee who wants the weakest points can read the open rows first, then the rows on constants that may vanish and on unused hypotheses. A reader who wants to check a statement of the source by themselves can use the second column as a list of places to read.

The register says nothing about the five theorems beyond what the source and its documents say. It records what a reader must know to read them with care.
