---
title: The three voices in this book
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three voices in this book

This section says how the three voices of Section 1 show on the pages of the book, what the status of a chapter means, and what work only a person can do. A reader who knows these rules can tell, on any page, who supports a sentence: the kernel, the source, or the book.

### The marks on a page

Each chapter of the book uses the same marks.

1. **A statement and its `Lean:` line.** A numbered theorem, lemma or proposition states in mathematical words what a declaration of the source states in Lean. The line under it names the declaration and its file. This is the place where the voice of the kernel enters. The kernel accepts the declaration, if the checks of Section 4 hold. The words above the line are the book's reading of the type. A person can test them against the type.
2. **A proof.** The proof under a statement is the book's account of the Lean proof: its main steps and the earlier results that they use. The kernel checked the Lean proof, not the account. A step that the book adds or leaves out is the book's choice.
3. **A remark on the formalization.** A `Remark (Formalization)` says where the object of the source differs from the textbook object, where a junk value or a chosen object matters, or where a hypothesis is not used. These remarks are the book's reading of the Lean text.
4. **A quotation of the source.** A sentence in quotation marks, with a file and a line, is the voice of the source. The book quotes it to report it, not to endorse it.
5. **A citation of the literature.** A book or paper cited with a chapter, section or theorem number is a source that this book has used. When the book reports a citation of the source that it has not compared, it says "as cited by the source".

The book does not state as fact a claim of the source that the book has not checked in the Lean file. It says who has checked what. The sentence "Lean accepts the five theorems" does not appear without its condition, "if the reported checks hold".

### The status of a chapter

Each chapter has a status, and the build prints it on the first page of the chapter.

1. **drafted.** The chapter is written, and the check of the book passes: each Lean name in it is a real declaration at the pin, each link resolves, and the text keeps the rules of form. A model can set this status, and no other. This chapter, like every chapter at the time of writing, is drafted by a model.
2. **checked.** A named person has compared each statement of the chapter with its Lean type, and has read each proof against the Lean proof. The person is named in the chapter.
3. **reviewed.** A named person who works in the field has read the chapter as mathematics. The person is named in the chapter.

The status is about the chapter, not about the source. A chapter can be `reviewed` while the proof of the source is still unread by any person. Then a person has checked the explanation of that part, and not the whole proof. The status of a chapter tells a reader how far a person stands behind its text. Nothing more. [How to read this book](/chapter/how-to-read/) has a table of the status of every chapter.

### What the book can and cannot add

The book can add three things to the claim of the source. It can make the five statements and their conditions plain, so that a reader can test condition 4 of Section 5. It can explain each step of the proof in mathematical words, so that a person can read the proof as mathematics. And it can collect, in [the register of findings](/chapter/register-of-findings/), every point where the source's documents and its Lean text differ, where a definition is weaker than its name, or where a question is open.

The book cannot add evidence to the machine checks. It did not run them. It reports the logs that a third party published (Section 4). It also cannot add the reading that the source says is missing. A model drafts the chapters, so a drafted chapter is one more text by a model about the proof. Only the status `checked` or `reviewed`, with a person's name, adds a person's reading.

### Work for a person

Some questions about the claim can be settled only by a person with access to a machine, to the authors, or to the literature. The book has an issue for each, and it will report the answer when there is one.

1. Rerun `lake build` and `scripts/PrintAxioms.lean` at the pin, and attach the log to a release of this book ([issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15)). A third party has published logs of both at the pin (`https://math.mit.edu/~drew/shortgrh/`). This book ran both on 2026-11-27 with Lean v4.35.0: `lake build` ends with exit code 0 (9852 jobs, 23 minutes on 64 cores), and all five theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The logs are attached to release v0.4.1 ([build logs](https://github.com/tamnd/grh-lean-handbook/releases/download/v0.4.1/grh-lean-72fead1-build-logs.tar.gz)). Done.
2. Ask the authors for the logs of the three independent checkers and of Comparator, and for a description of the stand-in for the sandbox ([issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16)). A third party has published its own logs of these checkers and of Comparator at the pin, with the sandbox of Comparator. The logs of the authors and the stand-in are still not public.
3. Check whether the settings file `Lib/Speed` can be emptied on Lean 4.35.0. The README says that "everything still compiled on Lean 4.33.1" (`grh/README.md`, line 36), which is not the pinned toolchain ([issue 17](https://github.com/tamnd/grh-lean-handbook/issues/17)). This book ran the test on Lean 4.35.0 with only `import Mathlib` kept in the file. The build fails in three files, so on the pinned toolchain the claim does not hold as stated. [The settings](/chapter/reading-the-lean/#the-settings-of-the-source) gives the details. Done.
4. Compare the algebraic part of the readable edition with the original proof of Alpöge, file by file. Section 3 gives what is public, the method of the original, and the differences at the analytic end. The search for the public form is recorded in [issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18).
5. Raise the status of the chapters. Each chapter needs a person to check it against the Lean source, and the main chapters need a person in the field to review them.

The first two items concern condition 1 of Section 5. The third concerns only the reading of inner statements, since the settings cannot change the five types. The fourth concerns the history of the method, not the truth of the theorems. The fifth is the purpose of the book.

### Where to go next

A reader who wants to test condition 4 reads [the statements](/chapter/statements/) next. A reader who wants the shape of the proof reads [the theorem and the plan](/chapter/theorem-and-plan/), the first chapter of Volume 1. A reader who wants to read Lean types reads [reading the Lean](/chapter/reading-the-lean/). [How to read this book](/chapter/how-to-read/) gives the reading paths for other readers.
