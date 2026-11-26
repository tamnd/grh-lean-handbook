---
title: The status of a chapter, and how to report an error
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The status of a chapter, and how to report an error

Each chapter of the book has a status. The status says how far a person stands behind the text of the chapter. This section defines the three status labels, says where a reader finds them, gives the status of the book at the time of writing, and says how to report an error. The status is about the explanation, not about the source: no label of this book says that the proof of the source is correct.

### The three labels

A chapter has one of three labels.

1. **drafted.** The chapter is written, and the check of the book passes on it. The check tests that each Lean name in the chapter is a declaration of the source at the pinned commit, that each file it names exists, that each link resolves or points to a planned chapter, and that the text keeps the rules of form and style. A model can set this label, and no other. A drafted chapter is a text by its writer, with no reading by a second person.
2. **checked.** A named person has compared each statement of the chapter with the type of the declaration on its `Lean:` line: the same objects, hypotheses, quantifiers and conclusion. The same person has read each proof against the Lean proof, and has checked each size against the source. The person is named in the chapter.
3. **reviewed.** A named person who works in the field has read the chapter as mathematics: the definitions, the proofs, the examples and the notes. The person is named in the chapter.

The labels test different things. The label `checked` tests the text against the Lean source. The label `reviewed` tests the text as mathematics. A chapter can be checked and still contain a proof that a mathematician finds unclear. A chapter can be reviewed and still contain a statement that does not match its Lean type exactly. A chapter has its final status when it has both.

The label `checked` is not a check of the source. A checker of a chapter reads the book's account of each Lean proof against that proof. The checker does not check that the Lean proof is right: Lean does that, if the reported checks hold. So a chapter that is checked tells the reader that the explanation matches the source. It does not tell the reader that the source proves what it claims. [The claim and its status](/chapter/claim-and-status/) says what a kernel check guarantees and what it does not.

### Where to find the status

The status of each chapter is printed on its first page, in a box under the title. For a drafted chapter the box reads "Status: drafted", gives the writer, and says "Not yet checked against the Lean source by a person". For a checked or reviewed chapter it names the person.

The status of a chapter is the lowest status of its sections. Each section carries its own label, so a checker can check a chapter one section at a time. The chapter shows the higher label only when every section has it.

[The glossary and index of Lean names](/chapter/lean-index/), the last chapter of this volume, has a table of every chapter of the plan with its status and its number of words. The build makes this table at each edition, from the chapters themselves. A chapter that has no text yet has the status `planned` there. That table is the reference. The paragraph below is a description at one date.

### The status at the time of writing

When this chapter was drafted, every chapter with text had the status `drafted`, and no chapter was checked or reviewed. Every chapter was drafted by a model. Volume 1 was complete. Volume 0 had its chapters on the claim, the statements, the notation, the Lean and the two editions. The argument Volumes 9 to 12 had their opening chapters, and Volume 2 had its first chapters. The other chapters were planned.

So the reading paths of Section 3 can be read in full only in their first part. Path 1 can be read in full except for the register of findings. Path 4 lacks the table of sizes and the register. Paths 2 and 3 lack most chapters after the opening chapters of the argument volumes. Beyond them, a link to a planned chapter prints its title with no number.

A reader should take the label `drafted` at its word. The text of a drafted chapter has passed a machine check of its names and its form, and nothing else. Its statements are the writer's reading of the Lean types. A reader who relies on a statement in other work should compare it with its type, as Section 4 describes. The remarks on the formalization say where the comparison needs care.

### How to report an error

The source of the book is a public repository on GitHub: github.com/tamnd/grh-lean-handbook. An error is reported as an issue there. Each chapter is one folder `content/NN-volume/<id>/`, where `<id>` is the identifier of the chapter in the plan of its volume, and each section is one file in it. So a report can name the exact file.

A good report has five parts.

1. **The place.** The volume, the chapter and the section, or the file of the book and its line. For a numbered statement, its number in the printed book.
2. **The Lean name**, if the error is in a statement or a proof: the name on the `Lean:` line, and the file of the source.
3. **What the text says**, in a short quotation.
4. **What is wrong.** For a statement: what the Lean type says that the text does not, or the reverse. For a proof: the step that fails, and why. For a size: the value in the source, with its file and line. For a citation: the correct chapter, section or theorem number.
5. **A correction**, if the reader has one.

The kinds of error differ in weight. The most serious is a statement that does not match its Lean type: a conclusion stronger than the type, a hypothesis that the type does not have, or a quantifier in the wrong place. Next is a proof that cites the wrong earlier result, or that skips a step that is not a rewriting. Then come a size that does not match the source, a wrong citation of the literature, and a broken link. A point of style is also welcome. The rules of style are those of `prompts/chapter.md` in the repository.

An error in the book is not the same as a problem in the source. A reader who finds that a definition of the source is weaker than its name, that a hypothesis is never used, or that a document of the source disagrees with the Lean text, has found a point for [the register of findings](/chapter/register-of-findings/). The report has the same five parts. The register lists each such point with its status: explained, with the chapter that explains it, or open, with its issue. Questions that only a person can settle, such as a rerun of the build at the pinned commit, are already open as issues; [the three voices in this book](/chapter/claim-and-status/#the-three-voices-in-this-book) lists them.

A report of an error does not change the status of a chapter by itself. A fix comes as a change to the files of the chapter, through a pull request, and the check of the book runs on it. A person who checks a chapter and finds no error raises its label in a pull request, with that person's own name in the front matter of each section. The brief for a checker is `prompts/review.md` in the repository.

### Who can raise a status

Only a person can raise a status above `drafted`. The check of the book enforces this rule: it fails if a section has the label `checked` with no person named in `checked_by`, or the label `reviewed` with no person named in `reviewed_by`, and it does not accept the name of a model there. The book was drafted by models under this rule. Its value as a guide to the proof grows with each chapter that a person checks and reviews.
