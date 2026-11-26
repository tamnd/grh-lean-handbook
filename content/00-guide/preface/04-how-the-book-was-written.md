---
title: How the book was written, and thanks
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## How the book was written, and thanks

A reader should know how a text was made before trusting it. This section says how this book was written, what the status of a chapter means, and what work remains for a person. It ends with thanks to the authors of the source.

### How the chapters were drafted

The chapters of this book were drafted by a model. Each writer drafted one chapter from two inputs: the Lean files of the source that the chapter explains, and a set of research notes on the source. The notes cover the documents of the source, the reduction at the top of the argument, the background theories and the steps of Theorems A, B and C. They are notes for writers, not part of the book, and they can contain small errors. The rule for every writer was that the Lean source is the truth. A writer read the head, the statements and the proofs of each file of the chapter, and stated each result as the Lean type states it: the same objects, hypotheses, quantifiers and conclusion. Where the object of the source differs from the textbook object, the chapter gives the textbook form with a citation, then the form of the source, then a remark on the difference.

A builder checks each chapter before it enters the book. It reads the source as text, at the pinned commit, and does not build the Lean files. It tests that each Lean name in a chapter is a declaration of the source, that each file that a chapter names exists, that each link resolves or points to a planned chapter, and that the text keeps the rules of form and style. A chapter that passes these tests is `drafted`. This test is about names and form. It does not test that a statement of the book matches its Lean type, and it does not test that a proof of the book is right.

### What the status of a chapter means

Each chapter has one of three labels, and the build prints it on the first page of the chapter.

1. **drafted.** The chapter is written, and the check of the book passes. A model can set this label, and no other.
2. **checked.** A named person has compared each statement of the chapter with its Lean type, and has read each proof against the Lean proof. The person is named in the chapter.
3. **reviewed.** A named person who works in the field has read the chapter as mathematics. The person is named in the chapter.

The check of the book refuses the label `checked` or `reviewed` without the name of a person, and it refuses the name of a model there. So no label above `drafted` can come from the process that drafted the book. [The three voices in this book](/chapter/claim-and-status/#the-three-voices-in-this-book), in Volume 0, chapter 2, gives the rules in full. [The status of a chapter, and how to report an error](/chapter/how-to-read/#the-status-of-a-chapter-and-how-to-report-an-error) says where to find the labels and how to report an error.

The status is about the chapter, not about the source. A chapter that is checked tells the reader that its explanation matches the Lean source. It does not tell the reader that the source proves what it claims. This preface, like every chapter at the time of writing, is `drafted`. A drafted chapter is one more text by a model about a proof that the source says no mathematician has read. Its value grows with each person who checks it.

### Work for a person

The book is open, and it asks for readers who check. A reader who finds an error reports it as an issue in the repository of the book, with the place, the Lean name, the text and what is wrong. A reader who checks a chapter and finds no error raises its label, with the reader's own name, in a pull request. The brief for a checker is `prompts/review.md` in the repository of the book. Some questions only a person can settle: a rerun of the build at the pin, the logs of the independent checkers and of Comparator, and the public form of Alpöge's original proof. [The three voices in this book](/chapter/claim-and-status/#the-three-voices-in-this-book) lists them with their issues.

### Thanks

This book exists because the source exists, and it thanks the authors of the source. It reports their roles in the words of the source, since it knows no more than these words.

The README of the readable edition says: "The proof is Levent Alpöge's, with Claude." (`grh/README.md`, line 5.) The root README says that the proof "is based on Levent Alpöge's, with Claude", and that the repository is "a shorter version, produced in collaboration with my colleagues at Anthropic, and Claude" (root `README.md`, lines 9 to 11). The book thanks Levent Alpöge, whose proof both READMEs name. It thanks the author of the root README, who published the repository under the account lsernau, and the colleagues at Anthropic that the README names as collaborators. It thanks Claude, which by the account of the source wrote the Lean text and the documents of the readable edition (`grh/README.md`, line 6).

The book also thanks the developers of Lean and the authors of Mathlib. The five theorems are stated with the definitions of Mathlib, and a reader who trusts the five theorems trusts these definitions. Without that library, there would be no short list of things to trust.

Last, the book thanks in advance each person who checks or reviews a chapter. The name of that person goes on the first page of the chapter.
