---
title: What the book assumes and what it does not do
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the book assumes and what it does not do

This section says what a reader needs before the book, and what the book does not try to do. A reader who knows both limits can use the book for what it is.

### What the book assumes

The main reader is a graduate student in number theory. The book assumes a first course in each of four subjects.

1. Complex analysis, and the analytic theory of Dirichlet L-functions at the level of Davenport, *Multiplicative Number Theory*, chapters 1 to 9.
2. Algebraic number theory: Neukirch, *Algebraic Number Theory*, chapters I to III, or the same material in another book.
3. Lie groups and their representations: Knapp, *Lie Groups Beyond an Introduction*, chapters I to V, or the same.
4. Commutative algebra and schemes: Atiyah and Macdonald, *Introduction to Commutative Algebra*, and Hartshorne, *Algebraic Geometry*, chapter II, or the same.

Volume 1 needs only the first two. Each background volume opens with its own list of prerequisites and the textbook chapters that give them. Other readers, such as an analytic number theorist, an expert in automorphic forms, a referee or a user of Lean, can take a shorter path. [Reading paths](/chapter/how-to-read/#reading-paths) gives each path as a list of chapters.

The book does not assume that the reader knows Lean. The text is mathematics. The code appears in two places only: the `Lean:` line under each statement, and the remarks on the formalization. A reader who wants to read the Lean types needs only the little Lean of [reading the Lean](/chapter/reading-the-lean/).

### What the book does not do

The book is not a check of the proof. It does not rerun the machine checks that the source reports, and it does not certify that the Lean files build. A person who wants that evidence can run the build and the script of axioms at the pinned commit. An issue of this book asks a person to do so and to attach the log to a release.

The book is not a review. It gives no verdict on the claim, either way. A chapter of this book can have the status `reviewed`, but that status says that a person in the field has read the chapter as mathematics. It says nothing about the proof as a whole.

The book is not a list of declarations. The readable edition has more than 20,000 of them. A chapter states the results that carry its argument, and it puts the small lemmas, the second names and the wrappers into the `Lean:` lines and into the proofs. A reader who wants every name uses [the index of Lean names](/chapter/lean-index/).

The book is not a paraphrase of the comments of the source. The source has a comment at the head of each file, a guide to its folders, an index of results and a list of references. By the account of the source, the same author wrote these documents and the Lean text. The book reads them as a guide for its writers, and checks each fact in the Lean text before it states the fact. The source warns about its citations itself: "Only some of the citations were compared with their sources." (`grh/REFERENCES.md`, line 3.)

The book does not treat other L-functions, and it does not draw the classical consequences of the generalized Riemann hypothesis. The source does not state them, and the book stays with what the source states.

The book does not compare the proof with Alpöge's earlier Lean proof. The documents of the source point to that proof only through the URL `https://alpo.ge/remark.pdf`. This book has not read the document at that address, and it does not know which steps of the method go back to the earlier proof and which are new in the rewriting. When a chapter says "the method of the source", it means the method that the Lean files of the readable edition carry out, as this book reads them.

The book does not follow the compact edition. A claim about "the source" in this book is a claim about the readable edition at the pin. [The two editions](/chapter/two-editions/) is the only chapter that reads the compact edition, and it compares the two at the top of the argument only.

### How to use the book

A reader who wants the whole proof reads the volumes in order. A reader who wants the design reads Volume 0, chapters 1 to 3, and then Volume 1. A reader who doubts one step finds it on the map of Volume 1 and goes to the chapter that explains it. In each case the reader keeps the three voices apart: a statement of the book is the book's reading of a Lean type, and the `Lean:` line under it says which type.
