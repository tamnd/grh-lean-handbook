---
title: The origin of the proof
lean:
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The origin of the proof

This section collects what the documents of the source say about the authors of the proof, about the earlier proof that it rewrites, and about the two editions in the repository. Every sentence in quotation marks is from a file of the repository at the pinned commit. The section also lists what this book looked for and did not find. It makes no judgement of the persons named.

### What the documents say

The repository has two top folders, `grh/` and `grh-compact/`, and a root README. The documents speak of the authors in five places.

1. The root README says: "The proof is based on Levent Alpöge's, with Claude (https://alpo.ge/remark.pdf). This repository is a shorter version, produced in collaboration with my colleagues at Anthropic, and Claude." (root `README.md`, lines 9 to 11.) The word "my" refers to the person who wrote the README. The README does not name that person. The repository is under the account lsernau.
2. The README of the readable edition says: "The proof is Levent Alpöge's, with Claude. The Lean text and the documents in this project were written by Claude (AI)." (`grh/README.md`, lines 5 and 6.)
3. The same README says: "This project is a shorter rewriting of Levent Alpöge's Lean proof (see <https://alpo.ge/remark.pdf>). It follows that proof's method; many steps are proved by other arguments, and parts of it, mostly background material, were ported from there and then rewritten." (`grh/README.md`, line 10.)
4. The NOTICE of the readable edition says that the file of statements, and the names and types of the five theorems, are "taken from that proof unchanged", and that the lakefile "is adapted from it" (`grh/NOTICE`, lines 6 and 7).
5. The first line of the file of main theorems is the comment "The proof is Levent Alpöge's, with Claude." ([Main.lean](lean:Main.lean#L1)).

The README of each edition thanks "the colleagues at Anthropic whose direction and suggestions shaped this rewriting" (`grh/README.md`, line 41). The license is Apache 2.0, with the copyright line "Copyright 2026 Anthropic, PBC" (root `README.md`, line 38). The root README calls the repository a "Research artifact. Not maintained and not accepting contributions." (line 3).

The two READMEs use different words for the relation to Alpöge's proof. The root README says that the proof is "based on" Alpöge's. The README of the edition says that the proof "is" Alpöge's, and that the edition rewrites his Lean proof. This book does not choose between the two. It reports both.

### What there is not

The documents name no paper, and the root README says that none comes with the proof: "No mathematician has read it through, and no paper comes with it." (root `README.md`, line 34.) This sentence is a statement by the source about itself. This book has no evidence against it. A reader must take it at its word: at the pinned commit, by the account of the source, no person has read the proof through.

The only pointer to the earlier proof is the URL `https://alpo.ge/remark.pdf`. This book has not read that document. It does not know whether the document is a paper, a sketch of the method, or a note on the formalization. It does not know whether the earlier Lean proof is public. The documents do not list the steps that the rewriting proves "by other arguments", and they do not list the parts that were "ported from there and then rewritten".

So the book cannot say which steps of the method go back to Alpöge, and which are new in the rewriting. When a chapter says "the method of the source", it means the method that the Lean files of the readable edition carry out, as this book reads them. It does not mean the method of the earlier proof. An issue of this book asks a person to find the public form of the original proof ([issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18)).

The repository at the pin has one commit, dated 25 November 2026, with the message "Lean proof of GRH". So the history of the repository says nothing about how the proof was made.

### Two editions, two proofs

The repository holds two Lean projects. The readable edition `grh/` has about 300,000 lines of code in 803 files. The compact edition `grh-compact/` has about 76,000 lines of code (root `README.md`, lines 15 and 16). Each README says that the other edition uses other arguments for some steps (`grh/README.md`, line 12).

The two editions share the file of statements, the five theorem types, the file `Challenge.lean`, the configuration of Comparator, the lakefile, the toolchain and the manifest. Below the file of main theorems they differ. They are two proofs of the same five statements, not two layouts of one proof. One difference is visible at the top of the argument. The readable edition reaches the second cut-off of its prime sums by a prime number theorem in arithmetic progressions with an error term. The compact edition has no such theorem and uses a different argument there. The one-sided bounds that the two editions prove for the same prime sum also have different exponents.

This book follows the readable edition only. A claim about "the source" in this book is a claim about the readable edition at the pin. [The two editions](/chapter/two-editions/) maps the names of the compact edition to those of the readable edition. The documents of the two editions also report different checks. Section 4 gives both lists.

### The documents are notes, not evidence

The documents of the source are written by the same author as the code, by its own account. That author is a model. So the documents are not an independent witness of the proof. They are a map of the code, written with it.

The book uses the documents as notes for the writers, and it checks each fact in the Lean file before it states the fact. The guide of the compact edition says the same thing about itself: "Lean checks neither comments nor this guide." (`grh-compact/GUIDE.md`, line 6.) The readable edition makes a similar point in its list of references: "Only some of the citations were compared with their sources." (`grh/REFERENCES.md`, line 3.) That file counts 228 compared citations, of which 66 have a confirmed place, and it says that the citations of 122 other files were not part of the check (`grh/REFERENCES.md`, lines 5 to 10).

These facts matter for a reader of a later chapter. A file of the source can say that a result is "known" and cite a book for it. The citation may not have been compared with the book. The result in the file may be a special case of the result in the book, or a variant with its own definitions. A chapter of this book that uses such a result states the textbook form with a source that this book checked, then the form of the source, and then the difference.

### What this means for the claim

The origin of the proof does not change what Lean checks. A proof term is checked by its type and its axioms, and not by its author. The origin changes what a reader can take from the documents and from the literature. There is no paper to compare with, no list of the steps that differ from the earlier proof, and no person who has read the whole. The documents are the work of the same model as the code. So the only independent evidence for the claim is the evidence of the machine checks. Section 4 describes it.
