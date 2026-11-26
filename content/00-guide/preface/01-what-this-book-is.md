---
title: What this book is
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What this book is

This book is a textbook on one proof. The proof is a Lean 4 development in the repository lsernau/grh-lean. The book follows its readable edition, the folder `grh/`, at the commit `72fead1` (in full, `72fead102f663d5c7a407964a13dc0cf9d977207`). The book calls this text "the source". The source builds on Mathlib, the library of mathematics for Lean, at a commit that the source pins. The book explains the mathematics that the Lean files carry out, as a graduate textbook explains a long proof to a strong student: the whole design first, then each theorem that the design needs, then the theory under each theorem.

### The claim of the source

The source states five theorems. Four of them are forms of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet L-functions. The fifth is a special case. The main one is the half-plane form. For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$ and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$. Here $\chi_0$ is the principal character modulo $q$, and $L(s, \chi)$ is the Dirichlet L-function of Mathlib, continued to $\mathbb{C}$. [The theorem and the plan](/chapter/theorem-and-plan/), the first chapter of Volume 1, states all five theorems in full, with their Lean names. [The statements](/chapter/statements/) reads each of them against the definitions of Mathlib.

The five theorems speak of Dirichlet L-functions only. They say nothing about Dedekind zeta functions, Hecke L-functions or the L-functions of modular forms. They say nothing about zeros with $\operatorname{Re} s \leq 0$, and they give no quantitative bound. The word "GRH" in the title of the source and in the title of this book means the generalized Riemann hypothesis for Dirichlet L-functions, and nothing more.

### The status of the claim

A reader must know the status of a proof before reading an explanation of it. [The claim and its status](/chapter/claim-and-status/), the second chapter of this volume, gives the status with a source for each fact. Here is its summary, in the same words.

The source claims Lean proofs of five theorems, among them the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet L-functions, in the forms of Mathlib. The source reports machine checks that, if they hold, show that Lean accepts these proofs with three standard axioms: `propext`, `Classical.choice` and `Quot.sound`. The repository holds no record of these checks. No mathematician has read the proof through, by the account of the source. This book explains the proof as the Lean files carry it out. It does not check it.

The root README of the repository says the last point in its own words: "No mathematician has read it through, and no paper comes with it" (root `README.md`, line 34). This book did not rerun the checks. So this book does not say that the proof is correct, and it does not say that the Riemann hypothesis or the generalized Riemann hypothesis is proved. It also does not say that the proof is wrong. It has no evidence for either verdict. In its own voice it says "the source claims", "Lean accepts, if the reported checks hold", and "this chapter explains".

### Three voices

A book about a formal proof speaks in three voices, and this book keeps them apart on every page. The first voice is what Lean checks: the kernel of Lean accepts a proof term only if the term has its stated type. This voice concerns the Lean statements as written, and it speaks only if the reported checks hold. The second voice is what the source says: its documents, the comments at the head of its files, and the names of its declarations. The kernel reads none of these. The third voice is what the book explains: the statements in mathematical words, the proofs on paper, the examples and the remarks. The book can contain errors that are not in the source. [The three voices in this book](/chapter/claim-and-status/#the-three-voices-in-this-book) says how each voice shows on a page.

### The origin of the source

The documents of the repository speak of the authors in two ways, and this book reports both in their own words. The README of the readable edition says: "The proof is Levent Alpöge's, with Claude." It continues: "The Lean text and the documents in this project were written by Claude (AI)." (`grh/README.md`, lines 5 and 6.) The root README says: "The proof is based on Levent Alpöge's, with Claude (https://alpo.ge/remark.pdf). This repository is a shorter version, produced in collaboration with my colleagues at Anthropic, and Claude." (root `README.md`, lines 9 to 11.) The first README says that the proof "is" Alpöge's. The second says that it is "based on" Alpöge's. This book does not choose between the two. [The origin of the proof](/chapter/claim-and-status/#the-origin-of-the-proof) gives the other facts, and lists what this book looked for and did not find.

The readable edition calls itself "a shorter rewriting of Levent Alpöge's Lean proof", and says that "many steps are proved by other arguments" (`grh/README.md`, line 10). The repository also holds a compact edition, `grh-compact/`, of about 76,000 lines, against about 300,000 lines for the readable edition. The two editions prove the same five statements, by partly different arguments. This book follows the readable edition only. [The two editions](/chapter/two-editions/) maps the names of the compact edition to the names of this book.

### The shape of the book

The book has thirteen volumes. Volume 0 is the guide: the claim and its status, the statements, the notation, the sizes, the little Lean that a reader needs, the register of findings, the two editions and an index of Lean names. Volume 1 is the spine. It proves the five theorems from three theorems about a lattice of automorphic forms, called Theorems A, B and C, with full proofs of every step above them. Volumes 2 to 8 give the background theories by subject. Volumes 9 to 12 prove Theorems A, B and C. [The volumes and the map of the proof](/chapter/how-to-read/#the-volumes-and-the-map-of-the-proof) gives the map and the reasons for the order.
