---
title: The claim and its status
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The claim and its status

This chapter says what the source claims, who made the claim, what evidence the repository holds for it, and what a check by the Lean kernel can and cannot guarantee. It proves no theorem. Each later chapter of the book explains one part of a long formal proof. A reader must know the status of that proof before reading the explanation. This chapter gives that status, with a source for each fact.

The short form is this. The repository lsernau/grh-lean holds a Lean 4 development on top of Mathlib. It states five theorems. Four of them are forms of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet L-functions. The fifth is a special case. The documents of the repository say that these theorems have passed machine checks. They also say: "No mathematician has read it through, and no paper comes with it" (root `README.md`, line 34). The repository contains no log of any check. This book did not rerun the checks. This book is an explanation of the mathematics in the source. It is not a check of the source.

### Three voices

A book about a formal proof speaks in three voices. A reader must know at each point which voice speaks. This book keeps the three apart in every chapter, and this chapter defines them.

1. **What Lean checks.** Lean is a proof assistant. Its kernel is a small program that checks that a proof term has the type that it claims. If the checks that the source reports hold, then the kernel accepts proofs of the five theorems, with three standard axioms and nothing more. This is the only part of the claim that a machine supports. It concerns the five Lean statements as written, and nothing else.
2. **What the source says.** The source has documents (READMEs, a guide, an index, a list of references), a docstring at the head of each file, and a name for each declaration. The source says that Claude, an AI model, wrote all of them, and the Lean text too (`grh/README.md`, line 6). The kernel checks none of them. A docstring can be wrong, and a name can promise more than the statement gives, and Lean accepts the file in each case.
3. **What the book explains.** Each chapter of this book explains the mathematics of one part of the source: the statements, the definitions, the proofs and the sizes. The book can contain errors that are not in the source. Each chapter shows its status. A model can set the status `drafted` only. The status `checked` or `reviewed` needs a named person.

The book does not say in its own voice that the proof is correct, or that the Riemann hypothesis or the generalized Riemann hypothesis is proved. It says "the source claims", "Lean accepts, if the reported checks hold", and "this chapter explains". It also does not say that the proof is wrong. It has no evidence for either verdict, and it is not a review.

### What the chapter covers

The claim has four parts, and the chapter takes them in order.

The first part is the statements. The five theorems are about the zeta function of Mathlib and the Dirichlet L-functions of Mathlib. Section 2 states the classical conjectures, then gives the five theorems of the source in words, and says what they do not say. For example, they say nothing about Dedekind zeta functions, Hecke L-functions or the L-functions of modular forms. "GRH" in the title of the source means the generalized Riemann hypothesis for Dirichlet L-functions only.

The second part is the origin. Section 3 gives what the documents say about the authors: the proof is "Levent Alpöge's, with Claude"; the readable edition is a shorter rewriting of an earlier Lean proof by Alpöge; the only pointer to that proof is a URL. The section also says what this book could not find.

The third part is the evidence. Section 4 lists each check that the documents report: the build, the list of axioms, an export that three independent checkers accept, and a run of the tool Comparator "with a stand-in for its sandbox". For each check it says what the check would show, what the repository holds, and how a reader can run the check again.

The fourth part is the meaning of the evidence. Section 5 says what a check by the kernel guarantees, under what assumptions, and what it does not guarantee. The main point is a division of labour. If the checks hold, the kernel guarantees that the five Lean statements follow from the axioms. It cannot guarantee that the five Lean statements mean the classical theorems. That needs a person to read 16 lines of the source and a few definitions of Mathlib. [The statements](/chapter/statements/) does that reading.

Section 6 says how the three voices show on the pages of this book, and it lists the work that only a person can do. Section 7 has exercises and the notes.

### A first example of the difference

A small example shows why the three voices differ. The file `Main.lean` of the source has a docstring for its third theorem. The docstring says that nothing is stated "at s = 1 for the trivial character". The Lean statement excludes the pair $(\chi, s)$ with $\chi = 1$ and $s = 1$, where $1$ is the principal character modulo $N$, for each modulus $N$. The two agree here, but the word "trivial" is the source's word, and the kernel does not read it. A reader who takes "trivial" to mean the character modulo $1$ only would read a different exclusion into the theorem. The type is the claim. The docstring is a comment on the claim.

The same holds for the whole development. It has more than 20,000 declarations (`grh/README.md`, line 28), each with a name and most with a docstring. The kernel checks the types and the proofs. It does not check that a name such as `New.grh` describes its type. For the five theorems, a reader can check the types against the classical statements in an afternoon. For the inner declarations, the book states each type that it uses in mathematical words, and it checks the words against the type, not against the docstring.

### What the chapter uses

The chapter uses the documents of the source at the pinned commit: the root `README.md`, `grh/README.md`, `grh/NOTICE`, `grh/GUIDE.md`, `grh/REFERENCES.md`, `grh-compact/README.md` and `grh-compact/GUIDE.md`. It uses the short Lean files `Statements.lean`, `Main.lean`, `grh/Challenge.lean`, `grh/scripts/PrintAxioms.lean` and the configuration `grh/comparator.json`. Each fact taken from a document is cited by file and line. Each fact about Lean is about the files, read as text. The book did not build them.
