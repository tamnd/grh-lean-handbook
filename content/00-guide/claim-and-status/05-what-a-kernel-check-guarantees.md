---
title: What a kernel check guarantees
lean:
  - Statements.lean
  - Main.lean
  - Lib/Speed.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What a kernel check guarantees

This section says what follows from the machine checks of Section 4, if they hold, and what does not follow. The answer is a conditional statement with a short list of conditions. One condition is a reading of a few definitions by a person, and the kernel cannot replace it. The section ends with the list of what a reader must trust, and with the list of what the checks do not touch.

### The conditional statement

Suppose that these four things hold.

1. The build of Section 4 succeeds at the pin, and the list of axioms of the five theorems is `propext`, `Classical.choice` and `Quot.sound`.
2. The kernel that accepted the proofs is correct: it accepts a term of a type only if the term has that type in the type theory of Lean. The independent checkers make this more likely, if their runs are confirmed.
3. The type theory of Lean with the three axioms is consistent.
4. The five Lean propositions mean the classical statements: Mathlib's `riemannZeta` is the Riemann zeta function, Mathlib's `DirichletCharacter.LFunction` is the Dirichlet L-function, the principal character and primitivity are the classical ones, and the 16 lines of the file of statements say what they appear to say.

Then the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet L-functions hold, in the forms of Section 2. Conditions 1 to 3 are about the machine and the foundations. Condition 4 is about mathematics and can only be settled by reading.

This book does not assert the conclusion. It does not assert condition 1, because it has not seen the output of the checks. It explains why each condition matters, and where a reader can test it.

**Remark.** Condition 3 is the usual assumption of all of formal mathematics in Lean, and of Mathlib. Carneiro, *The Type Theory of Lean* (master's thesis, Carnegie Mellon University, 2019), gives a model of the type theory of Lean in set theory with inaccessible cardinals. This book takes condition 3 as given, as every user of Mathlib does. It is not a special doubt about this source.

### Why condition 4 needs a person

The kernel checks that a proof has a type. It does not check that the type is the theorem that a reader has in mind. Three small examples show the gap. None of them is a defect of the source. They show what a reader of any formal statement must check.

**Example (A hypothesis that never holds).** Consider the proposition: for every $s \in \mathbb{C}$ with $\zeta(s) = 0$ and $2 < \operatorname{Re} s < 1$, we have $\operatorname{Re} s = 1/2$. No $s$ satisfies $2 < \operatorname{Re} s < 1$. So the proposition is true, and it has a proof of one line. The kernel accepts that proof. The proposition says nothing about the zeros of $\zeta$. A reader of a formal statement must check that its hypotheses can hold, and that they hold where the classical statement needs them. In the five theorems of the source, the hypotheses are $0 < \operatorname{Re} s < 1$, or $\operatorname{Re} s > 1/2$ with the clause $\chi \neq \chi_0$ or $s \neq 1$, and they hold on the regions that the classical conjectures concern.

**Example (An object with the wrong definition).** Suppose that a file defines its own function $Z(s) = 1$ for all $s$, and calls it a zeta function. Then the proposition "every zero of $Z$ has real part $1/2$" is true, since $Z$ has no zeros, and its proof is short. The kernel accepts it. The name is the only link between $Z$ and $\zeta$, and the kernel does not read names. This is why the five theorems are stated with the functions of Mathlib, and why the file of statements imports only Mathlib. A reader who trusts the five theorems trusts the definitions of Mathlib at the pinned commit. The definitions of the source, in its 800 files, cannot enter the five types.

**Example (A value by convention).** Mathlib defines $\zeta(s)$ for every $s \in \mathbb{C}$, and also at the pole. Its value at $s = 1$ is $(\gamma - \log 4\pi)/2$, which is not $0$. Mathlib's Dirichlet L-function also has a value at $s = 1$ for a principal character. These values are conventions of the library. A statement that used them would depend on the convention, not on the mathematics. The half-plane form of the source excludes the pair ($\chi$ principal, $s = 1$), so it does not depend on the value there. The zeta form excludes $s = 1$ too, although that exclusion is not needed, since the value is not $0$. [The statements](/chapter/statements/) checks the other conventions that touch the five types.

These three checks are short for the five theorems of the source. The types use five definitions of Mathlib and 16 lines of the source. That is the design of the source, and it is the reason that a kernel check can carry the claim: the part that needs a person is small. The book does the reading in [the statements](/chapter/statements/). That chapter is drafted by a model, like this one, so its reading also needs a person before it counts as checked.

### What a reader must trust

If the checks of Section 4 pass, a reader must trust these things and nothing more, for the truth of the five theorems.

1. The kernel of Lean, or one of the independent kernels, and the three axioms.
2. The definitions in Mathlib, at the pinned commit, of `riemannZeta`, `DirichletCharacter.LFunction`, `DirichletCharacter.IsPrimitive` and `RiemannHypothesis`, and the definitions that these use.
3. The 16 lines of the file of statements.
4. The five statements of the file of main theorems.

The theorems of Mathlib are not on the list. Their proofs are checked by the kernel like the proofs of the source, and the export of Section 4 contains them. No line of the folders `Lib` and `New` of the source is on the list either. The source has about 300,000 lines of code. For the truth of the five theorems, a reader need not trust any of them, if the kernel has checked them.

**Remark (Formalization).** The source has a settings file, `Lib/Speed`, that changes the priority of many instances of Mathlib and takes many lemmas out of the default set of the simplifier for every file that imports it ([Speed.lean](lean:Lib/Speed.lean#L1)). Other files use `seal`, irreducibility and options of unification. These settings steer the elaborator, which searches for proofs. They do not change the kernel, which checks them. So they cannot make the kernel accept a false proof. They also cannot change the five types: the file of statements imports only Mathlib, and not `Lib/Speed` (`grh/GUIDE.md`, line 141). The settings do matter to a reader of the inner statements of the source, because they can change which instance a statement inside the development uses. [Reading the Lean](/chapter/reading-the-lean/) explains them.

### What the checks do not touch

A kernel check is a check of types. Here is a list of things that it does not check, each with the place in this book that treats it.

1. **The documents, the docstrings and the names.** The kernel reads none of them. A name such as `New.grh` and a docstring such as "Main theorem, in half-plane form" are comments by the author. The source itself warns: "Lean checks neither comments nor this guide." (`grh-compact/GUIDE.md`, line 6.) Each chapter of this book states the type of each declaration that it uses, and it checks its text against the type.
2. **The meaning of the inner statements.** The proof has more than 20,000 declarations. Their types use definitions of the source, many of them weaker or narrower than the textbook objects with the same names. The kernel checks that each proof has its type. It does not check that a definition of the source is the textbook object. For the five theorems this does not matter. For a reader who wants to learn the method, it matters on every page. The background volumes of this book state the textbook theory first, then the definition of the source, then the difference.
3. **The method.** The kernel does not see the plan of the proof. That the proof goes through a lattice of automorphic forms, three theorems A, B and C, and a criterion of Landau type is a reading of the Lean files by this book. [The theorem and the plan](/chapter/theorem-and-plan/) gives the plan. Whether this is the method of Alpöge's earlier proof, the book cannot say (Section 3).
4. **The citations.** A file can cite a book for a result. The kernel checks the proof in the file, not the citation. The source's own list of references says that only some citations were compared with their sources (Section 3).
5. **The unused code.** The README says: "Several hundred of the more than 20,000 declarations are not used by the five theorems" (`grh/README.md`, line 28). The kernel checks them too, but their truth does not bear on the claim. No list of them exists in the repository.
6. **This book.** The kernel does not read the book. An explanation in this book can be wrong where the source is right, or can state a result more strongly than the source proves it. Each chapter shows its status, and only a named person can raise it above `drafted`.

### What the checks do not mean

A kernel check, if it holds, is strong evidence of a narrow kind. It is not a refereed paper, and it does not replace one. It does not say that the method is understood, that the steps are new, or that the argument can be told in a form that a person can follow. These are the questions that a reading by a person answers, and the source says that no such reading has taken place.

So the honest summary of the status, at the pinned commit, is this. The source claims Lean proofs of five theorems, among them the Riemann hypothesis and the generalized Riemann hypothesis for Dirichlet L-functions, in the forms of Mathlib. The source reports machine checks that, if they hold, show that Lean accepts these proofs with three standard axioms. The repository holds no record of these checks. No mathematician has read the proof through, by the account of the source. This book explains the proof as the Lean files carry it out. It does not check it.
