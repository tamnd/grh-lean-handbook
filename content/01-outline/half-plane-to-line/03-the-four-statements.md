---
title: The four statements
lean:
  - Statements.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - RiemannZetaZerosOnLine
  - DirichletLNonvanishingRightOfHalf
  - DirichletLZerosOnLine
  - PrimitiveDirichletLZerosOnLine
  - New.grh
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The four statements

The file of statements of the source imports only Mathlib. It defines four propositions and proves nothing. The source says that this file, and the names and types of the five theorems, are taken without change from Alpöge's original proof. This section states the four propositions in the notation of Section 2, says what each hypothesis does, and states the half-plane theorem. A reader who wants to know what the source claims must check this section against the Lean file and against the Mathlib definitions of Section 2, and nothing else (Volume 0, Chapter 3).

### The propositions

**Definition (The zeta statement).** The *zeta statement* is the proposition: for every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `RiemannZetaZerosOnLine` (Statements.lean).

Here $\mathbb{N}$ contains $0$, so the excluded points are $-2, -4, -6, \dots$, the trivial zeros of $\zeta$. The statement is about all of $\mathbb{C}$, not only the critical strip.

**Definition (The half-plane statement).** The *half-plane statement* is the proposition: for every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `DirichletLNonvanishingRightOfHalf` (Statements.lean).

**Definition (The line statement).** The *line statement* is the proposition: for every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `DirichletLZerosOnLine` (Statements.lean).

**Definition (The primitive line statement).** The *primitive line statement* is the proposition: for every integer $q \geq 1$ and every primitive Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `PrimitiveDirichletLZerosOnLine` (Statements.lean).

In each statement, $L(s, \chi)$ is Mathlib's L-function of Section 2, which is the imprimitive L-function when $\chi$ is imprimitive, and $\chi_0$ is the principal character modulo $q$. The binder `[NeZero N]` of the Lean statements says $q \neq 0$, that is, $q \geq 1$. So every modulus is covered, and the modulus $q = 1$ gives the zeta function.

### What each hypothesis does

**Remark (Formalization).** The clause "$\chi \neq \chi_0$ or $s \neq 1$" of the half-plane statement uses Mathlib's character `1`, which is the principal character modulo $q$, for each $q$. The docstring of the third theorem of the source calls it "the trivial character". In this book it is the principal character. It is not only the character modulo $1$. So the clause excludes exactly the point $s = 1$ for each principal character, which is the pole of $L(s, \chi_0)$. For $\chi \neq \chi_0$ the statement includes $L(1, \chi) \neq 0$, which is Dirichlet's theorem.

**Remark (Formalization).** Mathlib's $\zeta$ has a value at $s = 1$. It is $\zeta(1) = (\gamma - \log 4\pi)/2 = -0.9769\ldots$, where $\gamma$ is Euler's constant (Mathlib: `riemannZeta_one`, in Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean). This value is not $0$. So the hypothesis $s \neq 1$ of the zeta statement excludes no point that the statement could be false at. It makes the statement agree with Mathlib's `RiemannHypothesis`. The line statements exclude the junk value $L(1, \chi_0)$ by $\operatorname{Re} s < 1$.

**Remark.** The line statements say nothing about $\operatorname{Re} s \leq 0$, and they cannot. Take $q = 2$. By the change of level formula, $L(s, \chi_0) = (1 - 2^{-s})\zeta(s)$. The factor $1 - 2^{-s}$ vanishes at $s = 2\pi i k / \log 2$ for every $k \in \mathbb{Z}$. So $L(s, \chi_0)$ modulo $2$ has infinitely many zeros on $\operatorname{Re} s = 0$, and none of them is on the critical line. A statement about the closed strip $0 \leq \operatorname{Re} s < 1$ would be false for Mathlib's L-function.

**Remark.** The primitive line statement is a special case of the line statement: it adds a hypothesis. The half-plane statement implies the other three. Section 6 proves this. The converse also holds, with one classical input. The line statement excludes the zeros with $1/2 < \operatorname{Re} s < 1$, and the non-vanishing of $L(s, \chi)$ on $\operatorname{Re} s \geq 1$ (Mathlib: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`) excludes the rest. So, given the classical theory, the half-plane statement and the line statement are equivalent. The source proves the half-plane form because its method gives that form.

### The half-plane theorem

This chapter uses the half-plane theorem only as a hypothesis, but the five theorems need it.

**Theorem (The half-plane theorem).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

*Proof.* The proof is the content of Volumes 1 to 12. The last step is in [the main inequality and the end of the proof](/chapter/main-inequality/). Here is its shape. Let $\rho$ satisfy the hypotheses. If $\rho = 1$, then $\chi \neq \chi_0$, and $L(1, \chi) \neq 0$ by the classical non-vanishing on $\operatorname{Re} s \geq 1$, which Mathlib has (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`). If $\rho \neq 1$, choose $\beta$ with $1/2 < \beta < \operatorname{Re} \rho$. The proof lifts $\chi$ to the modulus $q_0 = 18480\, q$ and applies the criterion of Chapter 4, with the one-sided bound of Chapter 13 as its hypothesis. The criterion gives $L(\rho, \chi') \neq 0$ for the character $\chi'$ that $\chi$ induces modulo $q_0$. By the change of level formula, $L(\rho, \chi')$ is $L(\rho, \chi)$ times finitely many factors, so $L(\rho, \chi) \neq 0$. $\square$

**Remark (Formalization).** The file that proves the half-plane theorem imports the file of statements directly. So the theorem is stated with the same proposition `DirichletLNonvanishingRightOfHalf` that the five theorems use, and not with a copy of it.
