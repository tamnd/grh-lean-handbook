---
title: The theorem and the plan
lean:
  - Main.lean
  - New/Main.lean
decls:
  - riemannHypothesis
  - riemannZeta_eq_zero_re
  - LFunction_ne_zero_of_half_lt_re
  - LFunction_eq_zero_re
  - LFunction_eq_zero_re_of_isPrimitive
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The theorem and the plan

This chapter opens the outline of the proof. It states the five theorems of the source, it says what is known about their status, and it gives the plan of the proof in one page. It then explains the idea of the method, and it gives a map of the book and of this volume. The chapter proves nothing new. Each step that it names is stated here in full, and each proof is in a later chapter, with a link.

The source is a Lean 4 development in the readable edition of lsernau/grh-lean, at the pinned commit of this book. Its main theorem says that no Dirichlet L-function vanishes in the half-plane $\operatorname{Re} s > 1/2$, except at the pole $s = 1$ of a principal L-function. Its proof compares two bounds for the covolume of a lattice of automorphic forms. The prime numbers enter through the difference of the two bounds.

### The objects

Let $\zeta$ be the Riemann zeta function, continued to $\mathbb{C}$. Mathlib gives it a value at the pole $s = 1$, and this value is not $0$. For an integer $q \geq 1$ and a Dirichlet character $\chi$ modulo $q$, let $L(s, \chi)$ be the Dirichlet L-function of Mathlib, continued to $\mathbb{C}$. For an imprimitive character this is the L-function of $\chi$ itself, with all its Euler factors, and not the L-function of the primitive character that induces $\chi$. Let $\chi_0$ be the principal character modulo $q$. It is the character `1` of Mathlib, for each $q$. [From the half-plane to the line](/chapter/half-plane-to-line/) gives the definitions in full, with their junk values.

### The five statements

The file of statements of the source imports only Mathlib. It defines four propositions and proves nothing. The file of main theorems proves five theorems. The first has the type `RiemannHypothesis` of Mathlib, and the other four have the types of the four propositions. The source says that the file of statements, and the names and types of the five theorems, are taken without change from Alpöge's original proof (NOTICE, in the readable edition).

**Theorem (The Riemann hypothesis).** For every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `riemannHypothesis` (Main.lean).

*Proof.* Apply [Theorem](/decl/New.zeta_zeros_on_line/) to the half-plane theorem, [Theorem](/decl/New.grh/). $\square$

**Theorem (The zeta statement).** For every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `riemannZeta_eq_zero_re` (Main.lean).

*Proof.* This is the same proposition as the first theorem, in the notation of the file of statements. $\square$

**Theorem (The generalized Riemann hypothesis, half-plane form).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `LFunction_ne_zero_of_half_lt_re` (Main.lean).

*Proof.* This is [Theorem](/decl/New.grh/). $\square$

**Theorem (The generalized Riemann hypothesis).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `LFunction_eq_zero_re` (Main.lean).

*Proof.* Apply [Theorem](/decl/New.zeros_on_line/) to [Theorem](/decl/New.grh/). $\square$

**Theorem (The generalized Riemann hypothesis for primitive characters).** For every integer $q \geq 1$, every primitive Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `LFunction_eq_zero_re_of_isPrimitive` (Main.lean).

*Proof.* This is the case of the fourth theorem for a primitive $\chi$. $\square$

The third theorem is the main theorem. The other four come from it by the reflection of zeros under $s \mapsto 1 - s$. A zero $\rho$ of $L(s, \chi)$ with $0 < \operatorname{Re} \rho < 1/2$ gives a zero $1 - \rho$ of $L(s, \bar\chi)$ with $\operatorname{Re}(1 - \rho) > 1/2$, and the third theorem excludes it. Mathlib has the functional equation only for primitive characters, so the source proves the reflection for every character. [From the half-plane to the line](/chapter/half-plane-to-line/) does this step in full.

**Remark (Formalization).** The statements cover every modulus $q \geq 1$ and every character, primitive or not. The modulus $q = 1$ gives the zeta function. The fifth theorem does not use its hypothesis of primitivity: its Lean proof is the term `fun N _ χ _ ↦ LFunction_eq_zero_re N χ` ([Main.lean](lean:Main.lean#L21)), and the second `_` is the unused proof that $\chi$ is primitive. This is not a gap, because the fifth theorem adds a hypothesis to the fourth. The hypothesis $s \neq 1$ of the zeta statement excludes no possible zero, because Mathlib's value $\zeta(1)$ is not $0$. The last three theorems say nothing about zeros with $\operatorname{Re} s \leq 0$. They cannot, since an imprimitive L-function has zeros on $\operatorname{Re} s = 0$ from its Euler factors.

### The status of the claim

Three things must be kept apart: what Lean checks, what the source says, and what this book explains. Here they are, one sentence each.

Lean accepts the five theorems above, with only the axioms `propext`, `Classical.choice` and `Quot.sound`, if the checks that the source reports hold; this book did not rerun the checks, the repository has no logs and no CI configuration for them, and a third party has published logs of them at the pin (`https://math.mit.edu/~drew/shortgrh/`). The source says that "the proof is Levent Alpöge's, with Claude", that its Lean text and documents were written by Claude, and that "no mathematician has read it through, and no paper comes with it". This book explains the mathematics of each step, chapter by chapter, and each chapter has a status; this chapter was drafted by a model and no person has checked it.

The reported checks are a full build, a script that prints the axioms, an export that three independent kernels accept (nanoda, con-leche and con-ron), and a run of the tool Comparator "with a stand-in for its sandbox". [The claim and its status](/chapter/claim-and-status/) lists them with the evidence in the repository and the logs of the third party. If the kernel checks hold, a reader must trust only the Lean kernel and the three axioms, Mathlib's definitions of `riemannZeta`, `DirichletCharacter.LFunction`, `DirichletCharacter.IsPrimitive` and `RiemannHypothesis`, the 16 lines of the file of statements, and the five statements. [The statements](/chapter/statements/) reads them line by line.

### What the chapter uses

The chapter uses no result that it does not state. Section 3 uses the notions of a lattice, its covolume, Hadamard's inequality and the product formula for $\mathbb{Q}$. [Twisted lattices](/chapter/twisted-lattices/) defines them for the source.

### The plan of the chapter

Section 2 is the plan of the proof in one page, with a diagram of the chain of steps from the background theories up to the five theorems. Section 3 is the idea: an integral lattice of automorphic forms whose covolume has an upper bound and a lower bound with the same main amount, so that the difference bounds a sum over primes. It also explains why the method stops at the exponent $1/2$. Section 4 gives a map of the thirteen volumes of the book, the reading paths, and the chapter map of this volume. Section 5 has the exercises and the notes.
