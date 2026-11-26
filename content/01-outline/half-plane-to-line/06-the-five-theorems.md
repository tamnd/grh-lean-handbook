---
title: The deduction and the five theorems
lean:
  - New/Main.lean
  - Main.lean
decls:
  - New.zeros_on_line
  - riemannHypothesis
  - riemannZeta_eq_zero_re
  - LFunction_ne_zero_of_half_lt_re
  - LFunction_eq_zero_re
  - LFunction_eq_zero_re_of_isPrimitive
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The deduction and the five theorems

This section proves the line statement from the half-plane statement, with the reflection theorem of Section 5. Then it proves the five theorems of the source. Each of the five is one line: it applies a theorem of this chapter to the half-plane theorem, or it is a special case of another of the five.

### The line statement

**Theorem (The line statement from the half-plane statement).** Assume the half-plane statement. Then the line statement holds: for every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `New.zeros_on_line` (New/Main.lean).

*Proof.* Let $q$, $\chi$ and $s$ satisfy the hypotheses. Since $0 < \operatorname{Re} s < 1$, we have $s \neq 1$ and $1 - s \neq 1$, and $\operatorname{Re} s \neq 0$.

The gamma factor is not zero at $s$: $G_\chi(s) = \Gamma_{\mathbb{R}}(s + a(\chi))$ with $\operatorname{Re}(s + a(\chi)) > 0$, and $\Gamma_{\mathbb{R}}$ is not zero on $\operatorname{Re} s > 0$ (Section 2). So the first alternative of [Theorem](/decl/New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero/) fails, and $L(1 - s, \bar\chi) = 0$.

Apply the half-plane statement to $\chi$ at $s$, with the clause $s \neq 1$. If $\operatorname{Re} s > 1/2$, it gives $L(s, \chi) \neq 0$, which is false. So $\operatorname{Re} s \leq 1/2$. Apply the half-plane statement to $\bar\chi$ at $1 - s$, with the clause $1 - s \neq 1$. In the same way, $\operatorname{Re}(1 - s) = 1 - \operatorname{Re} s \leq 1/2$. So $\operatorname{Re} s = 1/2$. $\square$

**Remark.** The proof uses the half-plane statement only at points of the strip $1/2 < \operatorname{Re} s < 1$, and only through the clause $s \neq 1$, never through $\chi \neq \chi_0$. It uses it at $\chi$ and at $\bar\chi$. A version for one character at a time would use the corollary of Section 5, and so the conjugate symmetry. The source quantifies over all characters, so it does not need the conjugate symmetry.

**Remark (Formalization).** The two lemmas of the last step, this theorem and [Theorem](/decl/New.zeta_zeros_on_line/), are stated under a hypothesis `h : DirichletLNonvanishingRightOfHalf`, which the Lean file introduces as a section variable ([New/Main.lean](lean:New/Main.lean#L21)). So each of them has the type "half-plane statement implies line statement" or "half-plane statement implies zeta statement". They do not use the half-plane theorem. The file imports the file of the half-plane theorem, but only the five theorems apply the lemmas to it.

### The five theorems

The five theorems of the source are stated with Mathlib's `RiemannHypothesis` and with the four propositions of Section 3.

**Theorem (The Riemann hypothesis).** For every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `riemannHypothesis` (Main.lean).

*Proof.* Apply [Theorem](/decl/New.zeta_zeros_on_line/) to [Theorem](/decl/New.grh/). $\square$

**Theorem (The zeta statement).** For every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `riemannZeta_eq_zero_re` (Main.lean).

*Proof.* This is the same proposition as [Theorem](/decl/riemannHypothesis/). $\square$

**Remark (Formalization).** The first theorem has the type `RiemannHypothesis` of Mathlib (Mathlib/NumberTheory/LSeries/RiemannZeta.lean). The second has the type `RiemannZetaZerosOnLine` of the source. The two propositions differ only in notation: Mathlib writes the hypotheses as binders of a universal quantifier, and the source writes them as implications, with an explicit cast $(n : \mathbb{C}) + 1$. They are equal by unfolding the definitions, and the source proves each theorem with the other. The source says that the names and types of the five theorems are those of Alpöge's original proof.

**Theorem (The generalized Riemann hypothesis, half-plane form).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `LFunction_ne_zero_of_half_lt_re` (Main.lean).

*Proof.* This is [Theorem](/decl/New.grh/). $\square$

**Theorem (The generalized Riemann hypothesis).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `LFunction_eq_zero_re` (Main.lean).

*Proof.* Apply [Theorem](/decl/New.zeros_on_line/) to [Theorem](/decl/New.grh/). $\square$

**Theorem (The generalized Riemann hypothesis for primitive characters).** For every integer $q \geq 1$, every primitive Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, we have $\operatorname{Re} s = 1/2$.

Lean: `LFunction_eq_zero_re_of_isPrimitive` (Main.lean).

*Proof.* This is the case of [Theorem](/decl/LFunction_eq_zero_re/) for a primitive $\chi$. $\square$

**Remark (Formalization).** The Lean proof of the fifth theorem is the term `fun N _ χ _ ↦ LFunction_eq_zero_re N χ` ([Main.lean](lean:Main.lean#L21)). The first `_` binds the instance $q \neq 0$. The second `_` binds the proof that $\chi$ is primitive, and the term does not use it. So the hypothesis of primitivity is not used. This is not a gap, since the fifth theorem adds a hypothesis to the fourth. The classical route proves the primitive case first. The source goes the other way: its main theorem is for every character, and the primitive case is a corollary.

**Remark (Formalization).** The docstring of the third theorem says that nothing is stated "at $s = 1$ for the trivial character". The character `1` there is the principal character modulo $q$, for each $q$ (Section 3).

### What the five theorems rest on

The five theorems rest on the half-plane theorem, the two lemmas of the last step, the reflection theorem with its three lemmas, and the classical facts of Mathlib that Section 2 lists. All but the half-plane theorem are classical, and this chapter proves them or gives a source. The half-plane theorem is the claim of the source. Volume 0, Chapter 2 says what a reader can rerun.
