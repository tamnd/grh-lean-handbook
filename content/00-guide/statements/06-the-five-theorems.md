---
title: The five theorems and the half-plane theorem
lean:
  - Main.lean
  - New/Main.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.grh
  - riemannHypothesis
  - riemannZeta_eq_zero_re
  - LFunction_ne_zero_of_half_lt_re
  - LFunction_eq_zero_re
  - LFunction_eq_zero_re_of_isPrimitive
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The five theorems and the half-plane theorem

Sections 2 to 5 read the five propositions. This section reads the theorems that claim them. They are in Main.lean, a file of 22 lines. Each proof is one term, and each term goes back to one theorem of the source, the half-plane theorem `New.grh`. The section gives the Lean text, states each theorem, and says what a check of the file does and does not show.

### The file Main.lean

Here is the file without its comments and docstrings.

```lean
import New.Main

theorem riemannHypothesis : RiemannHypothesis :=
  New.zeta_zeros_on_line New.grh
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine :=
  riemannHypothesis
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  New.grh
theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  New.zeros_on_line New.grh
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
```

The types after the colons are the whole claim. The first is a constant of Mathlib. The other four are constants of Statements.lean. The terms after `:=` name two lemmas of New/Main.lean and the theorem `New.grh`. Those lemmas take the half-plane statement as a hypothesis `h` (New/Main.lean, lines 21 to 23), so the only theorem with real content is `New.grh`.

### The half-plane theorem

**Theorem (Half-plane theorem).** For every $N \neq 0$, every Dirichlet character $\chi$ of level $N$ with values in $\mathbb{C}$, and every $s \in \mathbb{C}$ with $1/2 < \operatorname{Re} s$, and $\chi \neq 1$ or $s \neq 1$, `LFunction χ s` $\neq 0$.
Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

```lean
theorem grh : DirichletLNonvanishingRightOfHalf
```

The theorem is in the namespace `New`. Its type is the proposition of Section 5. The file OneSidedBound.lean imports Statements.lean directly (line 5), so the name `DirichletLNonvanishingRightOfHalf` in it is the constant of Statements.lean, and not a local copy.

*Proof.* The source claims a proof. The case $s = 1$, $\chi \neq 1$ is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` of Mathlib. In every other case the source picks $\beta$ with $1/2 < \beta < \operatorname{Re} s$ and passes to the character $\chi'$ induced by $\chi$ at level $q_0 = 18480N$. It proves a one-sided bound $x^{\beta - 1}$ for a weighted sum over primes in a class $d_0 \bmod q_0$, with $d_0 = 9240N - 1$, and deduces $L(s, \chi') \neq 0$ by a criterion of Landau type. The change of level theorem `DirichletCharacter.LFunction_changeLevel` writes $L(s, \chi')$ as $L(s, \chi)$ times a finite product, so $L(s, \chi) \neq 0$. The steps are the subject of the whole book. [The one-sided bound and the theorem](/chapter/main-inequality/) gives the last step, and [the theorem and the plan](/chapter/theorem-and-plan/) gives the plan. $\square$

### The five theorems

**Theorem (Riemann hypothesis).** Mathlib's `RiemannHypothesis` holds: every $s \in \mathbb{C}$ with $\zeta(s) = 0$, $s \notin \{-2, -4, -6, \ldots\}$ and $s \neq 1$ has $\operatorname{Re} s = 1/2$.
Lean: `riemannHypothesis` (Main.lean).

*Proof.* The term is `New.zeta_zeros_on_line New.grh`. The lemma [New.zeta_zeros_on_line](/decl/New.zeta_zeros_on_line/) deduces `RiemannZetaZerosOnLine` from the half-plane statement, at level $1$ and with the functional equation of $\zeta$. Lean accepts this term at the type `RiemannHypothesis`, since the two propositions are equal by definition (Section 2). $\square$

**Theorem (Zeta zeros on the line).** `RiemannZetaZerosOnLine` holds: every $s \in \mathbb{C}$ with $\zeta(s) = 0$, $s \neq -2(n+1)$ for all $n \in \mathbb{N}$, and $s \neq 1$ has $\operatorname{Re} s = 1/2$.
Lean: `riemannZeta_eq_zero_re` (Main.lean).

*Proof.* The term is `riemannHypothesis`. The two types are equal by definition. $\square$

**Theorem (Generalized Riemann hypothesis, half-plane form).** `DirichletLNonvanishingRightOfHalf` holds: for every $N \neq 0$, every character $\chi$ of level $N$ and every $s$ with $1/2 < \operatorname{Re} s$, and $\chi \neq 1$ or $s \neq 1$, `LFunction χ s` $\neq 0$.
Lean: `LFunction_ne_zero_of_half_lt_re` (Main.lean).

*Proof.* The term is `New.grh`. $\square$

**Theorem (Generalized Riemann hypothesis).** `DirichletLZerosOnLine` holds: for every $N \neq 0$, every character $\chi$ of level $N$ and every $s$ with $0 < \operatorname{Re} s < 1$ and `LFunction χ s` $= 0$, $\operatorname{Re} s = 1/2$.
Lean: `LFunction_eq_zero_re` (Main.lean).

*Proof.* The term is `New.zeros_on_line New.grh`. The lemma [New.zeros_on_line](/decl/New.zeros_on_line/) deduces the statement from the half-plane statement. It sends a zero $s$ of $L(\cdot, \chi)$ to the zero $1 - s$ of $L(\cdot, \chi^{-1})$ by the functional equation, after a reduction to a primitive character, and applies the half-plane statement to both. $\square$

**Theorem (Generalized Riemann hypothesis, primitive characters).** `PrimitiveDirichletLZerosOnLine` holds: the statement of the last theorem holds for every primitive character.
Lean: `LFunction_eq_zero_re_of_isPrimitive` (Main.lean).

*Proof.* The term `fun N _ χ _ ↦ LFunction_eq_zero_re N χ` takes $N$, the instance of `NeZero N`, the character $\chi$ and the proof of primitivity, drops the last one, and applies the last theorem. $\square$

### Remarks on the five theorems

**Remark (Formalization).** The primitivity hypothesis of the fifth theorem is not used. The fifth theorem is a special case of the fourth, and its docstring says so (Main.lean, lines 19 and 20). It is in the list because it is the form that many texts state.

**Remark (Formalization).** The proof of the fourth theorem applies the half-plane theorem only at points inside the strip with $\operatorname{Re} s > 1/2$. The half-plane theorem is stronger in form than the fourth theorem, since it also covers $\operatorname{Re} s \geq 1$. Section 5 shows that the two are equivalent, by a theorem of Mathlib for $\operatorname{Re} s \geq 1$.

**Remark (Formalization).** The names `riemannHypothesis` and `RiemannHypothesis` differ in the case of the first letter. The first is the theorem of Main.lean, in the root namespace. The second is the definition of Mathlib. Lean does not allow a file to define a name again, so no file of the source can change the meaning of `RiemannHypothesis` or of a name in Statements.lean.

**Remark (Formalization).** The files of the proof import a settings file, Lib/Speed.lean, through Lib/Base.lean. It changes instance search and the `simp` set. Statements.lean does not import it, so it cannot change how the four propositions are elaborated. The source says the same (grh/GUIDE.md, section 5). The settings can change how statements inside the proof are elaborated, but those statements are not part of the claim.

### What a check of the five theorems shows

The source describes three kinds of check (grh/README.md, lines 25 to 30).

1. A build of all files with the pinned Lean v4.35.0 and Mathlib, without errors and without `sorry`.
2. The command `#print axioms` for each theorem, in scripts/PrintAxioms.lean. The source reports that each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, the three standard axioms of Lean and Mathlib. A proof with `sorry` would show the axiom `sorryAx`, and a new axiom would show its name.
3. An export of the five theorems and all their dependencies, Mathlib included, checked by the independent kernels nanoda, con-leche and con-ron. Separately, the tool Comparator compares the five theorems with grh/Challenge.lean. That file imports only Statements.lean and states the five theorems with `sorry`. Comparator checks that the theorems of Main.lean have the same names and types as those of Challenge.lean, and that they use only the permitted axioms. The file grh/comparator.json lists the three axioms and an empty list `definition_names`, so no definition of the source is part of the comparison.

This book did not rerun these checks. A third party has published logs of them at the pin (`https://math.mit.edu/~drew/shortgrh/`), and [the claim and its status](/chapter/claim-and-status/#the-reported-checks) reports what they say. If they hold, then Lean accepts the five theorems, with the types that Sections 2 to 5 read. They do not show that those types say what the reader wants. That part is the reading of this chapter. The source reports that it ran Comparator with a stand-in for its sandbox (grh/README.md, line 30). [The claim and its status](/chapter/claim-and-status/) discusses what this means for trust.
