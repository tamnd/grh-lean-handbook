---
title: Reading a statement
lean:
  - Statements.lean
  - Main.lean
  - New/Main.lean
  - New/Reduction/OneSidedBound.lean
  - Lib/Analytic/ZeroSymmetry.lean
decls:
  - DirichletLNonvanishingRightOfHalf
  - New.grh
  - New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero
  - New.prod_euler_factor_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Reading a statement

This chapter teaches a mathematician to read the Lean statements of the source. The rest of the book gives each statement of the source in mathematical form, with a `Lean:` line under it that names the declaration and its file. A reader who wants to compare the two must read a few lines of Lean. That is not hard. A Lean statement is a sentence of mathematics in a strict notation, and most of the notation is standard. Some of it is not. Lean gives a value to every expression, also where a mathematician says "undefined". Lean separates a proof that an object exists from the object itself. Lean has a language of filters for limits. And the source has settings files that change how Lean finds hidden arguments. Each of these can change what a statement means to a reader who does not know the rule. This chapter states each rule, shows it on a real declaration of the source, and says what it means for the reader of a statement.

The chapter does not teach the reader to write Lean. It teaches the reader to check that a sentence of this book says what the Lean says. The plan of the argument is in [the theorem and the plan](/chapter/theorem-and-plan/). The conventions of the book itself are in [how to read this book](/chapter/how-to-read/). Every example in this chapter is a declaration of the source, quoted exactly from the readable edition, with its file.

The sections are in this order. This section reads one statement in full: the half-plane statement that the whole argument proves. Section 2 treats numbers, coercions between number systems, and finite sums. Section 3 treats junk values: Lean's values for $x/0$, for a divergent series and for a divergent integral, and the constants that the source allows to be $0$. Section 4 treats the difference between a proof of existence and a datum, and the objects that the source defines by choice. Section 5 treats filters, limits and the symbol $O$. Section 6 treats the settings of the source. Section 7 tells the reader how to find a declaration and its proof. Section 8 has exercises and notes.

### Types and terms

Lean has one basic judgment: a term has a type. The line `n : ℕ` says that $n$ is a natural number. The line `s : ℂ` says that $s$ is a complex number. The line `χ : DirichletCharacter ℂ N` says that $\chi$ is a Dirichlet character modulo $N$ with values in $\mathbb{C}$. A function type is written with an arrow: `f : ℝ → ℝ` is a real function.

A proposition is also a type, of the kind `Prop`. A proof of a proposition is a term of that type. So the line `h : 1 / 2 < s.re` says that $h$ is a proof of $1/2 < \operatorname{Re} s$. This is the main rule for a reader. A hypothesis of a theorem is an argument of the theorem, and its name is the name of a proof. A theorem is a function: it takes the objects and the proofs of the hypotheses, and it gives a proof of the conclusion.

An implication $P \Rightarrow Q$ is the function type `P → Q`: a proof of it takes a proof of $P$ to a proof of $Q$. A universal statement $\forall x \in X, P(x)$ is written `∀ x : X, P x`: a proof of it takes a point $x$ and gives a proof of $P(x)$. The negation `¬P` is `P → False`, and `a ≠ b` is `a = b → False`.

### The half-plane statement

The statement that the argument of the source proves is a definition of `Statements.lean`. That file imports only Mathlib.

**Definition (The half-plane statement).** The proposition `DirichletLNonvanishingRightOfHalf` says: for every natural number $N \neq 0$, every Dirichlet character $\chi$ modulo $N$ and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$ and with $\chi \neq 1$ or $s \neq 1$, the value $L(s, \chi)$ is not $0$.

Lean: `DirichletLNonvanishingRightOfHalf` (Statements.lean).

**Example.** The Lean text is this.

```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

Read it from left to right. The word `def` makes a definition, and `: Prop` says that the defined object is a proposition. The binder `∀ (N : ℕ)` gives a natural number $N$. The square brackets in `[NeZero N]` mark an instance argument. Here it is a proof that $N \neq 0$, but the user of the statement does not write it: Lean finds it by instance search (Section 6). Then come a character $\chi$ and a point $s$. The two arrows give two hypotheses: $1/2 < \operatorname{Re} s$, and the disjunction $\chi \neq 1 \vee s \neq 1$. The conclusion is $L(s, \chi) \neq 0$. The function `DirichletCharacter.LFunction` is the Mathlib L-function. The character $1$ is the principal character modulo $N$.

**Remark (Formalization).** Mathlib defines $L(s, \chi)$ at every $s \in \mathbb{C}$, also at $s = 1$ for the principal character, where the classical function has a pole. There the Mathlib value is a junk value (Section 3), and it has no classical meaning. The hypothesis $\chi \neq 1 \vee s \neq 1$ removes exactly this point. The docstring of `LFunction_ne_zero_of_half_lt_re` in `Main.lean` says that "nothing is stated" there. For $N = 1$ the statement includes the Riemann zeta function, since the L-function of the character modulo $1$ is $\zeta$ in Mathlib.

The source proves this proposition in the last file of the argument.

**Example.** The theorem `New.grh` has this head, and its proof starts with one line.

```lean
theorem grh : DirichletLNonvanishingRightOfHalf := by
  intro q _ χ ρ hρ h_pole
```

Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

The line says that `grh` is a term of the type `DirichletLNonvanishingRightOfHalf`. The word `by` starts a proof in tactics. The tactic `intro` takes the bound objects of the statement and gives them names: the modulus `q`, an unnamed proof `_` of `NeZero q`, the character `χ`, the point `ρ`, a proof `hρ` of $1/2 < \operatorname{Re} \rho$, and a proof `h_pole` of $\chi \neq 1 \vee \rho \neq 1$. The rest of the proof must prove $L(\rho, \chi) \neq 0$. The names in the proof need not be the names in the statement. The source claims a proof of this theorem, and Volume 1 of this book explains the argument. Lean accepts it, if the reported checks hold.

### Hypotheses as arguments

A theorem is applied like a function. The reflection lemma of the source shows this.

**Lemma (Reflection of zeros).** Let $N \geq 1$, let $\chi$ be a Dirichlet character modulo $N$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$, $s \neq 1$ and $L(s, \chi) = 0$. Then $G_\chi(s) = 0$ or $L(1 - s, \chi^{-1}) = 0$. Here $G_\chi$ is the gamma factor of $\chi$ in Mathlib.

Lean: `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` (Lib/Analytic/ZeroSymmetry.lean).

Its Lean head is this.

```lean
lemma New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero (s : ℂ) (h_re : s.re ≠ 0)
    (h_ne_one : s ≠ 1) (hs : χ.LFunction s = 0) :
    χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by
```

The head does not show $N$ or $\chi$. They come from a line near the top of the file:

```lean
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
```

A `variable` line declares arguments for every declaration after it in the same section. A declaration gets such an argument if its statement uses it. So the full statement has the arguments `{N : ℕ}`, `[NeZero N]`, `(χ : DirichletCharacter ℂ N)`, `(s : ℂ)` and three proofs. The braces in `{N : ℕ}` mark an implicit argument: Lean computes $N$ from the type of $\chi$, and the user does not write it. Round brackets mark an explicit argument. The proof of this lemma and its use are in [the half-plane and the line](/chapter/half-plane-to-line/), where it is [Theorem](/decl/New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero/).

In `New/Main.lean` the source applies the lemma in one line:

```lean
    (gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero χ s h_pos.ne' hs1 h_zero).resolve_left h_gamma
```

The term in parentheses is the lemma applied to $\chi$, to $s$, and to three proofs: `h_pos.ne'` proves $\operatorname{Re} s \neq 0$ from $0 < \operatorname{Re} s$, `hs1` proves $s \neq 1$, and `h_zero` proves $L(s, \chi) = 0$. The result is a proof of the disjunction. Then `.resolve_left h_gamma` uses a proof `h_gamma` of $G_\chi(s) \neq 0$ to keep the right side. In the same file the line `h N χ s hlt (.inr hs1) h_zero` applies a proof `h` of the half-plane statement to $N$, $\chi$, $s$, a proof of $1/2 < \operatorname{Re} s$, the right case of the disjunction, and a proof of $L(s, \chi) = 0$. The result is a proof of `False`, because $L(s, \chi) \neq 0$ is the function type `LFunction χ s = 0 → False`.

### Section variables that are hypotheses

A `variable` line can also declare a hypothesis. The file `New/Main.lean` has these two lines at its top:

```lean
variable (h : DirichletLNonvanishingRightOfHalf)
include h
```

The line `include h` adds `h` to every declaration of the section, even where the statement does not mention it. So the lemma `New.zeta_zeros_on_line` has the Lean head `lemma New.zeta_zeros_on_line : RiemannZetaZerosOnLine`, but its type is `DirichletLNonvanishingRightOfHalf → RiemannZetaZerosOnLine`. This is why `Main.lean` can write `theorem riemannHypothesis : RiemannHypothesis := New.zeta_zeros_on_line New.grh`: the term applies the lemma to the proof `New.grh` of its hypothesis. Mathlib's `RiemannHypothesis` (Mathlib) and the source's `RiemannZetaZerosOnLine` have the same form after the definitions are unfolded, and Lean accepts the term, if the reported checks hold.

The opposite of `include` is `omit`. It takes a section variable out of one declaration.

**Lemma.** Let $N$ be a natural number, let $\chi$ be a Dirichlet character modulo $N$, let $M$ be a natural number, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$. Then $\prod_{p \mid M} (1 - \chi(p) p^{-s}) \neq 0$, where $p$ runs over the primes that divide $M$.

Lean: `New.prod_euler_factor_ne_zero` (Lib/Analytic/ZeroSymmetry.lean).

The Lean text is this.

```lean
omit [NeZero N] in
lemma New.prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h_re : s.re ≠ 0) :
    ∏ p ∈ M.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 := by
```

The line `omit [NeZero N] in` removes the hypothesis $N \neq 0$ from this lemma alone. So the lemma holds also for $N = 0$. The statement above has no hypothesis on $N$ for this reason. A reader who sees `omit` must remove the named argument from the list of the `variable` line.

*Proof.* Suppose that the factor at a prime $p \mid M$ vanishes. Then $\chi(p) = p^{s}$. For a character with values in $\mathbb{C}$, $\overline{\chi(p)} = \chi(p)^{-1}$. Take norms: $p^{\operatorname{Re} s} = |\chi(p)| = |\chi(p)^{-1}| = p^{-\operatorname{Re} s}$. Since $p \geq 2$, this gives $\operatorname{Re} s = -\operatorname{Re} s$, so $\operatorname{Re} s = 0$, against the hypothesis. $\square$

### What to take from the statements

A statement of the source is a type. Its arguments are the objects and the proofs of the hypotheses, in the order of the binders. Some arguments are hidden: implicit arguments in braces, instance arguments in square brackets, and section variables from a `variable` line, with `include` and `omit` lines that change the list. A reader who checks a sentence of this book against the Lean must collect all of them. Section 7 shows where to find them.
