---
title: The three statements about L-functions
lean:
  - Statements.lean
  - Main.lean
decls:
  - DirichletLNonvanishingRightOfHalf
  - DirichletLZerosOnLine
  - PrimitiveDirichletLZerosOnLine
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three statements about L-functions

Statements.lean defines three propositions about Dirichlet L-functions. With Sections 3 and 4, each word in them has a known meaning. This section gives the Lean text of each one, says it in words, and names its classical form. Then it shows that the three propositions are equivalent, by short arguments from theorems of Mathlib, and that each one implies the zeta statement of Section 2.

### The classical generalized hypothesis

**Conjecture (Generalized Riemann hypothesis for Dirichlet L-functions).** Let $\chi$ be a Dirichlet character modulo $q \geq 1$. Every zero of $L(s, \chi)$ with $0 < \operatorname{Re} s < 1$ has real part $1/2$.

Many texts state it for primitive characters only, for example Iwaniec and Kowalski, Chapter 5. The remark "The primitive form is not weaker" below shows that the two forms are the same.

### The half-plane statement

**Definition (Nonvanishing right of one half).** The proposition `DirichletLNonvanishingRightOfHalf` says: for every $N \in \mathbb{N}$ with $N \neq 0$, every character $\chi$ of level $N$ with values in $\mathbb{C}$, and every $s \in \mathbb{C}$, if $1/2 < \operatorname{Re} s$, and $\chi \neq 1$ or $s \neq 1$, then `LFunction χ s` $\neq 0$.
Lean: `DirichletLNonvanishingRightOfHalf` (Statements.lean).

```lean
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

In classical words: no Dirichlet L-function has a zero in the half-plane $\operatorname{Re} s > 1/2$. The point $s = 1$ for the principal character is excluded, because classically it is a pole and in Lean its value is junk. This is the statement that the source proves first, as [New.grh](/decl/New.grh/). The other four theorems follow from it.

Two special cases show what it says. At $N = 1$ and $\chi = 1$ it says $\zeta(s) \neq 0$ for $\operatorname{Re} s > 1/2$ and $s \neq 1$, by `DirichletCharacter.LFunction_modOne_eq`. At $N = 4$ and $\chi = \chi_{-4}$ it says that the continuation of $1 - 3^{-s} + 5^{-s} - 7^{-s} + \cdots$ has no zero with $\operatorname{Re} s > 1/2$.

### The two statements on the line

**Definition (Zeros on the line).** The proposition `DirichletLZerosOnLine` says: for every $N \neq 0$, every character $\chi$ of level $N$ with values in $\mathbb{C}$, and every $s \in \mathbb{C}$, if $0 < \operatorname{Re} s$, $\operatorname{Re} s < 1$ and `LFunction χ s` $= 0$, then $\operatorname{Re} s = 1/2$.
Lean: `DirichletLZerosOnLine` (Statements.lean).

```lean
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

This is the conjecture above, for every character, primitive or not.

**Definition (Zeros on the line, primitive characters).** The proposition `PrimitiveDirichletLZerosOnLine` says the same as `DirichletLZerosOnLine`, with the added hypothesis that $\chi$ is primitive.
Lean: `PrimitiveDirichletLZerosOnLine` (Statements.lean).

```lean
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 →
      s.re = 1 / 2
```

This is the conjecture in the form for primitive characters. It is weaker than `DirichletLZerosOnLine` as a proposition, since it has one more hypothesis. The remark "The primitive form is not weaker" shows that it is not weaker in fact.

### Remarks on the three statements

**Remark (Formalization).** The binder `[NeZero N]` is a hypothesis $N \neq 0$. It is in square brackets so that Lean finds it by instance search. When the source applies the statement, as in `h N χ s hlt (.inr hs1) h_zero` in New/Main.lean, the proof of $N \neq 0$ is found from the context and is not written. For the reader the statements hold for every modulus $N \geq 1$. The case $N = 0$ is not a classical modulus, and Section 3 shows that `ZMod 0` is $\mathbb{Z}$.

**Remark (Formalization).** The hypothesis `χ ≠ 1 ∨ s ≠ 1` is the same as "if $\chi = 1$, then $s \neq 1$". It excludes one pair, the principal character of level $N$ at the point $1$, for each $N$. It does not exclude the principal character at other points. For $\chi = 1$ of level $N$ and $s \neq 1$, `LFunction 1 s` is $\zeta(s) \prod_{p \mid N} (1 - p^{-s})$ (Section 4). The factors have no zero with $\operatorname{Re} s > 0$. So at $\chi = 1$ the half-plane statement is exactly $\zeta(s) \neq 0$ for $\operatorname{Re} s > 1/2$, $s \neq 1$.

**Remark (The primitive form is not weaker).** Assume `PrimitiveDirichletLZerosOnLine`. Let $\chi$ have level $N$, and let $\chi^*$ be the primitive character of level $M$ that induces it (Section 3). By `DirichletCharacter.LFunction_changeLevel`, for $s \neq 1$ the function $L(s, \chi)$ is $L(s, \chi^*)$ times the factors $1 - \chi^*(p) p^{-s}$ for primes $p \mid N$. These factors have zeros only on $\operatorname{Re} s = 0$ (Section 4). So a zero of $L(s, \chi)$ with $0 < \operatorname{Re} s < 1$ is a zero of $L(s, \chi^*)$, and it has real part $1/2$. This gives `DirichletLZerosOnLine`. The source does not use this argument. It proves `DirichletLZerosOnLine` first, and gets the primitive form by dropping the hypothesis (Main.lean, lines 21 and 22).

**Remark (Formalization).** The upper bound `s.re < 1` in the statements on the line excludes nothing of interest. By `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, `LFunction χ s` $\neq 0$ for $\operatorname{Re} s \geq 1$, except at the pole. It does exclude the junk point $s = 1$ for $\chi = 1$, whose value Mathlib does not compute.

**Remark (Formalization).** The lower bound `0 < s.re` in the statements on the line is needed. Imprimitive characters have zeros on $\operatorname{Re} s = 0$, and an even primitive $\chi \neq 1$ has a zero at $s = 0$ (Section 4). So with $0 \leq \operatorname{Re} s$ the statement would be false. The statements say nothing about $\operatorname{Re} s \leq 0$, as the README of the source says (grh/README.md, line 22). Classically, the zeros there are the trivial zeros and the zeros of the Euler factors, and no conjecture is needed for them.

**Remark (Formalization).** None of the three propositions says anything about the order of a zero. They are statements about the zero set.

### How the four propositions relate

The following facts use only theorems of Mathlib and the functional equation. They are paper arguments, and this book does not claim that Lean checks them in this form, except for the two deductions that the source proves.

**Remark (The three statements are equivalent).** The three propositions about L-functions are equivalent.

1. The half-plane statement implies `DirichletLZerosOnLine`. Let $\chi$ have level $N$, and let $s$ be a zero with $0 < \operatorname{Re} s < 1$. The half-plane statement gives $\operatorname{Re} s \leq 1/2$. The functional equation gives a zero of $L(\cdot, \chi^{-1})$ at $1 - s$, since the gamma factor has no pole for $\operatorname{Re} s > 0$. The half-plane statement for $\chi^{-1}$ gives $\operatorname{Re}(1 - s) \leq 1/2$. So $\operatorname{Re} s = 1/2$. The source proves this as [New.zeros_on_line](/decl/New.zeros_on_line/).
2. `DirichletLZerosOnLine` implies the primitive form, since the primitive form has one more hypothesis.
3. The primitive form implies `DirichletLZerosOnLine`, by the remark above.
4. `DirichletLZerosOnLine` implies the half-plane statement. Let $1/2 < \operatorname{Re} s$, and $\chi \neq 1$ or $s \neq 1$. If $\operatorname{Re} s < 1$, a zero at $s$ would have $\operatorname{Re} s = 1/2$. If $\operatorname{Re} s \geq 1$, `DirichletCharacter.LFunction_ne_zero_of_one_le_re` gives $L(s, \chi) \neq 0$.

**Remark (The zeta statement is weaker).** Each of the three propositions implies `RiemannZetaZerosOnLine`. Take $N = 1$ and $\chi = 1$ in `DirichletLZerosOnLine`. By `DirichletCharacter.LFunction_modOne_eq` it gives the strip form of the Riemann hypothesis. Section 2 shows that the strip form is the Lean form. The source proves the implication from the half-plane statement as [New.zeta_zeros_on_line](/decl/New.zeta_zeros_on_line/). The converse is not known: the Riemann hypothesis for $\zeta$ is not known to imply it for other L-functions.

So the content of the source is one proposition, the half-plane statement, in four forms. Section 6 lists the five theorems that state these forms.
