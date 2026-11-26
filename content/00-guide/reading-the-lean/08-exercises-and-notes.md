---
title: Exercises and notes
lean:
  - New/Main.lean
  - New/Reduction/Zeros/PrimeError.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Apply the half-plane statement with $N = 1$ and the character $1$ modulo $1$. Show that it gives $\zeta(s) \neq 0$ for every $s$ with $\operatorname{Re} s > 1/2$ and $s \neq 1$. Then find the line of `New/Main.lean` that makes this step, and name each argument of the application.

*Hint.* The line is `le_of_not_gt fun hlt ↦ h 1 1 z hlt (.inr hz1) (by simpa using hz)`. The first `1` is the modulus, the second is the character. The instance `NeZero 1` is found by search. The last argument turns $\zeta(z) = 0$ into $L(z, 1) = 0$.

**Exercise 2.** Take $q = 1$ and $d = 7$, as in the example of Section 2. Compute the Lean values of $R_1(1/2)$, $R_1(0)$ and $R_1(-3)$ in terms of the constant $c_1 = \operatorname{Re} G_1(1)$. Which of the conventions of Section 3 does each computation use?

*Hint.* For $y < 1$ the set `Icc 1 ⌊y⌋₊` is empty, so both sums are $0$, also after the division by $y$. The answers are $\log 2 - c_1$, $-c_1$ and $-\log 3 - c_1$. The last one uses $\log(-3) = \log 3$.

**Exercise 3.** Show that in Mathlib the sum `∑' n : ℕ, (-1 : ℝ) ^ n / (n + 1)` is $0$, while the classical sum of the series is $\log 2$. Then give a statement about this series that is true in Lean and false classically, and one that is true in both.

*Hint.* In $\mathbb{R}$ a summable family is absolutely summable, and $\sum 1/(n+1)$ diverges. Then apply the convention for `∑'`. For the second part, compare an equation with $0$ and an inequality $|\sum'| \leq 1$.

**Exercise 4.** Let $z \in \mathbb{N}$. Show that `RankOneIndex z` has $20$ elements if $z \leq 10$ and $2z$ elements if $z \geq 10$. Deduce that the condition `HasLiftRank (RankOneIndex z)`, which asks that the type has $2z$ elements and that $z \geq 2$, holds if and only if $z \geq 10$.

*Hint.* The type is a disjoint union of `Fin 12`, `Fin 4`, `Fin 4` and `Fin (2 * z - 20)`, with truncated subtraction. For $2 \leq z < 10$ the condition asks $20 = 2z$.

**Exercise 5.** Let $c \in \mathbb{C}^\times$ and let $L$ and $C$ be two linear maps between complex vector spaces. Assume that $L = 0$ and $C = 0$. Show that $L = cC$ for every unit $c$. Use this to explain why the conclusion of [Theorem](/decl/New.Data.seesaw_identity/) of Section 3, with its unit $c$, does not imply that the lower chain of a Poincaré series is nonzero. Which statement of the source would a reader need for that?

*Hint.* The identity $0 = c \cdot 0$ holds for every $c$. The proof of the seesaw identity sets $u = 1$ when the natural constant is $0$. The reader needs a statement that the lower chain is nonzero on some form, from another part of the argument (finding F-068).

**Exercise 6.** Let $f, g : \mathbb{N} \to \mathbb{R}$ with $f =O[\mathrm{atTop}]\, g$. Show that $f + h =O[\mathrm{atTop}]\, g$ for every $h$ that is $0$ outside a finite set. Deduce that [Theorem](/decl/New.zero_density_quadTwist/) of Section 5 gives no bound for the count of bad primes up to any fixed $X$.

*Hint.* The filter `atTop` contains every cofinite set, and the definition of $O$ asks the bound only on a set of the filter.

**Exercise 7.** Find the declaration `New.Data.seesawConst` in the source. Name its file, the namespace block that contains it, and the `variable` line that gives its arguments. Then explain why `D.seesawConst⁻¹` is not a junk value, while `(D.seesawConst : ℂ)⁻¹` would be one if the constant were $0$.

*Hint.* Search for `def seesawConst`. The inverse of a unit is computed in the group `ℂˣ`. The inverse in `ℂ` uses the convention $0^{-1} = 0$, but the coercion of a unit is never $0$.

## Notes and references

The type theory of Lean, with types, terms, propositions as types, implicit arguments, structures, type classes and the axioms of choice, is explained in J. Avigad, L. de Moura, S. Kong and S. Ullrich, *Theorem Proving in Lean 4*, in the chapters "Dependent Type Theory", "Propositions and Proofs", "Quantifiers and Equality", "Tactics", "Structures and Records", "Type Classes" and "Axioms and Computation". The last chapter explains `Classical.choice`, the source of `Classical.choose` and `Classical.epsilon`, and why a proof of existence is not a datum. J. Avigad and P. Massot, *Mathematics in Lean*, explain filters, limits and the use of Mathlib for analysis in their chapter "Topology". The documentation of Mathlib gives the definition and the lemmas of each name of Mathlib that this chapter cites.

The conventions on junk values are those of Mathlib, and they are a design choice of the library, not a property of Lean. K. Buzzard explained the reasons for $x/0 = 0$ in the blog post "Division by zero in type theory: a FAQ" (2020) on the blog *Xena*. The general rule of Section 3, that a junk value makes a statement shorter and can make it weaker, is the reason for the remarks on the formalization in this book.

The source documents its own conventions in `grh/GUIDE.md`, Section 4 (conventions) and Section 5 (global settings), and its trust model in `grh/README.md`, sections "Build" and "Checks". This chapter follows those sections, and quotes them where it cites them. The findings cited here, F-017 to F-041, F-068 to F-075, F-110 and F-111, are in [the register of findings](/chapter/register-of-findings/) of this volume. Risks R5 (junk values and chosen objects hide the content of a statement) and R6 (constants that may be $0$) are from the plan of this book. The register marks F-019 (the speed settings on the pinned Lean) and F-068 (where the nonvanishing in the seesaw identity comes back) as open.

This chapter explains how to read the statements of the source. It does not say that the proof is correct. The source claims a proof of the five theorems, and Lean accepts it, if the reported checks hold.

Status: drafted by a model. No person has checked this chapter against the Lean source.
