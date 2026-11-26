---
title: Exercises
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $Z(s)$ be the function $s \mapsto \texttt{completedRiemannZeta}(s) / \Gamma_{\mathbb{R}}(s)$, without the update at $s = 0$. Compute $Z(0)$ with the conventions of Lean. Show that `RiemannHypothesis` with $Z$ in place of `riemannZeta` is false. Then show that $Z$ and `riemannZeta` agree at every $s \neq 0$.

*Hint.* $\Gamma_{\mathbb{R}}(0) = \pi^0 \Gamma(0)$, and Mathlib's $\Gamma$ is $0$ at its poles, so $Z(0)$ is a quotient by $0$. The point $s = 0$ is not of the form $-2(n+1)$, it is not $1$, and its real part is not $1/2$. For the last claim, use `riemannZeta_def_of_ne_zero`.

**Exercise 2.** Use the formula of Section 2 for `completedRiemannZeta` to show that `riemannZeta 1` $=$ `completedRiemannZeta₀ 1` $- 1$. With `riemannZeta_one` and $\gamma = 0.5772\ldots$, compute `riemannZeta 1` to four decimal places. Then show that $\lim_{s \to 1} (\zeta(s) - 1/(s-1)) = \gamma$, so that the junk value is not the constant term of the Laurent series.

*Hint.* $\Gamma_{\mathbb{R}}(1) = 1$, and in Lean $1/(1 - 1) = 1/0 = 0$. The value is $(\gamma - \log 4\pi)/2 \approx -0.9769$. For the limit, compare $\zeta(s)$ with $\int_1^\infty x^{-s}\,dx = 1/(s-1)$ for real $s > 1$, and let $s \to 1^+$.

**Exercise 3.** List the four Dirichlet characters modulo $8$ by their values at $3$, $5$ and $7$. For each one, find its conductor and its parity, as in the example of modulus $12$ in Section 3. Check that the number of primitive characters modulo $8$ is $\sum_{d \mid 8} \mu(d)\, \varphi(8/d)$.

*Hint.* The group of units is $\{1, 3, 5, 7\}$, and each unit has square $1$. A character that factors through $4$ has $\chi(5) = 1$, since $5 \equiv 1 \pmod 4$. Two characters are primitive. One of them is even and one is odd.

**Exercise 4.** Let `LSeriesStatement` be `DirichletLNonvanishingRightOfHalf` with `LSeries (χ ·) s` in place of `DirichletCharacter.LFunction χ s`. Prove that `LSeriesStatement` is false. Do the same for `DirichletLZerosOnLine`, with a nonprincipal character.

*Hint.* Take $N = 1$, $\chi = 1$ and $s = 3/4$ for the first. By `DirichletCharacter.LSeriesSummable_iff` the series is not summable at $s$, and by `LSeries.eq_zero_of_not_LSeriesSummable` its value is $0$. For the second take $\chi_{-4}$ and $s = 3/4$.

**Exercise 5.** Let `ClosedStrip` be `DirichletLZerosOnLine` with the hypothesis `0 ≤ s.re` in place of `0 < s.re`. Prove that `ClosedStrip` is false. Find all its counterexamples at $N = 2$ and $\chi = 1$.

*Hint.* By `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`, `LFunction 1 s` of level $2$ is $(1 - 2^{-s})\zeta(s)$ for $s \neq 1$. Take $s = 0$. The counterexamples at this level are the points $2\pi i k / \log 2$ for $k \in \mathbb{Z}$, together with the zeros of $\zeta$ on $\operatorname{Re} s = 0$. The latter set is empty, by the argument of Exercise 6.

**Exercise 6.** Prove that `RiemannHypothesis` is equivalent to the statement: every zero $s$ of `riemannZeta` with $0 < \operatorname{Re} s < 1$ has $\operatorname{Re} s = 1/2$. Use only the theorems of Mathlib that Section 2 names.

*Hint.* For $\operatorname{Re} s \geq 1$ use `riemannZeta_ne_zero_of_one_le_re`. Let $w \neq 0$ be a zero with $\operatorname{Re} w \leq 0$, and apply `riemannZeta_one_sub` at $s = 1 - w$. Its hypotheses hold, since $\operatorname{Re} s \geq 1$ and $s \neq 1$. Then $\Gamma(s) \neq 0$ and $\zeta(s) \neq 0$, so $\cos(\pi s / 2) = 0$. So $s$ is an odd integer at least $3$, and $w \in \{-2, -4, \ldots\}$. At $w = 0$ use `riemannZeta_zero`.

**Exercise 7.** Let $N \equiv 2 \pmod 4$. Prove that no Dirichlet character modulo $N$ is primitive. Conclude that `PrimitiveDirichletLZerosOnLine` says nothing at such $N$, while `DirichletLZerosOnLine` does.

*Hint.* Write $N = 2M$ with $M$ odd. Reduction gives a bijection $(\mathbb{Z}/N\mathbb{Z})^\times \to (\mathbb{Z}/M\mathbb{Z})^\times$. So every character modulo $N$ is `changeLevel` of a character modulo $M$. Compare the example of modulus $6$ in Section 3.

## Notes and references

Riemann stated the hypothesis in his paper of 1859 on the number of primes below a given bound. The functional equation of $\zeta$ by the theta relation, which Section 2 finds inside Mathlib's definition, is in Titchmarsh, *The Theory of the Riemann Zeta-Function*, Chapter II, and in Davenport, *Multiplicative Number Theory*, Chapter 8. Dirichlet characters, the principal character and the continuation of $L(s, \chi)$ are in Davenport, Chapter 4, and in Apostol, *Introduction to Analytic Number Theory*, Chapters 6 and 12. Apostol, Chapter 12, also gives the Hurwitz zeta function and the formula that writes $L(s, \chi)$ by Hurwitz zeta functions, which is Mathlib's definition. Primitive and induced characters and the conductor are in Davenport, Chapter 5. The functional equation for primitive characters is in Davenport, Chapter 9. The generalized Riemann hypothesis in the form for the L-functions of the general theory is in Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5.

The definitions of Mathlib that this chapter reads are in the files NumberTheory/LSeries/RiemannZeta.lean, NumberTheory/LSeries/HurwitzZetaEven.lean, NumberTheory/LSeries/HurwitzZeta.lean, NumberTheory/LSeries/ZMod.lean, NumberTheory/LSeries/DirichletContinuation.lean, NumberTheory/LSeries/Basic.lean, NumberTheory/DirichletCharacter/Basic.lean and NumberTheory/MulChar/Basic.lean of Mathlib, at the commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The value `riemannZeta_one` is in NumberTheory/Harmonic/ZetaAsymp.lean, and the nonvanishing on $\operatorname{Re} s \geq 1$ is in NumberTheory/LSeries/Nonvanishing.lean. The chapter quotes these statements from the text of the files, and Lean did not check the quotations.

The source states its trusted base in grh/GUIDE.md, section 1, and in grh/README.md, sections "Theorems" and "Checks". The file grh/NOTICE says that Statements.lean and the names and types of the five theorems are taken unchanged from Alpöge's proof. The deduction of the four forms from the half-plane form uses the reflection of zeros in Lib/Analytic/ZeroSymmetry.lean, which cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollaries 10.3 and 10.8. The list of citations of the source puts this file among those whose citations were not compared, and this book has not compared them. Volume 1, [from the half-plane to the line](/chapter/half-plane-to-line/), gives that deduction in full.

The method of pinning a function by a theorem on a half-plane and the identity theorem is standard in the reading of formal statements. It moves the trust from the construction of a function to the statement of a few theorems. It does not reach the values at the points where the function is not holomorphic. For those points this chapter computed the values from the definitions.

Status: drafted by a model. No person has checked this chapter against the Lean source.
