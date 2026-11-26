---
title: What the proof uses
lean:
  - Lib/Analytic/QuadraticTwist.lean
  - Lib/Analytic/PolyaVinogradov.lean
  - Lib/Analytic/DirichletTheta.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the proof uses

A reader who checks the reduction of GRH to a one-sided bound must know that the choice of the prime $d$ does not assume what the argument wants to prove. This section lists the inputs of the chapter. It describes the dependencies of the source; it does not claim that the proof is correct.

### The local files

The file Lib/Analytic/QuadraticTwist.lean imports Lib.Analytic.DirichletTheta and Lib.Analytic.EntireLFunction. The transitive closure of its imports, without Mathlib, contains thirteen other files of the source:

1. Lib.Analytic.DirichletTheta, Lib.Analytic.PolyaVinogradov, Lib.Analytic.ZeroSymmetry and Lib.Analytic.EntireLFunction. These are the theta series of [Dirichlet L-functions](/chapter/dirichlet-l-functions/), Section 2 of this chapter, the symmetry of the zeros, and the entire L-function with the twists.
2. Lib.General.NumberTheory.ImaginaryQuadraticField, which defines `New.quadTwist` and `New.entireL`, and the files that it needs: Lib.General.NumberTheory.EmbeddingsAndDifferent, Lib.Adelic.Adeles.Basic, Lib.Adelic.Adeles.AdditiveCharacter, Lib.Adelic.QuotientMeasure.Basic, Lib.General.Groups.CongruenceSubgroups and Lib.General.Measure.IdempotentKernel.
3. Lib.Base and Lib.Speed, which set options and notation.

No file under New/ is in the closure. In particular the closure contains no file on the prime number theorem, on zero-free regions, on the explicit formula, or on the one-sided bound of the main argument. So the statements of this chapter cannot depend on the hypotheses or the conclusions of the reduction. The import closure is a fact about the source that anyone can recompute from the `import` lines; the list above was computed from them at the pinned commit.

The adelic files enter only because Lib.General.NumberTheory.ImaginaryQuadraticField defines the twist next to other objects of the imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$. The proofs of this chapter use only the formula for the values of the twist.

### The Mathlib inputs

The chapter uses these results of Mathlib. Each is a standard theorem.

1. The analytic continuation of $L(s, \chi)$ to an entire function for $\chi \neq \chi_0$, and the Dirichlet series for $\operatorname{Re} s > 1$ (`DirichletCharacter.differentiable_LFunction` (Mathlib), `DirichletCharacter.LFunction_eq_LSeries` (Mathlib)).
2. The non-vanishing $L(s, \chi) \neq 0$ for $\operatorname{Re} s \geq 1$, except at the pole of $\chi_0$ (`DirichletCharacter.LFunction_ne_zero_of_one_le_re` (Mathlib)). Section 4 uses it twice: on the line $\operatorname{Re} s = 2$, and to get $\operatorname{Re} s < 1$ at a zero.
3. Hadamard's three lines theorem (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (Mathlib)).
4. The Jacobi symbol and its reciprocity law, the formula for $(2/m)$, and the Legendre symbol (`jacobiSym.quadratic_reciprocity'` (Mathlib), `jacobiSym.at_two` (Mathlib), `legendreSym` (Mathlib)).
5. The divergence of $\sum_{p \equiv a}\log p/p$ for an invertible class, which is the analytic core of Dirichlet's theorem on primes in progressions (`ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div` (Mathlib)).
6. Partial summation for Dirichlet series and the convergence of the derivative series (`LSeriesSummable_of_sum_norm_bigO` (Mathlib), `LSeriesSummable_logMul_of_lt_re` (Mathlib)).
7. The Gamma function: $\Gamma_{\mathbb R}(s) \neq 0$ for $\operatorname{Re} s > 0$ (`Complex.Gammaℝ_ne_zero_of_re_pos` (Mathlib)).

The functional equation of $L(s, \chi)$ enters only through the symmetry of the theta series, which the source proves by Poisson summation in [theta series](/chapter/dirichlet-l-functions/).

### What the chapter does not use

1. No zero-free region near $\operatorname{Re} s = 1$, and no bound on exceptional zeros. A Siegel zero of some twist would only make one prime $d$ bad. The count of Section 6 shows that few primes are bad, whatever the zeros of the individual L-functions are.
2. No prime number theorem for progressions. Dirichlet's divergence is enough, as Section 6 explains.
3. No large sieve. Section 5 replaces it with Pólya-Vinogradov for Jacobi symbols, because the sums are short compared with the range of $v$.
4. No information on the zeros of $L(s, \chi)$ for the characters $\chi$ modulo $q_0$ of the criterion. The chapter is about the twists $\xi\chi_K$ only.

### The weak points of the estimate

The estimate of Section 6 is weak in two ways. Both are harmless for the argument.

First, the exponent. A classical zero density estimate counts zeros with multiplicity, and its saving grows as $\sigma$ moves from $1/2$ to $1$. The source gives the saving $X^{-\delta/2}$ for the number of bad primes up to $X$, with $\delta = (\beta - 1/2)/9$. This is far from the truth: on average over $d$ one expects that a positive proportion of the twists have no zero in the box at all, and under GRH no prime is bad. The criterion needs only that the bad primes do not contain all the primes of the class, and any power saving gives that, because $\sum_{p \equiv a}\log p/p$ diverges.

Second, the constants. All constants are existential in the Lean statements, and some come from `choose`. The threshold for $T$ in Section 4 comes from a compactness argument: the minimum of $|\Gamma_j|$ on a rectangle. So the source gives no explicit $d$, and no bound for the least good $d$ in terms of $q_0$, $\beta$ and $H$. The criterion needs only the existence of $d$, because its hypothesis is a bound for all primes $d$ of the class, and its conclusion does not mention $d$.

Third, a point of logic rather than size. The theorem on the choice of the prime is proved by contradiction, and the contradiction uses a divergent series. So the proof is not constructive, in the sense that it gives no algorithm that finds $d$. This is normal in Lean, whose logic is classical, and it does not affect the use: the criterion is itself an existence statement about zeros.
