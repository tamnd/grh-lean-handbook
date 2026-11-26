---
title: Primes in progressions for a fixed modulus
lean:
  - Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
  - Lib/Analytic/PrimeNumberTheorem/Tauberian.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Primes in progressions for a fixed modulus

This chapter gives the background for two analytic tools of the proof. The first is a zero-free region for a Dirichlet L-function near the line $\operatorname{Re} s = 1$, with a bound for the logarithmic derivative in that region. The second is a Tauberian theorem that turns such a region into an error term for a prime sum. Together they give the prime number theorem in an arithmetic progression, for a fixed modulus, with an error that saves every power of the logarithm. The chapter states the classical theory first: the zero-free region of de la Vallée Poussin, the prime number theorem for progressions, the theorem of Siegel and the theorem of Siegel and Walfisz. Then it states and proves the forms of the source. These forms are weaker than the classical ones. A remark on the formalization follows each difference and says why the argument does not need more.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof ends with a one-sided bound for the weighted prime remainder $R_q(y)$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/), at a first scale $x$. The bound at $x$ has a second scale $x_1$, near $\exp(x^{\varepsilon/6})$, and it contains the two terms $|R_{q_0}(x_1)|$ and $\log b \cdot |R_1(x_1)|$. These terms must be at most $x^{-2}$. Volume 1 shows this in [the prime number theorem at the cut-off](/chapter/main-inequality/#the-prime-number-theorem-at-the-cut-off). Its tool is [the prime number theorem for $R_q$](/decl/New.eventually_abs_primeRemainder_le/): for an odd prime $d$, a modulus $q \geq 1$ prime to $d$, and every natural number $B$,
$$|R_q(y)| \leq (\log y)^{-B} \qquad \text{for all large } y.$$
Volume 1 proves this theorem from two results of `Lib/Analytic/PrimeNumberTheorem`, which it recalls without proof. This chapter proves them. They are [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/) and [the Tauberian theorem](/decl/New.eventually_abs_le_inv_pow_of_transform/).

The zero-free region has a second use. Its quantitative form, [Lemma](/decl/New.norm_logDeriv_entireL_le/), is uniform in the modulus, and the source applies it to characters modulo $M^k$ with $k$ unbounded. This gives primes $p \equiv 1 \bmod M^k$ with $\log p$ in a window. Chapter 5 of this volume, [primes in windows](/chapter/primes-in-windows/), treats that use, and Volume 1 states the result in [the data exist](/chapter/data-exist/). This chapter proves the region and says what the uniform form needs.

### What the chapter uses

The chapter uses the L-functions of Mathlib and the entire L-function $\tilde L(s, \chi)$ of [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/). It does not repeat their definitions. It takes four results from Mathlib, and it states each one where it is used:

1. the inequality $|L(\sigma, \chi_0)^3 L(\sigma + it, \chi)^4 L(\sigma + 2it, \chi^2)| \geq 1$ for $\sigma > 1$;
2. the non-vanishing $L(s, \chi) \neq 0$ on $\operatorname{Re} s \geq 1$, except at the pole;
3. the three lines theorem of Hadamard, and the Cauchy estimates for the derivatives of a holomorphic function;
4. partial summation for a Dirichlet series, and the bound $\zeta(\sigma) \leq 1 + 1/(\sigma - 1)$ for $\sigma > 1$.

The chapter does not use the Hadamard product, the functional equation, Stirling's formula or the explicit formula. It does not use [Landau's theorem](/chapter/landau-theorem/) or the polar functions of [Chapter 2](/chapter/polar-functions/). This is a real difference from the textbooks, and Section 2 explains it.

### The letters

The modulus is $q \geq 1$; the source writes $N$. A character modulo $q$ is $\chi$, and $\chi_0$ is the principal character modulo $q$. We write $s = \sigma + it$. The source has one free parameter $l \geq 1$, which plays the role of $\log T$ in the textbooks: the regions of this chapter are cut off at $|s| \leq e^l$, and their width is a negative power of $l$. For a character $\chi$ we put
$$f_\chi(s) = \begin{cases} L(s, \chi) & \chi \neq \chi_0, \\ \dfrac{s - 1}{s} L(s, \chi_0) & \chi = \chi_0, \end{cases}$$
on $\operatorname{Re} s > 0$. So $f_\chi = \tilde L(\cdot, \chi)$ for $\chi \neq \chi_0$, and $f_{\chi_0}(s) = \tilde L(s, \chi_0)/s$. The factor $1/s$ keeps the size of $f_{\chi_0}$ equal to the size of $L(s, \chi_0)$ for large $|s|$. Section 3 gives the definition with its Lean name.

### A sketch of the proof

The proof has three steps.

*Step 1. Growth.* Partial summation against $\sum_{n \leq t} \chi(n) = \mu_\chi t + O(q)$, with $\mu_\chi$ the mean value of $\chi$, gives $|f_\chi(s)| \leq 1 + 4q|s|$ in $\operatorname{Re} s \geq 1/2$. To the right of $\operatorname{Re} s = 1 + 1/l$ one has $|f_\chi| \leq 1 + l$ from the series. The three lines theorem interpolates between the two lines. At distance $1/l$ to the left of $\operatorname{Re} s = 1$ the large bound $e^{3l}$ carries the weight $6/l$, and $(e^{3l})^{6/l} = e^{18}$ is a constant. So $|f_\chi(s)| \leq l^2$ for $\operatorname{Re} s \geq 1 - 1/l$ and $|s| \leq 3e^l$, if $q \leq e^l$ and $l \geq 10^{10}$. The Cauchy estimate on a disc of radius $1/(2l)$ gives $|f_\chi'| \leq 2l^3$.

*Step 2. The zero-free region.* For $\sigma = 1 + \eta$ the inequality of Mathlib, with the growth bounds for the two other factors, gives $\eta^3 \leq 256\, l^7 |f_\chi(s)|^4$. With $\eta = l^{-25}$ this is $|f_\chi(s)| \geq 12\, l^{-22}$. A step of length $2\eta$ to the left changes $f_\chi$ by at most $2l^3 \cdot 2\eta = 4\,l^{-22}$. So $|f_\chi| \geq 8\,l^{-22}$ on $\operatorname{Re} s \geq 1 - l^{-25}$, $|s| \leq e^l$, and $|f_\chi'/f_\chi| \leq l^{25}$ there. For a real character near $s = 1$ the inequality gives nothing. There the source uses $f_\chi(1) \neq 0$ and continuity. This is the only place where the size of $l$ depends on $\chi$ and not only on $q$.

*Step 3. The Tauberian theorem.* Let $R$ be a Lipschitz function on $[0, \infty)$ with Laplace transform $(F(s) - F(1))/(s - 1)$. Suppose that $F$ is holomorphic and at most $l^A$ in the region $\operatorname{Re} s \geq 1 - l^{-A}$, $|s| \leq e^l$. The $k$-th Taylor coefficient of the transform at a far real point $1 + H$, suitably normalized, is a mean of $R$ against a Gamma density. With $H = (k + 1)/u$, the density has mean $u$ and variance $u^2/(k + 1)$. So the coefficient is close to $R(u)$. The Cauchy estimate on the disc about $1 + H$ that reaches to $1 - l^{-A}$ makes the coefficient small. With $k + 1 \approx u^{2B + 4}$ and $l = (2B + 5)\log u$ this gives $|R(u)| \leq u^{-B}$.

### The plan of the chapter

Section 2 states the classical theory with its sources and compares it with what the proof needs. Section 3 proves the growth bounds. Section 4 proves the zero-free region. Section 5 proves the Tauberian theorem. Section 6 puts the two together, says exactly what the source proves and what it takes from Mathlib, and collects the remarks on the formalization that concern the whole chapter. Section 7 has exercises and notes.

All constants of the source are kept: $10^{10}$, $256$, the exponents $2$, $3$, $7$, $22$ and $25$, and the choices $k = \lfloor u^{2B + 4} \rfloor$ and $l = (2B + 5)\log u$. None of them is optimal. The source chose round numbers that make each inequality a short computation.

Lean accepts the results of this chapter if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
