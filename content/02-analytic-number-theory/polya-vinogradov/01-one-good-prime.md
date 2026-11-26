---
title: One good prime
lean:
  - Lib/Analytic/PolyaVinogradov.lean
  - Lib/Analytic/QuadraticTwist.lean
  - New/Reduction/Zeros/Criterion.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One good prime

This chapter proves the theorem that chooses the prime $d$ in [Landau's criterion](/chapter/landau-criterion/). Fix a modulus $N$, a box $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq H$ with $\beta > 1/2$, and a class $a$ modulo $N$ whose primes are all $\equiv 7 \bmod 8$ and prime to $N$. The theorem says that some prime $d$ of the class is *good*: no L-function $L(s, \xi\chi_K)$, with $\xi$ a character modulo $N$ and $\chi_K = (\cdot/d)$, vanishes in the box. The proof counts the bad primes. With $\beta = 1/2 + 9\delta$, at most $O(X^{1 - \delta/2})$ primes $d \leq X$ of the class are bad. Since the primes of the class are not that rare, a good prime exists.

The tools are classical. The first is the Pólya-Vinogradov inequality, which bounds a sum of a non-principal character over an interval by $\sqrt q \log q$, independently of the length. The second is quadratic reciprocity, which turns the twist $(n/d)$, a character in $n$, into the Jacobi symbol $(-d/n^\circ)$, a character in $d$; here $n^\circ$ is the odd part of $n$. The third is the theta series of [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/), Section 4, with the three lines theorem of Hadamard.

### Where the chapter sits

Volume 1 reduces the main theorem to a one-sided bound for a weighted prime sum $R_{q_0}$ ([the plan](/chapter/theorem-and-plan/)). The weights are $\Lambda(n)(1 - \chi_K(n))$ on $n \equiv 1 \bmod q_0$. Landau's lemma turns the one-sided bound into the absence of zeros, but only if the residues of the transform of $R_{q_0}$ have one sign near the real axis. The zeros of $L(s, \psi)$ give residues of one sign. The zeros of the twists $L(s, \psi\chi_K)$ give residues of the other sign. So the criterion needs one prime $d$ whose twists have no zeros in a box around the real segment $(\beta, \infty)$ and the point $\rho$ under study. This chapter supplies that $d$.

The result is used at exactly one place of the argument. The proof of the one-sided criterion, `New.LFunction_ne_zero_of_primeRemainder_le` ([Criterion.lean](lean:New/Reduction/Zeros/Criterion.lean#L55)), applies `New.exists_entireL_quadTwist_ne_zero` with $N = q_0$, the class $d_0 \bmod q_0$ and the height $H = |\operatorname{Im}\rho|$. No other file of the argument uses a result of this chapter by name. The Pólya-Vinogradov inequality and the count of bad primes are used only inside the background.

### The model case

Here is the simplest case of the idea. Take $N = 1$ and $\xi = 1$, so that the twists are the single characters $\chi_d = (\cdot/d)$. Suppose that $L(s, \chi_d)$ has a zero $s_0$ with $\operatorname{Re} s_0 \geq 1/2 + 9\delta$. The completed function $\Lambda(s, \chi_d)$ is, up to the factor $2$, the Mellin transform of the theta series $\theta_{\chi_d}$, and on the critical line it is at most twice the integral of $|\theta_{\chi_d}(u)|\,du/u$ over $u > d^{-1/2}$. A zero to the right of the line is a point where the function is small. The three lines theorem, applied to $\Lambda(s, \chi_d)$ times a mollifier, shows that this is possible only if the theta series is large on the line: the integral $J$ of $|\theta|$ over $u > 1/T$, with $T^2 \approx d$, must exceed $T^{2\delta}$.

Now let $d$ run over the primes up to $X$. By reciprocity, $\theta_{\chi_d}$ is the theta series with the coefficients $(-d/n^\circ)$. Its mean square over all $v \leq T^2$, in place of $d$, is small: expand the square, and the inner sums $\sum_v (-v/(nm)^\circ)$ are character sums of length $T^2$, which Pólya-Vinogradov bounds by about $\sqrt{nm}$. The theta weight makes $n$ and $m$ effectively at most $1/u \leq T$. So the sum over $v$ of the integrals $J$ is $O(T^{2 + \delta})$. Each bad $d$ contributes more than $T^{2\delta}$. So there are $O(T^{2 - \delta})$ bad $d$, and $T^2 \approx X$.

### The plan of the chapter

Section 2 states the classical Pólya-Vinogradov inequality and proves the form of the source, with the constant $2\sqrt q(1 + \log q)$. Section 3 treats Jacobi symbols as characters, the reciprocity law for $d \equiv 7 \bmod 8$, and the twists. Section 4 shows that a zero in the box makes the theta tail large. Section 5 proves the mean square bound. Section 6 counts the bad primes and chooses the good one. Section 7 explains why no step assumes a zero-free region or a density hypothesis. Section 8 has exercises and notes.

The chapter uses: the Gauss sum of a primitive character and the reduction to primitive characters ([Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/), Section 2); the theta series, their Mellin transforms and their symmetry (the same chapter, Section 4); the twist $\psi\chi_K$ and the fact that it is not principal (the same chapter, Section 2); the non-vanishing of $L(s, \chi)$ on $\operatorname{Re} s \geq 1$ and Dirichlet's theorem in the form that $\sum (\log p)/p$ diverges over an invertible class (Mathlib). It does not use [Landau's theorem](/chapter/landau-theorem/) or [the prime number theorem in progressions](/chapter/prime-number-theorem/).

### What the source proves, and how it compares

The classical theory has much stronger results. Jutila (1975) and Heath-Brown (1995) bound the number of zeros of $L(s, \chi_d)$ in a rectangle, summed over $d \leq X$, with explicit exponents; Heath-Brown's quadratic large sieve is the main tool. The source proves only the count of bad primes, and only for a fixed modulus $N$ and a fixed height $H$. The implied constant depends on $N$, $\delta$ and $H$, and the threshold for large $X$ is not explicit. This weak form is all that the criterion uses. Section 6 explains why one good prime is enough, and Section 8 compares the result with the literature.

Lean accepts the statements of this chapter, if the checks that the source reports hold. This book did not rerun them ([the claim and its status](/chapter/claim-and-status/)).
