---
title: Newman's method and the generating function
lean:
  - Lib/Analytic/Primes.lean
  - Lib/Analytic/EntireLFunction.lean
decls:
  - New.hasSum_residueClass_one
  - New.norm_one_sub_mul_sum_div_totient_le
  - New.summable_vonMangoldt_not_prime
  - New.norm_term_le_exp_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Newman's method and the generating function

This section explains the method of the proof and sets up its generating function. It starts with Newman's analytic theorem, which gives the prime number theorem from the non-vanishing of $\zeta$ on the line $\operatorname{Re} s = 1$ alone. It then gives a model case of the argument of the source, for the primes with no condition of congruence. Finally it proves the four lemmas on Dirichlet series that the bound on the circle in Section 5 uses.

### Newman's analytic theorem

Newman found a short proof of the prime number theorem. Its analytic core is the following theorem. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104 (1997), 705 to 708, calls it the Analytic Theorem and gives a complete proof in one page. Newman's paper is *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87 (1980), 693 to 696.

**Theorem (Newman).** Let $f \colon [0, \infty) \to \mathbb{C}$ be bounded and locally integrable. Suppose that the function $g(z) = \int_0^\infty f(t)e^{-zt}\,dt$, which is holomorphic on $\operatorname{Re} z > 0$, extends holomorphically to an open set that contains $\operatorname{Re} z \geq 0$. Then $\int_0^\infty f(t)\,dt$ exists and equals $g(0)$.

The proof applies Cauchy's formula to $g(z)e^{zT}(1 + z^2/R^2)/z$ on a contour about $0$, and compares $g$ with the truncated transform $g_T(z) = \int_0^T f(t)e^{-zt}\,dt$. The factor $e^{zT}$ makes the truncation small on the right half of the contour. The factor $1 + z^2/R^2$ cancels the denominator on the circle $|z| = R$. The application to primes takes $f(t) = \psi(e^t)e^{-t} - 1$, or the same with $\theta$.

The source uses this idea in a finite form. It needs no limit. Its contour is one circle, its kernel is a Gaussian, and its conclusion is the existence of one prime in a window. The finite form makes the dependence on the modulus explicit.

### A model case: primes with no congruence

To see the argument with the fewest details, take $q = 1$, so that every prime counts. Let $L^\ast(s) = (s - 1)\zeta(s)$, an entire function with $L^\ast(1) = 1$. For $\operatorname{Re} z > 0$,
$$\sum_{n \geq 1}\frac{\Lambda(n)}{n^{1 + z}} = -\frac{\zeta'}{\zeta}(1 + z) = \frac{1}{z} - \frac{(L^\ast)'}{L^\ast}(1 + z) = \frac{F(z)}{z}, \qquad F(z) = 1 - z\frac{(L^\ast)'}{L^\ast}(1 + z).$$
The function $L^\ast$ does not vanish at $1$, so there are $\delta_0 > 0$ and $c_0$ with $L^\ast(1 + z) \neq 0$ and $|(L^\ast)'/L^\ast(1 + z)| \leq c_0$ for $|z| \leq \delta_0$. Let $X \geq \max(1/\delta_0, c_0)$. On the disc $|z| \leq 1/X$ the function $F$ is holomorphic and $|F(z)| \leq 1 + |z|c_0 \leq 2$.

Now fix $U \geq X^2$, and suppose that no prime $p$ has $\log p \in [U, U + X^2]$. Let $P(z) = \sum_{n < e^U}\Lambda(n)n^{-1-z}$, a finite sum, and put
$$G(z) = \bigl(F(z) - zP(z)\bigr)\exp\bigl(-E(z)\bigr), \qquad E(z) = 2 - Uz - \tfrac{X}{4}(1 + Xz)^2.$$
For $\operatorname{Re} z > 0$, the function $F(z) - zP(z)$ is $z$ times the tail $\sum_{n \geq e^U}\Lambda(n)n^{-1-z}$. By hypothesis, the terms of the tail with $\log n$ in the window come from prime powers only. Section 5 proves, in the general case, that $|G(z)| \leq 3U$ on the circle $|z| = 1/X$ if $X \geq 200$ and $X \geq C$, where $C \approx 1.96$ is the constant of the [lemma on prime powers](/decl/New.summable_vonMangoldt_not_prime/) below. At the centre, $E(0) = 2 - X/4$ and $F(0) = 1$, so $|G(0)| = e^{X/4 - 2}$. The maximum principle gives
$$e^{X/4 - 2} \leq 3U.$$
So every window $[U, U + X^2]$ with $U \geq X^2$ and $3U < e^{X/4 - 2}$ holds a prime. Put $W = X^2$. The condition reads $\sqrt{W} > 4\log(3U) + 8$. For large $U$ the window length $W = 17(\log U)^2$ is enough.

The model case needs only that $\zeta(s) \neq 0$ near $s = 1$, which is trivial, since $\zeta$ has a pole there. It gives a prime in $[x, x\exp(17(\log\log x)^2)]$ for large $x$. This is much weaker than the prime number theorem, and much stronger than Chebyshev's bounds, which give a prime in $[x, cx]$ for a fixed $c$. The general case is the same argument, with one change. For the modulus $q = Q^k$, the function $F$ involves all $\varphi(q)$ characters, and the disc on which none of their L-functions vanishes must be uniform in $k$. Section 3 gave this disc, of radius $1/X$, for all $q \leq X^A$.

### The generating function of a progression

Fix $q \geq 1$. Let $a_q(n) = \Lambda(n)$ if $n \equiv 1 \pmod q$ and $a_q(n) = 0$ otherwise. So $a_q \geq 0$, and $a_q(0) = 0$ since $\Lambda(0) = 0$. For a function $c$ on $\mathbb{N}$ and $s \in \mathbb{C}$ write $c(n)n^{-s}$ for the $n$-th term of its Dirichlet series, with the term $0$ at $n = 0$.

**Lemma (The generating function).** Let $q \geq 1$ and let $\operatorname{Re} z > 0$. The series $\sum_{n \geq 1} a_q(n)n^{-1-z}$ converges absolutely, and
$$\sum_{n \geq 1}\frac{a_q(n)}{n^{1 + z}} = \frac{F_q(z)}{z}, \qquad F_q(z) = \frac{1}{\varphi(q)}\Bigl(1 - z\sum_{\chi \bmod q}\frac{(L^\ast)'}{L^\ast}(1 + z, \chi)\Bigr).$$
Lean: `New.hasSum_residueClass_one` (Lib/Analytic/Primes.lean), with `ArithmeticFunction.vonMangoldt.residueClass` (Mathlib) for $a_q$.

*Proof.* By the orthogonality of the characters, $a_q(n) = \varphi(q)^{-1}\sum_\chi \chi(n)\Lambda(n)$, since $\bar\chi(1) = 1$. For $\operatorname{Re} s > 1$ and every $\chi$,
$$\sum_{n \geq 1}\frac{\chi(n)\Lambda(n)}{n^s} = -\frac{L'}{L}(s, \chi) = \frac{[\chi = \chi_0]}{s - 1} - \frac{(L^\ast)'}{L^\ast}(s, \chi),$$
where $[\chi = \chi_0]$ is $1$ for the principal character and $0$ otherwise. The second equality is the definition of $L^\ast$: for principal $\chi$, $\log L^\ast = \log(s - 1) + \log L$. The source proves this as `New.LSeriesHasSum_mul_vonMangoldt` (Lib/Analytic/EntireLFunction.lean). Sum over $\chi$ at $s = 1 + z$ and divide by $\varphi(q)$. The principal character gives $1/z$, and the result is $\varphi(q)^{-1}(1/z - \sum_\chi (L^\ast)'/L^\ast(1 + z, \chi)) = F_q(z)/z$. Absolute convergence holds since $|a_q(n)n^{-1-z}| \leq \Lambda(n)n^{-1-\operatorname{Re} z}$. $\square$

The term $1$ in $F_q$ is the pole of the principal L-function. It is the source of the main term: $F_q(0) = 1/\varphi(q)$, which is the density of the class $1$ among the classes prime to $q$.

**Lemma (A bound for the generating function).** Let $q \geq 1$, let $z \in \mathbb{C}$, and let $c(\chi) \in \mathbb{C}$ for each character $\chi$ modulo $q$, with $|z\,c(\chi)| \leq 1$ for every $\chi$. Then
$$\Bigl|\frac{1}{\varphi(q)}\Bigl(1 - z\sum_{\chi \bmod q} c(\chi)\Bigr)\Bigr| \leq 2.$$
Lean: `New.norm_one_sub_mul_sum_div_totient_le` (Lib/Analytic/Primes.lean).

*Proof.* There are $\varphi(q) \geq 1$ characters modulo $q$. So the left side is at most $(1 + \varphi(q))/\varphi(q) \leq 2$. $\square$

With $c(\chi) = (L^\ast)'/L^\ast(1 + z, \chi)$ and the [lemma on no zeros near 1](/decl/New.eventually_norm_logDeriv_entireL_le_near_one/), this gives $|F_q(z)| \leq 2$ on $|z| \leq 1/X$: there $|z c(\chi)| \leq (1/X) \cdot X = 1$.

### The prime powers

In the window, the hypothesis "no prime" leaves the prime powers $p^j$ with $j \geq 2$. Their contribution is controlled by one absolutely convergent series. Let $b(n) = \Lambda(n)$ if $n$ is not prime, and $b(n) = 0$ if $n$ is prime. So $b$ is supported on the prime powers $p^j$ with $j \geq 2$.

**Lemma (The prime powers).** The series $\sum_{n \geq 1} b(n)n^{-3/4}$ converges.
Lean: `New.summable_vonMangoldt_not_prime` (Lib/Analytic/Primes.lean).

*Proof.* $\sum_{n \leq x} b(n) = \psi(x) - \theta(x) = O(\sqrt{x})$, by Chebyshev's bound $\theta(y) = O(y)$ applied at $y = x^{1/j}$ for $j \geq 2$. Partial summation then gives convergence of $\sum b(n)n^{-\sigma}$ for every $\sigma > 1/2$, in particular at $\sigma = 3/4$. $\square$

Let $C = \sum_{n \geq 1} b(n)n^{-3/4}$. The source uses only that $C$ is finite. A short computation, which this book made and the source does not need, gives
$$C = \sum_p \log p\sum_{j \geq 2}p^{-3j/4} = \sum_p \frac{\log p}{p^{3/2} - p^{3/4}} \approx 1.96.$$
The primes $2$, $3$, $5$ and $7$ give about $0.61$, $0.38$, $0.21$ and $0.14$. So the condition $X \geq C$ of Section 5 is implied by the condition $X \geq 200$.

The exponent $3/4$ is a choice. Any exponent in $(1/2, 1)$ works. The proof in Section 5 compares the terms of the tail at $1 + z$ with the series of $b$ at $3/4$, and it needs the gap $1/4$ between $1$ and $3/4$ to absorb a loss of $e^{U/200}$.

### Moving a term to the real axis

The last lemma of this section compares one term of a Dirichlet series at a complex point with the term at a real point.

**Lemma (Moving a term).** Let $c \colon \mathbb{N} \to \mathbb{C}$, let $z \in \mathbb{C}$, let $\sigma, E \in \mathbb{R}$ and $n \in \mathbb{N}$, and suppose that $\log n \cdot (\sigma - \operatorname{Re} z) \leq E$. Then
$$|c(n)n^{-1-z}| \leq e^E\,|c(n)n^{-1-\sigma}|.$$
Lean: `New.norm_term_le_exp_mul` (Lib/Analytic/Primes.lean).

*Proof.* For $n = 0$ both terms are $0$. For $n \geq 1$, $|n^{-1-z}| = n^{-1-\operatorname{Re} z} = n^{-1-\sigma}\exp(\log n\,(\sigma - \operatorname{Re} z))$, and the exponent is at most $E$. $\square$

The lemma is used in two ways. With $\sigma = 1/U$ it compares the terms at $1 + z$ with those at $1 + 1/U$, whose sum is $F_q(1/U)\,U$. With $\sigma = -1/4$, applied to $b$, it compares them with the series of the prime powers at $3/4$.

**Remark (Formalization).** The source writes the Dirichlet series with Mathlib's `LSeries.term`, which is $c(n)/n^s$ for $n \geq 1$ and $0$ for $n = 0$, and the progression with Mathlib's `ArithmeticFunction.vonMangoldt.residueClass`, which takes values in $\mathbb{R}$. The generating function is stated as `LSeriesHasSum`, which asserts the summability and the value together. The point $3/4$ appears in Lean as `1 + -4⁻¹`, so that the same lemma on moving terms applies with $\sigma = -1/4$. The value of $C$ is not in the source.
