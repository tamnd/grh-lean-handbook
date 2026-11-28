---
title: Abscissae of convergence
lean:
  - Lib/Analytic/Landau.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Abscissae of convergence

This section defines the abscissa of convergence of a Dirichlet series and of a Laplace transform of a positive measure, and proves that the transform is analytic to the right of its abscissa, with derivatives under the integral sign. For coefficients of one sign the abscissa of convergence and the abscissa of absolute convergence are equal. This is the first place where the sign enters, and Landau's theorem in Section 3 uses it.

### Dirichlet series

A *Dirichlet series* is a series $\alpha(s) = \sum_{n \geq 1} a_n n^{-s}$ with complex coefficients $a_n$. If it converges at $s_0$, then it converges at every $s$ with $\operatorname{Re} s > \operatorname{Re} s_0$, uniformly on each sector $|\arg(s - s_0)| \leq \theta < \pi/2$, by partial summation. So there is $\sigma_c \in [-\infty, \infty]$, the *abscissa of convergence*, such that the series converges for $\sigma > \sigma_c$ and diverges for $\sigma < \sigma_c$. In the same way there is an *abscissa of absolute convergence* $\sigma_a$, the infimum of the real $\sigma$ with $\sum |a_n| n^{-\sigma} < \infty$. The sum $\alpha$ is analytic on $\sigma > \sigma_c$, and it can be differentiated term by term. In general $\sigma_c \leq \sigma_a \leq \sigma_c + 1$. These facts are in Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 1. This chapter needs them only for nonnegative coefficients, and in that case the proofs are short.

**Proposition (Nonnegative coefficients).** Let $a_n \geq 0$ for every $n$, and let $\sigma_c$ be the infimum of the real $\sigma$ such that $\sum a_n n^{-\sigma} < \infty$. Then:

1. For every $s$ with $\operatorname{Re} s > \sigma_c$, the series $\sum a_n n^{-s}$ converges absolutely. For real $\sigma < \sigma_c$ it diverges. So $\sigma_c = \sigma_a$.
2. The sum $\alpha(s)$ is analytic on $\operatorname{Re} s > \sigma_c$, and $\alpha^{(k)}(s) = \sum_n a_n (-\log n)^k n^{-s}$ there, for every $k \geq 0$.
3. $|\alpha(\sigma + it)| \leq \alpha(\sigma)$ for every real $\sigma > \sigma_c$ and real $t$.

Not in the source. The source applies Landau's lemma to a measure only, the measure of [Lemma](/decl/New.exists_measure_laplace_eq/), and never to a Dirichlet series.

*Proof.* For $\operatorname{Re} s = \sigma$ we have $|a_n n^{-s}| = a_n n^{-\sigma}$. If $\sigma > \sigma_c$, there is $\sigma'$ with $\sigma_c < \sigma' < \sigma$ and $\sum a_n n^{-\sigma'} < \infty$, and $a_n n^{-\sigma} \leq a_n n^{-\sigma'}$. This gives 1 and 3. For 2, fix $\delta > 0$. On the half-plane $\operatorname{Re} s \geq \sigma_c + \delta$ the terms are bounded by $a_n n^{-\sigma_c - \delta}$, a convergent series of constants. So the series converges uniformly there, by the Weierstrass test. A uniform limit of analytic functions is analytic, and the derivatives converge uniformly on compact sets to the derivative of the limit. $\square$

So for nonnegative coefficients there is one abscissa, and it is read off the real axis.

**Example (Four series).** (a) $\zeta(s) = \sum n^{-s}$ has $\sigma_c = 1$. (b) The prime zeta function $P(s) = \sum_p p^{-s}$ has $\sigma_c = 1$, since $\sum_p 1/p$ diverges and $\sum_p p^{-\sigma} \leq \zeta(\sigma)$ for $\sigma > 1$. (c) $\log \zeta(s) = \sum_n \Lambda(n) (\log n)^{-1} n^{-s}$ for $\operatorname{Re} s > 1$, with coefficients $\geq 0$, has $\sigma_c = 1$, since its value at real $\sigma \to 1^+$ tends to $\infty$. (d) The series $\sum_n 2^{-n} n^{-s}$ converges for every $s$, so $\sigma_c = -\infty$. Its sum is entire.

**Example (Coefficients of both signs).** For $\eta(s) = \sum (-1)^{n - 1} n^{-s}$ we have $\sigma_c = 0$ and $\sigma_a = 1$. The series converges for $\operatorname{Re} s > 0$ by partial summation, since its partial sums of coefficients are $0$ or $1$. It converges absolutely only for $\operatorname{Re} s > 1$. So part 1 of the proposition fails without the sign.

### Laplace transforms of positive measures

A Dirichlet series is a Laplace transform. Let $\mu = \sum_n a_n \delta_{\log n}$, where $\delta_x$ is the unit mass at $x$. Then
$$\int_0^\infty e^{-sv}\, d\mu(v) = \sum_n a_n e^{-s \log n} = \sum_n a_n n^{-s}.$$
A Mellin integral is a Laplace transform too. Let $A$ be a measurable function on $[1, \infty)$. The substitution $x = e^v$ gives
$$\int_1^\infty A(x)\, x^{-s}\, dx = \int_0^\infty A(e^v)\, e^{(1 - s)v}\, dv = \int_0^\infty e^{-sv}\, d\mu(v), \qquad d\mu(v) = A(e^v)\, e^v\, dv.$$
If $A \geq 0$ the measure is positive. The source works with $E(v) = R(e^v)$ and the transform $\int_0^\infty E(v) e^{(1 - s)v}\, dv$, which is the second form ([Polar functions](/chapter/polar-functions/#polar-functions)).

So let $\mu$ be a positive Borel measure on $[0, \infty)$, and let $F(\sigma) = \int_0^\infty e^{-\sigma v}\, d\mu(v) \in [0, \infty]$ for real $\sigma$. Since $e^{-\sigma v}$ decreases in $\sigma$ for $v \geq 0$, the set of $\sigma$ with $F(\sigma) < \infty$ is a half-line. Its left end point is the abscissa of convergence $\sigma_c \in [-\infty, \infty]$. For complex $s$ with $\operatorname{Re} s > \sigma_c$, put $F(s) = \int_0^\infty e^{-sv}\, d\mu(v)$. The integral converges absolutely, since $|e^{-sv}| = e^{-\sigma v}$.

**Proposition (Analyticity of the transform).** Let $\mu$ be a positive Borel measure on $[0, \infty)$ with abscissa of convergence $\sigma_c < \infty$. Then $F$ is analytic on $\operatorname{Re} s > \sigma_c$. For every $k \geq 0$ and every such $s$, the function $v^k e^{-\sigma v}$ is $\mu$-integrable and
$$F^{(k)}(s) = \int_0^\infty (-v)^k e^{-sv}\, d\mu(v).$$
For real $\sigma > \sigma_c$ the sign of $F^{(k)}(\sigma)$ is $(-1)^k$ (or $F^{(k)}(\sigma) = 0$), and $|F(\sigma + it)| \leq F(\sigma)$.

Mathlib: `ProbabilityTheory.analyticOn_complexMGF` and `ProbabilityTheory.iteratedDeriv_complexMGF`, for the moment generating function $s \mapsto \int e^{sX}\, d\mu$ on the strip where it converges; the source uses them in this form.

*Proof.* Fix $\delta > 0$ and put $\sigma_0 = \sigma_c + \delta$. Since $v^k e^{-\delta v/2} \leq (2k/(e\delta))^k$ for $v \geq 0$, we have $v^k e^{-\sigma v} \leq (2k/(e\delta))^k e^{-(\sigma_c + \delta/2)v}$ for $\sigma \geq \sigma_0$, and the right side is $\mu$-integrable. So the integrand $(-v)^k e^{-sv}$ has an integrable bound that does not depend on $s$ in the half-plane $\operatorname{Re} s \geq \sigma_0$. By the theorem on differentiation under the integral sign (dominated convergence applied to the difference quotients, with the bound for $k + 1$), $F$ is complex differentiable at each $s$ with $\operatorname{Re} s > \sigma_0$, with the derivative $\int (-v) e^{-sv}\, d\mu$. Induction on $k$ gives the formula for $F^{(k)}$. Since $\delta$ is arbitrary, this holds on $\operatorname{Re} s > \sigma_c$. At real $\sigma$ the integrand $(-v)^k e^{-\sigma v}$ has the sign $(-1)^k$, and $|\int e^{-(\sigma + it)v}\, d\mu| \leq \int e^{-\sigma v}\, d\mu$. $\square$

So $F$ restricted to $(\sigma_c, \infty)$ is completely monotone: $(-1)^k F^{(k)} \geq 0$. This is the property that Landau's theorem uses. The Taylor series of $F$ at a real point $a > \sigma_c$ is
$$\sum_{k \geq 0} \frac{F^{(k)}(a)}{k!}(s - a)^k = \sum_{k \geq 0} \frac{(a - s)^k}{k!} \int_0^\infty v^k e^{-av}\, d\mu(v),$$
and at a real $s = \sigma < a$ every term is $\geq 0$.

**Example (Transforms in closed form).** (a) For $d\mu = dv$ on $(0, \infty)$ we get $F(s) = 1/s$ and $\sigma_c = 0$, with a pole at $0$. (b) For $d\mu = e^{\beta v}\, dv$ we get $F(s) = 1/(s - \beta)$ and $\sigma_c = \beta$. (c) For $d\mu = e^{v}(1 + v^2)^{-1}\, dv$ we get $\sigma_c = 1$, and $F(1) = \int_0^\infty (1 + v^2)^{-1}\, dv = \pi/2$ is finite. The function $F$ is continuous on the closed half-plane $\operatorname{Re} s \geq 1$, so it has no pole at $1$. Landau's theorem says that it is still not analytic at $1$ (Exercise 4). (d) For $\mu$ with compact support, or for $d\mu = e^{-v^2}\, dv$, we get $\sigma_c = -\infty$, and $F$ is entire.

### The real axis decides

The last part of the proposition, $|F(\sigma + it)| \leq F(\sigma)$, is the simplest form of the dominance of the real axis. A second form concerns the point $\sigma_c$ itself, when $\sigma_c$ is finite. If $F(\sigma)$ stays bounded as $\sigma \to \sigma_c^+$, then $F(\sigma_c) < \infty$ by monotone convergence, and the integral converges absolutely on the closed half-plane $\operatorname{Re} s \geq \sigma_c$. So the integral converges at $\sigma_c$ if and only if $F$ is bounded on $(\sigma_c, \sigma_c + 1)$. A singularity at $\sigma_c$ need not be a point where $F$ is unbounded: Example (c) is bounded there.

A general Dirichlet series behaves otherwise. Its abscissa of convergence can lie to the left of its abscissa of absolute convergence, as for $\eta$. Its sum can be analytic at every point of the line $\sigma = \sigma_c$, as for $\eta$ again. And the location of $\sigma_c$ is not decided by the values on the real axis. Landau's theorem in the next section completes the picture for coefficients of one sign: the point $\sigma_c$ itself is a singularity.
