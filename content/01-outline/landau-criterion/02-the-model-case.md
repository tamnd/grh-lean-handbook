---
title: The model case
lean:
  - Lib/Analytic/Landau.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model case

This section proves Landau's theorem for Laplace transforms of positive measures, and applies it to the Riemann zeta function. The application is the model of the whole chapter: a one-sided bound for a remainder of the primes, weighted by $1/n - 1/x$, excludes the zeros of $\zeta$ to the right of the exponent of the bound. The section has no Lean statements. The source proves the general form of Section 3 and uses it only for the remainder $R_{q_0}$.

### Landau's theorem

Let $\mu$ be a positive Borel measure on $[0, \infty)$. For real $\sigma$ put
$$F(\sigma) = \int_0^\infty e^{-\sigma v}\, d\mu(v) \in [0, \infty].$$
The set of $\sigma$ with $F(\sigma) < \infty$ is a half-line, since $e^{-\sigma v}$ decreases in $\sigma$ for $v \geq 0$. Let $\sigma_c \in [-\infty, \infty]$ be its left end point, the abscissa of convergence. For $\operatorname{Re} s > \sigma_c$ the integral $F(s) = \int e^{-sv}\, d\mu(v)$ converges absolutely, $F$ is analytic, and $F^{(k)}(s) = \int_0^\infty (-v)^k e^{-sv}\, d\mu(v)$, by differentiation under the integral sign.

**Theorem (Landau).** Let $\mu$ be a positive Borel measure on $[0, \infty)$ whose abscissa of convergence $\sigma_c$ is finite. Then $F$ is not analytic at $\sigma_c$: there is no function analytic on a disc about $\sigma_c$ that is equal to $F$ on the part of the disc with $\operatorname{Re} s > \sigma_c$.

Not in the source. The source proves the local form for the moment generating function of a measurable $X \leq 0$, [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet_of_analyticAt/), and the abscissa form follows from it.

*Proof.* Suppose that $g$ is analytic on the disc $|s - \sigma_c| < \varepsilon$ and equal to $F$ where both are defined. Let $a = \sigma_c + \varepsilon/3$. The disc $|s - a| < 2\varepsilon/3$ lies in the disc of $g$, and $F = g$ on its right part. So the Taylor series of $F$ at $a$ converges in $|s - a| < 2\varepsilon/3$. Let $\sigma = a - \varepsilon/2 = \sigma_c - \varepsilon/6$. Then
$$g(\sigma) = \sum_{k \geq 0} \frac{(\sigma - a)^k}{k!} F^{(k)}(a) = \sum_{k \geq 0} \frac{(a - \sigma)^k}{k!} \int_0^\infty v^k e^{-av}\, d\mu(v),$$
and the series converges. Each term is a nonnegative real number, since $a - \sigma > 0$ and $\mu \geq 0$. By the theorem of Tonelli the sum is
$$\int_0^\infty \sum_{k \geq 0} \frac{((a - \sigma) v)^k}{k!} e^{-av}\, d\mu(v) = \int_0^\infty e^{-\sigma v}\, d\mu(v) = F(\sigma).$$
So $F(\sigma) < \infty$ with $\sigma < \sigma_c$, against the definition of $\sigma_c$. $\square$

The positivity of $\mu$ is used once: to change the order of the sum and the integral with no condition of convergence. Without positivity the theorem is false. The integral $\int_0^\infty e^{-\sigma v} |\sin v|\, dv$ is finite exactly for $\sigma > 0$, but the transform $\int_0^\infty e^{-sv} \sin v\, dv = 1/(s^2 + 1)$ is analytic at $0$.

The classical form is for Dirichlet series. Let $a_n \geq 0$, and let $\mu = \sum_n a_n \delta_{\log n}$. Then $F(s) = \sum a_n n^{-s}$. So a Dirichlet series with nonnegative coefficients has a singularity at the real point of its abscissa of convergence. This is the form in which Landau used the theorem.

We need the theorem in a form with a pole.

**Corollary (The residue at the abscissa).** Let $\mu$ and $\sigma_c$ be as in the theorem. Let $\Psi$ be meromorphic on a disc about $\sigma_c$ and equal to $F$ on the part of the disc with $\operatorname{Re} s > \sigma_c$. Suppose that $\Psi$ has at most a simple pole at $\sigma_c$, with residue $c$. Then $c$ is a positive real number.

Not in the source. The source proves the form with $\operatorname{Re} c \leq 0$ that extends the convergence, [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet/).

*Proof.* For real $x > \sigma_c$ near $\sigma_c$, the number $(x - \sigma_c)\Psi(x) = (x - \sigma_c)F(x)$ is real and $\geq 0$. It tends to $c$ as $x \to \sigma_c^+$. So $c$ is real and $c \geq 0$. If $c = 0$, then $\Psi$ has a removable singularity at $\sigma_c$, and the theorem gives a contradiction. So $c > 0$. $\square$

The source uses the contrapositive: if the continuation has, at each real point, at most a simple pole with residue of real part $\leq 0$, then the transform converges further to the left.

### The model: the zeta function

Let $\psi(x) = \sum_{n \leq x} \Lambda(n)$ and let $\gamma$ be Euler's constant. Define the remainder
$$R(x) = \sum_{n \leq x} \Lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \log x + 1 + \gamma, \qquad x \geq 1.$$
It is the remainder $R_{q}$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/) with the weight $\Lambda$ in place of $\Lambda(1 - \chi_K)$ and with $q = 1$. Since $\frac{1}{n} - \frac{1}{x} = \int_n^x t^{-2}\, dt$, we have
$$\sum_{n \leq x} \Lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) = \int_1^x \frac{\psi(t)}{t^2}\, dt, \qquad R'(x) = \frac{\psi(x) - x}{x^2}$$
for $x$ not a prime power. So $R$ is an average of $\psi(t) - t$, weighted by $t^{-2}$.

**Proposition (The model criterion).** Let $0 < \beta < 1$. Suppose that $R(x) \leq x^{\beta - 1}$ for all large $x$. Then $\zeta(s) \neq 0$ for every $s$ with $\operatorname{Re} s > \beta$.

Not in the source. The source proves the criterion only for its remainder $R_{q_0}$ and the L-functions modulo $q_0$, as `New.LFunction_ne_zero_of_primeRemainder_le` (New/Reduction/Zeros/Criterion.lean).

*Proof.* Let $Z(s) = (s - 1)\zeta(s)$. It is an entire function with $Z(1) = 1$ and $Z'(1)/Z(1) = \gamma$, from the Laurent expansion $\zeta(s) = 1/(s - 1) + \gamma + O(s - 1)$. For $\operatorname{Re} \rho > 0$ and $\rho \neq 1$, its zeros are those of $\zeta$, with the same orders.

Step 1: the transform. For $\operatorname{Re} s > 1$,
$$\int_n^\infty \Bigl(\frac{1}{n} - \frac{1}{y}\Bigr) y^{-s}\, dy = \frac{n^{-s}}{s - 1} - \frac{n^{-s}}{s} = \frac{n^{-s}}{s(s - 1)},$$
and $\int_1^\infty y^{-s}\log y\, dy = (s - 1)^{-2}$, $\int_1^\infty y^{-s}\, dy = (s - 1)^{-1}$. With $-\zeta'/\zeta = \sum \Lambda(n) n^{-s}$ and $-\zeta'/\zeta = -Z'/Z + 1/(s - 1)$, a short computation gives
$$\Phi(s) := \int_1^\infty R(y)\, y^{-s}\, dy = \frac{1}{s - 1}\Bigl(\frac{G(s)}{s} + 1 + \gamma\Bigr), \qquad G(s) = -\frac{Z'(s)}{Z(s)} - 1.$$
The right side is meromorphic on $\mathbb{C}$. It is the continuation of $\Phi$.

Step 2: the residues. At $s = 1$ the bracket is $-\gamma - 1 + 1 + \gamma = 0$, and it is analytic there. So $\Phi$ has no pole at $1$. This is why the constant is $1 + \gamma$. At $\rho \neq 0, 1$ with $\operatorname{Re} \rho > 0$, the function $-Z'/Z$ has residue $-\operatorname{ord}_\rho Z$. So
$$\operatorname{Res}_{s = \rho} \Phi(s) = \frac{-\operatorname{ord}_\rho Z}{\rho(\rho - 1)} = \frac{\operatorname{ord}_\rho \zeta}{\rho(1 - \rho)}.$$
For real $x$ with $0 < x < 1$ this is $\geq 0$. For real $x \geq 1$ it is $0$, since $\zeta$ has no zero on $\operatorname{Re} s \geq 1$.

Step 3: the positive measure. By the theorems of Chebyshev and Mertens, $R$ is bounded on $[1, \infty)$. With the hypothesis there is $C_0$ such that $y R(y) \leq C_0 y^\beta$ for all $y \geq 1$. Put $v = \log y$ and $d\mu(v) = (C_0 e^{\beta v} - e^v R(e^v))\, dv$ on $v > 0$. Then $\mu \geq 0$, and for $\operatorname{Re} s > 2$,
$$F(s) = \int_0^\infty e^{-sv}\, d\mu(v) = \frac{C_0}{s - \beta} - \Phi(s).$$

Step 4: Landau. Let $\sigma_c \leq 2$ be the abscissa of convergence of $\mu$. Suppose $\sigma_c > \beta$. The function $\Psi(s) = C_0/(s - \beta) - \Phi(s)$ is meromorphic on $\operatorname{Re} s > 0$. It is equal to $F$ for $\operatorname{Re} s > 2$, so by the identity theorem it is equal to $F$ on $\operatorname{Re} s > \sigma_c$ away from its poles. At $\sigma_c$ it has at most a simple pole, with residue $-\operatorname{ord}_{\sigma_c}\zeta / (\sigma_c(1 - \sigma_c)) \leq 0$ (or $0$ if $\sigma_c \geq 1$). This contradicts the corollary. So $\sigma_c \leq \beta$. Then $F$ is analytic on $\operatorname{Re} s > \beta$, and so is $\Phi = C_0/(s - \beta) - F$. So $\Phi$ has no pole at any $\rho$ with $\operatorname{Re} \rho > \beta$, and $\operatorname{ord}_\rho \zeta = 0$ there. $\square$

The converse holds too, so the proposition is an equivalence for the Riemann hypothesis: Exercise 1 asks for the proof. Under the Riemann hypothesis the explicit formula gives $R(x) = \sum_\rho x^{\rho - 1} / (\rho(1 - \rho)) + O(x^{-1})$, and the sum is $O(x^{-1/2})$ because $\sum_\rho |\rho|^{-2}$ converges.

### Why the weight 1/n - 1/x

The proof used the sign of the residues on the real segment $(\beta, 1)$. This subsection shows where this sign comes from, because the source depends on it. Compare the plain remainder $\psi(x) - x$. Its transform is
$$\int_1^\infty \bigl(\psi(y) - y\bigr) y^{-s-1}\, dy = -\frac{\zeta'(s)}{s\,\zeta(s)} - \frac{1}{s - 1},$$
with residue $-\operatorname{ord}_\rho \zeta / \rho$ at a zero $\rho$. This is negative at a real zero. So the same argument with the upper bound $\psi(x) - x \leq x^\beta$ meets a residue of the wrong sign at each real zero in $(\beta, 1)$. It works only with the extra fact that $\zeta$ has no real zero in $(0, 1)$. That fact is classical: $(1 - 2^{1 - \sigma})\zeta(\sigma) = \sum_{n \geq 1} (-1)^{n-1} n^{-\sigma} > 0$ for $0 < \sigma < 1$. For an L-function of a real character no such fact is known. A real zero near $1$ is a Siegel zero.

The weight $1/n - 1/x$ turns the sign. A zero $\sigma \in (0, 1)$ contributes $-x^\sigma/\sigma$ to $\psi(x) - x$, so it makes $\psi(x) - x$ negative. It contributes
$$-\int^x \frac{t^{\sigma - 2}}{\sigma}\, dt = \frac{x^{\sigma - 1}}{\sigma(1 - \sigma)}$$
to $R(x)$, so it makes $R(x)$ positive, because $\sigma - 1 < 0$. In words: by the prime number theorem with an error term, $R(x) = -\int_x^\infty (\psi(t) - t)\, t^{-2}\, dt$, and an upper bound for $R$ is a lower bound for $\psi(t) - t$ on average. A real zero pushes $\psi$ down, and so pushes $R$ up, and an upper bound for $R$ excludes it. The complex zeros give oscillating terms, and Landau's theorem excludes them.

The remainder of the source contains two families of L-functions with opposite signs. Section 4 shows what this costs.
