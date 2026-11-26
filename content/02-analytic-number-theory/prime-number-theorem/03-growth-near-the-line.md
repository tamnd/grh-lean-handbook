---
title: Growth near the line
lean:
  - Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean
decls:
  - New.charMean
  - New.norm_sum_char_sub_le
  - New.norm_LSeries_char_le
  - New.regularL
  - New.regularL_eq
  - New.norm_regularL_le_linear
  - New.norm_LSeries_le_mul_norm_regularL
  - New.norm_regularL_le_sq
  - New.norm_deriv_regularL_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Growth near the line

This section proves upper bounds for $L(s, \chi)$ and its derivative near the line $\operatorname{Re} s = 1$. The zero-free region of Section 4 needs them twice: to bound the two outer factors of the inequality (2.1), and to bound the change of $L(s, \chi)$ under a short step to the left. The main result is $|f_\chi(s)| \leq l^2$ for $\operatorname{Re} s \geq 1 - 1/l$ and $|s| \leq 3e^l$, if the modulus is at most $e^l$ and $l \geq 10^{10}$.

### The textbook form

The classical bound is the following. Let $\tau = q(|t| + 2)$. For $\sigma \geq 1 - 1/\log \tau$ and $|t| \geq 1$, one has $L(s, \chi) \ll \log \tau$, and the same holds for $|t| < 1$ if $\chi \neq \chi_0$. The proof splits $\sum \chi(n) n^{-s}$ at $n = \tau$. The terms up to $\tau$ are at most $\sum_{n \leq \tau} n^{-\sigma} \ll \log \tau$, since $n^{1 - \sigma} \leq e$ there. The tail is bounded by partial summation against $\sum_{n \leq x} \chi(n) = O(q)$. The source cites Montgomery and Vaughan, Lemma 10.15, for a bound of this type near $\operatorname{Re} s = 1$ and away from the pole. It proves a weaker form, with $l^2$ in place of $\log(q|t|)$, by a different route: a crude bound from partial summation, and the three lines theorem. The square costs nothing in the argument, because Section 4 needs only a fixed power of $l$.

### The mean value of a character

**Definition (The mean value).** Let $\chi$ be a character modulo $q \geq 1$. Its mean value is
$$\mu_\chi = \frac{1}{q} \sum_{a \bmod q} \chi(a).$$

Lean: `New.charMean` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean), with `New.norm_charMean_le_one` and `New.charMean_eq_zero`.

So $|\mu_\chi| \leq 1$, since $|\chi(a)| \leq 1$. If $\chi \neq \chi_0$, then $\mu_\chi = 0$ by orthogonality. If $\chi = \chi_0$, then $\mu_\chi = \varphi(q)/q$.

**Lemma (Sums of a character).** Let $\chi$ be a character modulo $q \geq 1$ and let $x \geq 0$. Then
$$\Big|\sum_{1 \leq n \leq x} \chi(n) - \mu_\chi x\Big| \leq 2q.$$

Lean: `New.norm_sum_char_sub_le` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean), with `New.sum_range_char_add`.

*Proof.* Let $S(M) = \sum_{0 \leq n < M} (\chi(1 + n) - \mu_\chi)$ for $M \geq 0$. A sum of $\chi$ over $q$ consecutive integers runs once over all classes modulo $q$, so it is $q\mu_\chi$. Hence $S(M + q) = S(M)$. Each term of $S(M)$ has absolute value at most $2$, so $|S(M)| \leq 2M$. Let $M = \lfloor x \rfloor$. Then
$$\sum_{1 \leq n \leq x} \chi(n) - \mu_\chi x = S(M) - \mu_\chi (x - M) = S(M \bmod q) - \mu_\chi(x - M).$$
Here $|S(M \bmod q)| \leq 2(q - 1)$ and $|\mu_\chi(x - M)| \leq 1$. The sum is at most $2q - 1 \leq 2q$. $\square$

**Example.** Let $q = 4$ and let $\chi$ be the nonprincipal character, with $\chi(1) = 1$ and $\chi(3) = -1$. Then $\mu_\chi = 0$ and $\sum_{n \leq x} \chi(n) \in \{0, 1\}$. The lemma gives $8$, and the truth is $1$. For $\chi_0$ modulo $4$, $\mu_{\chi_0} = 1/2$ and $\sum_{n \leq x} \chi_0(n) - x/2$ stays in $[-1/2, 1]$. The constant $2q$ is crude, but only a bound linear in $q$ matters.

### The series to the right of the line

**Lemma (The series near the line).** Let $\chi$ be a character modulo $q$, let $A > 0$, and let $\operatorname{Re} s \geq 1 + 1/A$. Then
$$\Big|\sum_{n \geq 1} \chi(n) n^{-s}\Big| \leq 1 + A.$$

Lean: `New.norm_LSeries_char_le` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean).

*Proof.* Let $\sigma = \operatorname{Re} s > 1$. The series is dominated by $\zeta(\sigma) = \sum_{n \geq 1} n^{-\sigma}$. For $\sigma > 1$, Mathlib gives $\zeta(\sigma) - 1/(\sigma - 1) = 1 - \sigma T$ with $T \geq 0$ (`ZetaAsymptotics.zeta_limit_aux1` (Mathlib)). So $\zeta(\sigma) \leq 1 + 1/(\sigma - 1) \leq 1 + A$. $\square$

The inequality $\zeta(\sigma) \leq 1 + 1/(\sigma - 1)$ is the comparison of the sum with $1 + \int_1^\infty u^{-\sigma}\, du$.

### The regularized L-function

**Definition (The regularized L-function).** Let $\chi$ be a character modulo $q \geq 1$. Put
$$f_\chi(s) = \frac{\tilde L(s, \chi)}{s} \ \text{ if } \chi = \chi_0, \qquad f_\chi(s) = \tilde L(s, \chi) \ \text{ if } \chi \neq \chi_0.$$

Lean: `New.regularL` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean), with `New.differentiableAt_regularL`.

The function $f_\chi$ is holomorphic in $\operatorname{Re} s > 0$. For $\chi = \chi_0$ it is $(s - 1)L(s, \chi_0)/s$, and $f_{\chi_0}(1) = \tilde L(1, \chi_0) = \varphi(q)/q$. The factor $s - 1$ removes the pole. The factor $1/s$ keeps $f_{\chi_0}$ of the size of $L(s, \chi_0)$ when $|s|$ is large; without it, $\tilde L(s, \chi_0)$ grows like $|s|$ times $L$.

**Lemma (The regularized function as a series).** Let $\operatorname{Re} s > 1$, and let $\delta = 1$ if $\chi = \chi_0$ and $\delta = 0$ otherwise. Then
$$f_\chi(s) = \frac{s - \delta}{s} \sum_{n \geq 1} \chi(n) n^{-s}.$$

Lean: `New.regularL_eq` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean).

*Proof.* For $\operatorname{Re} s > 1$, $L(s, \chi)$ is the series (`DirichletCharacter.LFunction_eq_LSeries` (Mathlib)), and $s \neq 1$. Insert this in the definition. $\square$

A small inequality is used several times. If $\operatorname{Re} s \geq 1/2$, then $|s - \delta| \leq |s|$, since $(\sigma - 1)^2 \leq \sigma^2$ for $\sigma \geq 1/2$ (`New.norm_sub_ite_le`).

### A crude bound by partial summation

**Proposition (A linear bound).** Let $\chi$ be a character modulo $q \geq 1$, and let $\operatorname{Re} s \geq 1/2$. Then
$$|f_\chi(s)| \leq 1 + 4q|s|.$$

Lean: `New.norm_regularL_le_linear` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean), with `New.norm_integral_mul_cpow_le`, `New.differentiableAt_integral_mul_cpow` and `New.integrableOn_mul_cpow_of_bounded`.

*Proof.* Write $\sum_{1 \leq n \leq t} \chi(n) = \mu_\chi t + r(t)$. By [the lemma on sums of a character](/decl/New.norm_sum_char_sub_le/), $|r(t)| \leq 2q$ for $t \geq 0$. Put
$$\Phi(z) = \int_1^\infty r(t)\, t^{-z - 1}\, dt.$$
For $\operatorname{Re} z > 0$ the integral converges absolutely, $|\Phi(z)| \leq 2q/\operatorname{Re} z$, and $\Phi$ is holomorphic. (The source reads $\Phi(z)$ as the Mellin transform at $-z$ of $r$ cut off below $1$, and uses the holomorphy of Mellin transforms in Mathlib.)

For $\operatorname{Re} z > 1$, partial summation (`LSeries_eq_mul_integral'` (Mathlib)) gives
$$\sum_{n \geq 1} \chi(n) n^{-z} = z \int_1^\infty \Big(\sum_{n \leq t} \chi(n)\Big) t^{-z - 1}\, dt = z\Big(\Phi(z) + \frac{\mu_\chi}{z - 1}\Big),$$
since $\int_1^\infty \mu_\chi t^{-z}\, dt = \mu_\chi/(z - 1)$. Multiply by $(z - \delta)/z$. If $\chi = \chi_0$ this gives $f_\chi(z) = \mu_\chi + \Phi(z)(z - 1)$. If $\chi \neq \chi_0$, then $\mu_\chi = 0$, and it gives $f_\chi(z) = \Phi(z) z$. In both cases
$$f_\chi(z) = \mu_\chi + \Phi(z)(z - \delta) \qquad (\operatorname{Re} z > 1).$$
Both sides are holomorphic in the half-plane $\operatorname{Re} z > 0$, which is connected. By the identity theorem the formula holds in $\operatorname{Re} z > 0$. For $\operatorname{Re} s \geq 1/2$,
$$|f_\chi(s)| \leq |\mu_\chi| + \frac{2q}{\operatorname{Re} s}|s - \delta| \leq 1 + 4q|s|. \qquad \square$$

**Lemma (From the series to $f_\chi$).** Let $\chi$ be a character modulo $q$, let $l \geq 1$, and let $\operatorname{Re} s > 1$. If $\chi = \chi_0$, assume that $|s - 1| \geq 1/l$. Then
$$\Big|\sum_{n \geq 1} \chi(n) n^{-s}\Big| \leq 2l\,|f_\chi(s)|.$$

Lean: `New.norm_LSeries_le_mul_norm_regularL` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean).

*Proof.* By [the series form](/decl/New.regularL_eq/), the left side is $|s|/|s - \delta|$ times $|f_\chi(s)|$. If $\delta = 0$ the ratio is $1 \leq 2l$. If $\delta = 1$, then $|s| \leq |s - 1| + 1 \leq |s - 1| + l|s - 1| \leq 2l|s - 1|$. $\square$

The lemma is the reason for the hypothesis $|s - 1| \geq 1/l$ in Section 4. Near the pole, $L(s, \chi_0)$ is large and $f_{\chi_0}$ is not.

### The three lines theorem

**Theorem (Hadamard's three lines theorem).** Let $a < b$, and let $g$ be bounded and continuous on the closed strip $a \leq \operatorname{Re} z \leq b$ and holomorphic in its interior. If $|g| \leq M_a$ on $\operatorname{Re} z = a$ and $|g| \leq M_b$ on $\operatorname{Re} z = b$, then for $z$ in the strip, with $\theta = (\operatorname{Re} z - a)/(b - a)$,
$$|g(z)| \leq M_a^{1 - \theta} M_b^{\theta}.$$

Mathlib: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`.

It follows from the maximum principle applied to $g(z) M_a^{(z - b)/(b - a)} M_b^{(a - z)/(b - a)}$, times a factor $e^{\varepsilon z^2}$ that tends to $0$ at the ends of the strip, and the limit $\varepsilon \to 0$.

**Proposition (Growth near the line).** Let $\chi$ be a character modulo $q$. Let $l \geq 10^{10}$ and $q \leq e^l$. Then
$$|f_\chi(s)| \leq l^2 \qquad \text{for } \operatorname{Re} s \geq 1 - \frac{1}{l} \text{ and } |s| \leq 3e^l.$$

Lean: `New.norm_regularL_le_sq` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean).

*Proof.* Fix $s$, and let $a = \operatorname{Re} s + 2/l - 1/3$. Consider the strip $a \leq \operatorname{Re} z \leq a + 1/3$ and the function
$$g(z) = \frac{f_\chi(z)}{z - (s - 2)}.$$
The point $s$ lies in the strip, since $2/l \leq 1/3$. On the strip, $\operatorname{Re}(z - s + 2) \geq 2/l + 5/3 \geq 1$, so the denominator has absolute value at least $1$, and $g$ is holomorphic there: $\operatorname{Re} z \geq a \geq 2/3 + 1/l > 0$.

*The whole strip.* Let $\operatorname{Re} z \geq a$, so that $\operatorname{Re} z \geq 1/2$. By [the linear bound](/decl/New.norm_regularL_le_linear/) and $q \leq e^l$, $|f_\chi(z)| \leq 1 + 4e^l|z|$. Also $|z| \leq |z - (s - 2)| + |s| + 2 \leq 4e^l |z - (s - 2)|$, since $|s| \leq 3e^l$ and $|z - (s - 2)| \geq 1$. So
$$|g(z)| \leq 1 + 16 e^{2l} \leq e^{3l}.$$
In particular $g$ is bounded on the strip, and $|g| \leq e^{3l}$ on the left edge.

*The right edge.* There $\operatorname{Re} z = \operatorname{Re} s + 2/l \geq 1 + 1/l$. By [the series form](/decl/New.regularL_eq/) and $|z - \delta| \leq |z|$, $|f_\chi(z)| \leq |\sum \chi(n) n^{-z}|$, and by [the series near the line](/decl/New.norm_LSeries_char_le/) with $A = l$, this is at most $1 + l$. So $|g(z)| \leq 1 + l$.

*Interpolation.* At $z = s$, $\theta = (\operatorname{Re} s - a)/(1/3) = 1 - 6/l$. The three lines theorem gives
$$|g(s)| \leq (e^{3l})^{6/l} (1 + l)^{1 - 6/l} \leq e^{18}(1 + l) \leq 3^{18}(1 + l).$$
Since $|s - (s - 2)| = 2$, $|f_\chi(s)| = 2|g(s)| \leq 2 \cdot 3^{18}(1 + l)$. Now $2 \cdot 3^{18} < 8 \cdot 10^8$, and $l \geq 10^{10}$, so this is at most $l^2$. $\square$

The proof shows the role of each size. The large bound $e^{3l}$ on the left edge is harmless because its weight is $6/l$: the distance from $s$ to the right edge is $2/l$, and the strip has width $1/3$. The denominator $z - s + 2$ makes $g$ bounded on the strip, which the three lines theorem needs, and it changes $|f_\chi(s)|$ only by the factor $2$.

**Remark (Formalization).** The proposition asks $q \leq e^l$ and nothing else about $\chi$. So it is uniform in the modulus: one threshold $10^{10}$ serves all characters of all moduli up to $e^l$. The classical bound has $\log \tau$ in place of $l^2$; with $l \approx \log \tau$ the source loses one power of the logarithm. Section 4 uses the bound at points with $\operatorname{Re} s > 1$ and at points to the left of the line, and in both cases only a fixed power of $l$ matters.

### The derivative

**Theorem (Cauchy's estimate).** Let $f$ be holomorphic on a neighbourhood of the closed disc $|z - c| \leq r$, and let $|f| \leq M$ on the circle $|z - c| = r$. Then $|f^{(k)}(c)| \leq k!\, M/r^k$.

Mathlib: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, and `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` for $k = 1$.

**Corollary (The derivative near the line).** Let $\chi$ be a character modulo $q$. Let $l \geq 10^{10}$ and $q \leq e^l$. Then
$$|f_\chi'(s)| \leq 2l^3 \qquad \text{for } \operatorname{Re} s \geq 1 - \frac{1}{2l} \text{ and } |s| \leq 2e^l.$$

Lean: `New.norm_deriv_regularL_le` (Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean).

*Proof.* Every point $z$ of the closed disc of radius $1/(2l)$ about $s$ has $\operatorname{Re} z \geq 1 - 1/l$ and $|z| \leq 2e^l + 1/(2l) \leq 3e^l$. So $|f_\chi| \leq l^2$ on the circle, by [growth near the line](/decl/New.norm_regularL_le_sq/), and $f_\chi$ is holomorphic on the disc. Cauchy's estimate gives $|f_\chi'(s)| \leq l^2 \cdot 2l = 2l^3$. $\square$
