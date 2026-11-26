---
title: The prime number theorem at the cut-off
lean:
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/PrimeNumberTheorem/Tauberian.lean
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.countError
  - New.abs_countError_le
  - New.primeRemainder_eq_integral_countError_sub
  - New.abs_primeRemainder_sub_le
  - New.abs_primeRemainder_exp_sub_le
  - New.eventually_norm_logDerivMean_div_le
  - New.eventually_abs_primeRemainder_le
  - New.tendsto_primeRemainder
  - New.eventually_abs_primeRemainder_exp_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The prime number theorem at the cut-off

The bound at $x$ has two terms at the second cut-off $x_1$: $|R_{q_0}(x_1)|$ and $\log b \cdot |R_1(x_1)|$. This section shows that both are at most $x^{-2}$ when $\log x_1 \geq x^{\varepsilon/12}$. The tool is the prime number theorem for the weighted count, for a fixed modulus, with an error that saves every power of $\log y$. The only analytic input about zeros is a weak zero-free region near the line $\operatorname{Re} s = 1$.

### The textbook form

The classical statement is the Siegel-Walfisz theorem for a fixed modulus. For $(a, q) = 1$ and every $B > 0$,

$$\sum_{n \leq y, \; n \equiv a \bmod q} \Lambda(n) \;=\; \frac{y}{\varphi(q)} + O_{q, B}\big( y (\log y)^{-B} \big).$$

The source cites Montgomery and Vaughan, *Multiplicative Number Theory I*, 2007, Corollary 11.19, for this theorem. It needs the theorem for the weights $\lambda_q(n) = \Lambda(n)(1 - \chi_K(n))$ on $n \equiv 1 \pmod q$, and for the smoothed sum in $R_q$. It proves its own form by a Tauberian argument.

### The count and its error

**Definition.** Let $d$ be a prime and $q \geq 1$. The error in the weighted count is

$$\mathcal{E}_q(w) \;=\; \sum_{0 \leq n \leq w} \lambda_q(n) - \frac{w}{\varphi(q)}.$$

Lean: `New.countError` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

**Lemma (Chebyshev's bound for the error).** For $w \geq 0$, $|\mathcal{E}_q(w)| \leq 13 w$.

Lean: `New.abs_countError_le` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* Since $0 \leq 1 - \chi_K(n) \leq 2$, $0 \leq \lambda_q(n) \leq 2\Lambda(n)$. Chebyshev's bound $\sum_{n \leq w} \Lambda(n) \leq (\log 4 + 4) w \leq 6w$ (`Chebyshev.psi_le_const_mul_self` (Mathlib)) gives $0 \leq \sum_{n \leq w} \lambda_q(n) \leq 12 w$. Also $0 \leq w/\varphi(q) \leq w$. The difference of two numbers in $[0, 12w]$ and $[0, w]$ has absolute value at most $12w + w = 13w$. $\square$

**Lemma (The remainder is an integral).** For $y \geq 1$,

$$R_q(y) \;=\; \int_1^y \frac{\mathcal{E}_q(w)}{w^2} \, dw - c_q.$$

Lean: `New.primeRemainder_eq_integral_countError_sub` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* For $1 \leq n \leq y$, $1/n - 1/y = \int_n^y w^{-2} \, dw$. Sum over $n$ with the weights $\lambda_q(n)$, and exchange the sum and the integral: $\sum_{n \leq y} \lambda_q(n)(1/n - 1/y) = \int_1^y S(w) w^{-2} \, dw$, where $S(w) = \sum_{n \leq w} \lambda_q(n)$. (The term $n = 1$ is zero since $\Lambda(1) = 0$.) Also $\int_1^y (w/\varphi(q)) w^{-2} \, dw = \log y / \varphi(q)$. Subtract, and subtract $c_q$. $\square$

So the smoothing $1/n - 1/y$ in $R_q$ is one integration of the count, and $R_q$ varies slowly.

**Lemma (Slow variation).** Let $d$ be a prime and $q \geq 1$. For $1 \leq y \leq z$,

$$|R_q(z) - R_q(y)| \;\leq\; 13 \, \frac{z - y}{y}.$$

For $0 \leq u \leq v \leq u + 1$, $|R_q(e^v) - R_q(e^u)| \leq 26(v - u)$.

Lean: `New.abs_primeRemainder_sub_le`, `New.abs_primeRemainder_exp_sub_le` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* By the integral formula, $R_q(z) - R_q(y) = \int_y^z \mathcal{E}_q(w) w^{-2} \, dw$. For $w > y$, $|\mathcal{E}_q(w)| w^{-2} \leq 13 w / w^2 \leq 13/y$. So the integral is at most $13(z - y)/y$. For the second form, take $y = e^u$ and $z = e^v$: then $(z - y)/y = e^{v - u} - 1 \leq 2(v - u)$ for $0 \leq v - u \leq 1$. $\square$

### The transform and the analytic input

Put $v = \log y$. The function $v \mapsto R_q(e^v)$ has a simple Laplace transform. Let $G_q = $ `logDerivMean d q` be

$$G_q(s) \;=\; \frac{1}{\varphi(q)} \Big( \sum_{\psi \bmod q} \Big( \frac{\tilde L'}{\tilde L}(s, \psi \chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi) \Big) - 1 \Big),$$

where $\tilde L(s, \chi)$ is $L(s, \chi)$, multiplied by $s - 1$ if $\chi$ is principal (the source's `New.entireL`). By orthogonality of the characters, $G_q$ continues $\sum_n \lambda_q(n) n^{-s} - s/(\varphi(q)(s - 1))$ from $\operatorname{Re} s > 1$. The constant of $R_q$ is $c_q = \operatorname{Re} G_q(1)$. [The weighted prime remainder](/chapter/weighted-prime-remainder/) gives these definitions.

**Lemma (Recalled: the transform).** Let $d$ be an odd prime and $q \geq 1$ prime to $d$. For $\operatorname{Re} s > 2$,

$$\int_0^\infty R_q(e^v) \, e^{(1 - s) v} \, dv \;=\; \frac{G_q(s)/s - \operatorname{Re} G_q(1)}{s - 1}.$$

Lean: `New.integral_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

Since $G_q(1)$ is real for such $d$ and $q$ (`New.ofReal_re_logDerivMean_one`), the right side is $(F(s) - F(1))/(s - 1)$ with $F(s) = G_q(s)/s$.

**Theorem (Recalled: zero-free region).** Let $\chi$ be a Dirichlet character. For all large $l$, and all $s$ with $\operatorname{Re} s \geq 1 - l^{-25}$ and $|s| \leq e^l$, $\tilde L(s, \chi) \neq 0$ and $|\tilde L'(s, \chi)/\tilde L(s, \chi)| \leq 2 l^{25}$.

Lean: `New.eventually_norm_logDeriv_entireL_le` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

This is the classical region in a crude form. It follows from the inequality $|L(u, \chi_0)^3 L(u + iv, \chi)^4 L(u + 2iv, \chi^2)| \geq 1$ for real $u > 1$ and $v$. Write $s = u + iv$. The region $\operatorname{Re} s \geq 1 - l^{-25}$ for $|s| \leq e^l$ is $u \geq 1 - (\log |v|)^{-25}$, much weaker than the classical $1 - c/\log |v|$. It is enough here, because the Tauberian theorem below needs only some power of $l$.

**Lemma (The transform is bounded).** Let $d$ be a prime and $q \geq 1$. For all large $l$, the function $G_q(s)/s$ is holomorphic and of norm at most $l^{26}$ on the set $\operatorname{Re} s \geq 1 - l^{-26}$, $|s| \leq e^l$.

Lean: `New.eventually_norm_logDerivMean_div_le` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* Apply the zero-free region to the finitely many characters $\psi$ modulo $q$ and $\psi \chi_K$. For large $l$, all of them are nonzero on the larger region $\operatorname{Re} s \geq 1 - l^{-25}$, $|s| \leq e^l$, with logarithmic derivative at most $2 l^{25}$. So $G_q$ is analytic there, and $|G_q(s)| \leq 4 n_q l^{25} + 1$, where $n_q$ is the number of characters modulo $q$. For $l \geq 2$, $\operatorname{Re} s \geq 1/2$, so $|s| \geq 1/2$ and $|G_q(s)/s| \leq (8 n_q + 2) l^{25} \leq l^{26}$ for $l \geq 8 n_q + 2$. $\square$

**Theorem (Recalled: a Tauberian theorem).** Let $R \colon \mathbb{R} \to \mathbb{R}$ be measurable, and let $C_{\mathrm{Lip}}$ be a number (Lean's `L`) with $|R(v) - R(u)| \leq C_{\mathrm{Lip}}(v - u)$ for $0 \leq u \leq v \leq u + 1$. Let $F \colon \mathbb{C} \to \mathbb{C}$ with

$$\frac{F(s) - F(1)}{s - 1} \;=\; \int_0^\infty R(v) e^{(1 - s) v} \, dv \qquad (\operatorname{Re} s > 2).$$

Let $A$ be a natural number, and suppose that for all large $l$, $F$ is holomorphic and of norm at most $l^A$ on $\operatorname{Re} s \geq 1 - l^{-A}$, $|s| \leq e^l$. Then for every natural number $B$, $|R(u)| \leq u^{-B}$ for all large $u$.

Lean: `New.eventually_abs_le_inv_pow_of_transform` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

The proof reads one Taylor coefficient of the transform at a far point $1 + H$ in two ways. The coefficient is a mean of $R$ against a Gamma density that is concentrated near a given point $u$. Since $R$ is Lipschitz, the mean is close to $R(u)$. The coefficient is also small, by Cauchy's estimate on a disc that reaches to the left of the line $\operatorname{Re} s = 1$. The source compares this with Montgomery and Vaughan, Section 6.2, where a contour integral takes the place of the Taylor coefficient. Volume 2 proves the theorem.

### The theorem

**Theorem (Prime number theorem for $R_q$).** Let $d$ be an odd prime and let $q \geq 1$ be prime to $d$. For every natural number $B$,

$$|R_q(y)| \;\leq\; \frac{1}{(\log y)^B}$$

for all large $y$. In particular $R_q(y) \to 0$ as $y \to \infty$.

Lean: `New.eventually_abs_primeRemainder_le`, `New.tendsto_primeRemainder` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* Apply the Tauberian theorem to $R(v) = R_q(e^v)$, $F(s) = G_q(s)/s$, $C_{\mathrm{Lip}} = 26$ and $A = 26$. The Lipschitz condition is the slow variation lemma. The transform is the recalled lemma. The bound for $F$ is the lemma above. The conclusion is $|R_q(e^v)| \leq v^{-B}$ for large $v$. Put $v = \log y$. The limit follows from the case $B = 1$. $\square$

**Remark.** The limit $R_q(y) \to 0$ fixes the meaning of the constant $c_q = \operatorname{Re} G_q(1)$: it is the one constant that makes $R_q$ tend to $0$.

**Remark (Formalization).** The hypotheses $d \neq 2$ and $(q, d) = 1$ are needed for the transform, because then $\psi \chi_K$ is never principal (`New.quadTwist_ne_one`), so the twisted terms add no pole at $s = 1$. For the parameters of the data, $d > 64$, and $d$ is prime to $q_0$ and to $1$. The threshold "for all large $y$" depends on $d$, $q$ and $B$. No uniformity in $q$ is claimed or needed. So the theorem does not meet the problem of Siegel zeros: for a fixed modulus there are finitely many characters, and each has its own zero-free region.

### The bound at the cut-off

**Theorem (The remainders at the cut-off).** Let $P$ be parameters with modulus $q_0$ and prime $d$, and let $\varepsilon > 0$. For all large integers $x$ and all real $l \geq x^{\varepsilon/12}$,

$$|R_{q_0}(e^l)| \;\leq\; x^{-2} \quad\text{and}\quad |R_1(e^l)| \;\leq\; x^{-2}.$$

Lean: `New.eventually_abs_primeRemainder_exp_le` (New/Reduction/OneSidedBound.lean).

*Proof.* Choose a natural number $B \geq 24/\varepsilon$. The prime $d$ is not $2$, since $d > 64$, and $q_0$ is prime to $d$. Also $1$ is prime to $d$. The prime number theorem for $R_q$, with this $B$, for $q = q_0$ and for $q = 1$, gives a number $y_0$ such that $|R_{q_0}(y)| \leq (\log y)^{-B}$ and $|R_1(y)| \leq (\log y)^{-B}$ for all $y \geq y_0$. Take $x \geq 1$ so large that $x^{\varepsilon/12} \geq y_0$. Let $l \geq x^{\varepsilon/12}$. Then $e^l \geq l + 1 \geq y_0$, so

$$|R_q(e^l)| \;\leq\; l^{-B} \;\leq\; x^{-\varepsilon B/12} \;\leq\; x^{-2},$$

since $\varepsilon B / 12 \geq 2$ and $x \geq 1$. $\square$

The theorem holds for every $l \geq x^{\varepsilon/12}$, so its threshold does not depend on the data. Section 6 takes $l = \log x_1$.

**Remark.** The algebraic part of the method needs only $x_1 \geq x^{10^6}$. With $\log x_1 \approx 10^6 \log x$, the bound $(\log x_1)^{-B}$ would be a power of $\log x$, not of $x$, and too weak next to $x^{-1/2}$. So the data put $x_1$ near $\exp(x^{\varepsilon/6})$, and then an error that saves a fixed power of $\log$ is enough. The compact edition makes a different choice: it uses no prime number theorem at all, and finds a good cut-off $x_1$ in a window $\log x_1 \in [u, u^2]$ by an averaging argument (finding F-114 of Volume 0).
