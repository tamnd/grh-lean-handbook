---
title: The transform and its poles
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/EntireLFunction.lean
decls:
  - New.IsPolar
  - New.integrableOn_laplace_of_abs_le
  - New.laplace_pow
  - New.LSeries_lambdaKResidueClass
  - New.integral_primeRemainder
  - New.ofReal_re_logDerivMean_one
  - New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt
  - New.tendsto_sub_mul_logDerivMean
  - New.tendsto_logDerivMean_residue
  - New.isPolar_primeRemainder
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The transform and its poles

This section takes the steps 2, 3 and 4 of the plan, proves the main theorem, and explains the sign of the residues. The notation is that of Sections 3 and 4.

### Polar functions

The source works in the variable $v = \log y$. The substitution $y = e^v$ gives
$$\int_1^\infty R(y)\, y^{-s}\, dy = \int_0^\infty R(e^v)\, e^{(1 - s)v}\, dv.$$
The source packs the properties of the transform that Landau's argument needs in one definition.

**Definition (Polar function).** Let $E : \mathbb{R} \to \mathbb{R}$ and $r : \mathbb{C} \to \mathbb{C}$. The function $E$ is *polar with residues $r$* if $E$ is measurable and there are a real number $C$ and a function $\Phi : \mathbb{C} \to \mathbb{C}$ with these properties.

1. $\Phi$ is meromorphic on $\mathbb{C}$.
2. $|E(v)| \leq Ce^v$ for every $v \geq 0$.
3. $\Phi(s) = \int_0^\infty E(v) e^{(1 - s)v}\, dv$ for every $s$ with $\operatorname{Re} s > 2$.
4. For every $\rho$ with $\operatorname{Re} \rho > 0$, $(z - \rho)\Phi(z) \to r(\rho)$ as $z \to \rho$ with $z \neq \rho$.

Lean: `New.IsPolar` (Lib/Analytic/EntireLFunction.lean).

Condition 4 says that in $\operatorname{Re} s > 0$ the function $\Phi$ has at most simple poles, with residue $r(\rho)$ at $\rho$, and $r(\rho) = 0$ where there is no pole. [Polar functions](/chapter/polar-functions/) treats the definition in full.

**Remark (Formalization).** Three points of the definition matter. First, the integral in condition 3 is a Bochner integral, which is $0$ for a function that is not integrable. The next lemma shows that the integrand is integrable for $\operatorname{Re} s > 2$, so condition 3 is about a true integral. Second, the values of $\Phi$ at its poles, and the values of $r$ at points with $\operatorname{Re} \rho \leq 0$, are arbitrary. Third, the half-plane $\operatorname{Re} s > 2$ comes from the crude growth in condition 2. By uniqueness of analytic continuation, a smaller half-plane would give the same $\Phi$.

**Lemma (Convergence of the transform).** Let $E$ be measurable, with $|E(v)| \leq Ce^v$ for $v \geq 0$, and let $\operatorname{Re} s > 2$. Then $v \mapsto E(v)e^{(1 - s)v}$ is integrable on $(0, \infty)$.

Lean: `New.integrableOn_laplace_of_abs_le` (Lib/Analytic/EntireLFunction.lean).

*Proof.* The integrand has absolute value at most $Ce^v e^{(1 - \operatorname{Re} s)v} = Ce^{(2 - \operatorname{Re} s)v}$, and $2 - \operatorname{Re} s < 0$. $\square$

**Lemma (The transform of a power).** Let $\operatorname{Re} s > 0$ and $k \in \mathbb{N}$. Then $\int_0^\infty t^k e^{-st}\, dt = k!/s^{k + 1}$.

Lean: `New.laplace_pow` (Lib/Analytic/EntireLFunction.lean).

*Proof.* Differentiate $\int_0^\infty e^{zt}\, dt = -1/z$, for $\operatorname{Re} z < 0$, $k$ times under the integral sign, and put $z = -s$. $\square$

### The transform of the remainder

**Lemma (Partial summation).** Let $d$ be a prime, let $q \in \mathbb{N}$, let $r \in \mathbb{N}$, and let $\operatorname{Re} s > 2$. Then
$$\sum_{n \geq 1} \lambda(n) n^{-s} = (s + r - 1)\int_0^\infty \Sigma_r(e^v)\, e^{(1 - s)v}\, dv.$$

Lean: `New.LSeries_lambdaKResidueClass` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Put $f(n) = \lambda(n) n^{r - 1}$ and $w = s + r - 1$, so that $\lambda(n) n^{-s} = f(n) n^{-w}$. By the bound of Section 3, $\sum_{n \leq t} |f(n)| = t^r\Sigma_r(t) \leq 2t^{1 + r}$, and $\operatorname{Re} w > 1 + r$. Partial summation gives
$$\sum_{n \geq 1} f(n) n^{-w} = w\int_1^\infty \Bigl(\sum_{n \leq t} f(n)\Bigr) t^{-w - 1}\, dt = w\int_1^\infty \Sigma_r(t)\, t^{-s}\, dt.$$
The substitution $t = e^v$ gives the claim. $\square$

The lemma needs neither $q \geq 1$ nor $d \neq 2$. The cases $r = 0$ and $r = 1$ are the two simple identities of Section 2.

**Proposition (The transform of the remainder).** Let $d$ be an odd prime, let $q \geq 1$ with $\gcd(q, d) = 1$, and let $\operatorname{Re} s > 2$. Then
$$\int_0^\infty R_q(e^v)\, e^{(1 - s)v}\, dv = \frac{G_q(s)/s - c_q}{s - 1}.$$

Lean: `New.integral_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Write $D(s) = s/(\varphi(q)(s - 1)) + G_q(s)$ for the Dirichlet series of $\lambda$ (Section 4). The four terms of $R_q(e^v) = \Sigma_0(e^v) - \Sigma_1(e^v) - v/\varphi(q) - c_q$ have the transforms $D(s)/(s - 1)$, $D(s)/s$, $1/(\varphi(q)(s - 1)^2)$ and $c_q/(s - 1)$, by partial summation with $r = 0$ and $r = 1$ and by the transform of a power. Each term is integrable, so the transform of $R_q(e^v)$ is the sum. Now
$$\frac{D(s)}{s - 1} - \frac{D(s)}{s} = \frac{D(s)}{s(s - 1)} = \frac{1}{\varphi(q)(s - 1)^2} + \frac{G_q(s)}{s(s - 1)}.$$
The first term cancels the transform of $v/\varphi(q)$. What is left is $G_q(s)/(s(s - 1)) - c_q/(s - 1)$. $\square$

**Remark (Formalization).** To split the integral, the source needs each term to be integrable. For $v^k e^{(1 - s)v}$ it reads this off from the value $k!/(s - 1)^{k + 1} \neq 0$ of the integral, since a function that is not integrable has the integral $0$ by convention.

### The constant is the value at 1

**Proposition (The value at 1 is real).** Let $d$ be an odd prime, and let $q \geq 1$ with $\gcd(q, d) = 1$. Then $G_q(1)$ is real. So $c_q = G_q(1)$.

Lean: `New.ofReal_re_logDerivMean_one` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Put $F(s) = G_q(s)/s - c_q$. By [Lemma](/decl/New.analyticAt_logDerivMean_of_one_le_re/), $F$ is analytic at every real point $x \geq 1$. For real $x > 2$ the proposition above gives $F(x) = (x - 1)\int_0^\infty R_q(e^v)e^{(1 - x)v}\, dv$, which is real, since $R_q$ is real. So $x \mapsto \operatorname{Im} F(x)$ is a real analytic function on $[1, \infty)$ that vanishes on a neighbourhood of $3$. By the identity theorem it vanishes on $[1, \infty)$. At $x = 1$ this says that $G_q(1) - c_q$ is real, so $G_q(1)$ is real. $\square$

Exercise 6 gives a shorter proof through the conjugate characters. The proof of the source needs no fact about them.

The proposition fixes $c_q$. The numerator $F(s)$ of the transform vanishes at $s = 1$, so the transform has no pole there. Another constant $c$ would leave a simple pole with residue $G_q(1) - c$.

### The residues

**Lemma (The residue of a logarithmic derivative).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $s \in \mathbb{C}$. Then
$$(z - s)\frac{\tilde L'}{\tilde L}(z, \chi) \to \operatorname{ord}_s \tilde L(\cdot, \chi) \qquad (z \to s,\ z \neq s).$$

Lean: `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt` (Lib/Analytic/EntireLFunction.lean), with `New.analyticOrderAt_entireL_ne_top`.

*Proof.* The function $\tilde L(\cdot, \chi)$ is entire, and it is not identically $0$, since $\tilde L(1, \chi) \neq 0$. So it has a finite order $m$ at $s$, and $\tilde L(z, \chi) = (z - s)^m g(z)$ near $s$, with $g$ analytic and $g(s) \neq 0$. Then $\tilde L'/\tilde L = m/(z - s) + g'/g$ near $s$, and $g'/g$ is continuous at $s$. $\square$

**Remark (Formalization).** The source writes the order as `analyticOrderNatAt`, the order as a natural number. Mathlib gives this function the value $0$ where the order is infinite. Here the order is finite. Where $\tilde L(s, \chi) \neq 0$, the order is $0$ (`New.analyticOrderNatAt_entireL_eq_zero_iff`), and the lemma says that the logarithmic derivative has no pole there.

**Lemma (The residues of G_q).** Let $q \geq 1$ and $\rho \in \mathbb{C}$. Then
$$(z - \rho)G_q(z) \to \frac{n_K(\rho) - n(\rho)}{\varphi(q)} \qquad (z \to \rho,\ z \neq \rho).$$

Lean: `New.tendsto_sub_mul_logDerivMean` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Apply the lemma above to each $\psi$ and each $\psi\chi_K$. The term $-1/\varphi(q)$ of $G_q$ gives $(z - \rho)/\varphi(q) \to 0$. $\square$

**Lemma (The residues of the transform).** Let $q \geq 1$, let $\kappa \in \mathbb{C}$, and let $\rho \neq 0, 1$. Then
$$(z - \rho)\,\frac{G_q(z)/z - \kappa}{z - 1} \to \frac{n(\rho) - n_K(\rho)}{\varphi(q)\, \rho(1 - \rho)} \qquad (z \to \rho,\ z \neq \rho).$$

Lean: `New.tendsto_logDerivMean_residue` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Put $m = (n_K(\rho) - n(\rho))/\varphi(q)$. Write the function as $\bigl((z - \rho)G_q(z)/z - (z - \rho)\kappa\bigr)/(z - 1)$. By the lemma above, it tends to $(m/\rho - 0)/(\rho - 1) = -m/(\rho(1 - \rho))$. $\square$

### The main theorem

**Theorem (Poles).** Let $d$ be a prime with $d \equiv 7 \bmod 8$, and let $q \geq 1$ with $\gcd(q, d) = 1$. Then the function $v \mapsto R_q(e^v)$ is polar with the residues
$$r(s) = \frac{n(s) - n_K(s)}{\varphi(q)\, s(1 - s)} = \frac{1}{\varphi(q)\, s(1 - s)} \sum_{\psi \bmod q} \Bigl(\operatorname{ord}_s \tilde L(\cdot, \psi) - \operatorname{ord}_s \tilde L(\cdot, \psi\chi_K)\Bigr).$$

Lean: `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Since $d \equiv 7 \bmod 8$, $d$ is odd. Take $C = |c_q| + 5$ and $\Phi(s) = F(s)/(s - 1)$ with $F(s) = G_q(s)/s - c_q$. We check the four conditions.

1. $G_q$ is a finite linear combination of logarithmic derivatives of entire functions that are not identically $0$, and of a constant. So $G_q$ and $\Phi$ are meromorphic on $\mathbb{C}$.
2. The growth bound is [Lemma](/decl/New.abs_primeRemainder_exp_le/).
3. For $\operatorname{Re} s > 2$, $\Phi(s)$ is the transform, by the proposition on the transform of the remainder.
4. Let $\operatorname{Re} \rho > 0$. Then $\rho \neq 0$. If $\rho \neq 1$, the lemma on the residues of the transform, with $\kappa = c_q$, gives the limit $r(\rho)$. If $\rho = 1$, then $F$ is analytic at $1$, and $F(1) = G_q(1) - c_q = 0$ by the proposition on the value at $1$. So $(z - 1)\Phi(z) = F(z) \to 0$. Also $r(1) = 0$: the numerator $n(1) - n_K(1)$ is $0$, since no $\tilde L$ vanishes at $1$. $\square$

**Remark (Formalization).** At $s = 1$ the formula for $r(s)$ is a division by zero, since $1 - s = 0$. In Lean its value is $0$, and this is the correct residue, as the proof shows (finding F-039). A textbook statement says "no pole at $s = 1$" as a separate clause, as in Section 1. The numerator is also $0$, so the formula is $0/0$.

**Remark (Formalization).** The hypothesis $d \equiv 7 \bmod 8$ is stronger than the proof needs. The proof uses it only to get $d \neq 2$. So the theorem holds for every odd prime $d$ prime to $q$, but the source states it only for $d \equiv 7 \bmod 8$. This costs nothing, since the criterion applies it only to such primes.

In $\operatorname{Re} s \geq 1$ no $\tilde L$ vanishes, so $r(s) = 0$ there. So the poles in $\operatorname{Re} s > 0$ are in the strip $0 < \operatorname{Re} s < 1$, at zeros of the $L(s, \psi)$ and the $L(s, \psi\chi_K)$. Where zeros of both kinds meet, the contributions can cancel.

### The sign of the residues

The sign is the reason for the shape of the argument. Let $x$ be real with $0 < x < 1$. Then $\varphi(q)x(1 - x) > 0$, and $n(x) \geq 0$. So
$$r(x) \geq 0 \quad \text{if } n_K(x) = 0.$$
In the model case of Section 2 there is no twist, and the residues at real points are never negative. Here a real zero of a twist can make the residue negative. For $q = 1$, a real zero $\beta$ of $L(s, \chi_K)$ of order $m$ with $\zeta(\beta) \neq 0$ gives $r(\beta) = -m/(\beta(1 - \beta)) < 0$, and a term $-m x^{\beta - 1}/(\beta(1 - \beta))$ of $R_1(x)$. It pushes $R_1$ down, and an upper bound for $R_1$ says nothing about it. Whether such zeros exist is the open question of Siegel zeros.

The later chapters avoid the problem by the choice of $d$, with three results of the source.

1. Landau's theorem in the form of the source ([Lemma](/decl/New.IsPolar.landau/), [Landau's theorem](/chapter/landau-theorem/)). Let $E$ be polar with residues $r$, and let $\beta > 0$. Suppose that $\operatorname{Re} r(x) \geq 0$ for every real $x > \beta$, and that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$. Then $r(\rho) = 0$ for every $\rho$ with $\operatorname{Re} \rho > \beta$.
2. The choice of the prime ([Lemma](/decl/New.exists_entireL_quadTwist_ne_zero/)). Let $N \geq 1$, let $\beta > 1/2$, let $H$ be real, and let $a$ be a unit modulo $N$ such that every prime $d$ with $d \equiv a \bmod N$ satisfies $d \equiv 7 \bmod 8$ and $\gcd(N, d) = 1$. Then there is a prime $d \equiv a \bmod N$ such that for every character $\xi$ modulo $N$ and every $s$ with $\operatorname{Re} s \geq \beta$ and $|\operatorname{Im} s| \leq H$, $\tilde L(s, \xi\chi_K) \neq 0$, where $\chi_K = (\cdot/d)$.
3. The criterion ([Theorem](/decl/New.LFunction_ne_zero_of_primeRemainder_le/), [Landau's criterion](/chapter/landau-criterion/)). Let $q_0 \geq 1$ with $8 \mid q_0$, let $d_0 \equiv 7 \bmod 8$ with $\gcd(d_0, q_0) = 1$, and let $\beta > 1/2$. Suppose that for every prime $d \equiv d_0 \bmod q_0$ the remainder $R_{q_0}$ for this $d$ satisfies $R_{q_0}(x) \leq x^{\beta - 1}$ for all large $x$. Then $L(\rho, \psi) \neq 0$ for every character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$.

The criterion combines the main theorem with the first two results. Let $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$. Choose $d$ by the second result with $H = |\operatorname{Im} \rho|$. In the box $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq H$, every $n_K(s)$ is $0$, so $r(s) = n(s)/(\varphi(q_0)s(1 - s))$. This is at least $0$ at real $x \in (\beta, 1)$ and $0$ at real $x \geq 1$. Landau's theorem gives $r(\rho) = 0$, so $n(\rho) = 0$, and each $L(\rho, \psi) \neq 0$.

The notes record the sign of the residues as a point that a person must check line by line (finding F-077). This book has not done that check.

### The prime number theorem for the remainder

The source proves the two-sided bound at the second cut-off from the transform ([Theorem](/decl/New.eventually_abs_primeRemainder_le/), [the prime number theorem](/chapter/prime-number-theorem/)). Let $d$ be an odd prime, and let $q \geq 1$ with $\gcd(q, d) = 1$. Then for every $B \in \mathbb{N}$, $|R_q(y)| \leq (\log y)^{-B}$ for all large $y$. So $R_q(y) \to 0$ ([Theorem](/decl/New.tendsto_primeRemainder/)). The proof applies a Tauberian theorem with a zero-free region near $\operatorname{Re} s = 1$. The source calls the result a case of the Siegel-Walfisz theorem and cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19.
