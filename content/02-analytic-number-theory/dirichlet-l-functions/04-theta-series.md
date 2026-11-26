---
title: Theta series
lean:
  - Lib/Analytic/DirichletTheta.lean
decls:
  - New.gaussianMonomial
  - New.gaussianTheta
  - New.thetaSeries
  - New.gaussianMellin
  - New.gaussianMellin_eq
  - New.norm_thetaSeries_le
  - New.mellin_thetaSeries
  - New.mellin_thetaSeries_moebius
  - New.poisson_summation_gaussianMonomial
  - New.gaussianTheta_poisson_summation
  - New.norm_gaussianTheta_char_le
  - New.hasMellin_thetaSeries_char
  - New.norm_thetaSeries_inv
  - New.integral_norm_thetaSeries_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta series

The source does not use the theta series to prove the functional equation. Mathlib already has it. The source uses them to write $\Lambda(s, \chi)$ as an integral of a function whose size it can control. This section states the classical transformation formula, then the definitions and results of the source, and then the inequality that Chapter 6 of this volume builds on.

### The classical formula

Let $\chi$ be a character modulo $q > 1$ with parity $a$, and let
$$\vartheta(x, \chi) = \sum_{n \in \mathbb{Z}} n^{a}\chi(n)\, e^{-\pi n^2 x/q}, \qquad x > 0.$$
If $\chi$ is primitive, then
$$\vartheta(x, \chi) = w(\chi)\, x^{-a - 1/2}\, \vartheta(1/x, \bar\chi),$$
with the root number $w(\chi)$ of Section 3 (Davenport, *Multiplicative Number Theory*, Chapter 9). The proof splits $n$ into classes modulo $q$ and applies Poisson summation to each class. The result is a theta series with the coefficients $\tau(\chi, n)$. For a primitive $\chi$ these are $\bar\chi(n)\tau(\chi)$ by the proposition on Gauss sums. For an imprimitive $\chi$ the first step still holds, with the coefficients $\tau(\chi, n)$, but the second step can fail.

Since $|w(\chi)| = 1$, the formula implies the identity of absolute values $|\vartheta(x, \chi)| = x^{-a - 1/2}|\vartheta(1/x, \chi)|$, because $\vartheta(1/x, \bar\chi)$ is the complex conjugate of $\vartheta(1/x, \chi)$. This weaker form is the one that the source proves.

### The definitions of the source

The source works with a variable $u$ in which the map $x \mapsto 1/x$ becomes $u \mapsto 1/(qu)$. Let $j \in \{0, 1\}$ be a parity and let $c : \mathbb{N} \to \mathbb{C}$.

**Definition (Theta series).** The *Gaussian weight* of parity $j$ is $w_j(z) = z^{j}e^{-\pi z^2}$ for $z \in \mathbb{R}$. Put
$$\Theta_c(u) = \sum_{n \geq 1} c(n)\, w_j(nu), \qquad \theta_c(u) = u^{1/2}\,\Theta_c(u), \qquad \Gamma_j(s) = \int_0^\infty w_j(z)\, z^{s}\, \frac{dz}{z}.$$
For a character $\chi$ we write $\theta_\chi$ for $\theta_c$ with $c(n) = \chi(n)$.

Lean: `New.gaussianMonomial`, `New.gaussianTheta`, `New.thetaSeries`, `New.gaussianMellin` (Lib/Analytic/DirichletTheta.lean).

The source defines $\Gamma_j$ as the Mellin transform of $w_j$, with Mathlib's `mellin`. Mathlib gives a value to `mellin f s` also where the integral does not converge. So $\Gamma_j(s)$ is a junk value for $\operatorname{Re} s \leq 0$. Every result below assumes $\operatorname{Re} s > 0$.

With $x = qu^2$, the term $w_j(nu)$ is $q^{-j/2}x^{j/2} n^{j}e^{-\pi n^2 x/q}$. So, when $c = \chi$ has parity $j$ and $\chi(0) = 0$,
$$2\,\Theta_\chi(u) = q^{-j/2}x^{j/2}\,\vartheta(x, \chi).$$
The map $u \mapsto 1/(qu)$ corresponds to $x \mapsto 1/x$. Its fixed point is $u = q^{-1/2}$.

**Lemma (The Gaussian Mellin transform).** If $\operatorname{Re} s > 0$, then $\Gamma_j(s) = \Gamma_{\mathbb{R}}(s + j)/2$.

Lean: `New.gaussianMellin_eq` (Lib/Analytic/DirichletTheta.lean).

*Proof.* Substitute $v = z^2$: $\Gamma_j(s) = \tfrac12\int_0^\infty e^{-\pi v}v^{(s + j)/2}\, dv/v = \tfrac12\pi^{-(s + j)/2}\Gamma((s + j)/2)$. $\square$

So $\Gamma_j(s) = G_\chi(s)/2$ when $\chi$ has parity $j$. Hence $\Gamma_j(s)L(s, \chi) = \Lambda(s, \chi)/2$ for $\operatorname{Re} s > 0$.

### Results for every coefficient sequence

**Lemma (Trivial bound).** If $|c(n)| \leq 1$ for every $n$ and $t > 0$, then $|\theta_c(t)| \leq 3e^{-t}t^{-1/2}$.

Lean: `New.norm_thetaSeries_le` (Lib/Analytic/DirichletTheta.lean).

The proof bounds $|w_j(t)|$ by $3e^{-2t}$ for $t \geq 0$ and sums a geometric series. The bound shows that $\int_r^\infty |\theta_c(u)|\, du/u$ converges for every $r > 0$. Near $u = 0$ it is too weak for the Mellin integral at $\operatorname{Re} s \leq 1$.

**Proposition (Mellin transform).** If $|c(n)| \leq 1$ for every $n$ and $\operatorname{Re} s > 1$, then
$$\int_0^\infty \theta_c(u)\, u^{s - 1/2}\, \frac{du}{u} = \Gamma_j(s) \sum_{n \geq 1} \frac{c(n)}{n^s}.$$
For a character $\chi$ modulo $q \geq 1$ and the coefficients $c(n) = \chi(n)\mu(n)$, the right side is $\Gamma_j(s)/L(s, \chi)$.

Lean: `New.mellin_thetaSeries`, `New.mellin_thetaSeries_moebius` (Lib/Analytic/DirichletTheta.lean).

*Proof.* The factor $u^{1/2}$ of $\theta_c$ cancels the shift $-1/2$. Integrate term by term: $\int_0^\infty w_j(nu)u^{s}\, du/u = n^{-s}\Gamma_j(s)$. For the second statement, $\sum_n \chi(n)\mu(n)n^{-s} = 1/L(s, \chi)$ for $\operatorname{Re} s > 1$, by the Euler product. $\square$

The second formula is the one that Riemann used for $1/\zeta$. Chapter 6 uses its truncation as a mollifier.

### Poisson summation

**Lemma (Poisson summation for the weight).** Let $a \in \mathbb{R}$ and $t > 0$. There is a real number $S$ with
$$\sum_{n \in \mathbb{Z}} w_j((n + a)t) = S, \qquad \sum_{n \in \mathbb{Z}} e^{2\pi i a n}\, w_j(n/t) = i^{j}\, t\, S,$$
where both series converge.

Lean: `New.poisson_summation_gaussianMonomial` (Lib/Analytic/DirichletTheta.lean).

This is the Poisson summation formula for $w_j$. The Fourier transform of $e^{-\pi z^2}$ is itself, and that of $ze^{-\pi z^2}$ is $-i\xi e^{-\pi\xi^2}$. The source derives the lemma from the theta kernels of Mathlib.

**Proposition (Transformation of the theta series of a character).** Let $\chi \neq \chi_0$ be a character modulo $q \geq 1$ with $\chi(-1) = (-1)^{j}$, and let $t > 0$. Put $\hat\chi(n) = q^{-1}\tau(\chi, n) = q^{-1}\sum_{a \bmod q}\chi(a)e(an/q)$. Then
$$t\,|\Theta_\chi(t)| = |\Theta_{\hat\chi}(1/(qt))|.$$

Lean: `New.gaussianTheta_poisson_summation` (Lib/Analytic/DirichletTheta.lean).

*Proof.* Write $n = mq + b$ with $b$ a class modulo $q$, and apply the last lemma to each class, with $a = b/q$ and scale $qt$. Multiply by $\chi(b)$ and add over $b$. The first sums give $\sum_{n \in \mathbb{Z}}\chi(n)w_j(nt)$. The second sums give $q\sum_{n \in \mathbb{Z}}\hat\chi(n)w_j(n/(qt))$, and by the lemma this is $i^{j}qt$ times the first sum. Both $\chi$ and $\hat\chi$ have parity $j$ and vanish at $0$, since $\chi \neq \chi_0$. So each sum over $\mathbb{Z}$ is twice the sum over $n \geq 1$. This gives $\Theta_{\hat\chi}(1/(qt)) = i^{j}\, t\, \Theta_\chi(t)$. Take absolute values. $\square$

The proof gives an identity of complex numbers. The Lean statement keeps only its absolute value. The character need not be primitive. In Lean $\hat\chi$ is Mathlib's inverse discrete Fourier transform `ZMod.invDFT` of $\chi$.

**Lemma (Bound near $0$).** Let $\chi \neq \chi_0$ be a character modulo $q \geq 1$ with $\chi(-1) = (-1)^{j}$, and let $t > 0$. Then $|\Theta_\chi(t)| \leq 3eq\, e^{-t}$.

Lean: `New.norm_gaussianTheta_char_le` (Lib/Analytic/DirichletTheta.lean).

For $t \geq 1$ this follows from the trivial bound. For $t < 1$ the proposition moves the series to the point $1/(qt)$, where it is small, and $|\hat\chi(n)| \leq 1$. The character need not be primitive. The bound is the reason why the Mellin integral converges for $\operatorname{Re} s > 0$ and not only for $\operatorname{Re} s > 1$.

**Theorem (The L-function as a Mellin transform).** Let $\chi \neq \chi_0$ be a character modulo $q \geq 1$ with $\chi(-1) = (-1)^{j}$, and let $\operatorname{Re} s > 0$. Then the integral below converges absolutely, and
$$\int_0^\infty \theta_\chi(u)\, u^{s - 1/2}\, \frac{du}{u} = \Gamma_j(s)\, L(s, \chi).$$

Lean: `New.hasMellin_thetaSeries_char` (Lib/Analytic/DirichletTheta.lean).

*Proof.* By the bound near $0$ and the trivial bound, the integral converges absolutely for $\operatorname{Re} s > 0$ and defines a holomorphic function there. By the proposition on Mellin transforms it equals $\Gamma_j(s)L(s, \chi)$ for $\operatorname{Re} s > 1$. Both sides are holomorphic on $\operatorname{Re} s > 0$. The identity theorem extends the equality. $\square$

Mathlib's `HasMellin f s m` says that the Mellin integral of $f$ at $s$ converges and has the value $m$. Here $L(s, \chi)$ is Mathlib's L-function, the imprimitive one if $\chi$ is imprimitive.

### The primitive case

**Theorem (Symmetry of the theta series).** Let $\chi \neq \chi_0$ be a primitive character modulo $q$ with $\chi(-1) = (-1)^{j}$, and let $t > 0$. Then
$$|\theta_\chi(1/(qt))| = |\theta_\chi(t)|.$$

Lean: `New.norm_thetaSeries_inv` (Lib/Analytic/DirichletTheta.lean).

*Proof.* By the proposition on Gauss sums, $\hat\chi(n) = q^{-1}\tau(\chi)\bar\chi(n)$. The weight $w_j$ is real, so $\Theta_{\hat\chi}(u) = q^{-1}\tau(\chi)\overline{\Theta_\chi(u)}$, and $|\tau(\chi)| = q^{1/2}$ gives $q^{1/2}|\Theta_{\hat\chi}(u)| = |\Theta_\chi(u)|$. With the proposition on the transformation,
$$|\theta_\chi(1/(qt))| = (qt)^{-1/2}|\Theta_\chi(1/(qt))| = (qt)^{-1/2}q^{1/2}\, t\,|\Theta_\chi(t)| = t^{1/2}|\Theta_\chi(t)| = |\theta_\chi(t)|. \qquad \square$$

In the variable $x = qu^2$ this is the absolute value of the classical formula. The source calls it the functional equation of the theta series in absolute value.

**Corollary (Folding the integral).** Let $\chi \neq \chi_0$ be a primitive character modulo $q$ with $\chi(-1) = (-1)^{j}$. Then
$$\int_0^\infty |\theta_\chi(u)|\, \frac{du}{u} = 2\int_{q^{-1/2}}^\infty |\theta_\chi(u)|\, \frac{du}{u}.$$

Lean: `New.integral_norm_thetaSeries_div` (Lib/Analytic/DirichletTheta.lean).

*Proof.* The left integral converges, by the theorem on the Mellin transform at $s = 1/2$. Split it at $r = q^{-1/2}$. The map $u \mapsto 1/(qu)$ takes $(0, r)$ onto $(r, \infty)$, it keeps the measure $du/u$, and it keeps $|\theta_\chi|$ by the theorem. So the integrals over $(0, r)$ and $(r, \infty)$ are equal. $\square$

### The use in Chapter 6

The results of this section combine into one inequality. Let $\chi \neq \chi_0$ be a primitive character modulo $q$ with $\chi(-1) = (-1)^{j}$, and let $\operatorname{Re} z = 1/2$. Then $|u^{z - 1/2}| = 1$, so the theorem on the Mellin transform and the corollary give
$$|\Gamma_j(z)L(z, \chi)| \leq \int_0^\infty |\theta_\chi(u)|\, \frac{du}{u} = 2\int_{q^{-1/2}}^\infty |\theta_\chi(u)|\, \frac{du}{u}.$$
The source states it as follows. Let $T > 0$ with $q \leq T^2$, and let $J(T) = \int_{1/T}^\infty (|\theta_\chi(u)| + |\theta_{\chi\mu}(u)|)\, du/u$. Then $|\Gamma_j(z)L(z, \chi)| \leq 2J(T)$ for every $z$ with $\operatorname{Re} z = 1/2$. This is `New.norm_gaussianMellin_mul_LFunction_le` in Lib/Analytic/QuadraticTwist.lean, with $J$ the definition `New.thetaTailIntegral`. Chapter 6 of this volume, [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/), treats it. By the lemma on $\Gamma_j$, the left side is $|\Lambda(z, \chi)|/2$. So the inequality bounds the completed L-function on the critical line by a tail of the theta series.

**Remark (Formalization).** Four points separate the classical formula from the Lean statements.

1. Absolute values only. The source proves the transformation of $\theta_\chi$ in absolute value. The root number does not appear. The proof does compute the complex identity $\Theta_{\hat\chi}(1/(qt)) = i^j t\,\Theta_\chi(t)$, but the statement drops it. The functional equation of $L(s, \chi)$ does not follow from the absolute values, and the source does not try to derive it from them. It takes the functional equation from Mathlib (Section 3).
2. Parity as a hypothesis. The parity $j$ is an element of `Fin 2`, and each result for characters assumes $\chi(-1) = (-1)^{j}$. The results do not choose $j$ from $\chi$. With the wrong $j$ the Poisson step fails: the sum of $\chi(n)w_j(nt)$ over $n \in \mathbb{Z}$ is then $0$, and it is not twice the sum over $n \geq 1$.
3. The principal character is excluded. Each result for characters assumes $\chi \neq \chi_0$. For $\chi_0$ the coefficient sum at $n = 0$ is not $0$ and $L(s, \chi_0)$ has a pole at $1$. The source does not need the theta series of $\chi_0$.
4. Junk values. Lean's Bochner integral is $0$ for a function that is not integrable, and `mellin` is defined by it. The corollary on folding is an identity of such integrals. Its proof shows that the left side converges, so here the integral has its classical meaning. The bound on $\Gamma_j L$ uses only integrals that converge.
