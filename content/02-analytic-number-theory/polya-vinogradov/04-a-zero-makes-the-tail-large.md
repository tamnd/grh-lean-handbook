---
title: A zero makes the theta tail large
lean:
  - Lib/Analytic/QuadraticTwist.lean
  - Lib/Analytic/DirichletTheta.lean
decls:
  - New.thetaTailIntegral
  - New.mollifier
  - New.norm_mollifier_le
  - New.norm_mul_mollifier_sub_le
  - New.norm_gaussianMellin_mul_LFunction_le
  - New.gaussianMellin_differentiableOn_and_bdd
  - New.exists_pos_le_norm_gaussianMellin
  - New.three_lines_bound_of_LFunction_eq_zero
  - New.eventually_rpow_lt_thetaTailIntegral
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A zero makes the theta tail large

This section proves the detection step. For a primitive character $\chi$ of conductor $q \leq T^2$, a zero of $L(s, \chi)$ in the box $\operatorname{Re} s \geq 1/2 + 9\delta$, $|\operatorname{Im} s| \leq H$ forces a tail integral of the theta series of $\chi$ to be larger than $T^{2\delta}$, once $T$ is large. The tool is the three lines theorem. The notation is that of [theta series](/chapter/dirichlet-l-functions/): $w_j(z) = z^je^{-\pi z^2}$, $\theta_c(u) = u^{1/2}\sum_{n \geq 1}c(n)w_j(nu)$, and $\Gamma_j(s) = \int_0^\infty w_j(z)z^s\,dz/z$.

### The classical method

Zero detection by a mollifier is the standard first step of a zero density estimate (Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 10). Let $M(s) = \sum_{n \leq y}\mu(n)\chi(n)n^{-s}$ approximate $1/L(s, \chi)$. Then $L(s, \chi)M(s) - 1$ is small on $\operatorname{Re} s = 2$. At a zero $\rho$ it equals $-1$. A contour argument, or a convexity argument, moves the information from $\operatorname{Re} s = 2$ to $\rho$, and the cost is the size of $LM$ near the critical line. So each zero produces a large value of a Dirichlet polynomial or of a short sum. The density estimate then counts the large values with a mean value theorem.

The source follows the same plan with three changes. The mollifier is a Mellin integral of the theta series of $\chi\mu$, cut at $u = 1/T$. The factor $\Gamma_j$ is kept, so that every function is bounded on the strip. The convexity tool is Hadamard's three lines theorem on $1/2 \leq \operatorname{Re} z \leq 2$.

**Theorem (Hadamard three lines).** Let $a < b$, and let $f$ be holomorphic on $a < \operatorname{Re} z < b$, continuous and bounded on $a \leq \operatorname{Re} z \leq b$. Suppose that $|f| \leq M_a$ on $\operatorname{Re} z = a$ and $|f| \leq M_b$ on $\operatorname{Re} z = b$, with $M_a, M_b > 0$. Then, for $a \leq \operatorname{Re} z \leq b$ and $\lambda = (\operatorname{Re} z - a)/(b - a)$,
$$|f(z)| \leq M_a^{1 - \lambda}M_b^{\lambda}.$$

Mathlib: `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (Mathlib).

The classical proof applies the maximum principle to $f(z)M_a^{(z - b)/(b - a)}M_b^{(a - z)/(b - a)}$.

### The two integrals

Fix $j \in \{0, 1\}$, $c : \mathbb{N} \to \mathbb{C}$ and $T \in \mathbb{R}$. Write $\mu c$ for the sequence $n \mapsto c(n)\mu(n)$.

**Definition (Theta tail and mollifier).** The *theta tail* of $c$ is
$$J(c, T) = \int_{1/T}^\infty \bigl(|\theta_c(u)| + |\theta_{\mu c}(u)|\bigr)\,\frac{du}{u}.$$
The *mollifier* of $c$ is the function of $s \in \mathbb{C}$
$$\mathcal{M}(s) = \int_{1/T}^\infty \theta_{\mu c}(u)\,u^{s - 1/2}\,\frac{du}{u}.$$

Lean: `New.thetaTailIntegral`, `New.mollifier` (Lib/Analytic/QuadraticTwist.lean).

For $c = \chi$ and $\operatorname{Re} s > 1$, [Proposition](/decl/New.mellin_thetaSeries_moebius/) says that the integral of $\theta_{\mu\chi}(u)u^{s - 1/2}$ over all $u > 0$ is $\Gamma_j(s)/L(s, \chi)$. So $\mathcal M$ is the truncation of an integral for $\Gamma_j/L$. The truncation makes $\mathcal M$ entire in practice: by the [trivial bound](/decl/New.norm_thetaSeries_le/) the integrand is $O(T e^{-u}u^{\operatorname{Re} s - 1})$, uniformly for $u > 1/T$.

**Remark (Formalization).** Both are Bochner integrals, which Lean sets to $0$ when the integrand is not integrable. The source proves integrability where it uses them: for $|c(n)| \leq 1$ and $T > 0$, the two parts of $J(c, T)$ are integrable (`New.thetaTailIntegral_eq_add`), and $\mathcal M$ is holomorphic on $\operatorname{Re} s > 0$ and bounded on $1/2 \leq \operatorname{Re} s \leq 2$ (`New.mollifier_differentiableOn_and_bounded`). For $T \leq 0$ the domain $u > 1/T$ contains $u \leq 0$, where $\theta_c$ has junk values; no statement below allows $T \leq 0$.

### The bounds on the two lines

**Lemma (The mollifier on the critical line).** Let $|c(n)| \leq 1$ for every $n$, let $T > 0$, and let $\operatorname{Re} z = 1/2$. Then $|\mathcal M(z)| \leq J(c, T)$.

Lean: `New.norm_mollifier_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* On $\operatorname{Re} z = 1/2$ and for $u > 0$, $|u^{z - 1/2}| = 1$. So $|\mathcal M(z)|$ is at most the integral of $|\theta_{\mu c}(u)|/u$ over $u > 1/T$, which is one of the two non-negative parts of $J(c, T)$. $\square$

**Lemma (The right line).** Let $\chi$ be any character modulo $q \geq 1$, let $T > 0$, and let $\operatorname{Re} z = 2$. Then
$$\bigl|\Gamma_j(z)L(z, \chi)\mathcal M(z) - \Gamma_j(z)^2\bigr| \leq \frac9T,$$
where $\mathcal M$ is the mollifier of $c = \chi$.

Lean: `New.norm_mul_mollifier_sub_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Since $\operatorname{Re} z > 1$, $L(z, \chi) \neq 0$ by `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (Mathlib). Write the left side as $|\Gamma_jL|\cdot|\mathcal M - \Gamma_j/L|$. For $u > 0$ the trivial bound gives $|u^{z - 1/2}\theta_c(u)/u| \leq 3e^{-u}$ for every $c$ with $|c(n)| \leq 1$, since $|u^{z - 3/2}| = u^{1/2}$. First, $\Gamma_j(z)L(z, \chi)$ is the Mellin integral of $\theta_\chi$, so $|\Gamma_jL| \leq \int_0^\infty 3e^{-u}du = 3$. Second, $\Gamma_j/L - \mathcal M$ is the integral of $\theta_{\mu\chi}(u)u^{z - 3/2}$ over $0 < u \leq 1/T$, which is at most $3 \cdot (1/T)$. The product is at most $9/T$. $\square$

The lemma asks nothing of $\chi$: it may be principal or imprimitive. The parity $j$ is also free here.

**Lemma (The critical line).** Let $\chi \neq \chi_0$ be a primitive character modulo $q$ with $\chi(-1) = (-1)^j$. Let $T > 0$ with $q \leq T^2$, and let $\operatorname{Re} z = 1/2$. Then
$$|\Gamma_j(z)L(z, \chi)| \leq 2J(\chi, T).$$

Lean: `New.norm_gaussianMellin_mul_LFunction_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* By [Theorem](/decl/New.hasMellin_thetaSeries_char/), $\Gamma_j(z)L(z, \chi)$ is the Mellin integral of $\theta_\chi$ at $z - 1/2$, so it is at most $\int_0^\infty|\theta_\chi(u)|du/u$. By [Corollary](/decl/New.integral_norm_thetaSeries_div/), this is $2\int_{q^{-1/2}}^\infty|\theta_\chi(u)|du/u$. Since $q \leq T^2$, $1/T \leq q^{-1/2}$, so the integral grows when the lower end moves to $1/T$. It is then at most $J(\chi, T)$. $\square$

This is the only place where primitivity and parity enter the detection step. It is the inequality that the chapter on [Dirichlet L-functions](/chapter/dirichlet-l-functions/) prepared. The condition $q \leq T^2$ is the reason that the count of Section 6 takes $T^2 = NX$.

**Lemma (The Gaussian factor).** The function $\Gamma_j$ is holomorphic on $\operatorname{Re} s > 0$, and there is $G \in \mathbb{R}$ with $|\Gamma_j(s)| \leq G$ for $1/2 \leq \operatorname{Re} s \leq 2$. If $K \subset \mathbb{C}$ is compact with $\operatorname{Re} s > 0$ on $K$, there is $c > 0$ with $c \leq |\Gamma_j(s)|$ for every $s \in K$.

Lean: `New.gaussianMellin_differentiableOn_and_bdd`, `New.exists_pos_le_norm_gaussianMellin` (Lib/Analytic/DirichletTheta.lean).

*Proof.* The weight satisfies $|w_j(t)| \leq 3e^{-t}$ for $t > 0$, so the Mellin integral converges locally uniformly on $\operatorname{Re} s > 0$ and is bounded by $3\int_0^\infty e^{-t}t^{\sigma - 1}dt = 3\Gamma(\sigma)$ on $\operatorname{Re} s = \sigma$, which is bounded for $\sigma \in [1/2, 2]$. For the lower bound, [Lemma](/decl/New.gaussianMellin_eq/) gives $\Gamma_j(s) = \Gamma_{\mathbb R}(s + j)/2$, which has no zero for $\operatorname{Re} s > 0$. A continuous function without zeros on a compact set has a positive minimum of its absolute value. $\square$

### Three lines

**Theorem (Three lines at a zero).** For each $j \in \{0, 1\}$ there is a constant $C$ with the following property. Let $\delta > 0$ and $T > 0$. Let $\chi \neq \chi_0$ be a primitive character modulo $q \leq T^2$ with $\chi(-1) = (-1)^j$ and $J(\chi, T) \leq T^{2\delta}$. Let $s$ be a zero of $L(s, \chi)$ with $1/2 + 9\delta \leq \operatorname{Re} s \leq 1$. Then
$$|\Gamma_j(s)|^2 \leq C\,T^{-2\delta}.$$

Lean: `New.three_lines_bound_of_LFunction_eq_zero` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $G$ be the bound for $\Gamma_j$ of the last lemma, and put $C = 9 + G^2$. Since $q \geq 1$ and $q \leq T^2$, we have $T \geq 1$. Put
$$\Psi(z) = \Gamma_j(z)L(z, \chi)\mathcal M(z) - \Gamma_j(z)^2.$$
On $\operatorname{Re} z = 1/2$, the critical line lemma and the hypothesis give $|\Gamma_jL| \leq 2T^{2\delta}$, and the mollifier lemma gives $|\mathcal M| \leq T^{2\delta}$. So $|\Psi| \leq 2T^{4\delta} + G^2 \leq CT^{4\delta}$. On $\operatorname{Re} z = 2$, the right line lemma gives $|\Psi| \leq 9/T \leq CT^{-1}$. The function $\Psi$ is holomorphic on $\operatorname{Re} z > 0$, since $L(\cdot, \chi)$ is entire for $\chi \neq \chi_0$. It is bounded on the closed strip, since $\Gamma_jL$ is the Mellin transform of a function that is $O(e^{-u})$ (by [Lemma](/decl/New.norm_thetaSeries_le/) and the bound near $0$ in [theta series](/chapter/dirichlet-l-functions/)), and $\Gamma_j$, $\mathcal M$ are bounded. The three lines theorem with $a = 1/2$, $b = 2$ and $\lambda = (\operatorname{Re} s - 1/2)/(3/2)$ gives
$$|\Psi(s)| \leq (CT^{4\delta})^{1 - \lambda}(CT^{-1})^{\lambda} = C\,T^{4\delta - \lambda(1 + 4\delta)}.$$
Since $\operatorname{Re} s - 1/2 \geq 9\delta$, we have $\lambda \geq 6\delta$, and the exponent is at most $4\delta - 6\delta = -2\delta$. Since $T \geq 1$, $|\Psi(s)| \leq CT^{-2\delta}$. At the zero, $L(s, \chi) = 0$, so $\Psi(s) = -\Gamma_j(s)^2$. $\square$

The factor $9$ in $1/2 + 9\delta$ is what this proof needs: the exponent $4\delta(1 - \lambda) - \lambda$ is at most $-2\delta$ exactly when $\lambda(1 + 4\delta) \geq 6\delta$. The hypothesis $\operatorname{Re} s \leq 1$ makes $\lambda \leq 1/3$, so $s$ is in the strip. The constant $C$ depends only on $j$, through $G$.

**Theorem (A zero forces a large tail).** Let $j \in \{0, 1\}$, $\delta > 0$ and $H \in \mathbb{R}$. For every sufficiently large $T$ the following holds. Let $\chi \neq \chi_0$ be a primitive character modulo $q \leq T^2$ with $\chi(-1) = (-1)^j$. If $L(s, \chi) = 0$ for some $s$ with $\operatorname{Re} s \geq 1/2 + 9\delta$ and $|\operatorname{Im} s| \leq H$, then
$$T^{2\delta} < J(\chi, T).$$

Lean: `New.eventually_rpow_lt_thetaTailIntegral` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $C$ be the constant of the last theorem. Let $c > 0$ be a lower bound for $|\Gamma_j|$ on the compact rectangle $1/2 \leq \operatorname{Re} s \leq 1$, $|\operatorname{Im} s| \leq H$. Take $T > 0$ so large that $CT^{-2\delta} < c^2$. Let $s$ be a zero in the box. By Mathlib's non-vanishing on $\operatorname{Re} s \geq 1$, $\operatorname{Re} s < 1$. If $J(\chi, T) \leq T^{2\delta}$, the last theorem gives $c^2 \leq |\Gamma_j(s)|^2 \leq CT^{-2\delta} < c^2$, a contradiction. $\square$

The threshold for $T$ depends on $j$, $\delta$ and $H$, and on nothing else. It does not depend on $q$, on $\chi$ or on $s$: the quantifier over $T$ comes first in the Lean statement (`∀ᶠ T in atTop, ∀ {q} ...`). This uniformity is what allows Section 6 to apply the theorem to all twists at once.

**Remark (Formalization).** The height $H$ enters only through the lower bound $c$ for $|\Gamma_j|$. The source does not compute the threshold, and the argument needs only its existence, since $H = |\operatorname{Im}\rho|$ is fixed in the [Landau criterion](/chapter/landau-criterion/). The source applies Mathlib's three lines theorem in the form with explicit bounds on the two boundary lines; the hypotheses `BddAbove` and `DiffContOnCl` are proved from the lemma on $\Gamma_j$ and from the Mellin bound on $\Gamma_jL$.

**Example.** Take $\delta = 1/90$, so the box starts at $\operatorname{Re} s = 0.6$. The theorem says: for large $T$, every primitive $\chi$ of conductor at most $T^2$ with a zero in $\operatorname{Re} s \geq 0.6$, $|\operatorname{Im} s| \leq H$, has $J(\chi, T) > T^{1/45}$. For a "random" $\chi$ one expects $\theta_\chi(u)$ to be of size $u^{1/2}(1/u)^{1/2} = 1$ for $u \leq 1$ by square root cancellation in $\sum_{n \leq 1/u}\chi(n)$, which gives $J(\chi, T) \approx \log T$. So the theorem detects a zero by a power saving over the random size. Section 5 shows that the average of $J$ over the twists that Section 6 needs is $O(T^{\delta})$.
