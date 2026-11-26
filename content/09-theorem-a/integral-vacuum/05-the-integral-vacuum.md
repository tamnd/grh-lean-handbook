---
title: The integral vacuum
lean:
  - New/Derivatives/Vacuum/IntegralVacuum.lean
  - Lib/Weil/Construction/FourierInversion.lean
  - Lib/CM/FiniteLattices.lean
  - Lib/CM/ChowlaSelberg.lean
decls:
  - New.Parameters.exists_norm_gal_torsion_value_le
  - New.CMLattice.exists_norm_twistedTranslate_theta_le
  - New.CMLattice.complex_multiplication_theta
  - New.Space.exists_fourier_coefficients
  - New.Space.norm_mul_vacElem_le_one_of_eq_sum
  - New.Parameters.exists_smul_vac_eq_sum
  - New.Parameters.zetaCoord
  - New.Parameters.zetaCoord_smul
  - New.Parameters.zetaCoordThetaTranslate
  - New.Parameters.zetaLinearSeries
  - New.Parameters.IsThetaProduct
  - New.Parameters.IsThetaProduct.theta_eq_one
  - New.Parameters.exists_isThetaProduct
  - New.Parameters.exists_isThetaProduct_cmCurve
  - New.Parameters.IsThetaProduct.exists_smul_vacElem_eq_sum
  - New.Parameters.sq_q₁_pow_card_infinitePlace_le
  - New.Parameters.exists_mul_vacElem_integral_bounded
  - New.Parameters.vacuumBoundConst
  - New.Parameters.IsVacuumScale
  - New.Parameters.vacuumScale
  - New.Parameters.isVacuumScale_vacuumScale
  - New.Parameters.vacuumScale_ne_zero
  - New.Parameters.intVacuum
  - New.Parameters.intVacuum_finVec_eq_prod
  - New.Parameters.norm_intVacuum_le_one
  - New.Parameters.norm_gal_intVacuum_le
  - New.Parameters.exists_algEquiv_norm_eq
  - New.Parameters.norm_ringEquiv_intVacuum_le
  - New.Parameters.norm_dataInner_self_le
  - New.Parameters.exists_intVacuum_ne_zero
  - New.Parameters.integralAfter
  - New.Parameters.standardData
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The integral vacuum

This section applies the theorem of Section 4 to the frame of powers of $\zeta$, with the theta function $\theta_C$ of the curve in every factor. The result is a vector $F$ with $\theta(F) = 1$ whose values at finite points are integral. Fourier inversion then writes a nonzero multiple of $\mathrm{vac}$ as a sum of translates of $F$. The values of that multiple are integral and have bounded conjugates. This gives the scalar $c_s$ and the integral vacuum $\theta^\circ = c_s^n\,\mathrm{vac}$.

### Coordinates along the frame of powers

**Definition (Coordinates).** For $0 \le k < q_1$ and $y \in E$, put
$$\mathrm{zc}_k(y) = -\frac{\mathrm{tr}_{E/K}(y\, \bar\zeta^k)}{q_1} \in K .$$
For a CM lattice $C$ and a unit $\Omega$ of $\mathbb{C}$, let $\vartheta_{k,y} = T^1_{\mathrm{zc}_k(y)\Omega}\, \theta_C$ be the twisted translate of degree $1$ of the theta function of $C$.

Lean: `New.Parameters.zetaCoord`, `New.Parameters.zetaCoord_smul`, `New.Parameters.zetaCoordThetaTranslate` (New/Derivatives/Vacuum/IntegralVacuum.lean).

The coordinate is $K$-linear, so $\mathrm{zc}_k(ay) = a\,\mathrm{zc}_k(y)$ for $a \in K$. By the trace lemma of Section 2, $\mathrm{zc}_k(y)$ is $-\langle y, \zeta^k\rangle/q_1$, the coordinate of $-y$ along the frame vector $\zeta^k/q_1$. Let $\lambda_{k,j}(c)$ be the linear form $(\Omega/q_1)(c/\mathrm{areaScale}) \sum_\tau \overline{\tau(\zeta)}^{\,k} X_{\tau,j}$.

Lean: `New.Parameters.zetaLinearSeries` (New/Derivatives/Vacuum/IntegralVacuum.lean).

**Definition (Theta product).** Let $V$ be a space of rank $n$, $C$ a CM lattice, $\Omega$ a unit of $\mathbb{C}$ and $e \ge 1$ an integer. A vector $F$ is a *theta product* for $C$, $\Omega$ and $e$ if:

1. $F \in V^{\mathrm{fin}}$;
2. for every $\gamma \in E^n$, $\theta(\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F) = \prod_{k < q_1} \prod_{j} \vartheta_{k,\gamma_j}(0)^{q_1}$;
3. for every $\gamma \in E^n$ and $c \in \mathbb{C}$, $J_c(\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F) = \prod_{k} \prod_j \widehat{\vartheta_{k,\gamma_j}}(\lambda_{k,j}(c))^{q_1}$;
4. for every $p$-adic place and every finite adelic vector $x$, $|\iota_p(F(\mathrm{fin}(x)))| \le 1$;
5. $\mathrm{entireTheta}\, F$ is a theta function for $q_1 e\, \mathfrak{a}_0^n$.

Lean: `New.Parameters.IsThetaProduct` (New/Derivatives/Vacuum/IntegralVacuum.lean).

**Lemma.** If $F$ is a theta product, then $\theta(F) = 1$.

Lean: `New.Parameters.IsThetaProduct.theta_eq_one` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* Take $\gamma = 0$ in item 2. Then every coordinate is $0$, every factor is $\theta_C(0)$, and $\theta_C(0) = 1$ by the normalization of the theta function of a CM lattice. $\square$

**Theorem (Theta products exist).** Let $V$ be standard, and let $C$ be a CM lattice of area $|\Omega|^2\sqrt d/2$ whose lattice contains $\Omega e$. Then $V$ has a theta product for $C$, $\Omega$ and $e$.

Lean: `New.Parameters.exists_isThetaProduct` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* Apply the theorem of Section 4 with these data:

- $\delta = q_1 e$, so $N = \delta\bar\delta = q_1^2 e^2$;
- the frame of powers $\zeta^k$, each taken $q_1$ times, of length $M = q_1^2$ (Section 2);
- the triple $(1, 0, 0)$ in every factor, so every section is $\theta_C$ and has degree $1 = m_k$;
- $a = \Omega e$, which lies in the lattice by hypothesis.

The area condition holds:
$$\frac{|a|^2}{N} \cdot M \cdot \frac{\sqrt d}{2} = \frac{|\Omega|^2 e^2}{q_1^2 e^2}\, q_1^2\, \frac{\sqrt d}{2} = |\Omega|^2\frac{\sqrt d}{2} .$$
The scale is $b = a/\bar\delta = \Omega/q_1$. The theorem gives $F$ with items 1, 4 and 5. For items 2 and 3, the shift of the factor $(k, j)$ is
$$s(\gamma) = -\frac{\Omega}{q_1}\sum_\tau \tau(\gamma_j)\,\overline{\tau(\zeta^k)} = \mathrm{zc}_k(\gamma_j)\,\Omega,$$
so the translated factor is $\vartheta_{k,\gamma_j}$, and the linear form at scale $c$ is $\lambda_{k,j}(c)$. Each frame vector is taken $q_1$ times, so each factor appears to the power $q_1$. The product formula and the jet formula of Section 4 give items 2 and 3. $\square$

**Corollary.** A standard space has a theta product for the CM curve, $\Omega = \Omega_0$ and $e = 1$.

Lean: `New.Parameters.exists_isThetaProduct_cmCurve` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The area of $\Omega_0\mathcal{O}_K$ is $|\Omega_0|^2\sqrt d/2$, and $\Omega_0$ lies in it (Section 3). $\square$

### A multiple of the vacuum

For $x$ a finite adelic vector, let $\varrho^\pm(x)$ be the finite Heisenberg operator, the translation $\varrho(\mathrm{fin}(x))$ times the semicharacter of $x$.

**Theorem (Fourier coefficients).** Let $V$ be standard, $\delta$ integral with $\delta\bar\delta = N \ne 0$, and let $\mathrm{entireTheta}\,\varphi$ be a theta function for $\bar\delta\mathfrak{a}_0^n$. Let $r = f \cdot n$. There are finite families $(y_i)$ with $\delta y_i \in \mathfrak{a}_0^n$, $(\gamma_j)$ of $N^r$ elements of $\mathfrak{a}_0^n$, and numbers $c_i$, such that
$$c_i\,\mathrm{vac} = \sum_j \varrho^\pm(\alpha^{-1}\gamma_j)\,\varrho(\mathrm{fin}(-\alpha^{-1}y_i))\,\varphi \quad\text{for all } i, \qquad \sum_i c_i\, \varrho(\mathrm{fin}(\alpha^{-1}y_i))\,\mathrm{vac} = N^r \varphi .$$

Lean: `New.Space.exists_fourier_coefficients` (Lib/Weil/Construction/FourierInversion.lean).

This is the explicit form of Fourier inversion of Section 4.

**Proposition.** Let $V$ be standard and $\delta$ integral with $\delta\bar\delta = N \ne 0$. Let $\mathrm{entireTheta}\, F$ be a theta function for $\bar\delta\mathfrak{a}_0^n$ with $\theta(F) = 1$. Then there are $c \ne 0$, a finite set $\Gamma$ with $N^{fn}$ elements, finite adelic vectors $a_j$ and $b$, such that
$$c\,\mathrm{vac} = \sum_{j \in \Gamma} \varrho^\pm(a_j)\, \varrho(\mathrm{fin}(b))\, F .$$

Lean: `New.Parameters.exists_smul_vac_eq_sum` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* Take the families of the last theorem. If all $c_i$ were $0$, the second identity would give $N^r F = 0$, so $N^r = N^r\theta(F) = 0$, which is false. Take $i$ with $c_i \ne 0$, and $b = -\alpha^{-1}y_i$. $\square$

**Corollary.** If $F$ is a theta product of level $e = 1$ in a standard space, then there are $c \ne 0$, a set $\Gamma$ with $(q_1^2)^{fn}$ elements, and $a_j$, $b$ with $c\,\mathrm{vac} = \sum_{j\in\Gamma}\varrho^\pm(a_j)\varrho(\mathrm{fin}(b))F$.

Lean: `New.Parameters.IsThetaProduct.exists_smul_vacElem_eq_sum` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* Use $\delta = q_1$, $N = q_1^2$, item 5 and the lemma $\theta(F) = 1$. $\square$

**Lemma.** If the values of $\varphi$ at all finite points are integral at $\iota_p$, and $c\,\mathrm{vac} = \sum_j \varrho^\pm(a_j)\varrho(\mathrm{fin}(b))\varphi$, then the values of $c\,\mathrm{vac}$ at all finite points are integral at $\iota_p$.

Lean: `New.Space.norm_mul_vacElem_le_one_of_eq_sum` (Lib/Weil/Construction/FourierInversion.lean).

*Proof.* The value at $\mathrm{fin}(x)$ of the right side is a sum of values of $\varphi$ at finite points, times values of the self-dual character of the finite adeles. These values are roots of unity, so they have absolute value $1$ at $\iota_p$. The absolute value at $\iota_p$ is ultrametric. $\square$

### The bound on conjugates

**Lemma.** There is $M_0$ such that $|(T^1_u\theta_C)(0)| \le M_0$ for every CM lattice $C$ for $K$ and every $u \in \mathbb{C}$.

Lean: `New.CMLattice.exists_norm_twistedTranslate_theta_le` (Lib/CM/FiniteLattices.lean).

*Proof.* For one lattice, $u \mapsto |(T^1_u\theta_C)(0)|$ is continuous and periodic, so it is bounded. It depends only on the lattice of $C$. The normalization of a CM lattice fixes its scale, and the source proves that only finitely many lattices of $\mathbb{C}$ underlie a CM lattice for $K$. $\square$

**Lemma (Torsion values of the curve).** There is $M_0$ such that for every $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and every $x \in K$,
$$\bigl|\sigma\bigl((T^1_{x\Omega_0}\theta_C)(0)\bigr)\bigr| \le M_0,$$
for $C$ the CM curve.

Lean: `New.Parameters.exists_norm_gal_torsion_value_le` (New/Derivatives/Vacuum/IntegralVacuum.lean); `New.CMLattice.complex_multiplication_theta` (Lib/CM/ChowlaSelberg.lean).

*Proof.* By the theorem of complex multiplication for theta functions ([CM elliptic curves](/chapter/cm-elliptic-curves/)), $\sigma$ maps the Taylor series of $T^1_{x\Omega_0}\theta_C$ to the Taylor series of $T^1_{x'\Omega}\theta_{C^\sigma}$ for the conjugate lattice, a period $\Omega$, and every $x'$ near an idele multiple of $x$. Such $x' \in K$ exist by density. Compare the constant terms, and apply the last lemma to $C^\sigma$. $\square$

**Lemma.** $(q_1^2)^f \le e^{2q_1^2}$.

Lean: `New.Parameters.sq_q₁_pow_card_infinitePlace_le` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* $f = \varphi(q_1) \le q_1$ and $q_1 \le e^{q_1}$. $\square$

**Theorem (Integral vacuum of rank one).** There is $C \in \mathbb{N}$ such that for every $s$ there is $c \ne 0$ with, for the standard space of rank one over $E$:

1. $|\iota_p(c\,\mathrm{vac}(\mathrm{fin}(x)))| \le 1$ for every prime $p$, every $p$-adic place and every finite adele $x$;
2. $|\sigma(c\,\mathrm{vac}(\mathrm{fin}(x)))| \le \exp(C q_1^2)$ for every $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and every $x$.

Lean: `New.Parameters.exists_mul_vacElem_integral_bounded` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* Let $M_0$ be the constant of the lemma on torsion values, and $C = \lceil M_0\rceil + 2$. Fix $s$ and let $F$ be the theta product of level one for the CM curve. Take $c$, $\Gamma$, $a_j$, $b$ from the corollary, with $|\Gamma| = (q_1^2)^f$. Item 1 follows from item 4 of the theta product and the lemma on integral values.

For item 2, the value $c\,\mathrm{vac}(\mathrm{fin}(x))$ is a sum over $\Gamma$ of values of $F$ at finite points times roots of unity. A value of $F$ at a finite point is $\theta(\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F)$ for some $\gamma \in E$, since $F$ lies in the finite part. By item 2 of the theta product it is a product of $q_1 \cdot q_1$ numbers $\vartheta_{k,\gamma}(0) = (T^1_{\mathrm{zc}_k(\gamma)\Omega_0}\theta_C)(0)$, with $\mathrm{zc}_k(\gamma) \in K$. Each conjugate of each factor has modulus at most $M_0 \le e^{M_0}$. So
$$|\sigma(c\,\mathrm{vac}(\mathrm{fin}(x)))| \le |\Gamma|\, e^{M_0 q_1^2} \le e^{2q_1^2}\, e^{\lceil M_0\rceil q_1^2} = \exp(C q_1^2) . \qquad \square$$

**Definition (Vacuum scale).** $C_{\mathrm{vac}}$ is a constant $C$ of the theorem. A number $c$ is a *vacuum scale* for $s$ if $c \ne 0$ and $c$ has properties 1 and 2 of the theorem with $C = C_{\mathrm{vac}}$. The number $c_s$ is a vacuum scale for $s$.

Lean: `New.Parameters.vacuumBoundConst`, `New.Parameters.IsVacuumScale`, `New.Parameters.vacuumScale`, `New.Parameters.isVacuumScale_vacuumScale`, `New.Parameters.vacuumScale_ne_zero` (New/Derivatives/Vacuum/IntegralVacuum.lean).

**Remark (Formalization).** The constant $C_{\mathrm{vac}}$ and the scalars $c_s$ are chosen objects. The constant depends only on the parameters $P$, through $d$, and not on $s$. Later chapters use only the three properties, and $C_{\mathrm{vac}}$ enters the bounds of [theta kernels and gauges](/chapter/theta-kernels-gauges/). The source does not compute $c_s$, and a vacuum scale is not unique.

### The integral vacuum in rank n

Recall that $\theta^\circ = c_s^n\,\mathrm{vac}$ for a space of rank $n$.

**Proposition.** Let $V$ be a standard space of rank $n$ and $x$ a finite adelic vector. Then:

1. $\theta^\circ(\mathrm{fin}(x)) = \prod_{i} c_s\,\mathrm{vac}_1(\mathrm{fin}(x_i))$, with $\mathrm{vac}_1$ the vacuum of rank one;
2. $|\iota_p(\theta^\circ(\mathrm{fin}(x)))| \le 1$ at every $p$-adic place;
3. $|\sigma(\theta^\circ(\mathrm{fin}(x)))| \le \exp(C_{\mathrm{vac}}\, q_1^2)^n$ for every $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$;
4. the bound of item 3 holds for every ring automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Parameters.intVacuum_finVec_eq_prod`, `New.Parameters.norm_intVacuum_le_one`, `New.Parameters.norm_gal_intVacuum_le`, `New.Parameters.exists_algEquiv_norm_eq`, `New.Parameters.norm_ringEquiv_intVacuum_le` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The vacuum of a standard space is a product of the vacua of its coordinates, at points with real part $0$. This gives item 1, and items 2 and 3 follow from the case of rank one. For item 4, an automorphism $\sigma$ of $\mathbb{C}$ either fixes $\sqrt{-d}$ or maps it to $-\sqrt{-d}$. In the second case, $\sigma$ composed with complex conjugation fixes $K$ and has the same absolute values. $\square$

**Lemma.** Let $V$ be standard and $f \in \mathcal{S}(V)$ with $|f(\mathrm{fin}(x))| \le M$ for every finite adelic vector $x$. Then the mean $\langle f, f\rangle_{\mathrm{data}}$ of $|f|^2$ has modulus at most $M^2$.

Lean: `New.Parameters.norm_dataInner_self_le` (New/Derivatives/Vacuum/IntegralVacuum.lean).

**Proposition (Nonvanishing).** For a standard space $V$, there is a finite adelic vector $x$ with $\theta^\circ(\mathrm{fin}(x)) \ne 0$.

Lean: `New.Parameters.exists_intVacuum_ne_zero` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* If $\theta^\circ$ vanished at every finite point, then so would $\mathrm{vac}$, as $c_s \ne 0$. The last lemma with $M = 0$ would give $\langle \mathrm{vac}, \mathrm{vac}\rangle_{\mathrm{data}} = 0$. But it is $1$. $\square$

### Standard data

**Definition (Standard data).** Let $\delta \in \mathcal{O}_K$ and let $S$ be a set of finite places of $E$. The group $\mathrm{Int}(\delta, S)$ consists of the finite adelic vectors $x$ such that every coordinate of $\delta x$ is integral at every place in $S$. For a $p$-adic place $\iota_p$, with $\mathcal{O}_p$ the ring of $z \in \mathbb{C}$ with $|\iota_p(z)| \le 1$, the *standard data* are
$$\mathrm{SD}_p(V, \delta) = \mathcal{O}_p\text{-span of } \bigl\{\varrho^\pm(x)\,\theta^\circ : x \in \mathrm{Int}(\delta, \{w : w \mid p\})\bigr\} .$$

Lean: `New.Parameters.integralAfter`, `New.Parameters.standardData` (New/Derivatives/Vacuum/IntegralVacuum.lean).

So standard data are $p$-integral combinations of translates of the integral vacuum by vectors whose denominators at $p$ divide $\delta$. The translations by vectors integral at $p$ keep the values integral at $p$, and the denominators of $\delta$ are tested in [the count and the divisibility of standard data](/chapter/normal-forms/).

**Example.** For $\delta = 1$, $\mathrm{Int}(1, \{w \mid p\})$ is the group of vectors integral above $p$. The vector $\theta^\circ$ itself lies in $\mathrm{SD}_p(V, 1)$, with $x = 0$. Its values at finite points are integral at $\iota_p$ and some value is not zero. This is the starting point of the divisibility argument.

**Remark (Formalization).** The source defines the standard data as a module over the ring $\mathcal{O}_p$ of complex numbers that are integral at $\iota_p$, and not over a ring of algebraic integers. The place $\iota_p$ is any ring homomorphism $\mathbb{C} \to \mathbb{C}_p$. The source defines $\theta^\circ$ for every space, but proves the properties of this section only for standard spaces.
