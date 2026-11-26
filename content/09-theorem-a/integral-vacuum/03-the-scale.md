---
title: The scale
lean:
  - New/Derivatives/Vacuum/TightFrames.lean
  - New/Derivatives/Vacuum/IntegralVacuum.lean
  - New/Derivatives/Field/WeilData.lean
  - Lib/CM/ChowlaSelberg.lean
decls:
  - New.Parameters.cmCurve
  - New.Parameters.cmPeriod
  - New.Parameters.latticeModule_cmCurve
  - New.Parameters.chowlaSelbergUnit
  - New.Parameters.norm_iota_chowlaSelbergUnit
  - New.Parameters.area_mul_norm_chowlaSelbergUnit_sq
  - New.CMLattice.chowla_selberg
  - New.Parameters.areaScale
  - New.Parameters.vacuumRoot
  - New.Parameters.periodFactor
  - New.Parameters.jetScale
  - New.Parameters.exists_norm_adeleExtension_alpha_mul_eq_one
  - New.Parameters.adeleExtension_alpha
  - New.Parameters.norm_iota_vacuumRoot
  - New.Parameters.span_vacuumRoot_eq
  - New.Parameters.norm_iota_periodFactor
  - New.Parameters.norm_periodFactor_mul_conj_le_one
  - New.Parameters.norm_iota_periodFactor_eq_one
  - New.Parameters.jetScale_ne_zero
  - New.Parameters.norm_gal_vacuumRoot
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scale

The theta functions of this chapter are products of theta functions of one CM elliptic curve, composed with linear forms. A linear form $z \mapsto \langle z, w\rangle$ with $w \in \mathfrak{a}_0$ does not yet have the right size. It must be multiplied by a complex number that makes its coefficients integral at every prime and makes the Gaussian factors fit. This section fixes that number. It is the quotient of two transcendental numbers, the root $\mathrm{vacuumRoot}$ of the Weil data and the unit of Chowla and Selberg. Each is known only up to a unit at the primes, and only their absolute values at the $p$-adic places are computed.

Throughout, $p$ is a prime and $\iota_p \colon \mathbb{C} \to \mathbb{C}_p$ is a ring homomorphism, a *$p$-adic place* of $\mathbb{C}$. For a place $\tau$ of $E$, let $\phi_\tau \colon E \to \mathbb{C}_p$ be the embedding $y \mapsto \iota_p(\tau(\bar y))$. It extends to the finite adeles: take the component of an adele at the prime of $E$ that $\phi_\tau$ defines, and apply the continuous extension of $\phi_\tau$ to the completion. This extension is also written $\phi_\tau$.

### The CM curve and its period

**Definition (CM curve and period).** The *CM curve* $C$ is a CM lattice for $K$ whose lattice is $\Omega_0 \mathcal{O}_K$, for a nonzero complex number $\Omega_0$, the *period*.

Lean: `New.Parameters.cmCurve`, `New.Parameters.cmPeriod`, `New.Parameters.latticeModule_cmCurve` (New/Derivatives/Vacuum/TightFrames.lean).

A CM lattice is a lattice in $\mathbb{C}$, stable under $\mathcal{O}_K$, with its theta functions of each degree and a marked point of order two ([CM elliptic curves](/chapter/cm-elliptic-curves/)). The area of a period parallelogram of $\Omega_0\mathcal{O}_K$ is $|\Omega_0|^2 \sqrt d/2$, since $\mathcal{O}_K = \mathbb{Z} + \mathbb{Z}\beta$ and $\beta$ has imaginary part $\sqrt d/2$.

**Remark (Formalization).** The curve and the period are chosen objects. The source proves that some CM lattice with lattice $\Omega_0\mathcal{O}_K$ exists, and takes one by choice. Nothing in the chapter depends on which one. Only $\Omega_0 \ne 0$ and the shape of the lattice are used.

### The unit of Chowla and Selberg

**Theorem (Chowla and Selberg, with a unit).** For a CM lattice $C$ for $K$ there is $u \in \mathbb{C}$ with $|\iota_p(u)| = 1$ at every $p$-adic place, such that for every automorphism $\sigma$ of $\mathbb{C}$ over $K$,
$$\mathrm{area}(C^\sigma)\, |\sigma(u)|^2 = \pi\, e^{C_d}\, \frac{2\pi}{\sqrt d} .$$
Here $C^\sigma$ is the conjugate lattice and $C_d = \gamma - \mathrm{Re}\, L'/L(1, \chi_K)$.

Lean: `New.CMLattice.chowla_selberg` (Lib/CM/ChowlaSelberg.lean).

This is the form of the formula of Chowla and Selberg proved in [CM elliptic curves](/chapter/cm-elliptic-curves/), and the constant $C_d$ is the one of [the weighted prime remainder](/chapter/weighted-prime-remainder/). The *Chowla-Selberg unit* is the number $u$ of this theorem for the CM curve.

**Definition (Chowla-Selberg unit).** $u_{CS}$ is a number $u$ as in the theorem, for $C$ the CM curve.

Lean: `New.Parameters.chowlaSelbergUnit` (New/Derivatives/Vacuum/TightFrames.lean).

**Lemma.** At every $p$-adic place $|\iota_p(u_{CS})| = 1$, and for every $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$
$$\mathrm{area}(C^\sigma)\, |\sigma(u_{CS})|^2 = \pi\, e^{C_d}\, \frac{2\pi}{\sqrt d} .$$

Lean: `New.Parameters.norm_iota_chowlaSelbergUnit`, `New.Parameters.area_mul_norm_chowlaSelbergUnit_sq` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* These are the two properties of the chosen number. $\square$

### The root of the Weil data

The Weil data of $E$ give a splitting character $\upsilon$ and the character $\chi_{\mathrm{fin}}(x) = \upsilon(x)|x|^{-1/2}$ of the finite ideles ([the Weil representation](/chapter/weil-representation/)).

**Definition (Root of the vacuum).** $\mathrm{vacuumRoot} = \chi_{\mathrm{fin}}(\alpha)^{-1/f}$, with the principal branch of the complex power and $f$ the number of places of $E$.

Lean: `New.Parameters.vacuumRoot` (New/Derivatives/Field/WeilData.lean).

So $\mathrm{vacuumRoot}^f = \chi_{\mathrm{fin}}(\alpha)^{-1}$. [The field E at the primes](/chapter/field-at-primes/) shows that a positive power of $\mathrm{vacuumRoot}$ lies in $K$, and computes its absolute value under the automorphisms of $\mathbb{C}$ over $K$:

**Proposition.** For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, $|\sigma(\mathrm{vacuumRoot})|^2 = \mathrm{rd}(E)/\sqrt d$, where $\mathrm{rd}(E)$ is the root discriminant of $E$.

Lean: `New.Parameters.norm_gal_vacuumRoot` (New/Derivatives/Field/WeilData.lean).

### The scale

**Definition (Scale).** Put
$$\mathrm{areaScale} = \sqrt{2\pi/\sqrt d}, \qquad \mathrm{periodFactor} = \frac{\mathrm{vacuumRoot}}{u_{CS}}, \qquad \mathrm{jetScale} = \frac{\mathrm{periodFactor} \cdot \mathrm{areaScale}}{\Omega_0} .$$

Lean: `New.Parameters.areaScale`, `New.Parameters.periodFactor`, `New.Parameters.jetScale` (New/Derivatives/Vacuum/TightFrames.lean).

The number $\mathrm{areaScale}$ is the ratio of the Fock coordinates of [the Weil representation](/chapter/weil-representation/) to the coordinates on the curve. The number $\mathrm{periodFactor}$ multiplies the linear forms. The number $\mathrm{jetScale}$ is the scale at which Taylor series of theta functions are taken in this chapter and the next ones.

**Lemma.** $\mathrm{jetScale} \ne 0$.

Lean: `New.Parameters.jetScale_ne_zero` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The proposition with $\sigma = 1$ gives $|\mathrm{vacuumRoot}|^2 = \mathrm{rd}(E)/\sqrt d > 0$. The lemma on $u_{CS}$ with $\sigma = 1$ gives $u_{CS} \ne 0$, since the right side is not zero. The period is a unit and $\mathrm{areaScale} > 0$. $\square$

### The scale at the primes

The next lemmas compute $|\iota_p(\mathrm{periodFactor})|$. The first one is a density statement.

**Lemma.** For an embedding $\phi \colon E \to \mathbb{C}_p$ there is $y \in E$ such that $\alpha y$ is an integral adele and $|\phi(\alpha y)| = 1$.

Lean: `New.Parameters.exists_norm_adeleExtension_alpha_mul_eq_one` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The set of finite adeles $x$ with $p^{-1}(\alpha x - 1) \in \hat{\mathcal{O}}$ is open and contains $\alpha^{-1}$. As $E$ is dense in the finite adeles, it contains some $y \in E$. Then $\alpha y = 1 + p\,c$ with $c$ integral, so $\alpha y$ is integral and $|\phi(p c)| \le |p| < 1$. In an ultrametric field $|1 + x| = 1$ for $|x| < 1$. $\square$

**Lemma.** For an embedding $\phi \colon E \to \mathbb{C}_p$, $\phi(\alpha) = \phi(P'(\zeta))^{-1}$ if the prime of $\phi$ contains $\beta$, and $\phi(\alpha) = 1$ otherwise.

Lean: `New.Parameters.adeleExtension_alpha` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* This is the definition of $\alpha$, read at one prime. $\square$

**Proposition.** For every place $\tau$, $|\iota_p(\mathrm{vacuumRoot})| = |\phi_\tau(\alpha)|^{-1}$.

Lean: `New.Parameters.norm_iota_vacuumRoot` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* First, $|\phi_\tau(\alpha)|$ does not depend on $\tau$. The conjugates $g(P'(\zeta))$, $g \in \mathrm{Gal}(E/K)$, have the same valuation at every prime, since the different is stable under $g$. So $|\iota_p(\overline{\tau(P'(\zeta))})|$ does not depend on $\tau$. The condition $\beta \in$ (prime of $\phi_\tau$) does not depend on $\tau$, since $\tau(\beta) = \beta$ for all $\tau$. The last lemma now gives the claim. Second, the character $\chi_{\mathrm{fin}}$ satisfies $|\iota_p(\chi_{\mathrm{fin}}(\alpha))| = \prod_\tau |\phi_\tau(\alpha)|$ ([the Weil representation](/chapter/weil-representation/)). So
$$|\iota_p(\mathrm{vacuumRoot})|^f = |\iota_p(\chi_{\mathrm{fin}}(\alpha))|^{-1} = |\phi_\tau(\alpha)|^{-f} .$$
Both sides are not negative, and $f > 0$, so one can take $f$-th roots. $\square$

**Proposition.** Let $\mathcal{O}_p \subset \mathbb{C}$ be the ring of $z$ with $|\iota_p(z)| \le 1$. For every place $\tau$, the $\mathcal{O}_p$-module generated by $\mathrm{vacuumRoot}$ is the $\mathcal{O}_p$-module generated by the numbers $\overline{\tau(y)}$ with $\alpha y \in \hat{\mathcal{O}}$, that is, with $y \in \mathfrak{a}_0^{-1}$.

Lean: `New.Parameters.span_vacuumRoot_eq` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* By the last proposition,
$$\Bigl|\iota_p\Bigl(\frac{\overline{\tau(y)}}{\mathrm{vacuumRoot}}\Bigr)\Bigr| = |\phi_\tau(y)|\, |\phi_\tau(\alpha)| = |\phi_\tau(\alpha y)| .$$
If $\alpha y$ is integral, the right side is at most $1$, so $\overline{\tau(y)}$ is an $\mathcal{O}_p$-multiple of $\mathrm{vacuumRoot}$. In particular $\mathrm{vacuumRoot} \ne 0$, since $\phi_\tau(\alpha) \ne 0$. Conversely, the density lemma gives $y$ with $\alpha y$ integral and $|\phi_\tau(\alpha y)| = 1$. Then $\mathrm{vacuumRoot}/\overline{\tau(y)}$ lies in $\mathcal{O}_p$, and $\mathrm{vacuumRoot}$ is a multiple of a generator. $\square$

**Corollary.** For every place $\tau$, $|\iota_p(\mathrm{periodFactor})| = |\phi_\tau(\alpha)|^{-1}$.

Lean: `New.Parameters.norm_iota_periodFactor` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Divide by $u_{CS}$, which has absolute value $1$ at $\iota_p$. $\square$

**Corollary (Integral linear forms).** For $y \in \mathfrak{a}_0$ and every place $\tau$,
$$|\iota_p(\mathrm{periodFactor} \cdot \overline{\tau(y)})| \le 1 .$$

Lean: `New.Parameters.norm_periodFactor_mul_conj_le_one` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The left side is $|\phi_\tau(y)|\,|\phi_\tau(\alpha)|^{-1} = |\phi_\tau(\alpha^{-1} y)|$, and $\alpha^{-1}y$ is integral. $\square$

So the linear form $z \mapsto \mathrm{periodFactor} \sum_\tau \overline{\tau(y)}\, z_\tau$ has $p$-integral coefficients for every $y \in \mathfrak{a}_0$. This is the form that Section 4 composes with the theta functions of the curve.

**Proposition.** If $p \nmid q_1$, then $|\iota_p(\mathrm{periodFactor})| = 1$.

Lean: `New.Parameters.norm_iota_periodFactor_eq_one` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Take $\tau = 1$ in the span proposition. Every $y \in \mathfrak{a}_0^{-1}$ is integral, since $\mathcal{O}_E \subseteq \mathfrak{a}_0$, so every $\overline{\tau(y)}$ lies in $\mathcal{O}_p$, and so does $\mathrm{vacuumRoot}$. The number $q_1$ lies in $\mathfrak{a}_0^{-1}$, since $q_1 \mathfrak{a}_0 \subseteq \mathcal{O}_E$ ([the field E at the primes](/chapter/field-at-primes/)). So $q_1 = c \cdot \mathrm{vacuumRoot}$ with $c \in \mathcal{O}_p$. As $p \nmid q_1$, $|\iota_p(q_1)| = 1$, and $1 \le |\iota_p(\mathrm{vacuumRoot})|$. $\square$

**Example.** At a prime $p$ that divides $q_1$, the scale need not be a unit. Let $\mathfrak{P}$ be the prime of $\phi_\tau$. If $\beta \notin \mathfrak{P}$, then $\phi_\tau(\alpha) = 1$, and $\mathrm{periodFactor}$ is a unit at $\iota_p$. If $\beta \in \mathfrak{P}$, then $|\iota_p(\mathrm{periodFactor})| = |\phi_\tau(P'(\zeta))|$, which is less than $1$ when $\mathfrak{P}$ divides the different. Since $\beta\bar\beta = (d+1)/4$ and $d + 1 \equiv q_0/2 \pmod{q_0}$, the primes $3$, $5$, $7$ and $11$ divide $\beta\bar\beta$. They divide $q_1$ and ramify in $E$.

### The size at the infinite places

**Proposition.** Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and let $\Omega$ be a unit of $\mathbb{C}$ such that the area of $C^\sigma$ is $|\Omega|^2 \sqrt d/2$. Then
$$\Bigl| \frac{\sigma(\mathrm{periodFactor})}{\Omega}\, \mathrm{areaScale} \Bigr|^2 = \Omega_E^{-1}, \qquad \Omega_E = e^{C_d}\, \frac{2\pi}{\mathrm{rd}(E)} .$$

Lean: `New.Parameters.norm_gal_periodFactor_div_mul_areaScale_sq` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* From $|\Omega|^2 = 2\,\mathrm{area}(C^\sigma)/\sqrt d$,
$$\Bigl| \frac{\sigma(\mathrm{periodFactor})}{\Omega}\, \mathrm{areaScale} \Bigr|^2 = \frac{|\sigma(\mathrm{vacuumRoot})|^2}{|\sigma(u_{CS})|^2} \cdot \frac{2\pi}{\sqrt d} \cdot \frac{\sqrt d}{2\,\mathrm{area}(C^\sigma)} = \frac{|\sigma(\mathrm{vacuumRoot})|^2\, \pi}{\mathrm{area}(C^\sigma)\, |\sigma(u_{CS})|^2} .$$
Insert the value of $|\sigma(\mathrm{vacuumRoot})|^2$ and the formula of Chowla and Selberg:
$$\frac{(\mathrm{rd}(E)/\sqrt d)\, \pi}{\pi e^{C_d}\, 2\pi/\sqrt d} = \frac{\mathrm{rd}(E)}{2\pi e^{C_d}} = \Omega_E^{-1} . \qquad \square$$

For $\sigma = 1$ and $\Omega = \Omega_0$ the hypothesis holds, and the proposition says $|\mathrm{jetScale}|^2 = \Omega_E^{-1}$. The number $\Omega_E$ is positive.

**Remark (Formalization).** The number $u_{CS}$ is a chosen object. The statements of the chapter use only its two properties, so they hold for every choice. The number $\mathrm{vacuumRoot}$ is not chosen: it is defined with the principal branch of the complex power. The source defines $\Omega_E$ as the real number $e^{C_d}\cdot 2\pi/\mathrm{rd}(E)$, with $C_d$ written out through $L'/L(1,\chi_K)$. The $p$-adic place $\iota_p$ is any ring homomorphism $\mathbb{C} \to \mathbb{C}_p$, with no continuity condition, so all statements hold for every such map.
