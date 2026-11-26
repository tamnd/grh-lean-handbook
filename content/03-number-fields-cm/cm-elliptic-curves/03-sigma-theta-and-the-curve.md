---
title: Sigma, theta and the curve
lean:
  - Lib/CM/Sigma/Basic.lean
  - Lib/CM/Sigma/ThetaSections.lean
decls:
  - PeriodPair.σ
  - New.sigma_add_mul_sigma_sub
  - New.exists_lattice_of_g₂_g₃
  - New.CMLattice
  - New.CMLattice.θ
  - New.CMLattice.theta_sq
  - New.CMLattice.disc_eq
  - New.CMLattice.weierstrass_equation
  - New.CMLattice.theta_add_mul_theta_sub
  - New.CMLattice.sections_le_span_monomialSection
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sigma, theta and the curve

This section defines the objects of the source: the sigma function of a lattice as a theta function, the CM lattices for $K = \mathbb{Q}(\sqrt{-d})$, the theta function $\theta$ of a CM lattice, and the plane cubic $y^2 + a_1 xy = x^3 + x$. The main results are that the cubic has the discriminant $a_1^4 - 64$ ([Lemma](/decl/New.CMLattice.disc_eq/)) and that the coordinates $x$, $y$ satisfy it ([Lemma](/decl/New.CMLattice.weierstrass_equation/)). All later sections work with these objects.

### The sigma function as a theta function

Let $\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ be a lattice. Its area is $A = |\operatorname{Im}(\bar\omega_1 \omega_2)|$, and its hermitian form is
$$H(l, z) = \frac{\pi}{A}\, \bar l z.$$
The imaginary part $E = \operatorname{Im} H$ takes integer values times $\pi$ on $\Lambda \times \Lambda$, and $E(\omega_1, \omega_2) = \pm\pi$. A theta function for $H$ and a multiplier $\chi : \Lambda \to \{z : |z| = 1\}$ is an entire function $f$ with
$$f(z + l) = \chi(l)\, \exp\bigl(H(l, z) + \tfrac12 H(l, l)\bigr) f(z) \qquad (l \in \Lambda,\ z \in \mathbb{C}).$$
The space of these functions has dimension $1$ for this $H$ and every admissible $\chi$, by the theorem of Appell and Humbert. The source works with the multiplier $\chi_\sigma(l) = 1$ if $l/2 \in \Lambda$ and $\chi_\sigma(l) = -1$ otherwise.

**Definition (The sigma function).** For a lattice $\Lambda$, the sigma function $\sigma$ of the source is an odd theta function for the form $H$ and the multiplier $\chi_\sigma$, with $\sigma'(0) = 1$.

Lean: `PeriodPair.σ` (Lib/CM/Sigma/Basic.lean), with the existence statement `New.exists_odd_mem_thetaSpace_deriv_eq_one`.

The Weierstrass sigma function $\sigma_W$ of Section 2 satisfies $\sigma_W(z + l) = \pm\exp(\eta(l)(z + l/2))\sigma_W(z)$, where $\eta$ is additive. By Legendre's relation, $\eta(l) = \pi\bar l/A + c\,l$ for one constant $c$. So $\sigma(z) = \exp(-c z^2/2)\, \sigma_W(z)$, and the sign in the transformation law is $\chi_\sigma$. The two functions have the same zeros, and $\sigma$ also vanishes exactly on $\Lambda$, with simple zeros (`New.sigma_eq_zero_iff`, `New.deriv_sigma_ne_zero`). The function $\wp$ is $-(\log \sigma_W)''$, so $-(\log \sigma)'' = \wp + c$.

**Remark (Formalization).** The source does not define $\sigma$ by the product. It proves that a theta function for $(H, \chi_\sigma)$ exists, takes its odd part, and normalises the derivative at $0$. Then it defines $\sigma$ with `choose`. The space of such functions is a line, so the odd function with $\sigma'(0) = 1$ is unique, and the choice has no effect on the value. The source does not state the uniqueness. It uses only the properties of the choice: the transformation law, oddness, $\sigma'(0) = 1$, and the zeros. The form $H$ with the multiplier $\chi_\sigma$ is a global instance of Appell-Humbert data (`New.isAppellHumbert_hermitianForm`), proved with classical logic.

**Lemma (The addition formula).** For $u, v \notin \Lambda$,
$$\sigma(u + v)\, \sigma(u - v) = (\wp(v) - \wp(u))\, \sigma(u)^2 \sigma(v)^2.$$

Lean: `New.sigma_add_mul_sigma_sub` (Lib/CM/Sigma/Basic.lean).

*Proof.* For fixed $v$, the function $z \mapsto \sigma(z + v)\sigma(z - v)$ is a theta function for $(2H, \chi_\sigma^2)$, since the factors of automorphy at $z + v$ and $z - v$ multiply to the square of the one at $z$. This space has dimension $2$ and is spanned by $\sigma^2$ and $\wp \sigma^2$, where $\wp\sigma^2$ is extended by its limit on $\Lambda$ (`New.thetaSpace_two_eq_span_sigma`). So the product is $(a\wp + b)\sigma^2$. The value at $z = 0$ gives $a = -\sigma(v)^2$, and the zero at $z = v$ gives $b = \wp(v)\sigma(v)^2$. Put $z = u$. $\square$

The source also proves the duplication formula $\sigma(2z) = -\wp'(z)\sigma(z)^4$ (`New.sigma_two_mul`), and $\wp'' = 6\wp^2 - g_2/2$ off the lattice (`New.deriv_derivWeierstrassP`).

**Theorem (Uniformisation).** Let $a, b \in \mathbb{C}$ with $a^3 - 27 b^2 \ne 0$. Then there is a lattice with $g_2 = a$ and $g_3 = b$.

Lean: `New.exists_lattice_of_g₂_g₃` (Lib/CM/Sigma/Basic.lean).

*Proof.* Let $E_4$ be the Eisenstein series of weight $4$, $\Delta$ the discriminant cusp form, and $c = (12a)^3/(a^3 - 27b^2)$. The modular form $g = E_4^3 - c\Delta$ of weight $12$ tends to $1$ at the cusp. A modular form of weight $12$ for $\mathrm{SL}_2(\mathbb{Z})$ that tends to $1$ at the cusp has a zero $\tau$ in the upper half plane (`New.exists_eq_zero_of_weight_twelve_of_tendsto_one`: otherwise $1/g$ is a nonzero modular form of weight $-12$, and there is none). At $\tau$, $E_4(\tau)^3 (a^3 - 27b^2) = (12a)^3\Delta(\tau)$. So the ratio $g_2^3/\Delta$ of the lattice $\mathbb{Z}\tau + \mathbb{Z}$ is that of $(a, b)$. A suitable multiple $\lambda(\mathbb{Z}\tau + \mathbb{Z})$ then has $g_2 = a$ and $g_3 = b$, since $g_2$ scales by $\lambda^{-4}$ and $g_3$ by $\lambda^{-6}$. $\square$

### CM lattices

The source fixes the point of order $2$ and the scale of the lattice in one structure.

**Definition (CM lattice).** Let $d \in \mathbb{N}$, let $\omega = (1 + i\sqrt d)/2$, and let $\mathcal{O} \subset \mathbb{C}$ be the image of the ring of integers of $\mathbb{Q}(i\sqrt d)$. A CM lattice for $d$ consists of a lattice $\Lambda$, a number $t \in \mathbb{C}$ and a number $a_1 \in \mathbb{C}$ such that:

1. $t \notin \Lambda$ and $2t \in \Lambda$, so $t$ is a point of order $2$ of $\mathbb{C}/\Lambda$;
2. $g_2 = 12\wp(t)^2 - 4$;
3. $a_1^2 = 12\wp(t)$;
4. if $d \ne 0$, then $\alpha\Lambda \subseteq \Lambda$ for every $\alpha \in \mathcal{O}$;
5. if $d \ne 0$, then $\omega t \notin \Lambda$ and $\bar\omega t \notin \Lambda$.

Lean: `New.CMLattice` (Lib/CM/Sigma/Basic.lean), with `New.quadGen` for $\omega$ and `New.quadInt` for $\mathcal{O}$.

Condition 2 says $\wp''(t) = 2$, since $\wp''(t) = 6\wp(t)^2 - g_2/2$. A point $u$ of order $2$ has $\wp'(u) = 0$, and $\wp''(u) \ne 0$ since the roots of $4x^3 - g_2 x - g_3$ are simple. If $\Lambda$ is replaced by $c\Lambda$ and $t$ by $ct$, then $\wp''(t)$ becomes $c^{-4}\wp''(t)$. So condition 2 fixes $\Lambda$ up to multiplication by a fourth root of unity. Condition 5 picks one of the three points of order $2$. For $d \equiv 7 \pmod 8$ the prime $2$ splits in $K$, $\omega + \bar\omega = 1$, and $\omega\bar\omega = (1 + d)/4$ is even. So each prime above $2$ contains exactly one of $\omega$, $\bar\omega$, and the three points of order $2$ of $\mathbb{C}/\Lambda$ are $t$, $\omega t$ and $\bar\omega t$ modulo $\Lambda$, for the point $t$ that lies in neither the kernel of $\omega$ nor the kernel of $\bar\omega$. Their sum is $(1 + \omega + \bar\omega)t = 2t \in \Lambda$.

**Remark (Formalization).** For $d = 0$ conditions 4 and 5 are void, and a CM lattice for $0$ is only a lattice with a scaled point of order $2$. The source uses this. The results of this section hold for every $d$, and the hypothesis `PrimeSevenModEight d` enters only in the results of Sections 4 to 7. Every result below that needs complex multiplication states that hypothesis.

### The theta function and the cubic

For $u \in \mathbb{C}$ and $m \in \mathbb{N}$ the twisted translate of degree $m$ is
$$(T^m_u f)(z) = \exp\Bigl(-\frac{m\pi}{A}\bigl(z \bar u + \tfrac12 |u|^2\bigr)\Bigr) f(z + u).$$
It takes theta functions for $mH$ to theta functions for $mH$, with a multiplier twisted by a character of $\Lambda$.

**Definition (The theta function of a CM lattice).** For a CM lattice $(\Lambda, t, a_1)$,
$$\theta(z) = \frac{(T^1_t \sigma)(z)}{(T^1_t \sigma)(0)}.$$
The coordinates are $x(z) = \wp(z + t) - \wp(t)$ and $y(z) = \frac12\bigl(\wp'(z + t) - a_1 x(z)\bigr)$.

Lean: `New.CMLattice.θ` (Lib/CM/Sigma/Basic.lean), with `New.CMLattice.translatedX` and `New.CMLattice.translatedY`.

The denominator is $\exp(-\pi|t|^2/2A)\sigma(t) \ne 0$, since $t \notin \Lambda$. So $\theta(0) = 1$, $\theta$ is even, and $\theta$ vanishes exactly on $-t + \Lambda = t + \Lambda$, with simple zeros (`New.CMLattice.theta_zero`, `New.CMLattice.theta_neg`, `New.CMLattice.theta_eq_zero_iff`). It is a theta function for $H$ and the multiplier $\chi(l) = \chi_\sigma(l)\,\varepsilon(l, t)$, where $\varepsilon(\cdot, t)$ is the character of $\Lambda$ given by the Riemann phase of $H$ at $t$ (`New.CMLattice.multiplier`, `New.CMLattice.theta_mem`). In the language of algebraic geometry, $\theta$ is a section of degree $1$ of a line bundle of degree $1$ on $\mathbb{C}/\Lambda$, with its zero at $t$. The coordinates satisfy $x(0) = 0$ and $y(0) = 0$, since $\wp'(t) = 0$. So the map $z \mapsto (x(z), y(z))$ sends $0$ to the point $(0, 0)$ of the cubic below, and $-t$ to the point at infinity.

**Lemma.** For $z \notin \Lambda$, $\theta(z)^2 = (\wp(z) - \wp(t))\, \sigma(z)^2$.

Lean: `New.CMLattice.theta_sq` (Lib/CM/Sigma/ThetaSections.lean).

*Proof.* Since $\theta$ is even, $\theta(z)^2 = \theta(-z)\theta(z)$, and the exponential factors of the two twisted translates cancel up to $\exp(-\pi|t|^2/A)$. So $\theta(z)^2 = \sigma(t - z)\sigma(t + z)/\sigma(t)^2$. Apply [the addition formula](/decl/New.sigma_add_mul_sigma_sub/) with $u = t$ and $v = z$. $\square$

**Lemma (The discriminant).** For every CM lattice, $g_3 = 4\wp(t)^3 - g_2\wp(t)$ and
$$g_2^3 - 27 g_3^2 = a_1^4 - 64.$$

Lean: `New.CMLattice.disc_eq` (Lib/CM/Sigma/ThetaSections.lean), with `New.CMLattice.g₃_eq`.

*Proof.* Since $\wp'(t) = 0$, the equation $\wp'^2 = 4\wp^3 - g_2\wp - g_3$ at $t$ gives $g_3$. Write $e = \wp(t)$, so $a_1^2 = 12e$ and $g_2 = 12e^2 - 4$. Then $g_3 = -8e^3 + 4e$, and
$$(12e^2 - 4)^3 = 1728e^6 - 1728e^4 + 576e^2 - 64, \qquad 27(4e - 8e^3)^2 = 1728e^6 - 1728e^4 + 432e^2.$$
The difference is $144e^2 - 64 = a_1^4 - 64$. $\square$

**Theorem (The cubic).** For $z$ with $z + t \notin \Lambda$,
$$x'(z) = 2y(z) + a_1 x(z), \qquad x'(z)^2 = x(z)\bigl(4x(z)^2 + a_1^2 x(z) + 4\bigr), \qquad y'(z) = 1 + 3x(z)^2 - a_1 y(z),$$
and
$$y(z)^2 + a_1 x(z) y(z) = x(z)^3 + x(z).$$

Lean: `New.CMLattice.weierstrass_equation` (Lib/CM/Sigma/ThetaSections.lean), with `New.CMLattice.deriv_translatedX_sq` and `New.CMLattice.deriv_translatedY_eq`.

*Proof.* The first identity is the definition of $y$. For the second, $x' = \wp'(z + t)$, and $\wp'^2 = 4\wp^3 - g_2\wp - g_3$ is a cubic in $\wp$ with the root $\wp(t)$. Expand it at $\wp = x + e$ with $12e = a_1^2$ and $12e^2 - g_2 = 4$, and use the formula for $g_3$ of [the discriminant](/decl/New.CMLattice.disc_eq/). For the third, differentiate $y$ and use $\wp'' = 6\wp^2 - g_2/2$. For the cubic, substitute $x' = 2y + a_1x$ into the second identity and divide by $4$: $(2y + a_1x)^2 = 4x^3 + a_1^2x^2 + 4x$ gives $4y^2 + 4a_1xy = 4x^3 + 4x$. $\square$

The cubic $y^2 + a_1xy = x^3 + x$ has the Weierstrass coefficients $(a_1, 0, 0, 1, 0)$. Its classical invariants are $b_2 = a_1^2$, $b_4 = 2$, $b_6 = 0$, $b_8 = -1$, $c_4 = a_1^4 - 48$, and $\Delta = a_1^4 - 64$, in the notation of *AEC*, Chapter III, §1. This agrees with [the discriminant](/decl/New.CMLattice.disc_eq/), because the invariant differential $dx/(2y + a_1x)$ of the cubic is $dz$. The $j$-invariant is $(a_1^4 - 48)^3/(a_1^4 - 64)$. The point $(0, 0)$ is a point of order $2$ of the cubic, and $y$ is a local parameter there, since $y'(0) = 1$. The source uses $y$ as the parameter of its formal group (Section 5).

**Remark (Formalization).** The source never defines the cubic as a curve. The statements are identities between complex functions on the complement of $-t + \Lambda$. The hypothesis $z + t \notin \Lambda$ excludes the poles of $x$ and $y$.

### Sections and the addition law of theta

The sections of degree $m$ are the theta functions for $mH$ and the multiplier $\chi^m$. The functions $\theta$, $\sigma^2$ and $G = \sigma\bigl(\sigma'\theta - \sigma(\theta' + \frac12 a_1\theta)\bigr)$ are sections of degree $1$, $2$ and $3$. The function $G$ is entire and equals $y\theta^3$ off $t + \Lambda$ (`New.CMLattice.translatedYThetaCube`).

**Lemma (Addition for theta).** For $z$ with $z + t \notin \Lambda$ and every $w$,
$$\theta(z + w)\, \theta(z - w) = \theta(z)^2\bigl(\theta(w)^2 - x(z)\sigma(w)^2\bigr).$$

Lean: `New.CMLattice.theta_add_mul_theta_sub` (Lib/CM/Sigma/ThetaSections.lean).

*Proof.* For $w \notin \Lambda$, write each $\theta$ as a twisted translate of $\sigma$ by $t$, and apply [the addition formula](/decl/New.sigma_add_mul_sigma_sub/) at $z + t$ and $w$. Then use $\theta(w)^2 = (\wp(w) - \wp(t))\sigma(w)^2$ from [the square of theta](/decl/New.CMLattice.theta_sq/). Both sides are entire in $w$, so the identity extends to $w \in \Lambda$ (`PeriodPair.eq_of_eq_off_lattice`). $\square$

**Theorem (A basis of sections).** For every $m \in \mathbb{N}$, the sections of degree $m$ lie in the span of the monomials $\theta^a(\sigma^2)^b G^c$ with $c \le 1$ and $a + 2b + 3c = m$.

Lean: `New.CMLattice.sections_le_span_monomialSection` (Lib/CM/Sigma/ThetaSections.lean), with `New.CMLattice.monomialSection`.

*Proof.* By induction on $m$. In degree $0$ the sections are the constants, and in degree $1$ they form the line spanned by $\theta$ (`New.IsAppellHumbert.finrank_thetaSpace_nsmul`). Let $f$ be a section of degree $m + 2$. The monomial $e_0 = (\sigma^2)^{b}G^{c}$ with $c = m \bmod 2$ and $2b + 3c = m + 2$ has no factor $\theta$, and it does not vanish at $-t$. Put $g = f - (f(-t)/e_0(-t))\, e_0$. Then $g$ vanishes at $-t$, and by the transformation law it vanishes on $-t + \Lambda$, the zeros of $\theta$. So $g = q\theta$ with $q$ a section of degree $m + 1$ (`New.CMLattice.exists_mul_eq_of_mem_sections`). By induction $q$ is in the span of the monomials of degree $m + 1$, so $q\theta$ is in the span of the monomials of degree $m + 2$. $\square$

This theorem is the analogue of the Riemann-Roch basis $1, x, y, x^2, xy, \dots$ of the functions on the cubic with poles at one point. The source uses it to transport sections to a conjugate curve (Section 6) and to prove integrality of sections at torsion points (Section 5).
