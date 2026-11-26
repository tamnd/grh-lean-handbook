---
title: Conjugate curves and complex multiplication
lean:
  - Lib/CM/ConjugateCurve.lean
  - Lib/CM/ChowlaSelberg.lean
decls:
  - New.CMLattice.exists_galConjugate_of_g₂_g₃
  - New.CMLattice.exists_galConjugate
  - New.CMLattice.galConjugate
  - New.CMLattice.galConjugate_a₁
  - New.CMLattice.thetaQuotient_eq_one
  - New.CMLattice.taylorAtZero_theta_eq_taylorVia
  - New.CMLattice.exists_taylorVia_twistedTranslate_theta
  - New.CMLattice.latticeModule_galConjugate_eq_mul
  - New.CMLattice.exists_latticeModule_eq_scaledIdeal_sq
  - New.CMLattice.exists_finAdele_taylorVia_twistedTranslate_theta
  - New.CMLattice.IsComplexMultiplicationData
  - New.CMLattice.complex_multiplication_theta
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Conjugate curves and complex multiplication

The main theorem of complex multiplication describes how an automorphism $\sigma$ of $\mathbb{C}$ over $K$ acts on a CM curve and its torsion points, in terms of an idele $s$ with Artin symbol $\sigma$ on $K^{\mathrm{ab}}$ (Silverman, *Advanced Topics*, Chapter II, Theorem 8.2; Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, 1971, Theorem 5.4). The source proves a soft form of this theorem for the translates of $\theta$ by torsion points, without the reciprocity law. For [the Chowla-Selberg formula](/decl/New.CMLattice.chowla_selberg/) of Section 7 the source needs only two facts from this section: the lattice of the conjugate curve is in the class of a square, and the isogenies between curves are conjugate to isogenies with the same ideal. The theorem on torsion translates feeds [the integral vacuum](/chapter/integral-vacuum/) of Volume 9.

In this section $d$ is a prime with $d \equiv 7 \pmod 8$, and $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$ is a field automorphism of $\mathbb{C}$ that fixes $K$. In Lean, `Gal(ℂ/QuadField d)` is the group of $K$-algebra automorphisms of $\mathbb{C}$.

### Automorphisms act on Taylor coefficients

Most automorphisms of $\mathbb{C}$ are not continuous, and they do not act on holomorphic functions. They act on power series, coefficient by coefficient. For an analytic function $f$ at $0$, write $\sigma f$ for the series $\sum \sigma(f^{(n)}(0)/n!)\, z^n$ (`New.taylorVia σ f`), and $\hat f$ for the Taylor series of $f$ at $0$ (`New.taylorAtZero f`). The idea of the source is the following. If two CM lattices $C$ and $D$ satisfy $a_1(D) = \sigma(a_1(C))$, then the series of the coordinates $x$, $y$ of $D$ are the conjugates of those of $C$, because both solve the system $x' = 2y + a_1x$, $y' = 1 + 3x^2 - a_1y$ of [the cubic](/decl/New.CMLattice.weierstrass_equation/) with the same initial values $x(0) = y(0) = 0$ (`New.map_taylorAtZero_translatedX_and_translatedY`, which applies to any ring automorphism of $\mathbb{C}$). Sections of $C$ are combinations of monomials in $\theta$, $\sigma^2$ and $y\theta^3$, by [the basis of sections](/decl/New.CMLattice.sections_le_span_monomialSection/). So sections can be transported from $C$ to $D$, up to the power of one series $\theta_D/\sigma\theta_C$.

### The conjugate curve

**Theorem (Conjugate curve).** Let $C$ be a CM lattice for $d$ and $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$.

1. If $L$ is a lattice with $g_2(L) = \sigma(g_2(C))$ and $g_3(L) = \sigma(g_3(C))$, then there is a CM lattice $C'$ for $d$ with lattice $L$ and $a_1(C') = \sigma(a_1(C))$.
2. There is a CM lattice $C'$ for $d$ with $a_1(C') = \sigma(a_1(C))$.

Lean: `New.CMLattice.exists_galConjugate_of_g₂_g₃`, `New.CMLattice.exists_galConjugate` (Lib/CM/ConjugateCurve.lean).

*Proof.* (2) follows from (1) and [uniformisation](/decl/New.exists_lattice_of_g₂_g₃/), since $\sigma$ maps the discriminant $g_2^3 - 27g_3^2 \ne 0$ to a nonzero number. For (1), the cubic $4X^3 - g_2(L)X - g_3(L)$ is the $\sigma$-conjugate of the cubic of $C$, so it has the root $\sigma(\wp_C(t))$, and there is a point $t'$ of order $2$ of $L$ with $\wp_L(t') = \sigma(\wp_C(t))$. The conditions $g_2 = 12\wp(t')^2 - 4$ and $a_1^2 = 12\wp(t')$ for $\sigma(a_1)$ follow by applying $\sigma$. So $(L, t', \sigma(a_1))$ is a CM lattice for $d = 0$. For the conditions of complex multiplication, let $\alpha \in \mathcal{O}_K$. Multiplication by $\alpha$ is an isogeny from $\Lambda_C$ to $\Lambda_C$. Its transport to $L$ is multiplication by $\sigma(\alpha) = \alpha$ (`New.conj_isogeny_mul_mem_lattice`). So $\alpha L \subseteq L$. In the same way, $\alpha t' \in L$ implies $\alpha t \in \Lambda_C$ (`New.mul_t_mem_of_conj_isogeny_mul_t_mem`), so $\omega t' \notin L$ and $\bar\omega t' \notin L$. $\square$

**Definition (Galois conjugate).** For a CM lattice $C$ and $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$, $C^\sigma$ is a CM lattice with $a_1(C^\sigma) = \sigma(a_1(C))$, chosen by `choose` from the theorem above.

Lean: `New.CMLattice.galConjugate`, with `New.CMLattice.galConjugate_a₁` (Lib/CM/ConjugateCurve.lean).

**Remark (Formalization).** The number $a_1$ fixes $\wp(t) = a_1^2/12$, so it fixes $g_2$ and $g_3$, by condition 2 of [the definition](/decl/New.CMLattice/) and [the formula for g₃](/decl/New.CMLattice.disc_eq/). It therefore fixes the lattice of $C^\sigma$, and the point $t$ modulo the lattice. The choice only picks the representative $t \in \mathbb{C}$. The theta function depends only on the lattice (`New.CMLattice.theta_eq_of_latticeModule_eq`), so the choice does not affect $\theta$. This argument is classical. The proofs in the source use only the property $a_1(C^\sigma) = \sigma(a_1(C))$.

**Theorem (Conjugate theta series).** Let $C$, $D$ be CM lattices for $d$ with $a_1(D) = \sigma(a_1(C))$. Then $\hat\theta_D = \sigma\theta_C$, and the same holds for every monomial section.

Lean: `New.CMLattice.taylorAtZero_theta_eq_taylorVia`, `New.CMLattice.thetaQuotient_eq_one` (Lib/CM/ConjugateCurve.lean), with `New.thetaQuotient` and `New.CMLattice.taylorAtZero_monomialSection_eq_taylorVia`.

*Proof.* Let $q = \hat\theta_D/\sigma\theta_C$, a series with constant term $1$. Multiplication by $\omega$ is an isogeny of degree $N = \omega\bar\omega$ of $\Lambda_C$, and its transport to $D$ gives $q(\omega z) = q(z)^N$ (`New.rescale_thetaQuotient_of_conj_isogeny`). Suppose $q \ne 1$, and write $q - 1 = z^nW$ with $W(0) \ne 0$. The coefficients of $z^n$ in $q(\omega z) - 1 = q^N - 1$ are $\omega^nW(0)$ and $NW(0)$. So $\omega^n = \omega\bar\omega$. Since $|\omega| > 1$, the moduli give $n = 2$, and then $\omega = \bar\omega$. This is false, since $\omega = (1 + \sqrt{-d})/2$ is not real. So $q = 1$. $\square$

**Theorem (Translates by torsion points).** Let $C$, $D$ be CM lattices for $d$ with $a_1(D) = \sigma(a_1(C))$, and let $\Lambda_C = \Omega\mathcal{O}_K$. For every finite set $S \subset K$ there is $v \in \Lambda_D$ such that for all $s \in S$,
$$\sigma\bigl(T^1_{s\Omega}\theta_C\bigr) = \widehat{T^1_{sv}\theta_D}.$$

Lean: `New.CMLattice.exists_taylorVia_twistedTranslate_theta` (Lib/CM/ConjugateCurve.lean).

*Proof.* Take $n \ne 0$ with $nS \subseteq \mathcal{O}_K$, and write $\Omega = 2n^2w$. Transport the sections from $D$ to $C$ with $\sigma^{-1}$. This matches the point $w$ of $C$ with a point $w'$ of $D$, in the sense that the monomials vanish at $aw$ for $C$ if and only if they vanish at $aw'$ for $D$, for $a \in \mathcal{O}_K$. Put $v = 2n^2w'$. The zeros of $\sigma^2$ are the periods, so $v \in \Lambda_D$. For $s \in S$, the transport $g$ of $z \mapsto (T^1_{sv}\theta_D)(nz)$ vanishes at the zeros of $z \mapsto (T^1_{s\Omega}\theta_C)(nz)$. The zeros are simple, so $g = c \cdot (T^1_{s\Omega}\theta_C)(n\,\cdot)$ for a constant $c$ (`New.CMLattice.exists_eq_const_mul_twistedTranslate_theta`). A comparison of values gives $c = 1$ (`New.CMLattice.eq_one_of_taylorVia_twistedTranslate_theta`). Undo the scaling by $n$. $\square$

### Isogenies and ideal classes

**Lemma (Conjugate isogenies).** Let $C$, $D$ be CM lattices for $d$, $u \in \mathbb{C}^\times$, $\mathfrak{a}$ a nonzero fractional ideal, and $\Lambda_D = u\mathfrak{a}\Lambda_C$. Then $\Lambda_{D^\sigma} = \sigma(u)\, \mathfrak{a}\, \Lambda_{C^\sigma}$.

Lean: `New.CMLattice.latticeModule_galConjugate_eq_mul` (Lib/CM/ChowlaSelberg.lean), with `New.CMLattice.scaledIdeal_map_mul_galConjugate_le`.

*Proof.* For $y \in \mathfrak{a}$, multiplication by $uy$ maps $\Lambda_C$ into $\Lambda_D$. Its transport is multiplication by $\sigma(uy) = \sigma(u)y$, since $\sigma$ fixes $K$. So $\sigma(u)\mathfrak{a}\Lambda_{C^\sigma} \subseteq \Lambda_{D^\sigma}$. Apply the same to $\Lambda_C = u^{-1}\mathfrak{a}^{-1}\Lambda_D$ for the other inclusion. $\square$

Classically, the main theorem (Silverman, *Advanced Topics*, Chapter II, Theorem 8.2) also gives the class of the conjugate lattice, in terms of the idele $s$. The source does not prove which class $\Lambda_{C^\sigma}$ has. It proves only that it is the class of a square, since every class is a square.

**Lemma.** For every CM lattice $D$ for $d$ there are $w \in \mathbb{C}^\times$ and a nonzero integral ideal $\mathfrak{c}$ with $\Lambda_D = w\mathfrak{c}^2$.

Lean: `New.CMLattice.exists_latticeModule_eq_scaledIdeal_sq` (Lib/CM/ChowlaSelberg.lean).

*Proof.* $\Lambda_D = v\mathfrak{a}$. By [the odd class number](/decl/New.QuadField.classGroup_sq_bijective/), there is $\mathfrak{c}$ with $[\mathfrak{c}]^2 = [\mathfrak{a}]$. Then $\mathfrak{c}^2\mathfrak{a}^{-1} = (\gamma)$ is principal, and $\Lambda_D = v\gamma^{-1}\mathfrak{c}^2$. $\square$

### The soft main theorem

Let $\widehat{\mathcal{O}}_K = \prod_{\mathfrak{p}} \mathcal{O}_{K,\mathfrak{p}}$, and let $\mathbb{A}_{K,f}$ be the ring of finite adeles of $K$, with its topology (`𝔸f (QuadField d)` in Lean).

**Definition (Complex multiplication data).** Let $C$ be a CM lattice with $\Lambda_C = \Omega_0\mathcal{O}_K$. The data of complex multiplication for $(C, \sigma, \Omega_0)$ are $\Omega \in \mathbb{C}^\times$, an integral ideal $\mathfrak{c}$ and $\beta \in \mathbb{A}_{K,f}$ such that:

1. $\mathfrak{c} \ne 0$;
2. $\Lambda_{C^\sigma} = \Omega\, \mathfrak{c}^2/N\mathfrak{c}$, which is $\Omega\mathfrak{c}\bar{\mathfrak{c}}^{-1}$;
3. the area of $\Lambda_{C^\sigma}$ is $|\Omega|^2\sqrt d/2$;
4. $e\Omega \in \Lambda_{C^\sigma}$ for some integer $e \ge 1$;
5. for every $x \in K$ there is a neighbourhood $U$ of $\beta x$ in $\mathbb{A}_{K,f}$ such that for every $x' \in K \cap U$,
$$\sigma\bigl(T^1_{x\Omega_0}\theta_C\bigr) = \widehat{T^1_{x'\Omega}\theta_{C^\sigma}}.$$

Lean: `New.CMLattice.IsComplexMultiplicationData` (Lib/CM/ChowlaSelberg.lean).

**Theorem (Complex multiplication for theta).** Let $C$ be a CM lattice for $d$ with $\Lambda_C = \Omega_0\mathcal{O}_K$, and $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$. Then there are $\Omega$, $\mathfrak{c}$ and $\beta$ that are data of complex multiplication for $(C, \sigma, \Omega_0)$.

Lean: `New.CMLattice.complex_multiplication_theta` (Lib/CM/ChowlaSelberg.lean), with `New.CMLattice.exists_finAdele_taylorVia_twistedTranslate_theta`.

*Proof.* By the lemma above, $\Lambda_{C^\sigma} = w\mathfrak{c}^2$. Put $n = N\mathfrak{c}$ and $\Omega = wn$. Then (1) and (2) hold, and $n\Omega \in \Lambda_{C^\sigma}$ gives (4). The area of $w\mathfrak{c}^2$ is $|w|^2n^2\sqrt d/2 = |\Omega|^2\sqrt d/2$, by [the area formula](/decl/New.QuadField.area_eq_of_eq_scaledIdeal/). This is (3). For (5), [the translates by torsion points](/decl/New.CMLattice.exists_taylorVia_twistedTranslate_theta/) give, for each finite $S \subset K$, a period $\Omega b_S$ of $C^\sigma$ with $b_S \in K$ that works for all $x \in S$. The lattice lies in $\Omega e^{-1}\mathcal{O}_K$, so the $b_S$ lie in the compact set $e^{-1}\widehat{\mathcal{O}}_K$. Order the finite sets by inclusion. The net $b_S$ has a cluster point $\beta$. For $x \in K$, choose $m \ne 0$ with $mx$ integral, and $U$ so small that the points of $K$ in $U$ are congruent modulo $2me\mathcal{O}_K$. Translates of $\theta$ by points that are congruent in this sense agree (`New.CMLattice.twistedTranslate_theta_eq_of_isIntegral`). Take $S \ni x$ with $b_Sx \in U$. $\square$

Classically, $\beta$ plays the role of $s^{-1}$ for an idele $s$ with Artin symbol $\sigma|_{K^{\mathrm{ab}}}$, and the theorem says more: $\beta$ can be taken in $\mathbb{A}_{K,f}^\times$, and its class determines $\sigma$ on the field generated by the torsion values.

**Remark (Formalization).** The source states the limits of this theorem in its docstrings. The adele $\beta$ is obtained as a cluster point, by compactness, with no formula. It is not identified with the Artin map of [class field theory](/chapter/class-field-theory/), and it is not shown to be a unit of $\mathbb{A}_{K,f}$. No reciprocity law is used: the conjugate lattice comes from uniformisation, and points are matched by the transport of sections. The automorphism $\sigma$ can be discontinuous. All statements involve $\sigma$ only through its values on Taylor coefficients at $0$, so no statement applies $\sigma$ to a function. The conjugate $C^\sigma$ is the chosen one of `New.CMLattice.galConjugate`, and the data $\Omega$, $\mathfrak{c}$, $\beta$ come from an existence statement. The source uses this theorem in New/Derivatives/Vacuum/IntegralVacuum.lean.
