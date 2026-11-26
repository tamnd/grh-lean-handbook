---
title: Resolutions, partners and theta products
lean:
  - New/Derivatives/FormalGroup/Resolution.lean
  - New/Derivatives/FormalGroup/ThetaProducts.lean
decls:
  - New.IsResolution
  - New.IsResolution.sum_conj_mul
  - New.IsIntegralAbove
  - New.IsIntegralAbove.exists_mul_eq
  - New.daggerForms
  - New.CMLattice.thetaProd
  - New.Parameters.partner
  - New.Parameters.norm_pow_sub_conj_partner_le
  - New.Parameters.norm_conj_pow_sub_partner_le
  - New.Parameters.piPrimeInt_dvd_sum_linearSeries_sub_coupling
  - New.dvd_sum_subst_sub_couplingSum
  - New.CMLattice.rescale_thetaProd_eq_mul_expSubst
  - New.CMLattice.rescale_mem_range_of_mem_multiSeriesRing
  - New.Parameters.norm_pow_succ_div_mul_piPrimeInt
  - New.Parameters.exists_hasNormalForm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Resolutions, partners and theta products

This section proves the normal form for products of theta functions. The variables are now the coordinates $z_{(\tau, c)}$ of a vector over the infinite places $\tau$ of the field $E$. The theta functions are evaluated at linear forms $u_j^\dagger z$, for vectors $u_j$ that form a resolution of the identity. The partner rule of Section 5 is $\tau \mapsto u(-p^e)\tau$. The main theorem says that $\prod_j\theta(u_j^\dagger z)^{m_j}$, times any integral series in the $y(u_j^\dagger z)$, has the normal form, with one scale $\varpi$ and one family $\lambda_{ej}$ for all resolutions.

### The setting

Let $P$ be the parameters of the argument, with the prime $d = $ `P.d`. Fix a level $s$. The field $E = $ `P.E s` is $K$ with a root of unity $\zeta$ of order $q_1 = $ `P.q₁ s` adjoined. Its infinite places form the group $\Phi = $ `P.Φ s` $\cong \mathrm{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$. For an integer $\nu$, the place $u(\nu)$ is the class of $\nu$ in this group; see [fields, places and twists](/decl/New.Parameters.placeOfInt/). Each place $\tau$ comes with a complex embedding $\Phi_\tau$ of $E$, from the CM type. We write $\tau(\alpha)$ for $\Phi_\tau(\alpha)$. The curve is the CM curve `P.cmCurve` of [the integral vacuum and tight frames](/chapter/integral-vacuum/), with its theta function $\theta$ and its parameter $y$.

Let $n$ be a finite set of coordinates. A vector $u \in E^n$ is read as the complex vector with the coordinates $\tau(u_c)$ at $(\tau, c) \in \Phi \times n$. Its *dagger form* is the linear form
$$u^\dagger z = \sum_{(\tau, c)}\overline{\tau(u_c)}\,z_{(\tau, c)}.$$

### Resolutions of the identity

**Definition (Resolution of the identity, integral above p).** Let $J$ be a finite set, $u_j \in E^n$ and $m_j \in \mathbb{N}$ for $j \in J$.

1. The family $(u_j, m_j)$ is a *resolution of the identity* if $\sum_j m_j\,u_j\,u_j^\dagger = 1$, that is, for all $x = (\tau, c)$ and $x_1 = (\tau_1, c_1)$,
$$\sum_{j \in J} m_j\,\tau(u_{j,c})\,\overline{\tau_1(u_{j,c_1})} = \begin{cases}1 & x = x_1,\\ 0 & x \ne x_1.\end{cases}$$
2. An element $\beta \in E$ is *integral above $p$* if $w(\beta) \ge 0$ for every finite place $w$ of $E$ with $w \mid p$.
3. The dagger forms in $\mathbb{C}_p$ are the coefficients $\iota_p\bigl(\overline{\tau(u_{j,c})}\bigr)$ of $u_j^\dagger z$.
4. For linear forms $\mu_j$ over $\mathbb{C}_p$, the theta product is $\prod_j\theta(\mu_j z)^{m_j}$, with the Taylor series of $\theta$ read in $\mathbb{C}_p$ by $\iota_p$.

Lean: `New.IsResolution`, `New.IsIntegralAbove`, `New.daggerForms`, `New.CMLattice.thetaProd` (New/Derivatives/FormalGroup/Resolution.lean), with `New.dagger`.

Equivalently, $z = \sum_j m_j\,(u_j^\dagger z)\,u_j$ for every complex vector $z$. The module docstring says that a resolution of the identity is a Parseval frame. The next lemma is the Parseval identity.

**Lemma (Parseval, integrality above p).**

1. If $(u_j, m_j)$ is a resolution of the identity, then for all complex vectors $z$ and $z'$,
$$\sum_j m_j\,\overline{(u_j^\dagger z')}\,(u_j^\dagger z) = \sum_x \overline{z'_x}\,z_x.$$
2. If $\beta$ is integral above $p$, then $N\beta = \alpha$ for a natural number $N$ prime to $p$ and an integer $\alpha \in \mathcal{O}_E$. For every ring homomorphism $\sigma : E \to \mathbb{C}_p$, $|\sigma(\beta)| \le 1$. In particular $|\iota_p(\overline{\tau(\beta)})| \le 1$, so the dagger forms of vectors integral above $p$ have integral coefficients.

Lean: `New.IsResolution.sum_conj_mul`, `New.IsIntegralAbove.exists_mul_eq` (New/Derivatives/FormalGroup/Resolution.lean), with `New.IsIntegralAbove.norm_le_one`, `New.IsIntegralAbove.norm_conj_le_one`, `New.Parameters.norm_daggerForms_le_one` and `New.IsResolution.sum_smul_linearSeries`.

*Proof.* (1) Expand both dagger forms and exchange the sums. The inner sum over $j$ is the left side of the definition, which is $1$ for $x = x_1$ and $0$ otherwise. (2) Some $D \ne 0$ in $\mathbb{N}$ has $D\beta \in \mathcal{O}_E$. Write $D = p^kN$ with $p \nmid N$. Then $N\beta$ has $w(N\beta) \ge 0$ at the places above $p$, by the hypothesis, and at the other places, since $p^k$ is a unit there. So $N\beta \in \mathcal{O}_E$. An embedding $\sigma$ defines a place of $E$ above $p$, and $|\sigma(\beta)| \le 1$ follows. Complex conjugation followed by $\iota_p$ is such an embedding. $\square$

The identity in coordinates that the proof below uses is item 1 of the definition, read as an identity of linear forms over $\mathfrak{o}$:
$$\sum_j m_j\,\iota_p\bigl(\tau(u_{j,c})\bigr)\,\bigl(u_j^\dagger z\bigr) = z_{(\tau, c)}. \tag{R}$$
This is `New.IsResolution.sum_smul_linearSeries`.

### Partners

**Definition (Partner).** For $e \in \mathbb{N}$ and $\tau \in \Phi$, the *partner* of $\tau$ is $\tau'_e = u(-p^e)\,\tau$.

Lean: `New.Parameters.partner` (New/Derivatives/FormalGroup/ThetaProducts.lean).

The place $u(-p^e)$ is the class of $-p^e$ in $(\mathbb{Z}/q_1)^\times$ when this class is a unit. The source sets it to the identity otherwise. For nonsplit $p$ this junk value does not occur: every prime that divides $q_1$ splits in $K$ (`New.Parameters.chiK_eq_one_of_dvd`), so $p \nmid q_1$ and $-p^e$ is a unit modulo $q_1$.

**Example.** For illustration let $d = 7$, $p = 3$ and $q_1 = 11$. The prime $11$ splits in $K$, since $11 \equiv 4$ is a square modulo $7$. Then $-3 \equiv 8$ and $-27 \equiv 6$ modulo $11$. So the partner of the place $a \in (\mathbb{Z}/11)^\times$ is $8a$ for $e = 1$ and $6a$ for $e = 3$. For $p = d = 7$ and $e = 0$, the partner is $u(-1)\tau$, the complex conjugate place.

**Lemma (Partner congruence).** Let $p$ be a prime, $e \in I_p^\circ$ and $\tau \in \Phi$.

1. For every $\alpha \in \mathcal{O}_E$,
$$\bigl|\iota_p(\tau(\alpha))^{p^e} - \iota_p\bigl(\overline{\tau'_e(\alpha)}\bigr)\bigr| \le |\pi_p|.$$
2. For every $\beta \in E$ integral above $p$,
$$\bigl|\iota_p\bigl(\overline{\tau(\beta)}\bigr)^{p^e} - \iota_p(\tau'_e(\beta))\bigr| \le |\pi_p|.$$

Lean: `New.Parameters.norm_pow_sub_conj_partner_le`, `New.Parameters.norm_conj_pow_sub_partner_le` (New/Derivatives/FormalGroup/ThetaProducts.lean), with `New.piPrimeInt_dvd_iff`.

In words: modulo $\pi_p$, the $p^e$-th power at $\tau$ is complex conjugation at the partner. For $x \in \mathfrak{o}$, $\pi_p \mid x$ if and only if $|x| \le |\pi_p|$ (`New.piPrimeInt_dvd_iff`), so the lemma is a congruence modulo $\pi_p$.

*Proof.* (1) By the hypothesis $e \in I_p^\circ$, $\chi_K(p) \ne 1$, so $p \nmid q_1$, as above. Consider the two ring maps from $\mathcal{O}_E$ to $\mathfrak{o}/\pi_p$:
$$\alpha \mapsto \iota_p(\tau(\alpha))^{p^e}, \qquad \alpha \mapsto \iota_p\bigl(\tau(g(\overline{\alpha}))\bigr),$$
where $g$ is the automorphism of $E$ of the place $u(-p^e)$. The first is a ring map, since $p$-th powers are additive modulo $\pi_p \mid p$. The criterion [on Frobenius](/decl/New.Parameters.forall_map_galOfPlaceInt_eq_pow_iff/) of [the field E at the primes](/chapter/field-at-primes/) says that the two maps agree if they agree at $\zeta$ and at $\sqrt{-d}$, in the form given by `New.Parameters.IsIdOrConjWithSign`. At $\zeta$, conjugation followed by $g$ sends $\zeta$ to $\zeta^{-(-p^e)} = \zeta^{p^e}$, so the two maps agree. At $\sqrt{-d}$, conjugation gives $-\sqrt{-d}$ and $g$ fixes it, so the second map gives $-\iota_p(\tau(\sqrt{-d}))$. The first map gives $\chi_K(p)^e\,\iota_p(\tau(\sqrt{-d}))$ modulo $\pi_p$. If $p = d$, then $\iota_p(\tau(\sqrt{-d}))$ has the norm of $\pi_p$ and is $0$ modulo $\pi_p$, so both sides are $0$. If $p$ is inert, $\chi_K(p) = -1$ and $e$ is odd, so $\chi_K(p)^e = -1$. In both cases the maps agree. Finally $\tau(g(\overline{\alpha})) = \overline{\tau'_e(\alpha)}$, by the definition of the partner and of the CM type.

(2) Write $N\beta = \alpha$ with $p \nmid N$ and $\alpha \in \mathcal{O}_E$ (the last lemma). Apply (1) to $\overline{\alpha}$ in the form $\overline{\tau(\alpha)}^{p^e} \equiv \tau'_e(\alpha)$. Then $N^{p^e}a^{p^e} \equiv Nb$ for $a = \iota_p(\overline{\tau(\beta)})$ and $b = \iota_p(\tau'_e(\beta))$, both integral. By Fermat, $N^{p^e} \equiv N$ modulo $p$, and $N$ is a unit. So $a^{p^e} \equiv b$. $\square$

The set $I_p^\circ$ is the set of exponents for which the sign at $\sqrt{-d}$ is right. For inert $p$ and even $e$ the first map gives $+\iota_p(\tau(\sqrt{-d}))$, and the congruence would need $\sqrt{-d} \equiv 0$, which is false.

### The coupling as a sum of dagger forms

**Proposition (Coupling congruence).** Let $p$ be a prime and $e \in I_p^\circ$. Let $(u_j, m_j)$ be a resolution of the identity by vectors integral above $p$, and let $\mu_j$ be the dagger forms of $u_j$ over $\mathfrak{o}$. Then
$$\sum_j m_j\,(\mu_j z)^{p^e}\,(\mu_j z) \equiv \Gamma_e \pmod{\pi_p},$$
where $\Gamma_e = \sum_x z_x^{p^e}z_{x'_e}$ is the coupling of Section 5 for the partner rule $\tau \mapsto \tau'_e$.

Lean: `New.Parameters.piPrimeInt_dvd_sum_linearSeries_sub_coupling` (New/Derivatives/FormalGroup/ThetaProducts.lean), with `New.Parameters.dvd_pow_sub_sum_partner`.

*Proof.* Fix $j$. Modulo $\pi_p$, the $p^e$-th power is additive, so
$$(\mu_j z)^{p^e} \equiv \sum_{(\tau, c)}\iota_p\bigl(\overline{\tau(u_{j,c})}\bigr)^{p^e}z_{(\tau, c)}^{p^e} \equiv \sum_{(\tau, c)}\iota_p\bigl(\tau'_e(u_{j,c})\bigr)\,z_{(\tau, c)}^{p^e},$$
by part 2 of the partner congruence. Multiply by $m_j(\mu_jz)$ and sum over $j$. The coefficient of $z_{(\tau, c)}^{p^e}$ is $\sum_j m_j\,\iota_p(\tau'_e(u_{j,c}))\,(\mu_jz)$. By (R) at the coordinate $(\tau'_e, c)$, this is $z_{(\tau'_e, c)}$. So the sum is $\sum_{(\tau, c)}z_{(\tau, c)}^{p^e}z_{(\tau'_e, c)} = \Gamma_e$ modulo $\pi_p$. $\square$

The proof uses (R) at the partner coordinate. This is how a resolution of the identity turns the $p^e$-th power at one place into a variable at another place.

### From one curve to the product

**Lemma (Exponents add).** Let $\pi \mid p$ in $\mathfrak{o}$. Let $\Xi$ be an integral series in one variable with $\Xi \equiv \sum_{e \in S}\sum_j\lambda_{ej}(t^{p^e}t)^{p^j}$ modulo $\pi$. Let $L_j$ be integral series in the $z_x$ with $L_j(0) = 0$, such that $\sum_j m_jL_j^{p^e}L_j \equiv \Gamma_e$ modulo $\pi$ for every $e \in S$. Then
$$\sum_j m_j\,\Xi(L_j) \equiv \Xi_{S,\lambda} \pmod{\pi}.$$

Lean: `New.dvd_sum_subst_sub_couplingSum` (New/Derivatives/FormalGroup/ThetaProducts.lean).

*Proof.* Substitution of $L_j$ is a continuous ring map, so $\Xi(L_j) \equiv \sum_{e, j'}\lambda_{ej'}(L_j^{p^e}L_j)^{p^{j'}}$ modulo $\pi$, term by term. Fix $(e, j')$. Read the sum over $j$ with multiplicities as a sum over the pairs $(j, k)$ with $k < m_j$. Since $\pi \mid p$, the $p^{j'}$-th power is additive modulo $\pi$:
$$\sum_j m_j\,(L_j^{p^e}L_j)^{p^{j'}} \equiv \Bigl(\sum_j m_jL_j^{p^e}L_j\Bigr)^{p^{j'}} \equiv \Gamma_e^{\,p^{j'}}.$$
Multiply by $\lambda_{ej'}$ and sum over $(e, j')$. $\square$

**Lemma (Products at the scale).** Let $\mu_j$ be integral linear forms.

1. If $\theta(\varpi t) = W\exp(\kappa\,\Xi)$ with integral $W$, $\Xi$ and $\Xi(0) = 0$, then
$$\prod_j\theta(\varpi\,\mu_j z)^{m_j} = \Bigl(\prod_j W(\mu_j z)^{m_j}\Bigr)\exp\Bigl(\kappa\sum_j m_j\,\Xi(\mu_j z)\Bigr).$$
2. If $|\varpi| \le p^{-\rho_p}$ and $H$ is an integral series in the $y(\mu_j z)$, then $H(\varpi z)$ is integral.
3. If $\chi_K(p) \ne 1$ and $|\varpi| = p^{-\rho_p}$, then $|c_\varpi\pi_p| = p^{-1/(p-1)}$.

Lean: `New.CMLattice.rescale_thetaProd_eq_mul_expSubst`, `New.CMLattice.rescale_mem_range_of_mem_multiSeriesRing`, `New.Parameters.norm_pow_succ_div_mul_piPrimeInt` (New/Derivatives/FormalGroup/ThetaProducts.lean), with `New.expSubst_nsmul` and `New.CMLattice.rescale_thetaProd`.

*Proof.* (1) Scaling all variables by $\varpi$ scales each linear form by $\varpi$. Substitute $t = \mu_jz$ in the identity for $\theta(\varpi t)$, use $\exp(g)^m = \exp(mg)$ and $\exp(g)\exp(h) = \exp(g + h)$. (2) $H = G(y(\mu_1z), y(\mu_2z), \ldots)$ for an integral series $G$. Every series in $\mathfrak{o}[[y]]$ is integral at $\varpi t$ for $|\varpi| \le p^{-\rho_p}$. This is `New.CMLattice.rescale_mem_range_seriesToCp` (Lib/CM/FormalGroup/FormalParameter.lean), a consequence of [the theorem on the formal parameter](/decl/New.CMLattice.exists_scaled_formalParam/) of Volume 3. So $y(\varpi t) = Y(t)$ with $Y$ integral and $Y(0) = 0$. So $H(\varpi z) = G(Y(\mu_1z), \ldots)$ is integral. The ring of such $H$ is [the ring of Volume 3](/decl/New.CMLattice.translatedY_add_mem_multiSeriesRing/). (3) This is the computation after the proposition on the exponent modulo $\pi$ in Section 5. $\square$

### The normal form of theta products

**Theorem (Normal form at a nonsplit prime).** Let $p$ be a prime with $\chi_K(p) \ne 1$. There are $\varpi \in \mathbb{C}_p$ and numbers $\lambda_{ej} \in \mathfrak{o}$ with $|\varpi| = p^{-\rho_p}$, with $\lambda_{e0}$ a unit for every odd $e$ if $p$ is inert, such that the following holds. Let $n$ and $J$ be finite sets, and let $(u_j, m_j)_{j \in J}$ be a resolution of the identity by vectors $u_j \in E^n$ whose coordinates are integral above $p$. Let $\mu_j$ be the dagger forms of $u_j$ in $\mathbb{C}_p$, and let $H$ be an integral series in the $y(\mu_jz)$. Then
$$\prod_j\theta(\mu_j z)^{m_j}\cdot H$$
has the normal form for $(I_p^\circ,\ \tau \mapsto \tau'_e,\ \varpi,\ \lambda)$: there is an integral series $V$ with
$$\Bigl(\prod_j\theta(\mu_j\varpi z)^{m_j}\Bigr)H(\varpi z) = V\exp\Bigl(c_\varpi\sum_{e \in I_p^\circ}\sum_{j' \ge 0}\lambda_{ej'}\,\Gamma_e^{\,p^{j'}}\Bigr).$$

Lean: `New.Parameters.exists_hasNormalForm` (New/Derivatives/FormalGroup/ThetaProducts.lean).

*Proof.* By [the theorem on one curve](/decl/New.CMLattice.exists_exponent_tsum/) of Section 4, applied to the CM curve, there are $\varpi$, $W$, $\Xi$ and $\lambda$ with $|\varpi| = p^{-\rho_p}$, $\Xi(0) = 0$, $\theta(\varpi t) = W\exp(c_\varpi\Xi)$ and $\Xi \equiv \sum_{e \in I_p^\circ}\sum_j\lambda_{ej}(t^{p^e}t)^{p^j}$ modulo $\pi_p$, with the units $\lambda_{e0}$ at inert $p$. Fix these. They do not depend on the resolution.

Now let $(u_j, m_j)$ and $H$ be given. By part 2 of the lemma on Parseval, the dagger forms $\mu_j$ are integral. By the lemma on products at the scale, parts 1 and 2,
$$\Bigl(\prod_j\theta(\mu_j\varpi z)^{m_j}\Bigr)H(\varpi z) = \Bigl(\prod_j W(\mu_jz)^{m_j}\cdot V_H\Bigr)\exp\Bigl(c_\varpi\sum_j m_j\,\Xi(\mu_jz)\Bigr),$$
with $V_H = H(\varpi z)$ integral. By the coupling congruence, the hypothesis of the lemma on exponents adds holds with $\pi = \pi_p$, $S = I_p^\circ$ and $L_j = \mu_jz$, since $\pi_p \mid p$. So $\sum_j m_j\Xi(\mu_jz) \equiv \Xi_{S,\lambda}$ modulo $\pi_p$. This series has the constant term $0$. By part 3 of the lemma on products, $|c_\varpi\pi_p| \le p^{-1/(p-1)}$. The proposition on the exponent modulo $\pi$ of Section 5 now gives the normal form. $\square$

**Example.** Let $p = d$. Then $I_p^\circ = \mathbb{N}$, and the exponent contains $\lambda_{00}\Gamma_0$ with $\Gamma_0 = \sum_{(\tau, c)}z_{(\tau, c)}z_{(u(-1)\tau, c)}$. This term pairs each place with its conjugate place. Its source is the coupling congruence for $e = 0$: $\sum_j m_j(\mu_jz)^2 \equiv \Gamma_0$ modulo $\sqrt{-d}$. For inert $p$ the smallest coupling is $\Gamma_1 = \sum z_{(\tau, c)}^pz_{(u(-p)\tau, c)}$, of degree $p + 1$, with a unit coefficient $\lambda_{10}$.

**Remark (Formalization).**

1. The quantifiers are in this order: $\exists\,\varpi, \lambda$, then $\forall\,n, J, u, m, H$. So one $\varpi$ and one family $\lambda$ serve every resolution, every $n$ and every $H$. The [next chapter](/chapter/normal-forms/) needs this uniformity. It uses the theorem in `New.Parameters.exists_hasNormalForm_jetSeries` (New/Derivatives/Vacuum/Divisibility.lean). The source also uses it in the sharpness files, which are not part of Volume 9.
2. The theorem is stated for the chosen curve `P.cmCurve` and the chosen field `P.E s`. The proofs of the one-curve results in Sections 2 to 4 hold for every CM lattice. The file imports New/Derivatives/Vacuum/TightFrames.lean, which belongs to [the integral vacuum](/chapter/integral-vacuum/), an earlier chapter of Volume 9. No file of this chapter imports a later chapter.
3. The partner `P.partner s p e τ` is `P.placeOfInt s (-p ^ e) * τ`. The function `P.placeOfInt` has a junk value, the identity, when the class is not a unit. As shown above, this does not occur for nonsplit $p$. For split $p$ the set $I_p^\circ$ is empty, and the partner is not used.
4. At $p = d$ the set $I_p^\circ$ contains $e = 0$. The set $I_p$ of [the three inputs](/chapter/theorem-a-plan/) is the set of positive elements of $I_p^\circ$. The coupling $\Gamma_0$ is in the normal form, but the gain counted in $s_p(y, \sigma)$ runs over $e \in I_p$.
5. The unit condition is stated only for $\lambda_{e0}$ with $e$ odd and only for inert $p$. At $p = d$ no unit condition is stated.
6. The hypothesis on $H$ is membership in `P.cmCurve.multiSeriesRing (daggerForms u)`, the ring of integral series in the $y(u_j^\dagger z)$. The case $H = 1$ is the plain theta product.
