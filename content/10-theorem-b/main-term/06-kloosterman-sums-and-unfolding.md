---
title: Kloosterman sums and unfolding
lean:
  - New/Spanning/MainTerm/KloostermanSum.lean
  - New/Spanning/MainTerm/GlobalToLocal.lean
decls:
  - New.integral_comp_quotientMk
  - New.Floors.PlaceData.kloostermanSum
  - New.Floors.PlaceData.tsum_extendedBesselChar_mul_star_extendedBesselChar
  - New.Floors.IntegralPlace.IsLargeLatticeData.besselOrbitalIntegral_besselVector_apply
  - New.Filling.leadingMinor_mem_boundedNonzeroIntegers
  - New.Filling.NamesLink
  - New.Filling.exists_amplitudeSum_eq_sum_cosetAmplitude
  - New.Filling.IsFillingData.mem_principalLevel_iff
  - New.Filling.IsFillingData.reduction_eq_iff
  - New.Filling.IsFillingData.psi_simpleRootSum_eq_unipotentChar
  - New.Filling.IsFillingData.modulus_levelUnit
  - New.Filling.IsFillingData.unipotentOrder_mul_unipotentMass_eq_one
  - New.Filling.hasSum_besselOrbitalIntegral_cosetAmplitude
  - New.Filling.IsFillingData.cosetAmplitude_eq_kloostermanSum_smul
  - New.Filling.IsFillingData.scaledOrbitalIntegral_smul_eq_cosetAmplitude
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kloosterman sums and unfolding

This section writes a block of an amplitude sum as a finite sum of coset amplitudes, and each coset amplitude as a Kloosterman sum at $T$ times an orbital integral at the infinite places. The Kloosterman sum is in turn an entry of an orbital integral of the finite Bessel vector of [the finite places](/chapter/finite-densities/). So each block becomes a sum of products of a local integral at $T$ and a local integral at infinity.

In this section $F$ is a filling datum at $T$ ([Section 5](/chapter/main-term/#the-place-at-t-and-filling-data)) and $M^{-1}$ is integral off $T$. $K(M)$ is the principal congruence subgroup of level $M$ at $T$, $\mathsf U$ is the Bessel unipotent group and $\chi$ is the finite Bessel function, which is the character $\psi_{\mathsf U}$ on $\mathsf U$ ([the finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector)).

### The Kloosterman sum

**Lemma (Integrals over cosets).** Let $\mu$ be a left invariant measure on a second countable topological group $G$, and $J$ an open subgroup with $\mu(J) < \infty$. For a function $f$ on $G/J$,
$$\int_G f(yJ)\,d\mu(y) = \mu(J) \sum_{q \in G/J} f(q).$$

Lean: `New.integral_comp_quotientMk` (New/Spanning/MainTerm/KloostermanSum.lean).

*Proof.* The quotient is discrete, because $J$ is open, and countable, because $G$ is second countable. Each coset has measure $\mu(J)$ by left invariance. So the image of $\mu$ on $G/J$ is $\mu(J)$ times the counting measure. $\square$

**Remark (Formalization).** If $f$ is not summable, the Lean sum is $0$, and $f \circ \pi$ is not integrable, so the Bochner integral is $0$ too. The identity holds in all cases.

**Definition (Kloosterman sum).** For $x, s$ in the unitary group at $T$,
$$\operatorname{Kl}(x, s) = \sum_{w, w' \in \mathsf U/(\mathsf U \cap K(M))} \mathbf 1\bigl[s^{-1} w^{-1} x w' \in K(M)\bigr]\, \chi(w)\,\overline{\chi(w')},$$
with each coset read through a chosen representative.

Lean: `New.Floors.PlaceData.kloostermanSum` (New/Spanning/MainTerm/KloostermanSum.lean).

For $\mathrm{GL}_2$ and $x$ a Weyl element times a diagonal element, this is the classical Kloosterman sum $\sum e((a\bar d + d')/c)$ ([Notes](/chapter/main-term/#exercises-and-notes)).

**Lemma (The sum over cosets).** Let $s$ be integral. Then
$$\sum_{q \in G/K(M)} \chi(q s^{-1})\,\overline{\chi(x^{-1} q)} = \operatorname{Kl}(x, s).$$

Lean: `New.Floors.PlaceData.tsum_extendedBesselChar_mul_star_extendedBesselChar` (New/Spanning/MainTerm/KloostermanSum.lean).

*Proof.* The function $\chi$ is supported on $\mathsf U K(M)$ and is $\psi_{\mathsf U}(u)$ at $uk$. A term on the left is nonzero only if $q = w s K(M) = x w' K(M)$ with $w, w' \in \mathsf U$. These $w, w'$ are unique modulo $\mathsf U \cap K(M)$, and the term is $\chi(w)\overline{\chi(w')}$. So $(w, w') \mapsto x w' K(M)$ is a bijection between the supports of the two sums, and it keeps the terms. $\square$

**Theorem (Orbital integral at $T$).** Let $Z$ be a group between $K(M)$ and the integral points, with Bessel vector $W_a(y) = \chi(y a^{-1})$ for the cosets $a$ of $K(M)$ in $Z$. If $s^{-1} a b^{-1} \in K(M)$, then
$$\int W_a(y)\,\overline{W_b(x^{-1} y)}\,d\mu(y) = \mu(K(M))\,\operatorname{Kl}(x, s).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.besselOrbitalIntegral_besselVector_apply` (New/Spanning/MainTerm/KloostermanSum.lean).

*Proof.* Since $a, b \in Z$, $s$ is integral. Put $yb$ for $y$; the Haar measure is right invariant because $G$ is unimodular. The integrand becomes $\chi(y b a^{-1})\overline{\chi(x^{-1} y)}$. As $b a^{-1} \in s^{-1}K(M)$ up to conjugation by an integral element, and $\chi$ is invariant under $K(M)$ on the right, it is constant on the cosets $yK(M)$ and equals $\chi(q s^{-1})\overline{\chi(x^{-1}q)}$. $K(M)$ is open of finite measure. Apply the lemma on cosets and then the lemma on the sum over cosets. $\square$

### From a block to coset amplitudes

**Lemma (Bounded minors).** Let $\gamma$ be a term over $(c, s, c')$ with a nonzero cut amplitude. Then each nonzero leading minor of the frame products of $\gamma$ lies in $\operatorname{boundedNonzeroIntegers}$.

Lean: `New.Filling.leadingMinor_mem_boundedNonzeroIntegers` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* The frame products of a term are integers, so the minors are integers. The amplitude is nonzero, so at some point $y$ at infinity both $W^\flat(y)$ and $W^\flat(\gamma^{-1}y)$ are nonzero. Unipotent translates of the two points lie in the boxes of [the cut Bessel function](/chapter/bessel-real-place/#the-bessel-system-of-the-data), and the translates do not change the minors. In the boxes the minors have $|\Phi_v\delta|^2 \leq b^{270n^2}$. $\square$

**Definition (Names a link).** $(t, \sigma, k)$ *names the link* $\Lambda$ over $(c, s, c')$ if: $\sigma$ fixes the $\varrho$ hyperbolic pairs; $t$ is the last diagonal entry $h(z, \sigma z)$ of the frame products of $\sigma$; $N^2 < |\Phi_v t|^2$ for every infinite place $v$; $k \in K$ reduces to $s$; $\Lambda$ is the link of $w_1\sigma$; $t \in \mathcal T$; and $h_c^{-1}\sigma h_{c'}$ is integral off $T$.

Lean: `New.Filling.NamesLink` (New/Spanning/MainTerm/GlobalToLocal.lean).

**Theorem (Blocks as coset sums).** Let $S$ be admissible, let the elements of $\mathcal T$ be $T$-units, and let the leading minors $D_0, \dots, D_\varrho$ of every term over $(c, s, c')$ be nonzero. Let $A$ be the block of the cut amplitude sum over the terms with $\operatorname{termDisc} \neq 0$ and link $\Lambda$, and let $A \neq 0$. Then there is $(t, \sigma, k)$ that names $\Lambda$, and
$$A = \sum_{p : \{0, \dots, \varrho - 1\} \to \mathcal T} \operatorname{cosetAmplitude}(c, s, c')\bigl(w_{(p, t)}\sigma\bigr).$$

Lean: `New.Filling.exists_amplitudeSum_eq_sum_cosetAmplitude` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* Since $A \neq 0$, some term $\gamma_0$ has a nonzero amplitude. Its minors are nonzero, so it lies in the big cell: $\gamma_0 = u_0^{-1} w_{p_0} \sigma u_0'$ with $u_0, u_0' \in \mathsf U$, $\sigma$ in the floor group, and $p_0$ the list of quotients $D_{l+1}D_{l-1}/(D_l \bar D_l)$ of minors ([the anatomy of a term](/chapter/anatomy-of-a-term/)). By the lemma on bounded minors, each entry of $p_0$ is in $\mathcal T$. The last diagonal entry $t = h(z, \sigma z)$ satisfies $N\,\omega^*\omega = t\bar t - N^2$ for the last column $\omega$ of $\sigma$, and $\operatorname{termDisc} \neq 0$ gives $t\bar t \neq N^2$; then $N^2 < |t|^2$ at every place since $\omega^*\omega$ is totally nonnegative. The integrality of $h_c^{-1}\gamma_0 h_{c'}$ and the $T$-units give the integrality off $T$. Every other term with the link $\Lambda$ is $u^{-1} w_p \sigma u'$ for the same $\sigma$ and $t$ and some $p$ with entries in $\mathcal T$: the link fixes $\sigma$ up to the cell, and the map $(u, p, u') \mapsto u^{-1}w_p\sigma u'$ is injective. Group the terms by $p$. $\square$

### The coset amplitude as a product

The filling datum matches the adelic objects with the objects at $T$.

**Lemma (Matching at $T$).** Let $F$ be filling data with $M^{-1}$ integral off $T$.

1. $x$ is in the principal level $K(M)$ if and only if $x$ is integral off $T$ and its projection is in $K(M)$ at $T$.
2. Two $k, l \in K$ have the same reduction modulo $M$ if and only if $\operatorname{toPlaces}(k)^{-1}\operatorname{toPlaces}(l) \in K(M)$.
3. For $x$ integral off $T$, $\psi\bigl(M^{-1}\sum_{\text{simple roots}} x\bigr)$ at $T$ is the unipotent character of $S$ at $x$.
4. The modulus of $M$ at $T$ is $(M^f)^{-2}$.
5. The order of the reduction of the integral points of $\mathsf U$ modulo $M$, times the measure of $\mathsf U \cap K(M)$ at $T$, is $1$.

Lean: `New.Filling.IsFillingData.mem_principalLevel_iff`, `New.Filling.IsFillingData.reduction_eq_iff`, `New.Filling.IsFillingData.psi_simpleRootSum_eq_unipotentChar`, `New.Filling.IsFillingData.modulus_levelUnit`, `New.Filling.IsFillingData.unipotentOrder_mul_unipotentMass_eq_one` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* Item 1 is the theorem on levels of [Section 5](/chapter/main-term/#the-place-at-t-and-filling-data) with $u = M$. Item 2 is item 1 for $k^{-1}l$, which is integral off $T$. Item 3: $M^{-1}$ times the sum of the simple root coordinates is integral off $T$, and $\operatorname{charOnPlaces}(T)$ agrees with the global character on such adeles, since $\psi_f$ is trivial on $\hat{\mathcal O}$ times the inverse different. Item 4: $M$ is a rational integer, so its modulus at $T$ is the product of $|M|_w$ over $w \in T$, which is $\prod_{w}|M|_w$ over all finite places since $M$ is a unit off $T$; by the product formula this is $|N_{E/\mathbb Q}M|^{-1} = M^{-2f}$. Item 5: $\mathsf U \cap K(M)$ is a product of floors. By item 4 the floor $l$ has volume $(M^f)^{-(2d_l + 1)}$ with $d_l = k + 1 + 2(\varrho - l - 1)$, and the reduction of its integral points modulo $M$ has the inverse order. Sum the exponents over the floors. $\square$

**Lemma (Coset amplitudes as orbital integrals).** Let $\gamma = w_p\sigma$ with $\sigma$ in the floor group. Let $r$ and $r'$ list points of $\mathsf U$ without repetition, one in each coset $u\,\mathsf U_c(M)$ and $u'\,\mathsf U_{c'}(M)$ for which $u^{-1}\gamma u'$ is a term. Then $\operatorname{cosetAmplitude}(c, s, c')(\gamma)$ is the sum over the pairs $(r_i, r'_j)$ with $\delta = r_i^{-1}\gamma r'_j$ a term of the orbital integral $\int W(y) \otimes W(\delta^{-1}y)^*\,dy$ at the infinite places.

Lean: `New.Filling.hasSum_besselOrbitalIntegral_cosetAmplitude` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* The group $\mathsf U_c(M) \times \mathsf U_{c'}(M)$ acts freely on the terms in $\mathsf U\gamma\mathsf U$, by uniqueness in the big cell, and each orbit contains exactly one $r_i^{-1}\gamma r'_j$. The amplitude is the integral of $W(y) \otimes W(\delta^{-1}y)^*$ against the cutoffs of $c$ and $c'$. The cutoffs sum to $1$ over the orbit ([the anatomy of a term](/chapter/anatomy-of-a-term/)), so the sum over one orbit of the amplitudes is the integral over all $y$. $\square$

**Theorem (Unfolding).** Let $F$ be filling data, $M^{-1}$ integral off $T$, and $S$ admissible. Let $\gamma = w_p\sigma$ with the inverses of $p_0, \dots, p_{\varrho-1}$ $T$-integers, $\sigma$ in the floor group, and $h_c^{-1}\gamma h_{c'}$ integral off $T$. For $k \in K$ with reduction $\bar k$,
$$\operatorname{cosetAmplitude}(c, \bar k, c')(\gamma) = \operatorname{Kl}\bigl(\operatorname{toPlaces}(h_c^{-1}\gamma h_{c'}),\, \operatorname{toPlaces}(k)\bigr) \cdot \int W(y) \otimes W(\gamma^{-1}y)^*\,dy,$$
the integral taken at the infinite places for the full or the cut Bessel function.

Lean: `New.Filling.IsFillingData.cosetAmplitude_eq_kloostermanSum_smul` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* Choose the lists $r, r'$ of the lemma inside $\mathsf U$ with translates integral off $T$, one point in each coset modulo $M$; this uses the lifts of [Section 5](/chapter/main-term/#the-place-at-t-and-filling-data). For $u, u' \in \mathsf U$ the orbital integral of $u^{-1}\gamma u'$ at infinity is $\psi_\infty(u)\overline{\psi_\infty(u')}$ times that of $\gamma$, by the substitution $y \mapsto uy$. By item 3 of the matching lemma and the product formula for $\psi$ on rational points, $\psi_\infty(u) = \chi(\operatorname{toPlaces}(u))$, the value at $T$. By items 1 and 2, $r_i^{-1}\gamma r'_j$ is a term over $(c, \bar k, c')$ if and only if $\operatorname{toPlaces}(r_i)^{-1} x \operatorname{toPlaces}(r'_j) \in \operatorname{toPlaces}(k)K(M)$. So the sum of the lemma is the Kloosterman sum times the orbital integral of $\gamma$. $\square$

**Corollary (Scaled orbital integrals).** In the setting of the theorem let $Z$ be an intermediate group and $a, b$ cosets with $\operatorname{toPlaces}(k)^{-1}ab^{-1} \in K(M)$. Let $q = p$ read at $T$, $l = \operatorname{toPlaces}(h_c^{-1}\sigma h_{c'})$, and $\kappa$ the head density of $q$. Then the $(a, b)$ entry of the scaled orbital integral of $Z$ at $(q, l^{-1})$, times the orbital integral of $\gamma$ at infinity, is $\kappa\,\mu(K(M))\operatorname{cosetAmplitude}(c, \bar k, c')(\gamma)$.

Lean: `New.Filling.IsFillingData.scaledOrbitalIntegral_smul_eq_cosetAmplitude` (New/Spanning/MainTerm/GlobalToLocal.lean).

*Proof.* The scaled orbital integral is $\kappa$ times the orbital integral of the Bessel vector at $w_q l$, which is $\operatorname{toPlaces}(h_c^{-1}\gamma h_{c'})$. Apply the theorem on the orbital integral at $T$ and the theorem on unfolding. $\square$
