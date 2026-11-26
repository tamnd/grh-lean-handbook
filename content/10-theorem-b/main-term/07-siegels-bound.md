---
title: Siegel's bound
lean:
  - New/Spanning/MainTerm/SiegelTopBound.lean
decls:
  - New.Filling.IsFillingData.exists_scaledSiegelConst_eq_and_massRatio_le
  - New.Filling.IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure
  - New.Filling.IsFillingData.siegel_sum_le_lintegral_sphere
  - New.Filling.IsFillingData.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq
  - New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing
  - New.Filling.IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Siegel's bound

The sieve of [Section 4](/chapter/main-term/#the-global-sieve) bounds sums over the heads $p$, but the top form of the sieve is a density at the last entry $t$. This section bounds the squared norms of the class sums that share one last entry $t$ by the densities at $t$. The tool is Siegel's formula with one vector: the number of lattice vectors of a given norm, summed over the classes of the genus, is a product of local densities. Here only an upper bound is used, and only the factor at $T$ is kept.

In this section $F$ is a filling datum at $T$, $M^{-1}$, $N^{-1}$ and the lattice basis are integral off $T$, and $Z$ is an intermediate group. Siegel's constant is
$$\operatorname{siegelConst} = \Bigl(\frac{\pi^k}{(k-1)!\,N^k}\Bigr)^f |\operatorname{disc}E|^{1/4}\,(\operatorname{vol}\hat{\mathcal O})^k,$$
and $\operatorname{scaledSiegelConst}$ is a positive multiple of it ([the anatomy of a term](/chapter/anatomy-of-a-term/)).

Siegel's formula with one vector is the theorem `New.classSum_eq_mul_normDensity` of [One vector and Siegel's formula](/chapter/siegel-weil/): the sum over the classes of the genus of the numbers of representations of $\beta$, weighted by the inverse orders of the stabilizers, is the mass times the norm density $\int\int f(x)\psi_f(z(x^*x - \beta)/2)\,dx\,dz$ times the factor at infinity.

### The constants and the local density

**Lemma (Constants).** There is $D > 0$ with $\operatorname{scaledSiegelConst} = D \cdot \#\mathrm{Classes} \cdot \operatorname{siegelConst}$ and
$$\operatorname{massRatio}(Z) \leq \mu_H(K(M))\,\mu(K(M))^2\,\#(Z/K(M))\,D.$$

Lean: `New.Filling.IsFillingData.exists_scaledSiegelConst_eq_and_massRatio_le` (New/Spanning/MainTerm/SiegelTopBound.lean).

*Proof.* $\operatorname{massRatio}(Z) = \mu(Z)\mu(K(M))/\operatorname{unipotentMass}^2$. Cover $Z$ by its cosets of $K(M)$, so $\mu(Z) = \#(Z/K(M))\,\mu(K(M))$. The group $K(M)$ is the product of its part in $H$ and its part in the floors, and the floors below $\varrho$ give $\operatorname{unipotentMass}$. By the matching lemma of [Section 6](/chapter/main-term/#kloosterman-sums-and-unfolding) the remaining factors are explicit powers of $M^f$ and the order of the reduction. Take $D$ to be the quotient of these factors. $\square$

**Lemma (The norm density at $T$).** Let $\Psi \geq 0$ be continuous of compact support on $\operatorname{LocProd}(T)^k$, let $\beta$ be Hermitian, and let $f$ be $\Psi$ at $T$ times the indicator of the vectors integral off $T$. Then
$$\bigl|\operatorname{normDensity}(f, \beta)\bigr| \leq (1 + b^{-6})\,(\operatorname{vol}\hat{\mathcal O})^k \int \Psi\,d\nu_{\delta\beta},$$
where $\nu_{\delta\beta}$ is the fibre measure on the sphere $y^*y = \beta$ at $T$.

Lean: `New.Filling.IsFillingData.enorm_normDensity_le_mul_lintegral_normFiberMeasure` (New/Spanning/MainTerm/SiegelTopBound.lean).

*Proof.* Split the frequency $z$ into its part at $T$ and its part off $T$. The function $f$ is a product, so the density is a product of the density at $T$ and the density off $T$. At $T$, the inner integral over $z$ is the fibre measure of the sphere ([local frames](/chapter/local-frames/)). Off $T$, the density is $(\operatorname{vol}\hat{\mathcal O})^k$ times an integral of Gauss sums over the frequencies. Its norm is at most the ideal zeta value $\zeta_{\hat{\mathcal O}}(3\varrho + 4)$, since $2(3\varrho + 5) \leq k$. By the sizes of [the data](/chapter/data-and-sizes/) this value is at most $1 + b^{-6}$. $\square$

**Theorem (Siegel's sum).** Let $\Psi \geq 0$ be continuous of compact support and invariant under small translations. For pairs in a finite set with $N v^*v = t\bar t - N^2$ and $x$ integral off $T$, the values of $\Psi$ at the vectors with last entry $t$ add up to at most
$$(1 + b^{-6})\,\#\mathrm{Classes}\,\operatorname{siegelConst}\Bigl(\prod_v(|t|_v^2 - N^2)\Bigr)^{k-1} |\pi_N|^{-1}\int \Psi \circ v_t\,d\nu,$$
where $\pi_N$ is a unit at $T$ of norm $N$ and the integral is over the sphere $y^*y = (t\bar t - N^2)/N$.

Lean: `New.Filling.IsFillingData.siegel_sum_le_lintegral_sphere` (New/Spanning/MainTerm/SiegelTopBound.lean).

*Proof.* Group the pairs by their class. Apply Siegel's formula with one vector to each class, with $f$ as in the lemma on the norm density and $\beta = (t\bar t - N^2)/N$. The factor at infinity is the volume of the sphere of radius $\sqrt{\beta}$ in $\mathbb C^k$ at each infinite place, which is $\pi^k\beta_v^{k-1}/(k-1)!$. Multiply over $v$ and bound the density at $T$ by the lemma. $\square$

### From coset amplitudes to the fibre pairing

Fix heads $a_p$, $p \in J$, with entries below $\varrho$ that are $T$-units, and let $R$ be the Gram matrix of the tensors $\rho_p\int W(y) \otimes W((w_p\gamma)^{-1}y)^*\,dy$ at infinity.

**Lemma (One term).** Let $\rho_p$ times the head density of $a_p$ be a number $w$ independent of $p$, and let $n_i \in Z$ have distinct reductions $s_i$. Then
$$w^2\,\#(Z/K(M))\,\mu(K(M))^2 \sum_i \Bigl\|\sum_p\operatorname{cosetAmplitude}(c, s_i, c')(w_p\gamma)\Bigr\|^2$$
is at most the head sum of the scaled orbital integrals at $T$ against $R$.

Lean: `New.Filling.IsFillingData.sum_sq_norm_sum_cosetAmplitude_le_headSumNormSq` (New/Spanning/MainTerm/SiegelTopBound.lean).

*Proof.* By the corollary on scaled orbital integrals of [Section 6](/chapter/main-term/#kloosterman-sums-and-unfolding), each coset amplitude times $w\,\mu(K(M))$ is an entry of the scaled orbital integral at $T$ paired with the integral at infinity. The distinct reductions give distinct cosets $a$. The squared norms of the entries add up to at most the squared norm of the whole matrix, and the pairing with $R$ is the head sum. $\square$

**Lemma (One point).** Let the terms $(c'_i, s_i, \gamma_i)$ be distinct, with the same left class, the same $h(z, \gamma_i z)$ and the same $X_0$-part of $\gamma_i z$, so that all translates send $z$ to the same point $e$ at $T$. Let $R$ be positive semidefinite. Then
$$\begin{aligned} &w^2\,\mu_H(K(M))\,\mu(K(M))^2\,\#(Z/K(M))\sum_i\Bigl\|\sum_p\operatorname{cosetAmplitude}(w_p\gamma_i)\Bigr\|^2 \\ &\qquad\leq \operatorname{Re}\sum_{p,q}R_{pq}\,\operatorname{fiberPairing}(\omega_p, \omega_q)(e).\end{aligned}$$

Lean: `New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le_fiberPairing` (New/Spanning/MainTerm/SiegelTopBound.lean).

*Proof.* Terms with the same point $e$ differ by an element of $H$ at $T$. If two translates are congruent modulo $K(M)$, their classes agree and the terms are equal. So the terms over $e$ are distinct points of $H/(H \cap K(M))$. The fibre pairing is the integral over $H$ of the head sums; restrict the integral to the cosets of the terms and apply the lemma on one term to each. $\square$

### The bound at one last entry

**Theorem (Siegel's step).** Let $S$ be admissible. Let the terms $(c_i, c'_i, \bar n_i, \gamma_i)$, $i \in j$, be distinct, with $\gamma_i$ rational in the floor group, $h(z, \gamma_i z) = t$, translates integral off $T$, $n_i \in Z$ at $T$, and $j$ nonempty. Let $N^2 < |t|_v^2$ for all $v$, let every head have entry $t$ at $\varrho$, and let $R$ be the Gram matrix of the tensors for every $i$. If $\rho_p$ times the head density is $r\sqrt{G}$ with $G = (\prod_v(|t|_v^2 - N^2))^{k-1}$, then
$$\sum_i r^2\Bigl\|\sum_p\operatorname{cosetAmplitude}(w_p\gamma_i)\Bigr\|^2 \leq (1 + b^{-6})\,\operatorname{scaledSiegelConst}\cdot\operatorname{Re}\sum_{p,q}R_{pq}\frac{\rho_\pi(p, q)}{\operatorname{massRatio}(Z)}.$$

Lean: `New.Filling.IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity` (New/Spanning/MainTerm/SiegelTopBound.lean).

Here $\rho_\pi$ is the [last entry density](/chapter/finite-densities/#the-top-floor).

*Proof.* Group the terms by the point of Siegel's sum: the class and the $X_0$-part of $\gamma_i z$. The translate of a term sends $z$ to the vector with last entry $t$ over that point. It has norm $(t\bar t - N^2)/N$ and it is integral off $T$. By the [lemma on step functions](/chapter/finite-densities/#the-top-floor), the positive part of $\operatorname{Re}\sum R_{pq}\operatorname{fiberPairing}$ is a step function $\Psi$ of compact support. By the lemma on one point, the terms over one point are bounded by $\Psi$ at the point, divided by $w^2\mu_H(K(M))\mu(K(M))^2\#(Z/K(M))$. Siegel's sum adds these values over the points. The integral of $\Psi$ over the sphere, divided by $|\pi_N|$, is the real part of the sum of the last entry densities. The factor $G$ cancels against $w^2 = r^2 G$, and the lemma on constants turns the remaining masses into $\operatorname{scaledSiegelConst}/\operatorname{massRatio}(Z)$. $\square$
