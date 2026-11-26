---
title: Standard data as theta products
lean:
  - New/Derivatives/Vacuum/StandardDataProducts.lean
decls:
  - New.resolutionVectors
  - New.IsTightFrame.isResolution
  - New.CMLattice.exists_prod_twistedTranslate_eq_thetaProd_mul
  - New.Parameters.exists_coprime_mul_mem_of_mem_integralAfter
  - New.Parameters.exists_rho_finiteImage_eq_and_coprime_mul_mem
  - New.Parameters.exists_coprime_isTightFrame_sq
  - New.Parameters.mul_neg_sum_mul_conj_mem_cmCurve_lattice
  - New.Parameters.IsVacuumExpansion
  - New.Parameters.exists_intVacuum_eq_sum_of_isThetaFunction
  - New.Parameters.exists_isVacuumExpansion
  - New.Parameters.thetaMultiples
  - New.Parameters.mem_thetaMultiples_of_jetSeries_eq_prod
  - New.Parameters.exists_jetSeries_map_eq_thetaProd_pow_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Standard data as theta products

The count of Section 4 applies to series with the normal form, and [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/) proves the normal form for series of the shape $(\Theta_\nu^m)^N H$: a power of a theta product along a resolution of the identity, times an integral series in the parameters. This section shows that the theta series of standard data has this shape. The proof has three steps. Fourier inversion writes the integral vacuum through the translates of one vector $F$ whose theta function is a product of copies of $\theta$ along a tight frame, with a denominator prime to $p$. A translate of this product is a product of translates of $\theta$. Each translated factor is handled on one curve.

### Frames and resolutions

A *resolution of the identity* on $E^n$ is a family of vectors $u_j$ with multiplicities $m_j$ such that $z = \sum_j m_j (u_j^\dagger z)\, u_j$ for all complex vectors $z$ indexed by (infinite place, coordinate) ([the CM curve, its formal group and the normal form](/chapter/cm-formal-group/)). A *tight frame* of length $M$ is a family $w_i$ in the lattice $\mathfrak{a}_0$ with $\sum_i \tau(w_i)\overline{\sigma(w_i)} = M\,[\tau = \sigma]$ for the infinite places $\tau$, $\sigma$ ([the integral vacuum and tight frames](/chapter/integral-vacuum/)).

**Definition (Resolution vectors).** For $w_i \in E$ and $\nu \ge 1$, the vector of index $(i, c)$ has $w_i/\nu$ in the coordinate $c$ and $0$ elsewhere.

Lean: `New.resolutionVectors` (New/Derivatives/Vacuum/StandardDataProducts.lean).

**Lemma (A tight frame gives a resolution).** Let $w$ be a tight frame of length $b^2$, with $b \ne 0$, and $k \ne 0$. Then the resolution vectors for $\nu = bk$, each with multiplicity $k^2$, are a resolution of the identity.

Lean: `New.IsTightFrame.isResolution` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* The form $u^\dagger z$ of the vector of index $(i, c)$ involves only the coordinate $c$, with coefficient $\overline{\tau(w_i)}/(bk)$ at the place $\tau$. So the sum $\sum k^2 (u^\dagger z) u$ at $(\sigma, c)$ is $\sum_\tau \big(\sum_i \sigma(w_i)\overline{\tau(w_i)}\big) z_{\tau,c}/b^2 = z_{\sigma,c}$. $\square$

**Lemma (A frame of square length prime to $p$).** There is a tight frame with all multiplicities one whose length is $b^2$ with $b$ prime to $p$.

Lean: `New.Parameters.exists_coprime_isTightFrame_sq` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Take a tight frame of length $b$ prime to $p$ and repeat each vector $b$ times. If $p \nmid q_1$, the powers of $\zeta$ give $b = q_1$. Otherwise [the integral vacuum and tight frames](/chapter/integral-vacuum/) gives a frame whose length is prime to $q_1$, and so prime to $p$ since $p \mid q_1$. $\square$

### A product of translates on one curve

**Lemma (Translates by division points).** Let $C$ be a CM lattice for $d$, $\delta \ne 0$ in $\mathcal{O}_K$ with $\delta\bar\delta = N$, and $y_i \in \mathbb{C}$ with $\delta y_i \in \Lambda$. For linear forms $\mu_i$ over $\mathbb{C}_p$ there is $H \in \mathcal{M}(\mu)$ with

$$\prod_i (T_{y_i}\theta)\big(\iota_p(\bar\delta)\, \mu_i z\big) = \prod_i \theta(\mu_i z)^N \cdot H,$$

where $T_y\theta(z) = \exp\big(-\pi(z\bar y + |y|^2/2)/A\big)\,\theta(z + y)$ is the twisted translate and $A$ is the area of $\Lambda$.

Lean: `New.CMLattice.exists_prod_twistedTranslate_eq_thetaProd_mul` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Multiplication by $\bar\delta$ is an isogeny of degree $N$ of $\Lambda$ to itself. For each $i$, the integrality theorem on one curve (`New.CMLattice.exists_rescale_twistedTranslate_eq_theta_pow_mul`, in [CM elliptic curves](/chapter/cm-elliptic-curves/)) gives an integral series $u_i$ in $y$ with $(T_{y_i}\theta)(\bar\delta z) = \theta(z)^N u_i(z)$. Substitute $z = \mu_i z$ and take the product; $H = \prod_i u_i(\mu_i z)$. $\square$

**Remark (Formalization).** The series $u_i$ are chosen with `choose`, and $H$ is not unique.

### Rational translates

The Heisenberg translates of standard data are by finite adelic points. The theta function is computed for rational translates, so the proof replaces the adelic points by rational ones.

**Lemma (Clearing a denominator prime to $p$).** If a finite adelic vector $x$ is integral above $p$, there is $m$ prime to $p$ with $m x$ integral at every place.

Lean: `New.Parameters.exists_coprime_mul_mem_of_mem_integralAfter` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Some $m_0 \ne 0$ clears all denominators. Write $m_0 = p^e m$ with $p \nmid m$. Above $p$, $x$ is already integral, so $mx$ is. At the other places $p$ is a unit, so $mx$ is integral there if $p^e m x$ is. $\square$

**Lemma (A rational translate).** Let $V$ be a standard space, $F$ in the finite part of $\mathcal{S}(V)$, and $\delta x$ integral above $p$. There are a rational vector $\gamma$ and $m$ prime to $p$ with $\rho(x)F = \rho(\alpha^{-1}\gamma)F$ and $m\delta\gamma \in \mathfrak{a}_0^n$.

Lean: `New.Parameters.exists_rho_finiteImage_eq_and_coprime_mul_mem` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Approximate $x$ by a rational $\gamma$ with $\alpha^{-1}\gamma - x$ in the standard lattice, in a way that does not change the translate of $F$ (`New.exists_finiteImage_approx`, in [the Weil representation from a vacuum](/chapter/weil-representation/)). Then $\delta\alpha^{-1}\gamma$ is integral above $p$, and the previous lemma clears the other denominators. $\square$

**Lemma (Periods).** Let $w \in \mathfrak{a}_0$, $m\delta\gamma \in \mathfrak{a}_0$, $b \ne 0$ and $mb \mid k$. Then

$$k\delta \cdot \Big(-\frac{\Omega_0}{b} \sum_\tau \tau(\gamma)\overline{\tau(w)}\Big) \in \Omega_0 \mathcal{O}_K.$$

Lean: `New.Parameters.mul_neg_sum_mul_conj_mem_cmCurve_lattice` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* The lattice $\mathfrak{a}_0$ is self-dual over $\mathcal{O}_K$, so $t = \sum_\tau \tau(m\delta\gamma)\overline{\tau(w)}$ lies in $\mathcal{O}_K$. Write $k = mbl$; the point is $-l\,t\,\Omega_0$. $\square$

### The expansion of the vacuum

**Definition (Vacuum expansion).** A *vacuum expansion* of a standard space $V$ consists of $b$ prime to $p$, a tight frame $w$ of length $b^2$, a vector $F$ in the finite part of $\mathcal{S}(V)$, points $y_j$ with $b y_j$ integral and coefficients $a_j$ with $\iota_p(a_j)$ integral, such that

1. $\phi^\circ = \sum_j a_j\, \rho(y_j) F$, and
2. for every rational $\gamma$ and every $c \in \mathbb{C}$, the series $J_{c\,\mathrm{areaScale}/\Omega_0}\big(\rho(\alpha^{-1}\gamma)F\big)$ is the product, over the resolution vectors $u$ of index $(i, c')$ for $\nu = b$, of the twisted translates of $\theta$ by $-(\Omega_0/b)\sum_\tau \tau(\gamma_{c'})\overline{\tau(w_i)}$, taken along the forms $c\,u^\dagger z$.

Lean: `New.Parameters.IsVacuumExpansion` (New/Derivatives/Vacuum/StandardDataProducts.lean).

**Lemma (Fourier inversion with a denominator prime to $p$).** Let $b$ be prime to $p$ and $F$ a vector with $\theta(F) = 1$ whose theta function, divided by the Gaussian, is entire and invariant under the signed translations by $b\,\mathfrak{a}_0^n$. Then $\phi^\circ = \sum_j a_j\, \rho(y_j) F$ with $\iota_p(a_j)$ integral and $b\,y_j$ integral.

Lean: `New.Parameters.exists_intVacuum_eq_sum_of_isThetaFunction` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Fourier inversion ([the Weil representation from a vacuum](/chapter/weil-representation/)) gives points $x_i \in b^{-1}\mathfrak{a}_0^n$, periods and coefficients $c_i$ with $\sum_i c_i\, \phi(x_i) = M$, where $\phi$ is the vacuum and $M = (b^2)^{f|n|}$. So $\phi^\circ = \sum_i M^{-1}\phi^\circ(x_i)\, c_i\, \phi$, and each $c_i\phi$ is a sum of translates of $F$. The values $\phi^\circ(x_i)$ are integral by [the integral vacuum and tight frames](/chapter/integral-vacuum/), and $M$ is prime to $p$, so the coefficients are integral. A Heisenberg operator applied to a translate is an integral multiple of a translate (`New.Parameters.exists_finHeisenbergOp_rho_eq_smul`). $\square$

**Theorem (The vacuum has an expansion).** Every standard space has a vacuum expansion.

Lean: `New.Parameters.exists_isVacuumExpansion` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Take the frame of square length $b^2$ prime to $p$. [The integral vacuum and tight frames](/chapter/integral-vacuum/) gives a vector $F$ whose theta function is the product of $\theta$ along the frame, with the period $\Omega_0/\bar b$ (`New.Parameters.exists_isResolutionProduct_of_isTightFrame`), and with $\theta(F) = 1$ and the invariance needed for the previous lemma. Apply that lemma. The product formula for the translates of $F$ is the product formula of the resolution product, with the linear forms rewritten as $c\,u^\dagger z$. $\square$

**Remark (Formalization).** The data $b$, $w$, $F$, $y$ and $a$ are obtained by `obtain` from existence statements; nothing below depends on the choice.

### The main statement

For linear forms $\mu$, a scale $c$ and a series $\Theta$, the set $\mathcal{T}(\mu, c, \Theta)$ consists of the vectors $g$ with $J_c g = \Theta \cdot H$ (read in $\mathbb{C}_p$) for some $H \in \mathcal{M}(\mu)$. It is a submodule over the numbers $a$ with $\iota_p(a)$ integral, since $\mathcal{M}(\mu)$ is a ring that contains these numbers.

Lean: `New.Parameters.thetaMultiples` (New/Derivatives/Vacuum/StandardDataProducts.lean).

**Lemma (Products of translates are theta multiples).** Let $\delta \ne 0$ with $\delta\bar\delta = N$, $k \ne 0$, and suppose $J_c g$ is the product of the twisted translates $T_{t_i}\theta$ along the forms $\bar\delta\, u_i^\dagger z$, for the resolution vectors $u_i$ for $\nu = b$, with $k\delta t_i \in \Lambda$. Then $g \in \mathcal{T}(\mu, c, (\Theta_\mu^{k^2})^N)$, with $\mu$ the forms of the resolution vectors for $\nu = bk$.

Lean: `New.Parameters.mem_thetaMultiples_of_jetSeries_eq_prod` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* The form $\bar\delta\,u^\dagger z$ for $\nu = b$ is $\overline{k\delta}$ times the form for $\nu = bk$. Apply the lemma on translates by division points with $k\delta$, of norm $k^2 N$. $\square$

**Theorem (Standard data as theta products).** Let $f$ be standard data of level $\delta \ne 0$ on a standard space, and $N = \delta\bar\delta$. There is a resolution of the identity $(u_j, m_j)$ with each $\alpha^{-1}u_j$ integral above $p$, and $H \in \mathcal{M}(\nu)$ for the forms $\nu_j = u_j^\dagger z$, such that

$$J_{\bar\delta\,\mathrm{areaScale}/\Omega_0} f = (\Theta_\nu^m)^N \cdot H.$$

Lean: `New.Parameters.exists_jetSeries_map_eq_thetaProd_pow_mul` (New/Derivatives/Vacuum/StandardDataProducts.lean).

*Proof.* Fix a vacuum expansion. For $k \ge 1$ let $\mathcal{T}_k = \mathcal{T}(\mu_k, \bar\delta\,\mathrm{areaScale}/\Omega_0, (\Theta_{\mu_k}^{k^2})^N)$, with $\mu_k$ the forms for $\nu = bk$. First, if $\delta x$ is integral above $p$, there is $m$ prime to $p$ with $\rho(x)F \in \mathcal{T}_k$ for every $k \ne 0$ divisible by $m$: take the rational translate $\gamma$ with $m'\delta\gamma \in \mathfrak{a}_0^n$, put $m = m'b$, and combine the lemma on periods with the product formula and the previous lemma.

Next, prove by induction over the span that every standard data $f$ has such an $m$. A generator is $\rho(x)\phi^\circ = \sum_j a_j\, \rho(x)\rho(y_j)F$, and $\rho(x)\rho(y_j)F$ is an integral multiple of $\rho(x + y_j)F$; take $m$ as the product of the numbers for the points $x + y_j$, which are integral above $p$ after $\delta$, because $b$ is prime to $p$. For a sum take the product of the two numbers, and multiplication by an integral constant keeps $m$.

Finally take $k = m$. The resolution vectors for $\nu = bm$ with multiplicities $m^2$ are a resolution of the identity, their images $\alpha^{-1}u$ are integral above $p$ since $bm$ is prime to $p$, and $f \in \mathcal{T}_m$ is the claim. $\square$

**Remark (Formalization).** The number $m$ is not fixed in advance: it depends on $f$ through the induction, and so do the resolution and $H$. The statement is existential, and Section 8 uses it only in that form.
