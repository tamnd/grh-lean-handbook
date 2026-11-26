---
title: The open cell bound
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/GramSection.lean
  - New/Spanning/Bessel/MeanValue.lean
  - New/Spanning/Bessel/SobolevBound.lean
  - New/Spanning/Bessel/OpenCellBound.lean
  - New/Spanning/Bessel/OpenCellPairing.lean
decls:
  - New.frameDisc
  - New.RealPlace.gramDiscReal
  - New.Shape.openCellConst
  - New.pairingBoundSq
  - New.Shape.openCell
  - New.RealPlace.invCorner
  - New.RealPlace.oneSubNormSqInvCorner
  - New.RealPlace.IsBoundedInCell
  - New.RealPlace.mem_openCell_iff
  - New.RealPlace.sectionMatrix
  - New.RealPlace.sectionMatrix_isometry
  - New.RealPlace.gramSection
  - New.RealPlace.coe_gramSection
  - New.RealPlace.realFrameGram_gramSection
  - New.RealPlace.exists_eq_mul_gramSection_mul
  - New.RealPlace.IsBoundedInCell.norm_sectionMatrix_le
  - New.RealPlace.IsBoundedInCell.of_mem_ball
  - New.RealPlace.gramSectionMeasure
  - New.RealPlace.leGramFibre_gramSectionMeasure
  - New.RealPlace.lintegral_gramSection_le
  - New.Shape.fixerMeasure
  - New.Shape.fixerBall
  - New.RealPlace.HasDerivWords
  - New.RealPlace.lintegral_gramSection_le_of_hasDerivWords
  - New.RealPlace.lintegral_gramSection_integral_le
  - New.RealPlace.isBoundedInCell_of_inv_le_gramDiscReal
  - New.norm_le_of_besselLength_gramSection_mul_le
  - New.exists_mul_eq_mul_gramSection_mul
  - New.BesselSystem.IsKernelBound
  - New.BesselSystem.isL2Contraction_gramSection
  - New.BesselSystem.exists_isKernelBound_gramSection
  - New.BesselSystem.IsOpenCellBound
  - New.BesselSystem.exists_isOpenCellBound
  - New.BesselSystem.piKernel
  - New.BesselSystem.pairKernel
  - New.BesselSystem.adjointIsometry
  - New.BesselSystem.enorm_integral_pairKernel_cut_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The open cell bound

Let $\mathcal B$ be a Bessel system with full function $W$ and cut $W^\flat$, and let $\gamma \in G_1$. This section bounds the pairing $\int W^\flat(y) \otimes \overline{W^\flat(\gamma^{-1}y)}\,dy$ by a power of the *Gram discriminant* of $\gamma$, if it is positive. [The chapter on the remaining terms](/chapter/remaining-terms/) uses the bound.

The argument has four steps. (1) The Gram matrix $Z = Z(\gamma)$ of the frame with its translate determines $\gamma$ up to the fixer of the frame on both sides, and on the open cell there is an explicit section $Z \mapsto \gamma_Z$. (2) A mean value inequality bounds integrals over the coordinates $(Z, s, s')$ by integrals over $G_1$. (3) Sobolev's inequality on a small cube at $Z$ replaces the value at $Z$ by mean squares of derivatives, and the [Schur bound](/chapter/bessel-real-place/#schur-bounds-and-orthonormality) controls these. (4) The places are put together.

### The discriminant and the open cell

Write $Z(y) = (h(f_a, yf_b))_{a, b}$ for the $(\varrho + 1) \times (\varrho + 1)$ matrix of products of the frame $f = (e_0, \dots, e_{\varrho-1}, z)$ with its image (`New.realFrameGram`). Let $D_\varrho(Z)$ be its leading principal minor of order $\varrho$.

**Definition.** The *Gram discriminant* is $\mathsf g(Z) = |\det Z|^2 - |D_\varrho(Z)|^2$. Let $\xi(Z) = (Z^{-1})_{\varrho\varrho}$ be the last diagonal entry of the inverse and $\nu(Z)^2 = 1 - |\xi(Z)|^2$. The *open cell* $\Omega$ is the set of invertible $Z$ with $|\xi(Z)| < 1$. For $P \in \mathbb{R}$, the matrix $Z$ is *bounded in the cell by $P$* if $Z \in \Omega$ and $\|Z\|$, $\|Z^{-1}\|$ and $1/\nu(Z)$ are at most $P$.

Lean: `New.RealPlace.gramDiscReal` (New/Spanning/Bessel/Basic.lean); `New.Shape.openCell`, `New.RealPlace.invCorner`, `New.RealPlace.oneSubNormSqInvCorner`, `New.RealPlace.IsBoundedInCell`, `New.RealPlace.mem_openCell_iff` (New/Spanning/Bessel/GramSection.lean).

For invertible $Z$, Cramer's rule gives $\xi(Z) = D_\varrho(Z)/\det Z$, so $\mathsf g(Z) = |\det Z|^2\nu(Z)^2$. Hence $Z \in \Omega$ if and only if $\mathsf g(Z) > 0$ ([Lemma](/decl/New.RealPlace.mem_openCell_iff/)). The source defines $\mathsf g$ as the real part of $\operatorname{frameDisc}_1(Z)$, where $\operatorname{frameDisc}_N(Z) = \det Z\,\overline{\det Z} - N^2D_\varrho(Z)\overline{D_\varrho(Z)}$ over any commutative star ring.

Lean: `New.frameDisc` (New/Spanning/Bessel/Basic.lean).

**Definition (Constants).** Let $k = |\kappa|$ and $r = k + 2\varrho + 1$. Put
$$c_G = \frac{\operatorname{vol}U(k)}{\operatorname{vol}U(r)}\cdot\frac{2\pi^k}{(k - 1)!}.$$
For $\gamma \in G_1$ with $\mathsf g = \mathsf g(Z(\gamma))$, a degree $\deg$, a radius $\rho$ and a dimension $d$, put
$$\operatorname{pb}(\gamma, \deg, \rho, d) = \Bigl(\frac{\rho^{9n}}{\mathsf g}\Bigr)^{10^5n^4}\frac{d^2}{\deg\cdot c_G\cdot(\mathsf g/2)^{k-1}}.$$

Lean: `New.Shape.openCellConst`, `New.pairingBoundSq` (New/Spanning/Bessel/Basic.lean).

**Remark (Formalization).** The factor $2\pi^k/(k - 1)!$ is `New.sphereDensity k 1`, the area of the unit sphere of $\mathbb{C}^k$. For $\mathsf g \leq 0$ the number $\operatorname{pb}$ is a junk value of real division and powers; every use has $\mathsf g > 0$.

### The section $\gamma_Z$

**Theorem.** There is an explicit matrix $M(Z)$ with these properties.

1. For $Z \in \Omega$, $M(Z)$ preserves the form $J_1$, so it is the matrix of an element $\gamma_Z \in G_1$.
2. For $Z \in \Omega$, $Z(\gamma_Z) = Z$.
3. If $Z(\gamma) = Z \in \Omega$, then $\gamma = u\,k\,\gamma_Z\,(u'k')^{-1}$ with $u, u'$ in the unipotent fixer $\mathsf U^0$ of the frame and $k, k' \in H$.
4. The map $Z \mapsto \gamma_Z$ is measurable, and it is real differentiable on $\Omega$.
5. If $Z$ is bounded in the cell by $T \geq 4$, then $\|M(Z)\| \leq T^{18}$ and the real derivative of $M$ at $Z$ has norm at most $T^{25}$.
6. If $Z$ is bounded in the cell by $T \geq 4$ and $\|Y - Z\| < T^{-6}$, then $Y$ is bounded in the cell by $2T$.

Lean: `New.RealPlace.sectionMatrix`, `New.RealPlace.sectionMatrix_isometry`, `New.RealPlace.gramSection`, `New.RealPlace.coe_gramSection`, `New.RealPlace.realFrameGram_gramSection`, `New.RealPlace.exists_eq_mul_gramSection_mul`, `New.RealPlace.IsBoundedInCell.norm_sectionMatrix_le`, `New.RealPlace.IsBoundedInCell.of_mem_ball` (New/Spanning/Bessel/GramSection.lean).

*Proof.* Let $F$ be the matrix with the columns $f$ and $F'$ the matrix with the columns $e^*_0, \dots, e^*_{\varrho-1}, x_{k_0}$. Let $\zeta$ be the last row of $Z^{-1}$ and $s = \nu(Z)$. With a coefficient matrix $Y$ built from $\zeta$, the matrix $M(Z)$ sends $F$ to $(FY + F'\operatorname{diag}(1, \dots, 1, s))Z$ and fixes the $x_i$ with $i \neq k_0$. A block computation gives $F^*J_1MF = Z$ for every $Z$ (2), and on $\Omega$ it gives $M^*J_1M = J_1$ (1), because the two families that $M$ connects have the same Gram matrix. (3) is Witt's theorem: two isometric embeddings of the frame pair with the same Gram matrix differ by an element that fixes the frame, and the fixer is $\mathsf U^0 H$. (4) The entries of $M(Z)$ are polynomials in $Z$, $\overline Z$, $Z^{-1}$, $s$ and $s^{-1}$, with $s$ a branch of the square root on the slit plane; all are smooth on $\Omega$. (5) follows from the bounds $\|Y\| \leq 2 + 8P^2$, $|s| \leq 2$ and $|s^{-1}| \leq 2/\nu(Z)$. For the derivative, replace $\overline Z$ by an independent variable $W$: then $M$ is holomorphic in $(Z, W)$ and bounded by $P^{12}$ on a ball about $(Z, Z^*)$, and the Schwarz lemma bounds the derivative. (6) writes $Y = Z(1 + Z^{-1}(Y - Z))$ and $Y^{-1} - Z^{-1} = Y^{-1}(Z - Y)Z^{-1}$, and compares $\xi(Y)$ with $\xi(Z)$. $\square$

**Remark (Formalization).** Off $\Omega$ the section has the junk value $\gamma_Z = 1$. No statement uses $\gamma_Z$ for $Z \notin \Omega$. The index $k_0 \in \kappa$ is a fixed choice of the shape, so $\gamma_Z$ depends on it.

### The mean value inequality

Let $\mathsf R^0 = \mathsf U^0 H$ be the fixer of the frame, with Lebesgue measure on $\mathsf U^0$ times the Haar probability measure of $H$.

**Theorem (Mean value inequality).** For every measurable $f : G_1 \to [0, \infty]$,
$$\int_\Omega c_G\,\mathsf g(Z)^{k-1}\int_{\mathsf R^0}\int_{\mathsf R^0}f(s'\gamma_Zs)\,ds\,ds'\,dZ \leq \int_{G_1}f(\gamma)\,d\gamma.$$

Lean: `New.RealPlace.gramSectionMeasure`, `New.RealPlace.leGramFibre_gramSectionMeasure`, `New.RealPlace.lintegral_gramSection_le` (New/Spanning/Bessel/MeanValue.lean).

*Proof.* Consider the law of $s\gamma_Zf$ under $dZ\,ds$ with the density $2^{-(\varrho+1)}\cdot 2\pi^k/(k - 1)!\cdot\mathsf g(Z)^{k-1}$. A frame whose products with $f$ form $Z$ is $y'Z$, with $y'$ dual to $f$. The first $\varrho$ vectors of $y'$ are moved by $\mathsf U^0$, and the part in $X_0$ of the last vector runs over a sphere of squared radius $\nu(Z)^2$. In these coordinates the law is at most the fibre measure of the Gram map $Y \mapsto Y^*J_1Y$ over the Gram matrix of $f$. [The fibre comparison](/decl/New.LeGramFibre.mconv_fixerHaar_le/) of [the chapter on Bessel subgroups](/chapter/bessel-bruhat/) bounds the convolution of the fibre measure with $\mathsf R^0$ by $\operatorname{vol}U(r)/(\operatorname{vol}U(k)\,2^{\varrho+1})$ times Haar measure. The product of this ratio with $c_G$ is the density above. $\square$

The source cites Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935), for fibre measures of the Gram map. Here the comparison is only an inequality.

### Sobolev and the Schur bound

**Definition.** The measure $\mu_c$ on $H \times \mathsf U^0$ is $c_G\,c^{k-1}$ times the Haar measures. The *fixer ball* of radius $R$ is the set of $(h, u)$ with $\|u\| \leq R$. A family $V_w$ on $G_1$, indexed by words in a finite alphabet $L$, *has derivative words with constant $\Lambda$* if along every curve with $\gamma' = \gamma X$ and $\|X\| \leq C$ near $t$, $V_w \circ \gamma$ is differentiable at $t$ with derivative of norm at most $\Lambda C\sum_{l \in L}\|V_{l :: w}(\gamma(t))\|$.

Lean: `New.Shape.fixerMeasure`, `New.Shape.fixerBall`, `New.RealPlace.HasDerivWords` (New/Spanning/Bessel/SobolevBound.lean).

**Theorem.** Let $P \geq 8r$, let $F$ have the Schur bound $(P, D)$, and let $c > 0$. Let every $Y$ with $\|Y - Z\| < P^{-6}$ be bounded in the cell by $P$ and have $\mathsf g(Y) \geq c$. Let $\varphi$ be measurable and integrable, with $\varphi(y) \neq 0 \Rightarrow \|y\| \leq P^{20}$. Then
$$\int_{\text{fixer ball }P^{20}}\Bigl\|\int_{G_1}\varphi(y)\,F\bigl(\gamma_Z(uh)^{-1}y\bigr)\,dy\Bigr\|^2 d\mu_c(h, u) \leq P^{2000n^2}D\int_{G_1}|\varphi|^2.$$

Lean: `New.RealPlace.lintegral_gramSection_le_of_hasDerivWords`, `New.RealPlace.lintegral_gramSection_integral_le` (New/Spanning/Bessel/SobolevBound.lean).

*Proof.* Let $V_w$ be the derivatives of the Schur bound and $\Phi_w(g) = \int\varphi_w(y)V_w(gy)\,dy$, with weights $\varphi_w$ that absorb the factors of the chain rule (`New.RealPlace.convolutionWeight`). The real dimension of the space of $Z$ is $2n^2$. Sobolev's inequality on the cube of side $P^{-8}$ at $Z$ (`New.sobolev_trace_cube`, Lib/General/Analysis/PackingAndSobolev.lean) bounds $|\Phi(\gamma_Z k)|^2$ by $P^{550n^2}$ times the mean over the cube of $\sum_{|w| \leq 2n^2}|\Phi_w(\gamma_Yk)|^2$. On the cube, $\mathsf g(Y)^{k-1} \geq c^{k-1}$, so the mean value inequality bounds the integral over $(Y, k)$ by the integral over $G_1$. The function $|\Phi_w|^2$ is left invariant under $\mathsf U$, and the unfolding bound `New.lintegral_mul_le_of_frameMatrix_le` passes from $G_1$ to $\mathsf U\backslash G_1$ at the price of the volume of a ball in $\mathsf U$. There the Schur inequality for $V_w$ applies. $\square$

### The bound at one place

**Definition (Open cell bound).** Let $\gamma \in G_1$ and $\rho \in \mathbb{R}$. An *open cell bound* for $\mathcal B$ at $\gamma$ and $\rho$ is a compact set $A \subseteq G_1$, a probability measure $m$ on $H \times \mathsf U^0$, a measurable map $t$ into the fixer of the frame, and a finite measure $\nu$ on $G_1$, such that:

1. for every bounded measurable $\varphi$,
$$\int\sum_{i, j}\Bigl|\int_A\varphi(z)\,W_i(\gamma t(x)z)\,\overline{W_j(t(x)z)}\,dz\Bigr|^2 dm(x) \leq \int|\varphi|^2\,d\nu;$$
2. $\nu(G_1) \leq \operatorname{pb}(\gamma, \deg, \rho, |I|)$;
3. for $m$-almost every $x$, $A$ contains every $z$ in the frame box of radius $\rho$ with $\ell(\gamma t(x)z) \leq \rho$.

Lean: `New.BesselSystem.IsOpenCellBound`, `New.BesselSystem.IsKernelBound` (New/Spanning/Bessel/OpenCellBound.lean).

Item 1 is [`New.IsL2Contraction`](/decl/New.IsL2Contraction/).

**Theorem (Open cell bound).** Let $\mathsf g(Z(\gamma)) > 0$ and $\rho \geq b$. Let some $y$ have $y$ and $\gamma^{-1}y$ in the frame box of radius $\rho$. Then an open cell bound for $\mathcal B$ at $\gamma$ and $\rho$ exists.

Lean: `New.BesselSystem.exists_isOpenCellBound`, `New.RealPlace.isBoundedInCell_of_inv_le_gramDiscReal`, `New.RealPlace.gramDiscReal_div_two_le_and_isBoundedInCell`, `New.exists_mul_eq_mul_gramSection_mul`, `New.BesselSystem.exists_isKernelBound_gramSection`, `New.BesselSystem.isL2Contraction_gramSection`, `New.norm_le_of_besselLength_gramSection_mul_le` (New/Spanning/Bessel/OpenCellBound.lean).

*Proof.* Put $Z = Z(\gamma)$ and $M = \rho^{9n}/\mathsf g(Z)$. The frame boxes give $|Z_{ab}| \leq \rho^2$, and this gives $\rho \leq M$ and $M^{-1} \leq \mathsf g(Z)$. Then $Z$ is bounded in the cell by every $T \geq M^{8n}$, and for $P \geq M^{9n}$ every point of the ball of radius $P^{-6}$ about $Z$ is bounded in the cell by $P$ and has discriminant at least $\mathsf g(Z)/2$. By item 3 of the theorem on the section there are $s \in S$ and a measurable $t$ into the fixer with $\gamma t(h, v) = s\gamma_Z(vh)^{-1}$. Take for $A$ a tube over a set of $v \in \mathsf U^0$, for $m$ the Haar measure conditioned on that set, and for $\nu$ a multiple of $\|W\|^2$ on $A$. The Sobolev theorem with $P = (M^{9n})^{5n} = M^{45n^2}$ and the Schur bound of $\mathcal B$ (which holds for every $P \geq b^5$) give item 1. The total exponent is $93600n^4 + 2n^2 + 45n \leq 10^5n^4$, which gives item 2. Item 3 uses a bound for $\|z\|$ from the length of $\gamma_Zz$ ([Lemma](/decl/New.norm_le_of_besselLength_gramSection_mul_le/)). $\square$

That lemma moves $\gamma_Zz$ by some $w \in \mathsf U$, which must not change $\mathsf g$. For this, OpenCellBound.lean takes one result from [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/), a later chapter of this volume, through its import of Unfolding/Link.lean:

**Lemma (from Link.lean).** Let $T$ be a form over a commutative star ring, $\gamma \in G_T$, and $u, u' \in \mathsf U$. Then for every $N$, $\operatorname{frameDisc}_N\bigl(Z_T(u^{-1}\gamma u')\bigr) = \operatorname{frameDisc}_N\bigl(Z_T(\gamma)\bigr)$, where $\operatorname{frameDisc}_N(Z) = |D_{\varrho+1}(Z)|^2 - N^2|D_\varrho(Z)|^2$.

Lean: `New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU` (New/Spanning/Unfolding/Link.lean).

The source proves it there for the cells of Poincaré series; this chapter needs only $u' = 1$, $N = 1$.

### All places together

Let $(\mathcal B_v)_{v \in \iota}$ be a finite family of Bessel systems with the same $b$ and $f$. For $\sigma \in \{\text{full}, \text{cut}\}$ the *pair kernel* at $\gamma = (\gamma_v)$ and $y = (y_v)$ is the vector
$$K_\sigma(\gamma, y)_{(i, j)} = \prod_v W^\sigma_{v, i_v}(y_v)\,\overline{W^\sigma_{v, j_v}(\gamma_v^{-1}y_v)},$$
the matrix of $\bigotimes_v W^\sigma_v(y_v) \otimes \overline{W^\sigma_v(\gamma_v^{-1}y_v)}$ with the Hilbert-Schmidt norm.

Lean: `New.BesselSystem.pairKernel`, `New.BesselSystem.piKernel`, `New.BesselSystem.adjointIsometry` (New/Spanning/Bessel/OpenCellPairing.lean).

**Theorem (One pairing).** Let $\mathsf g(Z(\gamma_v)) > 0$ for every $v$, let some $y'$ have $y'_v$ and $\gamma_v^{-1}y'_v$ in the frame box of radius $\rho_v$, with $\rho_v \geq b^{6n+2}$. Let $\varphi$ be measurable on $G_1^\iota$, $|\varphi| \leq 1$, invariant under the fixer of the frame at each place, and such that $\varphi K_{\text{cut}}(\gamma, y) \neq 0$ implies $y_v$ in the frame box of radius $\rho_v$ for all $v$. Then $\varphi K_{\text{cut}}(\gamma, \cdot)$ has compact support and
$$\Bigl\|\int\varphi(y)K_{\text{cut}}(\gamma, y)\,dy\Bigr\| \leq \Bigl(\prod_v\operatorname{pb}(\gamma_v, \deg_v, \rho_v, |I_v|)\Bigr)^{1/2} + \int|\varphi(y)|\,\|K_{\text{full}}(\gamma, y) - K_{\text{cut}}(\gamma, y)\|\,dy.$$

Lean: `New.BesselSystem.enorm_integral_pairKernel_cut_le` (New/Spanning/Bessel/OpenCellPairing.lean).

*Proof.* The pair kernel at $\gamma$ is the adjoint of the kernel of $W(\gamma^{-1}y) \otimes \overline{W(y)}$ at $\gamma^{-1}$, and taking adjoints is an isometry. Also $Z(\gamma^{-1}) = Z(\gamma)^*$, so $\mathsf g$ is the same for $\gamma^{-1}$. Split $K_{\text{cut}} = K_{\text{full}} - (K_{\text{full}} - K_{\text{cut}})$. For $K_{\text{full}}$, the open cell bounds at each place multiply to an $L^2$ contraction on the product (`New.IsL2Contraction.pi`). Since $\varphi$ is invariant under the fixer, one shift $t$ is no worse than the mean, and Cauchy-Schwarz with $|\varphi| \leq 1$ gives the root of the product of the masses. $\square$

**Remark (Formalization).** The family $\iota$ is any finite type; in the users it is the set of infinite places. The hypothesis $\rho_v \geq b^{6n+2}$ puts every point with $W^\flat \neq 0$ under the length condition of item 3.
