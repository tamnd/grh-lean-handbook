---
title: The size of a block
lean:
  - New/Spanning/RemainingTerms/Size.lean
decls:
  - New.Filling.amplitudeSum_eq_inter_compl_add_inter
  - New.Filling.sqrt_secondMoment_add_le
  - New.Filling.sum_norm_amplitudeSum_sub_cut_le
  - New.Filling.card_residueGL_mul_b_pow_le
  - New.Filling.secondMoment_sub_cut_le
  - New.Filling.eq_one_of_mul_eq_mul_of_termDisc_ne_zero
  - New.Filling.enorm_integral_besselKernel_le
  - New.Filling.enorm_amplitudeSum_le_orbitBound_top
  - New.Filling.isNear_of_amplitudeMajorant_ne_zero
  - New.Filling.enorm_amplitudeSum_le_of_termDiscNorm_le
  - New.Filling.enorm_amplitudeSum_le_orbitBound
  - New.Filling.enorm_amplitudeSum_le_tsum_fibre
  - New.Filling.hasCellRank_cellRank_of_mem
  - New.Filling.enorm_amplitudeSum_le_tsum_termSize
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The size of a block

This section proves the first step of the sketch: a cut block of a stable set $T \subset \Gamma^*$ is at most $\nu$ times the sum of the sizes of its near representatives. It also proves three facts about the second moment: the blocks split over a partition of the terms, the square root of the second moment is subadditive, and the passage from the full Bessel functions to the cut ones costs little.

### Second moments

**Lemma (Splitting the terms).** For sets $T, U$ of rational points, $\mathcal{A}_T = \mathcal{A}_{T \cap U^c} + \mathcal{A}_{T \cap U}$, for the full and for the cut Bessel functions.

Lean: `New.Filling.amplitudeSum_eq_inter_compl_add_inter` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* The terms of $T$ over $(c, s, c')$ are the disjoint union of those in $U^c$ and those in $U$. The amplitudes are absolutely summable ([the chapter on Poincaré series](/chapter/poincare-series/)), so the sum splits. $\square$

**Lemma (Minkowski's inequality).** For two families $A, B$ of blocks, $\sqrt{\mathsf{E}(A + B, \Omega)} \leq \sqrt{\mathsf{E}(A, \Omega)} + \sqrt{\mathsf{E}(B, \Omega)}$.

Lean: `New.Filling.sqrt_secondMoment_add_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* $\sqrt{\mathsf{E}(A, \Omega)}$ is $\nu^{-1}$ times the norm of the restriction of $A$ to $\{(c, s, c') : s \in \Omega\}$ in the $\ell^2$ space of finitely many vectors. The norm satisfies the triangle inequality. $\square$

[The chapter on Poincaré series](/chapter/poincare-series/) bounds the tail of the Bessel functions ([Theorem](/decl/New.Filling.tsum_lintegral_enorm_besselKernel_sub_cut_le/)). In one line: for fixed $c, s$, the sum over the classes $d$ and the terms $\gamma \in U$ over $(c, s, d)$ of $\int\beta_c(y)\beta_d(\gamma^{-1}y)\|W(y) \otimes W(\gamma^{-1}y)^* - W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*\|\,dy$ is at most $\nu b^{-k^3f}/2$.

**Lemma (The cut changes a row little).** For a set $U$ of rational points and fixed $c, s$,

$$\sum_{c'}\|\mathcal{A}_U(c, s, c') - \mathcal{A}^\flat_U(c, s, c')\| \leq \nu b^{-k^3f}/2.$$

Lean: `New.Filling.sum_norm_amplitudeSum_sub_cut_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* The difference of the blocks is the sum over the terms of the integrals of $\beta_c\beta_{c'}$ times the difference of the kernels. Bound the norm of the sum by the sum of the norms, the norm of each integral by the integral of the norm, and use the tail bound. $\square$

**Lemma (The number of reductions).** $\#\bar G\cdot b^{40} \leq (2b^{k^3f})^2$.

Lean: `New.Filling.card_residueGL_mul_b_pow_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* $\bar G$ is a product over the chosen places of groups $\mathrm{GL}_r$ over residue fields, with $r = 2\varrho + k + 1$, so $\#\bar G \leq M^{r^2f} \leq b^{23r^2f}$. Since $k$ is large against $\varrho$, $r \leq 2k$, and $23r^2f + 40 \leq 92k^2f + 40 \leq 2k^3f$. $\square$

**Theorem (The cut costs little in the second moment).** For a set $U$ of rational points and every $\Omega$,

$$\mathsf{E}(\mathcal{A}_U - \mathcal{A}^\flat_U, \Omega) \leq b^{-40}\mathcal{D}_{\mathrm{id}}.$$

Lean: `New.Filling.secondMoment_sub_cut_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* Enlarge $\Omega$ to $\bar G$. For each row $(c, s)$, the sum of the squares over $c'$ is at most the square of the sum, which is at most $(\nu b^{-k^3f}/2)^2$ by the row lemma. There are $\#\mathrm{Classes}\cdot\#\bar G$ rows. So the second moment is at most $\#\mathrm{Classes}\cdot\#\bar G\,b^{-2k^3f}/4 \leq \#\mathrm{Classes}\cdot b^{-40}$ by the previous lemma. Finally $\#\mathrm{Classes} \leq \mathcal{D}_{\mathrm{id}} = \#\bar R_0\cdot\#\mathrm{Classes}\cdot\#\mathrm{BesselCoord}$, since both other factors are at least $1$. $\square$

### The open cell

If $\mathsf{g}(\gamma) \neq 0$, the term lies in the top cell, and its amplitude is bounded one term at a time.

**Lemma (The stabilizer of a coset is trivial).** Let $\mathsf{g}(\gamma) \neq 0$, $p \in \mathsf{U}^0_c$ and $w \in \mathsf{U}_{c'}$ with $p\gamma = \gamma w$. Then $w = 1$.

Lean: `New.Filling.eq_one_of_mul_eq_mul_of_termDisc_ne_zero` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* Put $\delta = \gamma^{-1}$. Then $w\delta = \delta p$. Since $\mathsf{g}(\gamma) \neq 0$, the matrix of products of the frame $\mathfrak{f}$ with $\delta\mathfrak{f}$ has a nonzero determinant: it is the conjugate transpose of the matrix for $\gamma$, whose determinant is not $0$ ([Theorem](/decl/New.Filling.termDisc_eq_zero_iff/) gives the meaning of $\mathsf{g} = 0$). As $p$ fixes the frame, $w$ fixes the vectors $\delta\mathfrak{f}$. Multiply these vectors on the right by the inverse of the matrix of products. This gives vectors $B$ fixed by $w$ whose products with the first $\varrho$ frame vectors form the identity matrix. A unipotent element of $\mathsf{U}$ that fixes such vectors is $1$. So $w = 1$. $\square$

So in each double coset $\mathsf{U}^0_c\gamma\mathsf{U}_{c'}$ with $\mathsf{g} \neq 0$ the pairs $(u, u')$ that move $\gamma$ to a chosen representative are unique. This makes an unfolding with a single chosen term per double coset possible.

**Theorem (Open cell).** Let $\gamma$ be near with $\mathsf{g}(\gamma) \neq 0$. Let $\omega \leq 1$ be measurable, invariant on the left under the fixer of the frame at each place, and zero at every point that lies in the cut but not in the frame box at some place. Let $\varepsilon \geq 0$ with $\prod_v\operatorname{pairingBoundSq}(\gamma_v) \leq \varepsilon^2$. Then

$$\Big\|\int\omega(y)\,W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*\,dy\Big\| \leq \varepsilon + \int\omega(y)\,\|W(y) \otimes W(\gamma^{-1}y)^* - W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*\|\,dy.$$

Lean: `New.Filling.enorm_integral_besselKernel_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* This is [Theorem](/decl/New.BesselSystem.enorm_integral_pairKernel_cut_le/) of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/), applied to the family $\gamma_v$ and the radius $\rho = b^{37n}$, which is at least $b^{6n+2}$. Its hypotheses hold. The real Gram discriminant of $\gamma_v$ is the image of $\mathsf{g}(\gamma)$ under $\Phi_v$ times a positive factor ([Lemma](/decl/New.Filling.gramDiscReal_realFrameGram_ratToInf/)), so it is positive. A boxed point lies in the frame box ([Theorem](/decl/New.Filling.mem_frameBox_of_mem_boxedPoints/)), and nearness gives a $y$ with $y$ and $\gamma^{-1}y$ boxed. $\square$

**Theorem (A block of the top cell).** Let $T$ be stable with $\mathsf{g} \neq 0$ on $T$. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\| \leq \sum_{\gamma \in T \text{ over } (c, s, c'),\ \gamma \text{ near rep.}}\nu\operatorname{orbitBound}(\varrho + 1, \operatorname{termDiscNorm}(\gamma)).$$

Lean: `New.Filling.enorm_amplitudeSum_le_orbitBound_top` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* In each double coset $\mathsf{U}^0_c\gamma\mathsf{U}_{c'}$ choose a representative, and choose a near representative if there is one. Let $\omega$ be the indicator of the reduced points; it is a partition of unity in boxes for $\mathsf{U}_{c'}$ modulo $\mathsf{U}^0_{c'}$. By the previous lemma, the weight "$\omega(uy)$ if $u\gamma u'^{-1}$ is the representative" sums to $1$ over $(u, u')$. A change of weight in the unfolding ([Lemma](/decl/New.Filling.hasSum_amplitudeSum_of_cutoff/), from [the chapter on Poincaré series](/chapter/poincare-series/)) writes the block as the sum over the representatives $\gamma$ of $\int\omega(y)W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*\,dy$, and bounds the same sum for $W - W^\flat$ by $\nu b^{-k^3f}/2$.

Take a representative $\gamma$. If it is a near representative, $\mathsf{g}(\gamma)$ is a nonzero algebraic integer, so $x = \operatorname{termDiscNorm}(\gamma) \geq 1$. Put $\varepsilon = \nu\operatorname{orbitBound}(\varrho + 1, x)/2$. [Lemma](/decl/New.Filling.prod_pairingBoundSq_le/) gives $\prod_v\operatorname{pairingBoundSq} \leq \varepsilon^2$. The open cell theorem bounds the integral by $\varepsilon$ plus the tail. The tail is at most $\nu b^{-k^3f}/2$, and $b^{-k^3f} \leq \operatorname{orbitBound}(\varrho + 1, x)$ by [the lower bound for the top orbit bound](/decl/New.Filling.IsNear.inv_pow_le_orbitBound/). So the integral is at most $2\varepsilon$. If no element of the double coset is a near representative, the kernel vanishes at every reduced point ([the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/#the-box-and-the-size-of-a-near-term)), so the integral is $0$. $\square$

### Schur's test on a block

**Lemma (Majorants of far terms vanish).** If $\operatorname{maj}(c, c', \gamma) \neq 0$, then $\gamma$ is near.

Lean: `New.Filling.isNear_of_amplitudeMajorant_ne_zero` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* By Cauchy-Schwarz the majorant is at most the square root of $I(c, c', \gamma, 0)I(c', c, \gamma^{-1}, 0)$. If $\gamma$ is not near, $\beta^\square_c(y)\beta^\square_{c'}(\gamma^{-1}y) = 0$ for every $y$, so $I(c, c', \gamma, 0) = 0$. $\square$

**Theorem (A block by Schur's test).** Let $T$ be stable, with every term of cell rank $j$, with $\operatorname{termDiscNorm} \leq N^f\operatorname{minorNorm}(j, \cdot)$ on $T$, and with no term over $(c, s, c')$ of cell rank $0$. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\| \leq \sum_{\gamma \in T \text{ over } (c, s, c'),\ \gamma \text{ near rep.}}\nu\operatorname{orbitBound}(j, \operatorname{maxGauge}(j, c, c', \gamma)).$$

Lean: `New.Filling.enorm_amplitudeSum_le_of_termDiscNorm_le` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* Bound the norm of the block by the sum of the majorants. Group the terms by their orbit under $\mathsf{U}^0_c \times \mathsf{U}^0_{c'}$; the orbits lie in $T$ and over the block, since $T$ is stable and $\mathsf{U}^0_c$ lies over $(c, 1, c)$. In each orbit let the chosen element be $\operatorname{out}$ of the double coset. If the sum over an orbit is not zero, some term has a nonzero majorant and is near, and then the chosen element is near too ([Lemma](/decl/New.Filling.IsNear.mul_of_mem_besselU0/)), so it is a near representative. Its cell rank $j$ is not $0$. The theorem on one orbit bounds the sum over the orbit by $\nu\operatorname{orbitBound}(j, \operatorname{maxGauge})$ at the chosen element, since the gauge is constant on the orbit. $\square$

**Remark (Formalization).** The chosen element of an orbit is `DoubleCoset.out`, an element chosen by the axiom of choice. Nothing depends on the choice: the bound is a sum of one number per orbit, and that number is constant on the orbit.

**Theorem (A block of one cell rank).** Let $T$ be stable, with every term of cell rank $j$, and with no term over $(c, s, c')$ of cell rank $0$. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\| \leq \sum\nu\operatorname{orbitBound}(j, \operatorname{maxGauge}(j, c, c', \gamma)),$$

where $\gamma$ runs over the terms of $T$ over $(c, s, c')$ that are near representatives, and the sum is empty unless $s$ agrees.

Lean: `New.Filling.enorm_amplitudeSum_le_orbitBound` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* If $s$ does not agree, the block of a stable set is $0$ ([Lemma](/decl/New.Filling.amplitudeSum_eq_zero_of_not_agrees/), in [the chapter on Poincaré series](/chapter/poincare-series/)). Let $K$ be the set of $\gamma$ with $N^f\operatorname{minorNorm}(j, \gamma) < \operatorname{termDiscNorm}(\gamma)$. It is stable, since the minor and $\mathsf{g}$ are invariant ([Lemma](/decl/New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU/)). On $K$, $\mathsf{g} \neq 0$, so $j = \varrho + 1$; there both indices $\iota$ are $1$ and $\operatorname{maxGauge} = \operatorname{termDiscNorm}$. So the top cell theorem bounds $\mathcal{A}^\flat_{T \cap K}$. Off $K$, the previous theorem bounds $\mathcal{A}^\flat_{T \cap K^c}$. Add, by the splitting lemma. $\square$

### The theorem on the size

**Lemma (Fibres).** For every map $\phi$ from the rational points to a set $I$, $\|\mathcal{A}^\flat_T(c, s, c')\| \leq \sum_{i \in I}\|\mathcal{A}^\flat_{T \cap \phi^{-1}(i)}(c, s, c')\|$.

Lean: `New.Filling.enorm_amplitudeSum_le_tsum_fibre` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* The block is the sum over $i$ of the blocks of the fibres, as the amplitudes are absolutely summable. Apply the triangle inequality. $\square$

**Lemma (Cell ranks in $\Gamma^*$).** Every $\gamma \in \Gamma^*$ has the cell rank $\operatorname{cellRank}(\gamma)$.

Lean: `New.Filling.hasCellRank_cellRank_of_mem` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* If $\mathsf{g}(\gamma) \neq 0$, $\gamma$ has the top cell rank ([Lemma](/decl/New.Filling.hasCellRank_last/)). Otherwise the definition of $\Gamma^*$ ([the chapter on Poincaré series](/chapter/poincare-series/)) contains a cell rank. In both cases $\operatorname{cellRank}$, chosen by Hilbert's epsilon, is a cell rank ([Lemma](/decl/New.Filling.HasCellRank.hasCellRank_cellRank/)). $\square$

**Theorem (Size).** Let $S$ be admissible over a field with a primitive root of unity of order $5040$. Let $T \subset \Gamma^*$ be stable, and fix $c, s, c'$. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\| \leq \sum_{\gamma \in \mathcal{R}_T(c, s, c')}\nu\operatorname{termSize}(c, c', \gamma),$$

where $\mathcal{R}_T(c, s, c')$ is the set of near representatives of $T$ over the block: the terms of $T$ over the block that are near, are the chosen element of their orbit and have a cell rank, provided $s$ agrees; it is empty otherwise.

Lean: `New.Filling.enorm_amplitudeSum_le_tsum_termSize` (New/Spanning/RemainingTerms/Size.lean).

*Proof.* Sort the terms by $\operatorname{cellRank}$, by the fibre lemma. Each fibre $T \cap \operatorname{cellRank}^{-1}(j)$ is stable, since the cell rank is invariant ([Lemma](/decl/New.Filling.isStable_hasCellRank/)), and all its terms have the cell rank $j$ by the previous lemma. No term of $\Gamma^*$ has cell rank $0$ ([Lemma](/decl/New.NormOnePairOccursFrom.notMem_remainingTerms/)). The previous theorem bounds each fibre. The terms that appear are exactly the near representatives of $T$ of cell rank $j$, and for them $\operatorname{orbitBound}(j, \operatorname{maxGauge}) = \operatorname{termSize}$. $\square$

**Example.** Let $T$ be one orbit $\mathsf{U}^0_c\gamma\mathsf{U}^0_{c'}$, saturated to a stable set. The size theorem bounds its cut block by $\nu$ times $\operatorname{termSize}$ of one point per near orbit. For $\gamma$ of cell rank $j \leq \varrho$ the size is $\tau^2(\tau^{-16}\mathcal{D}_{\mathrm{id}}/(n_pM^{2jfk}x^k))^{1/2}$. Since $M \geq b^{19}$ and $\tau^4 = b^{kf}$, the factor $M^{-jfk}$ is at most $\tau^{-76j}$, a very small number. So the terms below the top cell are cheap, but there are many of them, and the count of [the count and the sum](/chapter/remaining-terms/#the-count-and-the-sum) is needed.

