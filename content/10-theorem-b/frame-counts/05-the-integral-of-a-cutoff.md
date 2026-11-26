---
title: The integral of a cutoff
lean:
  - New/Spanning/Unfolding/CutoffIntegral.lean
decls:
  - New.Filling.continuous_besselKernel
  - New.Filling.enorm_besselKernel
  - New.Filling.enorm_amplitude_le
  - New.Filling.besselU_mul_apply_eq_add
  - New.Filling.rowCoords
  - New.Filling.measurePreserving_rowCoords
  - New.Filling.lintegral_classCutoff_eq_measure
  - New.Filling.freeLattice
  - New.Filling.exists_fundamental_domain_freeLattice
  - New.Filling.rowCoords_fst_mem_freeLattice
  - New.Filling.exists_rowCoords_fst_eq
  - New.Filling.rowCoords_snd_mem_imSkewLattice
  - New.Filling.exists_rowCoords_snd_eq
  - New.Filling.unipotentCovolume_eq_prod
  - New.Filling.exists_box_existsUnique_rowCoords_mem
  - New.Filling.lintegral_classCutoff_eq_unipotentCovolume
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The integral of a cutoff

This section computes the integral of a class cutoff over the real unipotent group $\mathsf U_\infty$, a copy of $\mathsf U$ at each infinite place. The measure is the product of the Haar measures $\mu_{\mathsf U}$ (`New.Shape.besselHaar`) of [Bessel subgroups and the big cell](/chapter/bessel-bruhat/). The answer is the number `S.unipotentCovolume`, defined in [the anatomy of a term](/chapter/anatomy-of-a-term/). It depends neither on the class nor on the point. The section first records three facts on the Bessel kernel.

### The Bessel kernel

The kernel is $K_\gamma(y) = W(y) \otimes W(\gamma^{-1}y)^*$, with $W$ the Bessel vector at the infinite places, full or cut.

**Lemma.** $K_\gamma$ is continuous, and $\|K_\gamma(y)\| = \prod_v\|W_v(y_v)\|\cdot\prod_v\|W_v((\gamma^{-1}y)_v)\|$. The norm of the amplitude $\int\beta_c(y)\beta_{c'}(\gamma^{-1}y)K_\gamma(y)\,dy$ is at most the integral of the norm of its integrand (`amplitudeMajorant`).

Lean: `New.Filling.continuous_besselKernel`, `New.Filling.enorm_besselKernel`, `New.Filling.enorm_amplitude_le` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* Each coordinate is a product of continuous local Bessel functions. For the norm, square both sides; the sum over pairs of index tuples of the squared coordinates factors over the places. The last claim is the triangle inequality for Bochner integrals. $\square$

**Remark (Formalization).** The amplitude is a Bochner integral. If the integrand is not integrable, Lean gives it the value $0$, and the bound holds trivially. The majorant is a lower integral in $[0, \infty]$, and it may be infinite.

### Coordinates on the unipotent group

An entry $(e_a, j)$ is *free* (`New.RealPlace.IsFreeEntry`) if $j$ is $e_b$ or $e^*_b$ with $b > a$, or a column of the middle block. The *coordinates* of $u \in \mathsf U_\infty$ (`rowCoords u`) are, for each row $e_a$ and place $v$, the free entries of the row $e_a$ of $u_v$, and the imaginary part of the entry at $(e_a, e^*_a)$.

**Lemma.** The coordinates carry the product of the Haar measures $\mu_{\mathsf U}$ to Lebesgue measure.

Lean: `New.Filling.rowCoords`, `New.Filling.measurePreserving_rowCoords` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* At each place, the free entries and the imaginary parts carry $\mu_{\mathsf U}$ to Lebesgue measure (`measurePreserving_freeEntries_besselHaar`, from [Bessel subgroups and the big cell](/chapter/bessel-bruhat/)). Regroup the coordinates by rows instead of places. $\square$

**Lemma (Additivity).** Let $j$ be $e^*_a$ or free for the row $a$. Suppose the free entries of $u$ vanish in the rows $e_b$, $b > a$, and in the row $e_b$ with $j = e^*_b$, and the entries of $u$ at $(e_b, e^*_b)$, $b > a$, are real. Then $(xu)_{e_a, j} = u_{e_a, j} + x_{e_a, j}$ for every $x \in \mathsf U$.

Lean: `New.Filling.besselU_mul_apply_eq_add` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* In $\sum_l x_{e_a, l}u_{l, j}$, the terms with $l$ of lower level vanish because $u$ is unitriangular, and the terms with $l$ of higher level vanish by the hypotheses. Only $l = e_a$ and $l = j$ remain. The real entries at $(e_b, e^*_b)$ contribute nothing to the imaginary part. $\square$

### The lattices

Let $\Gamma$ be the image of $\mathsf U_c(M)$ in $\mathsf U_\infty$. The *free lattice* $\Lambda_a$ (`freeLattice c a`) consists of the rescaled embeddings of rational vectors $x$ on the free columns of the row $a$ with $B_ax$ integral. Here $B_a$ (`freeBlock c a`) is the transposed block of the lattice basis of $c$ on these columns. The *skew lattice* $\Lambda'_a$ (`imSkewLattice`) consists of the vectors $(M\operatorname{Im}\Phi_v(s)/\sigma_v(a))_v$ for the integers $s$ of $E$ with $\bar s = -s$, where $\sigma_v(a)$ is `S.frameScaleSq v a`.

**Lemma.** The lattice $\Lambda_a$ has a measurable strict fundamental domain of volume

$$\Bigl(\frac{\prod_vM^2/\sigma_v(a)}{\operatorname{vol}(\hat{\mathcal O})}\Bigr)^{d_a},\qquad d_a = (\varrho - 1 - a) + (k + 1) + (\varrho - 1 - a),$$

where $d_a$ is the number of free columns of the row $a$.

Lean: `New.Filling.freeLattice`, `New.Filling.exists_fundamental_domain_freeLattice` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* The lattice is a class lattice of the matrix $B_a^{-1}$, rescaled at each place by the ratios of the basis scales. The general fundamental domain of a class lattice (`New.exists_fundamental_domain_classLattice`, see [the other tools](/chapter/fitting-ideals/)) gives volume $|\text{scale}|^2/\operatorname{vol}(\hat{\mathcal O})$ per column, times the index of $\det B_a$, which is $1$ (`genIndex_det_freeBlock`). The product of the squared scales is computed by `prod_norm_basisScale_sq_div_eq`. $\square$

**Lemma.** Let $\gamma \in \mathsf U_c(M)$.

1. The free entries of the row $e_a$ of $\gamma$ lie in $\Lambda_a$. Conversely, every $l \in \Lambda_a$ is the vector of free entries in the row $e_a$ of some $\gamma$ whose coordinates vanish in the rows $e_d$, $d > a$.
2. If right multiplication by $\gamma$ adds its $(e_a, e^*_a)$ entry, then the imaginary parts of this entry lie in $\Lambda'_a$. Conversely, every $l \in \Lambda'_a$ is this vector for some $\gamma$ whose other coordinates vanish.

Lean: `New.Filling.rowCoords_fst_mem_freeLattice`, `New.Filling.exists_rowCoords_fst_eq`, `New.Filling.rowCoords_snd_mem_imSkewLattice`, `New.Filling.exists_rowCoords_snd_eq` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* (1) The row of $M^{-1}(\gamma - 1)$ at $e_a$ is integral on the lattice of $c$ (`classUnipotent_sub_one_div_M_row_integral`). Conversely, apply the lemma on a prescribed row of [reduced points](/chapter/frame-counts/#reduced-points) with $s = 0$. (2) The entry is $M$ times a skew integer $s$, because $\gamma$ is unitary and the additivity makes the entry of $\gamma^{-1}\gamma$ zero (`star_inv_mul_apply_eStar_eq_neg`, `isIntegral_inv_mul_apply_eStar`). Conversely, apply the prescribed row with $l = 0$ and the given $s$. $\square$

**Lemma.** `S.unipotentCovolume` is the product over the rows $a$ of the covolume of $\Lambda_a$ and of

$$\prod_v\Bigl|\frac{M}{\sigma_v(a)}\Bigr|\cdot|D_E|^{1/4},$$

the covolume of $\Lambda'_a$.

Lean: `New.Filling.unipotentCovolume_eq_prod` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* Expand the definition and regroup the product by rows. Reindex the sum $\sum_a(a + (k + 1) + a)$ by $a \mapsto \varrho - 1 - a$; it becomes $\sum_ad_a$. The factor `S.frameScaleProd` is $\prod_v\prod_{a \leq \varrho}\sigma_v(a)^{k + 2(\varrho - a)}$, with $\sigma_v(a) = \kappa_v^{2(\varrho - a)}/N$. Its factor at $a = \varrho$ is $N^{-kf}$, and it cancels $N^{-k}$ in the definition. For $a < \varrho$, the identity $k + 2(\varrho - a) = d_a + 1$ gives the row $a$ the factor $M^{2d_a + 1}$, the scales $\sigma_v(a)^{-(d_a + 1)}$, the volume $\operatorname{vol}(\hat{\mathcal O})^{-d_a}$ and $|D_E|^{1/4}$. $\square$

### The unfolding

**Lemma (Unfolding).** Let $B \subseteq \mathsf U_\infty$ be measurable, and suppose $B$ meets each coset $u\Gamma$ in exactly one point. Then

$$\int_{\mathsf U_\infty}\beta_c(uy)\,du = \mu(B).$$

Lean: `New.Filling.lintegral_classCutoff_eq_measure` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* The inverse $B^{-1}$ is a fundamental domain for the left action of $\Gamma$. The measure is invariant under left translation and under inversion. Unfold the integral over $B^{-1}$, and use $\sum_{\gamma \in \Gamma}\beta_c(\gamma uy) = 1$ from [cutoffs, rigidity and packing](/chapter/frame-counts/#cutoffs-rigidity-and-packing). $\square$

**Lemma (A box).** There are measurable sets $F_a$ and $F'_a$ such that each coset $u\Gamma$ has exactly one point with coordinates in $\prod_aF_a \times \prod_aF'_a$. The product of the volumes of all $F_a$ and $F'_a$ is `S.unipotentCovolume`.

Lean: `New.Filling.exists_box_existsUnique_rowCoords_mem` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* Take $F_a$ a fundamental domain of $\Lambda_a$ and $F'_a$ one of $\Lambda'_a$. Order the coordinates from the last row upward. By the additivity lemma, once the coordinates of the later rows vanish, the group translates a coordinate of the row $a$ by the lattice $\Lambda_a$ or $\Lambda'_a$, and the elements given by the last lemma change no coordinate of the same or a later step. This is the triangular situation of `existsUnique_mul_mem_box`, the abstract form of the reduction lemma of [reduced points](/chapter/frame-counts/#reduced-points). The volumes multiply to the covolume by the last lemma. $\square$

**Theorem (The integral of a cutoff).** Let $S$ be admissible and $c$ a class. For every point $y$,

$$\int_{\mathsf U_\infty}\beta_c(uy)\,d\mu(u) = \texttt{S.unipotentCovolume}.$$

Lean: `New.Filling.lintegral_classCutoff_eq_unipotentCovolume` (New/Spanning/Unfolding/CutoffIntegral.lean).

*Proof.* Let $B$ be the preimage of the box under the coordinates. By the unfolding lemma the integral is $\mu(B)$. The coordinates preserve the measure, so $\mu(B)$ is the product of the Lebesgue volumes of the $F_a$ and $F'_a$, which is the covolume. $\square$

**Remark (Formalization).** The integral is a lower integral in $[0, \infty]$, and the right side is `ENNReal.ofReal` of a real number. The proof passes through `volume.real`, which gives $0$ for an infinite measure. The covolume is positive, so the measure is finite and no junk value enters. The source describes this result as a case of the covolume computation for Heisenberg radicals, with a fixed product Haar measure in place of Tate's self-dual measures.
