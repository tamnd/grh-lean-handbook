---
title: The gain
lean:
  - New/Spanning/RemainingTerms/Gain.lean
decls:
  - New.Filling.linkCorank_eq_zero_iff
  - New.Filling.le_finrank_commonLink_add
  - New.Filling.termDisc_eq_zero_iff_of_link_eq
  - New.Filling.abs_norm_det_gram_sub_le
  - New.Filling.one_le_mul_linkDiscSq
  - New.Filling.LinkSplitting.one_le_mul_linkDiscSq
  - New.Filling.torsionIndex_mul_discriminant_commonPart_le
  - New.Filling.map_commonPart_le
  - New.Filling.submoduleIndex_pairLattice_dvd_torsionIndex
  - New.Filling.isLatticeOfRank_and_pairDiscriminant_le
  - New.Filling.one_le_pairDiscriminant
  - New.Filling.pairDiscriminant_sq_le
  - New.Filling.IsNear.levelGauge_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The gain

Take two terms $\gamma, \gamma'$ over one block $(c, s, c')$ with $s$ agreeing. Their common lattice $L_{12}$ (`pairLattice`) is the part of $L_\gamma \cap L_{\gamma'}$ in $\operatorname{commonLink}(\gamma, \gamma')$, and $d_{12}$ (`pairDiscriminant`) is its discriminant. This section proves the bound

$$\big(d_{12}\cdot x\big)^2 \leq (2/M)^{2c^+f}\,\mathsf{g}^*(\gamma)\,\mathsf{g}^*(\gamma'),$$

where $c^+ = \operatorname{linkCorank}(\gamma, \gamma')$ and $x \leq \operatorname{meetNorm}(s)$ is a gain that is used only when the links are equal and $\gamma$ is in the top cell. When the links differ, the factor $(2/M)^{2c^+f}$ is the gain. It comes from the congruence: $\gamma\gamma'^{-1}$ is $1$ modulo $M$ on $\Lambda_c$, so the two links are close $M$-adically, and two lattices that pair integrally modulo $M$ cannot both be small.

### Coranks

**Lemma (Coranks).** $c^+ = 0$ if and only if the links of $\gamma$ and $\gamma'$ are equal. If $\gamma$ has the cell rank $j$, then $k \leq \dim\operatorname{commonLink}(\gamma, \gamma') + c^+ + (j - \varrho)$. If $\gamma, \gamma'$ have cell ranks and the same link, then $\mathsf{g}(\gamma) = 0$ if and only if $\mathsf{g}(\gamma') = 0$.

Lean: `New.Filling.linkCorank_eq_zero_iff`, `New.Filling.le_finrank_commonLink_add`, `New.Filling.termDisc_eq_zero_iff_of_link_eq` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Both links have dimension $k + 1$, so the intersection has codimension $0$ exactly when they are equal. The second claim is the dimension lemma of [the splitting](/chapter/remaining-terms/#link-vectors-and-the-splitting), rewritten with $c^+ = k + 1 - \dim(\operatorname{link}\gamma \cap \operatorname{link}\gamma')$. For the third, the link determines $X_0^\gamma$, which is $X_0$ if $\mathsf{g}(\gamma) = 0$ and a hyperplane of $X_0$ otherwise (by the dimension formula $\dim X_0^\gamma + (j - \varrho) = k$ and the cell rank). $\square$

### The congruence

**Lemma (A difference of isometries).** Let $b, b'$ be $i$ columns in $X_0 \perp Ez^+$ with the same Gram matrix. Then $|\operatorname{Nm}\det\operatorname{Gram}(b - b')| \leq 4^{2if}|\operatorname{Nm}\det\operatorname{Gram}(b)|$.

Lean: `New.Filling.abs_norm_det_gram_sub_le` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Write $b' = ub$ for an isometry $u$. At each infinite place the form is positive definite, and $1 - u$ has operator norm at most $2$, so the Gram determinant of $(1 - u)b$ is at most $4^i$ times that of $b$. Take the product of the squares of the moduli over the $f$ places. $\square$

**Lemma (Two lattices that pair modulo $M$).** Let $yv$ and $y'v'$ be lattices of rank $i$ in the links of $\gamma$ and $\gamma'$. Suppose that the link form pairs $y$ with $y'$ nondegenerately and pairs the lattices with values in $M\hat{\mathcal{O}}$. Then

$$1 \leq (2/M)^{4if}\operatorname{linkDiscSq}(y, v)\operatorname{linkDiscSq}(y', v').$$

Lean: `New.Filling.one_le_mul_linkDiscSq` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Let $a, b$ be the vectors of $X_0 \perp Ez^+$ under $y$ and $y'$, and $u = \Upsilon_\gamma^{-1}\Upsilon_{\gamma'}$. The link form of a pair from each link is the product of $a$ with $(1 - u)b$. So $M^{-1}$ times the pairing matrix $P$ of the lattices is integral, and it is nondegenerate. A nonzero integral determinant has a norm of absolute value at least $1$ after the indices of $v, v'$ are taken into account (Liouville's inequality). By Cauchy-Schwarz, $|\operatorname{Nm}\det P|^2$ is at most the product of the norms of the Gram determinants of $a$ and of $(1 - u)b$. The previous lemma bounds the second by $4^{2if}$ times that of $b$. Collect the powers: $1 \leq M^{-4if}4^{2if}\operatorname{linkDiscSq}(y, v)\operatorname{linkDiscSq}(y', v')$. $\square$

**Lemma (The congruence).** Let $\gamma, \gamma' \in$ the block $(c, s, c')$, and let $D, D'$ be link splittings of $(\gamma, \gamma')$ and $(\gamma', \gamma)$ with the same complement rank $i$. Then $1 \leq (2/M)^{4if}$ times the product of the squared discriminants of the two complement lattices.

Lean: `New.Filling.LinkSplitting.one_le_mul_linkDiscSq` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* The complements are paired nondegenerately by the link form, since the intersection of the links is the kernel of the pairing between them. The lifted lattices have integral lifts, so by [the integrality of the link form](/decl/New.Filling.HasIntegralLifts.isIntMatrix_linkForm/) they pair with values in $M\hat{\mathcal{O}}$. In the pairing of the lifts, the parts along the intersection of the links vanish. Apply the previous lemma. $\square$

**Lemma (The common parts).** Let $s$ agree, let $x \leq \operatorname{meetNorm}(s)$, and let $\gamma, \gamma'$ be terms over $(c, s, c')$ of cell ranks $j, j'$. Write $t, t'$ for the torsion indices and $d, d'$ for the discriminants of the common parts of $L_\gamma$ and $L_{\gamma'}$. Let $x^\flat = x$ if $j = \varrho + 1$ and $c^+ = 0$, and $x^\flat = 1$ otherwise. Then

$$t\,d\cdot t'\,d'\cdot(x^\flat)^2 \leq (2/M)^{2c^+f}\,\mathsf{g}^*(\gamma)\,\mathsf{g}^*(\gamma').$$

Lean: `New.Filling.torsionIndex_mul_discriminant_commonPart_le` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Choose a link splitting $D$ of $(\gamma, \gamma')$ with gain $x^\flat$ and a link splitting $D'$ of $(\gamma', \gamma)$ with gain $x^\flat$ if $j' = \varrho + 1$ and $c^+ = 0$, else $1$; both exist by [the splitting](/decl/New.Filling.nonempty_linkSplitting/), and $c^+$ is symmetric. If $c^+ = 0$ and $j = \varrho + 1$, then $\mathsf{g}(\gamma) \neq 0$, so $\mathsf{g}(\gamma') \neq 0$ by the corank lemma and $j' = \varrho + 1$. Each splitting gives $(t\,d\,x^\flat)^2D_{\mathrm{compl}} \leq \mathsf{g}^*(\gamma)^2$, and the same for $\gamma'$. Multiply the two and use the congruence lemma: $1 \leq (2/M)^{4c^+f}D_{\mathrm{compl}}D'_{\mathrm{compl}}$. Take square roots. $\square$

### The index

**Lemma (The index).** For $\gamma, \gamma'$ over the same block, the common part of $L_\gamma$ maps, under the products with the frame $\kappa'\mathfrak{f}$ of $\gamma'$, into $M$ times the sum of the images of $\Lambda \cap (A + \kappa'A)$ and $\Lambda \cap A$. The index of $L_{12}$ in the common part of $L_\gamma$ divides the torsion index of $\gamma'$.

Lean: `New.Filling.map_commonPart_le`, `New.Filling.submoduleIndex_pairLattice_dvd_torsionIndex` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Work in coordinates where $\Lambda$ is the lattice of integral vectors and $\gamma'$ acts by $\kappa'$. A vector $v$ of the common part has products with the frame of $\gamma$ equal to $M$ times those of a vector of $\Lambda \cap A$. Since $\kappa' - \kappa$ is divisible by $M$ and $v$ lies in both links, its products with $\kappa'\mathfrak{f}$ are $M$ times those of a vector of $\Lambda \cap (A + \kappa'A)$, up to $M$ times a vector of $\Lambda \cap A$. Such a $v$ lies in $L_{\gamma'}$ exactly when the vector can be taken in $\Lambda \cap A + \kappa'(\Lambda \cap A)$. So the common part modulo $L_{12}$ injects into $\Lambda \cap (A + \kappa'A)$ modulo $\Lambda \cap A + \kappa'(\Lambda \cap A)$, a group of order $t'$. $\square$

**Lemma (The common lattice).** Let $s$ agree and $\gamma, \gamma'$ be terms over $(c, s, c')$ with cell ranks. Then $L_{12}$ is a full lattice in $\operatorname{commonLink}(\gamma, \gamma')$, $1 \leq d_{12}$, and $d_{12} \leq d\cdot t'$.

Lean: `New.Filling.isLatticeOfRank_and_pairDiscriminant_le`, `New.Filling.one_le_pairDiscriminant` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* The common part is a full lattice by the splitting, and $L_{12}$ has finite index in it by the previous lemma, at most $t'$; the discriminant grows by the index. $L_{12}$ lies in the integral lattice $\Lambda_c \cap X_0$, so its Gram determinant is integral and nonzero, and $d_{12} \geq 1$. $\square$

**Theorem (Gain).** Let $s$ agree, $x \leq \operatorname{meetNorm}(s)$, and let $\gamma, \gamma'$ be terms over $(c, s, c')$ of cell ranks $j, j'$. With $x^\flat$ as above,

$$(d_{12}\,x^\flat)^2 \leq (2/M)^{2c^+f}\,\mathsf{g}^*(\gamma)\,\mathsf{g}^*(\gamma').$$

Lean: `New.Filling.pairDiscriminant_sq_le` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* Bound $d_{12}$ once from each side: $d_{12} \leq d\,t'$ and, since $L_{12}$ is symmetric in the two terms, $d_{12} \leq d'\,t$. So $d_{12}^2 \leq t\,d\cdot t'\,d'$, and the lemma on the common parts finishes the proof. $\square$

The torsion indices change places between the two bounds, and this is why the lemma on the common parts keeps them: each torsion index is paid by the gauge of its own term.

### The gauge of a near term

**Lemma (The gauge is at most $H$).** Let $S$ be admissible, and let $\gamma$ be a near term over a block of cell rank $j$. Then $\mathsf{g}^*(\gamma) = \operatorname{levelGauge}(j, c, c', \gamma) \leq b^{n^3f}$.

Lean: `New.Filling.IsNear.levelGauge_le` (New/Spanning/RemainingTerms/Gain.lean).

*Proof.* For a near term, every leading minor of the frame products has $|\cdot|_v^2 \leq b^{270n^2}$ at every place ([Lemma](/decl/New.Filling.IsNear.norm_map_leadingMinor_sq_le/) of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/)). So $\operatorname{termDiscNorm} \leq b^{270n^2f}$ ([Lemma](/decl/New.Filling.IsNear.termDiscNorm_le/)) and $\operatorname{minorNorm} \leq b^{270n^2f}$. The two indices in the denominator of the gauge are at least $1$. So $\mathsf{g}^* \leq M^{2\min(\varrho,j)f}N^f b^{270n^2f} \leq b^{(46n + 60n + 270n^2)f}$, using $M \leq b^{23}$ and $N \leq b^{60n}$. Finally $46n + 60n + 270n^2 \leq 376n^2 \leq n^3$, as $n \geq 376$ by the standing hypothesis $10^5 \leq \varrho$. $\square$

**Example.** Let $\gamma$ and $\gamma'$ be terms below the top cell whose links meet in codimension $c^+ = 1$. The gain is $(2/M)^{2f}$, and $M \geq b^{19}$, so it is at most $b^{-36f}$ (with $2 \leq b$). The gauges are at most $b^{n^3f}$. For $c^+ = 0$ there is no gain from the congruence, and the links are equal; then [the count and the sum](/chapter/remaining-terms/#the-count-and-the-sum) handles the pair as a pair in the same link class.
