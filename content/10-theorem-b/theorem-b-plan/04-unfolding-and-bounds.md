---
title: Unfolding and bounds
lean:
  - New/Spanning/Bessel/FillingData.lean
  - New/Spanning/Unfolding/Moments.lean
  - New/Spanning/Unfolding/MomentBounds.lean
  - New/Spanning/MainTerm/EnergyEstimate.lean
  - New/Spanning/RemainingTerms/Sum.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/Unfolding/SquareExpansion.lean
decls:
  - New.Data.exists_besselSystem
  - New.Filling.HasAmplitudeBlocks
  - New.Data.hasAmplitudeBlocks_scaledPoincare
  - New.Filling.sum_secondMoment_le
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le
  - New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le
  - New.Filling.linkSecondMoment_isOpenElement_le
  - New.Filling.secondMoment_remainingTerms_le
  - New.Data.isNearIsometry_e₀_comp_scaledPoincare
  - New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le
  - New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le
  - New.Data.finrank_targetForms_ne_zero
  - New.Filling.sqrt_secondMoment_compl_besselS_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Unfolding and bounds

This section states the results of layers 3 and 4 and assembles them into the proof of [Theorem](/decl/New.Data.isSpread_goodPoincare/). The statements are for abstract filling data $S$ with base $b$. Write $D_X$ for the dimension of the source, $\nu$ for the covolume of the rational unipotent points in the real unipotent group, and $\bar R_0$ for the image in $\bar G$ of the integral points of the Bessel subgroup. Two numbers measure the second moment:

$$\mathcal{D}_{\mathrm{id}} = \#\bar R_0\cdot D_X, \qquad \mathcal{D}_{\mathrm{main}} = \frac{D_X^2}{\deg\cdot\mathrm{mass}_r}.$$

The first is the contribution of the identity terms. The second is the value that random subspaces would give, as in [the section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof).

### Layer 3: Bessel functions, Poincaré series and unfolding

The Poincaré series are built from a Bessel function at each real place. There the group $G_1$ is the unitary group of a form made of $\varrho$ hyperbolic planes, a positive space $X_0$ and a line. A Bessel function on $G_1$ is bounded, has values in a finite-dimensional space, and transforms on the left by a character of the unipotent radical $U$ and by a representation of $H = U(X_0)$. A Bessel system adds a cut version of bounded support and explicit bounds.

**Theorem (Bessel systems at the real places).** For each infinite place $v$ of the field of $D$ there is a Bessel system for the shape of $Y_0$, with size parameter $b$ and decay rate set by the number $f$ of infinite places. Its full function is a Bessel function of the discrete series of doubled parameter $l_v$, and its type on the values is given by the numbers of columns of each height of the weight on $X_0$.

Lean: `New.Data.exists_besselSystem`, `New.Data.isDiscreteSeriesBessel_filling_besselSystem` (New/Spanning/Bessel/FillingData.lean).

[The chapter on Bessel functions at a real place](/chapter/bessel-real-place/) gives the proof. The function is an average of a discrete series coefficient over the Bessel subgroup, its bounds come from Laplace's method and a Schur bound for derivatives, and its cut uses the local bounds of [the chapter on densities at the real places](/chapter/real-densities/).

With these systems, the Poincaré map $\mathcal{P}$ sends a basis vector $(c, i)$ of the source, a class $c$ and a coordinate $i$ of the Bessel function, to a Poincaré series on $Y_0$. Scale it by $(\mathrm{vol}(K_{\mathrm{pr}})\,\nu)^{-1/2}$, where $K_{\mathrm{pr}}$ is the principal level. Call the result $P$.

**Definition (Amplitude blocks).** Let $\rho$ be a representation of $\bar G$ on $V$ and let $P$ map the source to $V$. Then $P$ *has amplitude blocks* if for all $s \in \bar G$ and all coordinates $x = (c, i)$, $y = (c', i')$, the entry $(x, y)$ of $P_s = P^*\rho(s)P$ is the complex conjugate of

$$\frac{1}{\nu}\,\mathcal{A}(c, s, c')_{i, i'},$$

where $\mathcal{A}(c, s, c')$ is the sum of the amplitudes $\int \beta_c(y)\beta_{c'}(\gamma^{-1}y)\, W(y)\otimes\overline{W(\gamma^{-1}y)}\, dy$ over all terms $\gamma$ over the block $(c, s, c')$.

Lean: `New.Filling.HasAmplitudeBlocks` (New/Spanning/Unfolding/Moments.lean).

**Theorem (Unfolding).** The scaled Poincaré map $P$ of the data $D$ has amplitude blocks for the representation of $\bar G$ on the forms of principal level on $Y_0$.

Lean: `New.Data.hasAmplitudeBlocks_scaledPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* This is the Petersson formula for the filling of [the model case](/chapter/theorem-b-plan/#the-model-case), divided by the factor $\mathrm{vol}(K_{\mathrm{pr}})\nu$ of the scaling. $\square$

So the operators $P_s$ have explicit blocks. The two numbers of layer 1 are now numbers about the sums $\mathcal{A}$: $\|P_s\|^2$ is the sum of $|\mathcal{A}(c, s, c')_{i,i'}|^2/\nu^2$ over all classes and coordinates. The source calls this the second moment of $\mathcal{A}$ at $s$.

Write $\mathcal{M}(s)$ for this second moment: the sum of $|\mathcal{A}(c, s, c')_{i,i'}|^2/\nu^2$ over all classes and coordinates.

**Theorem (Second moment over the whole group).** Let $S$ be admissible filling data over a CM field $E$ with Weil data. The Weil data include a primitive $5040$-th root of unity. Suppose that $\mathcal{M}$ has positive type, that is, $\mathcal{M}(a^{-1}b) = \langle u(a), u(b)\rangle$ for all $a, b \in \bar G$ and some vectors $u(a)$ of an inner product space. Suppose also that $\mathcal{M}(1) \leq 2D_X$. Then

$$\sum_{s \in \bar G}\mathcal{M}(s) \leq (1 + 9b^{-4})\,\mathcal{D}_{\mathrm{main}}.$$

Lean: `New.Filling.sum_secondMoment_le`, `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le` (New/Spanning/Unfolding/MomentBounds.lean, New/Spanning/Unfolding/Moments.lean).

For every $P$ with amplitude blocks and a unitary $\rho$, $\mathcal{M}(s) = \|P_s\|^2$. The hypothesis of positive type then holds with $u(a)$ the Hilbert-Schmidt vector of $\rho(a)PP^*\rho(a)^*$, and $\mathcal{M}(1) \leq 2D_X$ follows from the bound on $P^*P - 1$ below. [The chapter on moments](/chapter/moments/) proves the theorem from the bounds of layer 4.

### Layer 4: the terms and their bounds

Each term $\gamma$ of $\mathcal{A}(c, s, c')$ falls in one of three kinds, sorted in [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/).

1. *Identity terms*: $\gamma$ lies in the Bessel subgroup $R_0$. These give an operator $r_\psi(s)$ on the source, nonzero only for $s \in \bar R_0$. They are the counterpart of $\delta(m, n)$.
2. *Main terms*: $\gamma$ lies in the big cell, with a nonzero discriminant, over an open reduction $s$. These are the counterpart of the Kloosterman terms.
3. *Remaining terms*: all other terms. They have no counterpart in rank one. They are bounded by their number and their size.

**Theorem (The identity terms).** Let $P$ have amplitude blocks, over a field with a primitive $5040$-th root of unity. Then $\|P^*P - 1\|^2 \leq b^{-12}D_X$. For $i = 0, 1$,

$$\sum_s \|P_s - r_\psi(s)\|^2 \leq b^{-12}\,\mathcal{D}_{\mathrm{id}},$$

where the sum runs over the $s \in \bar G$ that agree with an element of $\bar R_0$ in the factor above the prime other than $p_i$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le`, `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le` (New/Spanning/Unfolding/Moments.lean).

**Theorem (The main term).** Let $S$ be admissible. Let $S_g$ be a set of chosen places above $p_0$. For each chosen place $w$ above $p_0$ fix a nonzero vector $D_w$ of the span of the frame modulo $w$ or modulo its conjugate. Sum the squared norms of the class sums of the cut amplitudes over all links, all pairs of classes and all reductions $s$ that are open and fix $D_w$ modulo $w$ for $w \in S_g$, using only the terms $\gamma$ with nonzero discriminant $|\Delta|^2 - N^2|\Delta'|^2$. Here $\Delta$ is the determinant and $\Delta'$ the leading minor of size $\varrho$ of the frame products of $\gamma$. The result is at most

$$(1 + b^{-4})\,(b^{6k})^{-\#S_g}\,\mathcal{D}_{\mathrm{main}}\,\nu^2,$$

where $k$ is the rank of $X_0$.

Lean: `New.Filling.linkSecondMoment_isOpenElement_le` (New/Spanning/MainTerm/EnergyEstimate.lean).

The proof is in [the chapter on the main term](/chapter/main-term/). It writes each block as a sum over double cosets of a Kloosterman sum, a local orbital integral at the finite places, times an integral at the real places. A one-sided sieve then bounds the sum by a product of local densities, computed in [the chapter on densities at the real places](/chapter/real-densities/) and [the chapter on densities at the finite places](/chapter/finite-densities/).

**Theorem (The remaining terms).** Let $S$ be admissible, over a field with a primitive $5040$-th root of unity. Let $\Omega$ be a set of reductions and $w \geq 0$. Suppose that the terms with nonzero discriminant, taken link by link, have a sum of squared norms of amplitude sums of at most $w\nu^2$ over $\Omega$. Then the second moment over $\Omega$ of the remaining terms, for the cut Bessel function, is at most $w + b^{-kf}\,\mathcal{D}_{\mathrm{id}}$.

Lean: `New.Filling.secondMoment_remainingTerms_le` (New/Spanning/RemainingTerms/Sum.lean).

The proof is in [the chapter on the remaining terms](/chapter/remaining-terms/). It bounds each term by its size, counts the terms by lattice points with Siegel's lemma, and gains a power of $b$ from the congruences modulo $M = p_0p_1$. Schur's test controls the sum over pairs.

### Assembly of the input theorem

**Theorem (Good forms).** The composite $e_0P$ is a near isometry with the error $5b^{-4}$: $\|e_0P\,\mathrm{pr}_U\|^2 \geq \dim U - 5b^{-4}D_X$ for every subspace $U$ of the source.

Lean: `New.Data.isNearIsometry_e₀_comp_scaledPoincare`, `New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp` (New/Spanning/SecondMoment/SpanningTheorem.lean, New/Spanning/Unfolding/Moments.lean).

*Proof.* By the identity terms, $\|P^*P - 1\|^2 \leq b^{-12}D_X$, so $P$ is a near isometry with the error $b^{-4}$. By [Theorem](/decl/New.Data.bad_types_rare/), the projection $e_0$ is a tensor product of two central idempotents that each remove a share at most $b^{-8}/2$. From this and the identity terms, the part $(1 - e_0)P$ that the idempotents remove has squared norm at most $4b^{-4}D_X$. A near isometry with the error $b^{-4}$, followed by a projection that removes at most $4b^{-4}D_X$ of the squared norm, is a near isometry with the error $b^{-4} + 4b^{-4} = 5b^{-4}$. $\square$

**Theorem (Second moment).** $\sum_{s \in \bar G}\|P^*sP\|^2 \leq (1 + 9b^{-4})\,\mathcal{D}_{\mathrm{main}}$.

Lean: `New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Lemma (Second moment with the dimension).** $d_T\sum_{s \in \bar G}\|P^*sP\|^2 \leq \#\bar G\,(1 + 9b^{-4})\,D_X^2$.

Lean: `New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Multiply the second moment by $d_T \leq \#\bar G\cdot\deg\cdot\mathrm{mass}_r$ from [Theorem](/decl/New.Data.targetDim_le_card_mul_besselDegree_mul_mass/). The factor $\deg\cdot\mathrm{mass}_r$ cancels the denominator of $\mathcal{D}_{\mathrm{main}}$. $\square$

**Lemma (The target is not zero).** $d_T \neq 0$.

Lean: `New.Data.finrank_targetForms_ne_zero` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* A near isometry with an error less than $1$ on a nonzero space has a range of positive dimension. Apply this to $e_0P$, with the error $5b^{-4} < 1$. $\square$

*Proof of the input theorem.* Apply [Theorem](/decl/New.isSpread_of_second_moment/) to the unitary representation of $\bar G$ on the forms of principal level, the central projection $e_0$, the map $P$ and $\varepsilon = (8b^2)^{-1}$. The near isometry holds since $5b^{-4} \leq (8b^2)^{-1}$. The moment hypothesis holds since $9b^{-4} \leq (8b^2)^{-1}$ and $\dim(\mathrm{range}\,e_0) = d_T$. So the maps $e_0\,s\,P$ spread with the error $\frac{3}{2}(8b^2)^{-1}$. The map $\mathfrak{g}_s = \#\bar G\, e_0\, s\,\mathcal{P}$ differs from $e_0\,s\,P$ by positive scalars and a change of coordinates on the source, and neither changes the dimension of a preimage. $\square$

**Remark (Formalization).** The amplitude sums come in two kinds, selected by an argument of the sum. The full kind uses the Bessel function $W$. The cut kind uses its cut version of bounded support. The Petersson formula and the definition of amplitude blocks use the full kind. The main term and the remaining terms are bounded for the cut kind. The two meet in one theorem.

**Theorem (Expansion of the squares).** Let $E$ contain a primitive $5040$-th root of unity and let $S$ be admissible. Let $\Omega$ be a set of reductions that avoids the cosets of $\bar R_0$ by the roots of unity $\zeta \neq 1$. Let $C \geq 0$, and suppose that the link second moment of the cut amplitudes over $\Omega$, for the terms with nonzero discriminant, is at most $C\nu^2$. Then the second moment over $\Omega$ of the terms off the Bessel subgroup, for the full Bessel function, has square root at most $\sqrt{C} + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}}$.

Lean: `New.Filling.sqrt_secondMoment_compl_besselS_le` (New/Spanning/Unfolding/SquareExpansion.lean).

The chain from the Petersson formula to the main term passes through this theorem. The constants $1 + b^{-4}$ of the main term and $b^{-15}$ of the expansion give the constant $1 + 4b^{-4}$ over the open elements, and the sum over the whole group gives $1 + 9b^{-4}$.
