---
title: Shared vectors and moves
lean:
  - New/Spanning/RemainingTerms/FrameCount.lean
  - New/Spanning/RemainingTerms/ColumnLattice.lean
decls:
  - New.Filling.HasCellRank.mulVec_eStar_eq_zero_and_sum_indexX₀_le
  - New.Filling.col_eq_zero_of_norm_lt_one
  - New.Filling.IsNearTermAt.eq_of_frameImage_eq
  - New.Filling.norm_adjugate_le
  - New.Filling.norm_coeff_le_norm_sum_frameVector
  - New.Filling.IsNear.norm_adjugate_paddedLeading_le
  - New.Filling.sharedVectors
  - New.Filling.HasCellRank.sharedVectors_mul_of_mem_besselU0
  - New.Filling.HasCellRank.norm_sharedVectors_le
  - New.Filling.skewSolution
  - New.Filling.skewSolution_mul
  - New.Filling.frameModulus
  - New.Filling.frameModulus_ne_zero
  - New.Filling.exists_frameImage_mul_eq_add_fromRows
  - New.Filling.exists_mem_classUnipotent₀_frameImage_mul_eq
  - New.Filling.columnLattice
  - New.Filling.span_columnLattice
  - New.Filling.exists_int_eq_sum_re
  - New.Filling.exists_isAddFundamentalDomain_columnLattice
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Shared vectors and moves

This section gives three tools for the count of the next section. Near terms are rigid: a short lattice vector is zero, and a frame fixes the term. The shared vectors of a near term are small. Two frames with the same products and the same shared vectors, congruent modulo a fixed number, differ by a move. A last part gives a lattice of columns with a fundamental domain of volume at least $1$.

Let $Z = $ `S.frameProducts γ`, and let $Y$ (`paddedLeading j Z`) be the first $j$ rows of $Z$ completed by rows of the identity. So $\det Y = D_j$. The admissible data $S$ satisfy the size bounds of [the data and their sizes](/chapter/data-and-sizes/), and $5 \leq N$.

### Rigidity of lattice columns

**Lemma.** Let $\gamma$ have cell rank $j$, and let $k$ be the last index or $j \leq k$. Let $y = \gamma f\cdot Y^{-1}e_k$. Then $y$ has no coordinate along any $e^*_a$, and at every infinite place $v$ the $X_0$-part of $y$ has $5\sum_i|\Phi_v(y_{x_i})|^2 \leq 1$.

Lean: `New.Filling.HasCellRank.mulVec_eStar_eq_zero_and_sum_indexX₀_le` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* For $j \leq k$ the vector lies in the span of the standard frame by the norm-one pairs, and there these coordinates vanish. Otherwise $k$ is the last index and $Y = Z$, so $Z$ maps the column to the last basis vector. Then $y$ has product $1$ with $z$ and none with the $e_a$. The coordinates along $e^*_a$ are these products, so they vanish. The norm of $y$ is a norm of $\gamma f$-vectors, and the frame relation gives $N$ times the sum as $1$ minus a square. As $5 \leq N$, the claim follows. $\square$

**Lemma.** Let the columns of $l$ be vectors of $X_0$ in the lattice of $c$. If column $i$ has squared length below $1$ at every infinite place, it is zero.

Lean: `New.Filling.col_eq_zero_of_norm_lt_one` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* The hermitian norm of the column is an algebraic integer, since the lattice is integral for the form. Its conjugates are the squared lengths, all below $1$. By rigidity ([cutoffs, rigidity and packing](/chapter/frame-counts/#cutoffs-rigidity-and-packing)) it is $0$. The form is definite on $X_0$, so the column is $0$. $\square$

**Lemma.** Let $u, u'$ be moves for $c$ and let $p = (c', \gamma)$, $p' = (c'', \gamma')$ be near terms for $c$ at the same position (`IsNearTermAt`). If $u\gamma$ and $u'\gamma'$ have the same frame image, then $p = p'$.

Lean: `New.Filling.IsNearTermAt.eq_of_frameImage_eq` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* Equal frames put the two residues in one coset (`termsOver.inv_mul_mem_reducedImage`), and their labels agree, so they are equal. Then the classes agree, and the two terms lie in one double coset $\mathsf U^0_c\gamma\mathsf U^0_{c'}$ (`termsOver.eq_and_mem_classUnipotent₀`). Both terms are the chosen representatives of this double coset, so $\gamma = \gamma'$. $\square$

### Shared vectors

**Lemma.** If the entries of a complex matrix $A$ of order $n + 1$ have norm at most $B$, the entries of its adjugate have norm at most $(n^2B)^n$. If $\gamma$ is near, then at every place the entries of $\operatorname{adj}Y$ have norm at most $b^{(2 + 134n)\varrho}$.

Lean: `New.Filling.norm_adjugate_le`, `New.Filling.norm_adjugate_le_pow`, `New.Filling.IsNear.norm_adjugate_paddedLeading_le` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* An entry of the adjugate is a minor of order $n$ up to sign. Its norm is at most the operator norm to the power $n$, and the operator norm is at most $n^2B$. For near $\gamma$ the entries of $Z$ are at most $b^{134n}$ at each place (`New.Filling.IsNear.norm_frameProducts_le`, from [the anatomy of a term](/chapter/anatomy-of-a-term/)), and the rows of the identity have entries at most $1$. $\square$

**Lemma.** Let $y$ be a point of $G_1$ in the box of radius $b^{37n}$ with `besselLength y` at most $b^{7n}$. Then each coefficient of a combination $\sum_lx_l\,y^{-1}f_l$ is at most $b^{46n^2}$ times its length.

Lean: `New.Filling.norm_coeff_le_norm_sum_frameVector` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* Take $u$ unipotent with $uy$ small (`RealPlace.exists_norm_le_of_besselLength_le`), and let $T$ be its unitriangular matrix on the frame. As $uf = (uy)(y^{-1}f)$, both $T$ and $Tx$ are small, and $x = \operatorname{adj}T\,(Tx)$ since $\det T = 1$. Apply the adjugate bound. $\square$

**Definition.** The *shared vectors* (`S.sharedVectors j γ`) are the coordinates along $e_0, \dots, e_{\varrho-1}$ of the columns $k \geq j$ of $\gamma f\cdot\operatorname{adj}Y$. The columns $k < j$ are set to $0$.

Lean: `New.Filling.sharedVectors` (New/Spanning/RemainingTerms/FrameCount.lean).

For $\gamma$ of cell rank $j$ and $k \geq j$, the column $k$ of $\gamma f\cdot\operatorname{adj}Y$ lies in the span of $f$ (`HasCellRank.exists_frameImage_one_mulVec_eq`). So it lies in the spans of both $f$ and $\gamma f$.

**Lemma.** Let $\gamma$ have cell rank $j$ and $u \in \mathsf U^0$. Then $u\gamma$ and $\gamma$ have the same products and the same shared vectors.

Lean: `New.Filling.frameProducts_mul_of_mem_besselU0`, `New.Filling.HasCellRank.sharedVectors_mul_of_mem_besselU0` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* $u$ is an isometry that fixes $f$, so $h(f, u\gamma f) = h(u^{-1}f, \gamma f) = h(f, \gamma f)$. The columns $k \geq j$ lie in the span of $f$, which $u$ fixes. $\square$

**Lemma.** Let $\gamma$ be near of cell rank $j$. At every place every shared vector entry has norm at most $b^{182n^2}$.

Lean: `New.Filling.HasCellRank.norm_sharedVectors_le` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* The vector is $\gamma fx = fw$ with $x$ a column of $\operatorname{adj}Y$. At the boxed point $\gamma^{-1}y$, its length is at most $b^{(2+134n)\varrho}\cdot b^{1 + 23\varrho + 37n}$ divided by a scale factor (`norm_sum_div_basisScale_smul_frameVector_le`, `norm_basisScale_besselFrame_le`). At the boxed point $y$, the coefficient lemma bounds $w$ by $b^{46n^2}$ times this length. The exponents sum to at most $182n^2$, by $\varrho \geq 10^5$. $\square$

### Moves from congruences

**Lemma (Skew solution).** Let $P^*\mu$ be skew-hermitian, and let $\mu\alpha P = \delta\mu$. Put $\sigma = \bar\delta\mu\alpha - \delta(\mu\alpha)^* - \alpha^*P^*\mu\alpha$. Then $\sigma^* = -\sigma$ and $\sigma P = \delta\bar\delta\mu$. If $P$, $\mu$, $\alpha$, $\delta$ lie in a subring stable under conjugation, so does $\sigma$.

Lean: `New.Filling.skewSolution`, `New.Filling.conjTranspose_skewSolution`, `New.Filling.skewSolution_mul`, `New.Filling.isIntMatrix_skewSolution` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* Skewness: the adjoint of $\bar\delta\mu\alpha - \delta(\mu\alpha)^*$ is its negative, and the adjoint of $\alpha^*P^*\mu\alpha$ is $\alpha^*\mu^*P\alpha = -\alpha^*P^*\mu\alpha$. For the product, $\bar\delta\mu\alpha P = \delta\bar\delta\mu$. Next, $\delta(\mu\alpha)^*P = \delta\alpha^*\mu^*P = -\delta\alpha^*P^*\mu$, and $\alpha^*P^*\mu\alpha P = \delta\alpha^*P^*\mu$. The last two terms cancel. $\square$

**Definition.** The *frame modulus* is $S.\texttt{frameModulus}\,j\,Z = M\det(YY^*) = M\,D_j\bar D_j$. It is nonzero if $D_j \neq 0$.

Lean: `New.Filling.frameModulus`, `New.Filling.frameModulus_ne_zero` (New/Spanning/RemainingTerms/FrameCount.lean).

**Lemma.** Let $\sigma$ be skew-hermitian and integral at every finite place, and let $P$ be the isotropic rows of $Z$. Some move $r \in \mathsf U^0_c$ adds $M\sigma P$ to the rows $e_a$ of $\gamma f$ and changes nothing else.

Lean: `New.Filling.exists_frameImage_mul_eq_add_fromRows` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* Take the Eichler element of [reduced points](/chapter/frame-counts/#reduced-points) with zero part in the lattice of $c$ and skew part $\sigma$ (`exists_mem_classUnipotent_eq_one_add_smul`). It is $r = 1 + M\,x\sigma x^*J$, with $x$ the inclusion of $A$. Then $r\gamma f = \gamma f + M x\sigma(x^*J\gamma f)$, and $x^*J\gamma f$ is $P$ (`inclMatrix_conjTranspose_mul_frameImage`). $\square$

**Theorem (Moves from congruences).** Let $\gamma$, $\gamma'$ have the same integral products $Z$ with $D_j \neq 0$ and the same shared vectors. Suppose their frames agree outside $A$ and differ in the rows $e_a$ by $M\det(YY^*)X$ with $X$ integral at every finite place. Then a move $r \in \mathsf U^0_c$ has $r\gamma f = \gamma'f$.

Lean: `New.Filling.exists_mem_classUnipotent₀_frameImage_mul_eq` (New/Spanning/RemainingTerms/FrameCount.lean).

*Proof.* Let $\delta = \det Y$ and $\alpha$ the columns $a < \varrho$ of $\operatorname{adj}Y$. The modulus is real, and both frames are isometric images with the same products, so $X^*P = -P^*X$ (`conjTranspose_mul_isotropicRows_eq_neg`). Next, $X\alpha P = \delta X$, column by column. For $k \geq j$ the columns of $X\operatorname{adj}Y$ vanish, as the shared vectors agree (`frameImage_sub_mul_adjugate_apply_eq_zero`). At the top cell rank the last column vanishes too (`mulVec_adjugate_top_eq_zero`). For the other columns, $Y\operatorname{adj}Y = \delta$ and the rows of $Y$ below $j$ are those of $P$. The skew solution $\sigma$ is integral and $M\sigma P = M\delta\bar\delta X$. The last lemma gives the move. $\square$

### The lattice of columns

The map `conjColumnsAtInfinity` sends a matrix $q$ over $E$ with columns in $X_0$ to the family $(\overline{\Phi_v(q_{al})})_{v, l, a}$. It is injective, and it has dense range because $E$ is dense in $\prod_v\mathbb C$. The *lattice of columns* (`S.columnLattice ι c`) is the image of the $\iota$-tuples of vectors of $\Lambda \cap X_0$.

**Lemma.** (1) The hermitian products of two tuples of vectors of $\Lambda \cap X_0$ are algebraic integers. (2) The lattice of columns spans the product over $\mathbb R$. (3) For an algebraic integer $x$, $\sum_v\operatorname{Re}\Phi_v(x)$ is an integer.

Lean: `New.Filling.columnLattice`, `New.Filling.isIntegral_conjTranspose_mul`, `New.Filling.span_columnLattice`, `New.Filling.exists_int_eq_sum_re` (New/Spanning/RemainingTerms/ColumnLattice.lean).

*Proof.* (1) The form is unimodular on the lattice of $c$. (2) Every tuple has a nonzero integer multiple in $\Lambda \cap X_0$, by a common denominator. So the span contains the dense image of all tuples, and a subspace is closed. (3) $E$ contains $i$ with $i^2 = -1$ and $\bar i = -i$, by the root of unity of order $5040$. Let $p$ be the trace of $x$ and $q$ that of $ix$. The sum $s = \sum_v\Phi_v(x)$ over the embeddings with $\Phi_v(i) = \sqrt{-1}$ is an algebraic integer with $s = (p - q\sqrt{-1})/2$. So $|s|^2 = (p^2 + q^2)/4$ is an algebraic integer in $\mathbb Q$, hence in $\mathbb Z$. Then $p^2 + q^2 \equiv 0 \pmod 4$, so $p$ is even and the sum $p/2$ is an integer. $\square$

**Theorem.** The lattice of columns has a measurable fundamental domain $D$ with $1 \leq \operatorname{vol}D < \infty$.

Lean: `New.Filling.exists_isAddFundamentalDomain_columnLattice` (New/Spanning/RemainingTerms/ColumnLattice.lean).

*Proof.* In the standard real basis, whose cube has volume $1$, the euclidean product of two lattice points is $\sum_v\operatorname{Re}\Phi_v(\operatorname{tr}q^*q')$. By (1) and (3) it is an integer. A full lattice with integral products has covolume $\sqrt{\det G} \geq 1$, with $G$ its Gram matrix (`exists_isAddFundamentalDomain_of_integral`). $\square$

**Remark (Formalization).** The measure is the Lebesgue measure in $[0, \infty]$. The theorem states $\operatorname{vol}D \neq \infty$ separately, so a division by the volume in the next section is safe.
