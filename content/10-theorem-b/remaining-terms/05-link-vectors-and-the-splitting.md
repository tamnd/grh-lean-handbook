---
title: Link vectors and the splitting
lean:
  - New/Spanning/RemainingTerms/LinkVectors.lean
  - New/Spanning/RemainingTerms/Cut.lean
  - New/Spanning/RemainingTerms/Denominators.lean
decls:
  - New.Filling.linkVectors
  - New.Filling.linkVectors_mulVec_eq_zero_iff
  - New.Filling.linkVectors_mulVec_perpToPositive_mem
  - New.Filling.exists_lift_mem_linkedX₀_iff_exists_orthogonal
  - New.Filling.HasCellRank.exists_linkIsometry_symm_eq_smul
  - New.Filling.HasCellRank.termDisc_eq_mul_linkIsometry_symm
  - New.Filling.gram_linkVectors
  - New.Filling.HasCellRank.norm_det_gram_linkVectors
  - New.Filling.linearIndependent_linkVectors
  - New.Filling.prod_norm_det_gram_linkVectors
  - New.Filling.HasCellRank.abs_norm_minor_gram_linkVectors_mul_le
  - New.Filling.minorNorm_sq_le_linkDiscSq_mul
  - New.Filling.HasLevelLifts.discriminant_sq_le
  - New.Filling.HasCellRank.finrank_link_inf_le
  - New.Filling.HasCellRank.finrank_link_inf_eq_add_two
  - New.Filling.LinkSplitting
  - New.Filling.nonempty_linkSplitting
  - New.Filling.HasIntegralLifts.isIntMatrix_linkForm
  - New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Link vectors and the splitting

The second moment pairs two terms $\gamma, \gamma'$ over one block. To count such pairs, the chapter attaches to them a lattice in $X_0$: the part of the lattice $L_\gamma$ of $\gamma$ that is common to the two links. This section splits the link of $\gamma$ along its intersection with the link of $\gamma'$ and proves that the discriminants of the pieces are bounded by the gauge $\mathsf{g}^* = \operatorname{levelGauge}$ of $\gamma$.

Recall from [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/) the following. $A$ is the span of $e_0, \dots, e_{\varrho-1}$. For $y$ orthogonal to $A$ and $\gamma A$, the pair of classes of $y$ and $\gamma^{-1}y$ in $A^\perp/A = X_0 \perp Ez$ lies in the link of $\gamma$. The link is the graph of an isometry $\Upsilon_\gamma$ of the positive space $X_0 \perp Ez^+$, where $z^+$ has the norm $N$. $X_0^\gamma = X_0 \cap \Upsilon_\gamma^{-1}X_0$ is `linkedX₀`. $L^+_\gamma$ is the image in the link of the vectors of $\Lambda_c$ orthogonal to $A$ and $\gamma A$ whose part in $A$ is divisible by $M$.

### The two link vectors

**Definition.** The link vectors of $\gamma$ are the two columns $z^+$ and $\Upsilon_\gamma^{-1}z^+$ in $X_0 \perp Ez^+$.

Lean: `New.Filling.linkVectors` (New/Spanning/RemainingTerms/LinkVectors.lean).

**Lemma (The orthogonal of the link vectors).** A vector $a$ of $X_0 \perp Ez^+$ is orthogonal to both link vectors if and only if it is the image of a vector of $X_0^\gamma$.

Lean: `New.Filling.linkVectors_mulVec_eq_zero_iff` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* The products of $a$ with $z^+$ and $\Upsilon_\gamma^{-1}z^+$ are $N$ times the $z^+$ coordinates of $a$ and of $\Upsilon_\gamma a$. Both vanish if and only if $a \in X_0$ and $\Upsilon_\gamma a \in X_0$. $\square$

**Lemma (Integral products).** Let $\gamma$ be a term over $(c, s, c')$. For every $y \in \Lambda_c$ orthogonal to $A$ and $\gamma A$, the products of $z^+$ and $\Upsilon_\gamma^{-1}z^+$ with the image of $y$ in $X_0 \perp Ez^+$ are integral.

Lean: `New.Filling.linkVectors_mulVec_perpToPositive_mem` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* These products are minus the products of $y$ with $\gamma z$ and $z$. In the lattice basis of $c$, the matrix of $\gamma$ is an integral matrix $\kappa$ of the lattice stabilizer, and the products with $\kappa z$ and $z$ have integral coefficients, as the lattice form is unimodular. $\square$

**Lemma (The lattice of a term).** A vector $v \in X_0$ lies in $L^+_\gamma$ and in $X_0^\gamma$ if and only if $v \in \Lambda_c$ and some vector of $v + M(\Lambda_c \cap A)$ is orthogonal to the frame $\gamma\mathfrak{f}$.

Lean: `New.Filling.exists_lift_mem_linkedX₀_iff_exists_orthogonal` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* A vector $a + v$, with $a \in A$ and $v \in X_0$, lies in $\Lambda_c$ if and only if $a$ is integral and $v \in \Lambda_c \cap X_0$. The condition that its image lies in $X_0^\gamma$ is, by the previous lemmas, the vanishing of its products with $z$ and $\gamma z$; with the orthogonality to $\gamma A$ this is the orthogonality to $\gamma\mathfrak{f}$. $\square$

This is the definition of the lattice $L_\gamma$ (`termLattice`) of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/): the lattice of a term is the part of $L^+_\gamma$ that lies in $X_0^\gamma$.

**Lemma (The Gram matrix).** The Gram matrix of the link vectors is $\begin{pmatrix} N & Nu \\ N\bar u & N\end{pmatrix}$, where $u$ is the $z^+$ coordinate of $\Upsilon_\gamma^{-1}z^+$. If $\gamma$ has the cell rank $j$, with leading minor $\delta_j \neq 0$, then

$$\mathsf{g}(\gamma) = |\delta_j|^2(1 - |u|^2),$$

so $|\delta_j|^2$ times the Gram determinant is $N^2\mathsf{g}(\gamma)$. At each infinite place $v$ the Gram determinant has the modulus $N^2|\mathsf{g}|_v/|\delta_j|_v^2$.

Lean: `New.Filling.gram_linkVectors`, `New.Filling.HasCellRank.termDisc_eq_mul_linkIsometry_symm`, `New.Filling.HasCellRank.norm_det_gram_linkVectors` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* The diagonal entries are the norms of $z^+$ and of its image under an isometry. The entry off the diagonal is the product of $z^+$ with $\Upsilon_\gamma^{-1}z^+$, which is $N$ times its $z^+$ coordinate. For the formula for $\mathsf{g}$: by the normal form of a term of cell rank $j$, the isometry $\Upsilon_\gamma$ maps a vector $y_0 + \delta' z^+$ with $y_0 \in X_0$ to $-(\delta_j/N)z^+$, where $\delta'$ is the next leading minor of the frame products up to a factor. Solve for $\Upsilon_\gamma^{-1}z^+$ and compare its $z^+$ coordinate $u$ with $\mathsf{g} = |\delta_n|^2 - N^2|\delta_{n-1}|^2$, the definition of $\mathsf{g}$. $\square$

**Lemma (Cell rank below the top).** If $\gamma$ has a cell rank and $\mathsf{g}(\gamma) = 0$, then $\Upsilon_\gamma^{-1}z^+$ is a multiple of $z^+$.

Lean: `New.Filling.HasCellRank.exists_linkIsometry_symm_eq_smul` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* If $\mathsf{g} = 0$, the cell rank $j$ is at most $\varrho$, and then $X_0^\gamma = X_0$: the isometry $\Upsilon_\gamma$ maps $X_0$ into $X_0$. So $\Upsilon_\gamma^{-1}z^+$ is orthogonal to $X_0$, and it is a multiple of $z^+$. $\square$

**Theorem (The link vectors in the top cell).** If $\mathsf{g}(\gamma) \neq 0$, the link vectors are linearly independent, and

$$\prod_v|\det\operatorname{Gram}(z^+, \Upsilon_\gamma^{-1}z^+)|_v = N^f\operatorname{Nm}\mathsf{g}/\mathsf{g}^\sharp,$$

where $\mathsf{g}^\sharp = \operatorname{minorGauge}(\varrho + 1, c, c', \gamma)$, for any classes $c, c'$.

Lean: `New.Filling.linearIndependent_linkVectors`, `New.Filling.prod_norm_det_gram_linkVectors` (New/Spanning/RemainingTerms/LinkVectors.lean).

*Proof.* The Gram determinant is $N^2\mathsf{g}/|\delta_n|^2 \neq 0$, so the vectors are independent. Multiply the moduli over the places: $\prod_v N^2 = N^{2f}$, $\prod_v|\mathsf{g}|_v = \operatorname{Nm}\mathsf{g}$, and $\prod_v|\delta_n|^2_v = |\operatorname{Nm}\delta_n|$. At the top cell rank both indices $\iota$ in the gauge are $1$, so $\mathsf{g}^\sharp = |\operatorname{Nm}\delta_n|/N^f$. $\square$

### The cost of the cut

Two $z$-forms act on the link: the products of each half of a pair with $z$. Their kernel in the link is the part in $X_0$. A piece of the link on which the $z$-forms are injective has rank at most $2$, and at most $1$ unless $j = \varrho + 1$. Its discriminant is bounded below by the following lemma.

**Lemma (Minors of the Gram matrix).** Let $\gamma$ have the cell rank $j$, let $r \leq 1 + (j - \varrho)$, and let $\rho$ choose $r$ of the two indices. Then

$$|\operatorname{Nm}\det(\operatorname{Gram}_{\rho\rho})|\cdot\mu^2 \leq G^2,\qquad G = \max(\operatorname{termDiscNorm}(\gamma), N^f\mu),$$

where $\mu = \operatorname{minorNorm}(j, \gamma) > 0$.

Lean: `New.Filling.HasCellRank.abs_norm_minor_gram_linkVectors_mul_le` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* For $x \in E$, $|\operatorname{Nm}x| = \prod_v|x|_v^2$, as all infinite places are complex. There are three cases. For $r = 0$ the minor is $1$, and $\mu \leq N^f\mu \leq G$. For $r = 1$ the minor is $N$, with $|\operatorname{Nm}N| = (N^f)^2$, and $N^f\mu \leq G$. For $r = 2$ we have $j = \varrho + 1$, and the minor is the whole Gram determinant. By the Gram lemma its norm is $\prod_v(N^2|\mathsf{g}|_v/|\delta_n|_v^2)^2 = N^{4f}\operatorname{termDiscNorm}^2/|\operatorname{Nm}\delta_n|^2$, while $\mu = |\operatorname{Nm}\delta_n|/N^{2f}$ at the top rank. So the product is $\operatorname{termDiscNorm}^2 \leq G^2$. $\square$

**Lemma (The cost of the cut).** Let $s$ agree, let $\gamma$ be a term over $(c, s, c')$ of cell rank $j$, and let $x \leq \operatorname{meetNorm}(s)$ with $x = 1$ unless $r = 2$. Let the $r$ columns of $y$ lie in the link, with $r \leq 1 + (j - \varrho)$, let the $z$-forms be injective on their span, and let them take on the basis $yv$ the same values as on a matrix with integral lifts. Then

$$x^2\mu^2 \leq \operatorname{linkDiscSq}(y, v)\cdot G^2.$$

Lean: `New.Filling.minorNorm_sq_le_linkDiscSq_mul` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* The $z$-forms are the products with the pairs over $-z^+$ and $-\Upsilon_\gamma^{-1}z^+$. Choose $r$ of them, by $\rho$, that pair nondegenerately with $y$. Their values on the lattice are integral, and at the places where $s$ meets they vanish modulo the place, so the determinant of the pairing has an index of at least $x$. By Cauchy-Schwarz for the determinant of a pairing, the squared discriminant of the lattice is at least $x^2$ divided by the norm of the Gram minor of the chosen forms. The previous lemma bounds that norm by $G^2/\mu^2$. $\square$

**Lemma (The part in $X_0$).** Let the columns of $m$, with a left inverse, span a subspace of the link on which both $z$-forms vanish, and let the lattice with basis $ma$ lie in $L^+_\gamma$. Let $V$ be the span of the parts of the columns in $X_0$ and $L = \Lambda_V \cap L_\gamma$. Then $r = \dim V$, $L$ is a lattice of rank $r$, and $(\operatorname{disc}_rL)^2 \leq \operatorname{linkDiscSq}(m, a)$.

Lean: `New.Filling.HasLevelLifts.discriminant_sq_le` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* On the kernel of the $z$-forms the link metric is the form of $X_0$, so the parts in $X_0$ have the same Gram matrix as $m$. The integral lifts of $ma$ show that the columns of the parts lie in $L$. So $L$ has finite index in $\Lambda_V$, and its discriminant is at most that of the lattice spanned by the parts. $\square$

### The splitting

**Lemma (Dimensions).** Let $\gamma$ have the cell rank $j$. Then $\dim(\operatorname{link}\gamma \cap \operatorname{link}\gamma') \leq \dim\operatorname{commonLink}(\gamma, \gamma') + 1 + (j - \varrho)$. If $j = \varrho + 1$ and the two links are equal, equality holds with $1 + (j - \varrho) = 2$.

Lean: `New.Filling.HasCellRank.finrank_link_inf_le`, `New.Filling.HasCellRank.finrank_link_inf_eq_add_two` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* $\dim X_0^\gamma + (j - \varrho) = k$, and $\dim X_0^\gamma + \dim(\operatorname{link}\gamma \cap \operatorname{link}\gamma') \leq \dim\operatorname{commonLink} + k + 1$. In the second case $\operatorname{commonLink} \subset X_0^\gamma$ and the corank is $0$. $\square$

**Definition.** A link splitting of $(\gamma, \gamma')$ with complement rank $i$ and gain $x$ consists of a family spanning $\operatorname{link}\gamma \cap \operatorname{link}\gamma'$, a basis of a complement of rank $i$ in $\operatorname{link}\gamma$, and a lattice in the complement whose basis vectors, moved along the intersection, have integral lifts, such that the common part $L_{12}$ of $L_\gamma$ (`commonPart`) is a full lattice in $\operatorname{commonLink}(\gamma, \gamma')$ and

$$(t\cdot\operatorname{disc}(L_{12})\cdot x)^2\cdot D \leq (\mathsf{g}^*)^2,$$

with $t$ the torsion index of $\gamma$ and $D$ the squared discriminant of the lattice in the complement.

Lean: `New.Filling.LinkSplitting` (New/Spanning/RemainingTerms/Cut.lean).

**Theorem (The splitting).** Let $s$ agree, let $\gamma$ be a term over $(c, s, c')$ of cell rank $j$, and let $x \leq \operatorname{meetNorm}(s)$ be $1$ unless $j = \varrho + 1$ and the links of $\gamma$ and $\gamma'$ are equal. Then there is a link splitting of $(\gamma, \gamma')$ with complement rank $\operatorname{linkCorank}(\gamma, \gamma')$ and gain $x$.

Lean: `New.Filling.nonempty_linkSplitting` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* Take a basis of the link in three parts: $m$ spans the kernel of the $z$-forms in the intersection of the links; $m$ and $u$ span the intersection, with $u$ orthogonal to $m$; $y$ completes them. By [the lattice of a link](/decl/New.Filling.exists_hasLevelLifts_linkDiscSq_le/) of [the chapter on frame counts](/chapter/frame-counts/), there is an adelic basis change $f$ with columns in $L^+_\gamma$ such that $t^2\operatorname{linkDiscSq} \leq (M^{2\min(\varrho,j)f}\mathsf{g}^\sharp/N^f)^2$. The squared discriminant of the link lattice is the product of those of three graded pieces, with bases $ma$, $uv_0$ and $yv$. The part lemma bounds $\operatorname{disc}(L_{12})^2$ by the first, the dimension lemma gives $\operatorname{rank}u \leq 1 + (j - \varrho)$ (and $= 2$ if $x \neq 1$), and the cost of the cut gives $x^2\mu^2 \leq \operatorname{linkDiscSq}(u, v_0)G^2$. Combine: $(t\operatorname{disc}(L_{12})x)^2D\mu^2 \leq (M^{2\min(\varrho,j)f}\mathsf{g}^\sharp G/N^f)^2$, and the right side divided by $\mu^2$ is $(\mathsf{g}^*)^2$ by the definition of the gauge. The rank of $y$ is $k + 1$ minus the dimension of the intersection, which is the link corank. $\square$

**Lemma (The link form is integral modulo the level).** Let $\gamma, \gamma'$ be terms over $(c, s, c')$ with the same $s$, and let $w, w'$ have integral lifts in the links of $\gamma$ and $\gamma'$. Then $w^*(M^{-1}\operatorname{linkForm})w'$ is integral.

Lean: `New.Filling.HasIntegralLifts.isIntMatrix_linkForm` (New/Spanning/RemainingTerms/Cut.lean).

*Proof.* The matrix $\kappa$ of $\gamma\gamma'^{-1}$ in the lattice basis is congruent to $1$ modulo $M$, since $\gamma$ and $\gamma'$ have the same reduction. The pairing is $-n^*J(\kappa - 1)n'/M$ for the integral lifts $n, n'$ and the Gram matrix $J$ of the lattice, which is integral. $\square$

This lemma is the source of the gain of [the gain](/chapter/remaining-terms/#the-gain).

**Remark (Formalization).** The file Denominators gives bases of $A^+/I_\gamma$ and $\gamma A^+/I_\gamma$, where $A^+$ is the span of the frame and $I_\gamma = A \cap \gamma A$ ([Theorem](/decl/New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq/)). The file Sum imports it, but no file of the proof uses any of its results, so the argument does not depend on it.

Lean: `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq` (New/Spanning/RemainingTerms/Denominators.lean).
