---
title: Frames over a lattice
lean:
  - New/Spanning/RemainingTerms/FrameParts.lean
  - New/Spanning/RemainingTerms/FramesOverLattice.lean
decls:
  - New.Filling.framePartX₀
  - New.Filling.exists_framePartX₀_mul_eq_sub_smul
  - New.Filling.IsLift
  - New.Filling.exists_isLift
  - New.Filling.exists_conjTranspose_mul_eq_of_row_mem
  - New.Filling.IsLift.exists_conjTranspose_framePartX₀_mul_eq_neg
  - New.Filling.complementLattice
  - New.Filling.submoduleIndex_smul_complementLattice
  - New.Filling.HasCellRank.sum_norm_sq_sub_mul_inv_lt_one
  - New.Filling.HasCellRank.exists_framePartX₀_sub_eq
  - New.Filling.HasCellRank.exists_framePartX₀_mul_eq_of_sub_mem
  - New.Filling.genIndex_algebraMap_le_pow_of_norm_sq_le
  - New.Filling.IsNear.genIndex_M_mul_leadingMinor_le
  - New.Filling.IsNear.genIndex_frameModulus_le
  - New.Filling.encard_le_of_encard_range_le
  - New.Filling.encard_le_of_colouring
  - New.Filling.IsFrameSet
  - New.Filling.IsFrameSet.encard_range_frameProducts_le
  - New.Filling.isIntegral_sharedVectors
  - New.Filling.IsFrameSet.encard_range_sharedVectors_le
  - New.Filling.IsFrameSet.encard_le_of_sharedVectors_eq
  - New.Filling.IsFrameSet.encard_le_of_framePartX₀_eq
  - New.Filling.IsFrameSet.encard_le_of_conjTranspose_mul_eq
  - New.Filling.IsFrameSet.encard_le_of_le_termLattice
  - New.Filling.IsFrameSet.encard_le
  - New.Filling.encard_setOf_isNearTermAt_and_le_termLattice_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Frames over a lattice

This section proves the frame count. Let $L \subseteq \Lambda \cap X_0$ be a lattice of rank $r$, with $r + l = k$, and let $\Lambda$ be the lattice of $c$. The *term lattice* $L_\gamma$ (`S.termLattice c c' γ`, from [the anatomy of a term](/chapter/anatomy-of-a-term/)) consists of the $v \in \Lambda \cap X_0$ such that some vector of $v + M(\Lambda \cap A)$ is orthogonal to the frame of $\gamma$. The count bounds the near terms with $L \subseteq L_\gamma$, up to moves.

The *part in $X_0$* of the frame of $\gamma$ (`framePartX₀ γ`) is the matrix $F(\gamma)$ of the coordinates at $\kappa$ of the vectors $\gamma f_l$. Let $\Xi_0$ be the isotropic rows of $Z$, and write $[d]$ for the generalised index of an idele $d$.

### Moves on the part in $X_0$

**Lemma.** Let the columns of $\eta$ be $\varrho$ rational vectors of $\Lambda \cap X_0$. Some move $u$ has $F(u\gamma) = F(\gamma) - M\eta\,\Xi_0(\gamma)$ for every $\gamma$.

Lean: `New.Filling.exists_framePartX₀_mul_eq_sub_smul` (New/Spanning/RemainingTerms/FrameParts.lean).

*Proof.* Take the Eichler element of [reduced points](/chapter/frame-counts/#reduced-points) made from $\eta$, with skew part $0$. It fixes the standard frame, as $\eta$ is orthogonal to it. It moves the coordinates in $X_0$ of $\gamma f$ by $-M\eta$ times the coordinates along $e^*_a$, and these are the rows of $\Xi_0$ (`frameProducts_castSucc_apply`). $\square$

**Lemma.** Let $\gamma$, $\gamma'$ have cell rank $j$ and the same integral matrix $Z$, and let $d = M D_j$. (1) The last column and the columns $k \geq j$ of $(F(\gamma') - F(\gamma))Y^{-1}$ have squared length below $1$ at every place. (2) If $F(\gamma') \equiv F(\gamma)$ modulo $d(\Lambda \cap X_0)$, then $F(\gamma') - F(\gamma) = M\eta\,\Xi_0$ for some $\eta$ with columns in $\Lambda \cap X_0$. (3) In this case some move $u$ has $F(u\gamma') = F(\gamma)$.

Lean: `New.Filling.HasCellRank.sum_norm_sq_sub_mul_inv_lt_one`, `New.Filling.HasCellRank.exists_framePartX₀_sub_eq`, `New.Filling.HasCellRank.exists_framePartX₀_mul_eq_of_sub_mem` (New/Spanning/RemainingTerms/FrameParts.lean).

*Proof.* (1) Each such column is the difference of two vectors of squared length at most $1/5$, by the first rigidity lemma of [shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves). Then $|x - x'|^2 \leq 2(1/5 + 1/5) < 1$. (2) Let $v$ be the difference. As $Y\operatorname{adj}Y = D_j$ and $d = MD_j$, the matrix $vY^{-1} = M\eta'$ has columns in $\Lambda \cap X_0$. By (1) and the second rigidity lemma, its last column and its columns $k \geq j$ vanish. The other rows of $Y$ are rows of $\Xi_0$, so $v = M\eta'Y = M\eta\,\Xi_0$. (3) Apply the last lemma with $\eta$. $\square$

### Lifts of the lattice

Let $L$ have the basis $m = ya$, with $y$ rational with independent columns and $a$ adelic.

**Definition.** A *lift* of $L$ for $\gamma$ (`IsLift γ y a w`) is a rational $w$ with $wa$ integral and $F(\gamma)^*y + M\,\Xi_0^*w = 0$. So $yt \mapsto M\sum_i e_i(wt)_i$ maps $L$ to $M(\Lambda \cap A)$, and each vector of $L$ plus its image is orthogonal to the frame of $\gamma$.

Lean: `New.Filling.IsLift`, `New.Filling.exists_isLift` (New/Spanning/RemainingTerms/FrameParts.lean).

If $L \subseteq L_\gamma$, a lift exists. Its columns come from the definition of $L_\gamma$, and rational representatives exist because the conditions are linear over $E$.

**Lemma.** Let the rows of $wa$ be integral combinations of the rows of $m^*m$. Then $w = \eta^*y$ for some $\eta$ with columns in $\Lambda \cap X_0$. If $w$ is a lift and the rows of $w'a - wa$ are such combinations, then some move $u$ has $F(u\gamma)^*y = -M\,\Xi_0^*w'$.

Lean: `New.Filling.exists_conjTranspose_mul_eq_of_row_mem`, `New.Filling.IsLift.exists_conjTranspose_framePartX₀_mul_eq_neg` (New/Spanning/RemainingTerms/FrameParts.lean).

*Proof.* A row $\lambda m^*m$ with $\lambda$ integral is the product of $m\lambda^* \in L \subseteq \Lambda \cap X_0$ with $m$. Solve over $E$ with the left inverse of $y$ to get rational $\eta$. For the second claim, write $w' - w = \eta^*y$ and take the move of the first lemma of this section with $\eta$. It changes $F(\gamma)^*y$ by $-M\Xi_0^*\eta^*y = -M\Xi_0^*(w' - w)$. $\square$

**Definition.** The *complement lattice* $P$ (`S.complementLattice c y`) is $\Lambda \cap X_0 \cap L^\perp$. If $r + l = k$, then $[P : dP] = [d]^l$.

Lean: `New.Filling.complementLattice`, `New.Filling.submoduleIndex_smul_complementLattice` (New/Spanning/RemainingTerms/FrameParts.lean).

*Proof.* $P$ is a saturated lattice of rank $l$. Multiplication by $d$ has index $[d]$ on each of the $l$ coordinates (`submoduleIndex_smul_saturatedLattice`). $\square$

### Sizes of the moduli

**Lemma.** If $|\Phi_v(x)|^2 \leq b^e$ at every place, then $[x] \leq b^{ef}$. For near $\gamma$, both $[MD_j]$ and $[S.\texttt{frameModulus}\,j\,Z]$ are at most $b^{2n^3f}$.

Lean: `New.Filling.genIndex_algebraMap_le_pow_of_norm_sq_le`, `New.Filling.IsNear.genIndex_M_mul_leadingMinor_le`, `New.Filling.IsNear.genIndex_frameModulus_le` (New/Spanning/RemainingTerms/FrameParts.lean).

*Proof.* The generalised index of a rational $x$ is $|\operatorname{Nm}x| = \prod_v|\Phi_v(x)|^2$. For near $\gamma$, $|\Phi_v(D_j)|^2 \leq b^{270n^2}$ at each place (`New.Filling.IsNear.norm_map_leadingMinor_sq_le`, from [the anatomy of a term](/chapter/anatomy-of-a-term/)), and $M \leq b^{23}$ (see [the data and their sizes](/chapter/data-and-sizes/)). So the squared absolute values of $MD_j$ and of $MD_j\bar D_j$ are at most $b^{46 + 540n^2} \leq b^{2n^3}$, as $n \geq 10^5$. $\square$

### Colourings

**Lemma (Colouring).** (1) Colour $A$ with at most $N$ colours so that elements of one colour are related by $R$. If every nonempty set of pairwise related elements has at most $x$ elements, then $|A| \leq Nx$. (2) Let $[K' : K \cap K']$ be finite, and attach to each $a \in A$ a family $f(a) \in K'^\iota$. If every nonempty subset whose families are congruent modulo $K$ has at most $x$ elements, then $|A| \leq [K' : K \cap K']^{|\iota|}x$.

Lean: `New.Filling.encard_le_of_encard_range_le`, `New.Filling.encard_le_of_colouring` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* These are the colouring lemmas of [reduced points](/chapter/frame-counts/#reduced-points) with the weight $1$. In (2) the colours are the classes in $(K'/(K \cap K'))^\iota$. $\square$

**Definition.** A *frame set* for $c$ (`S.IsFrameSet c B`) is a set of pairs $(c', \gamma)$ with $\gamma$ near and over some block $(c, s, c')$, such that $u\gamma f = u'\gamma'f$ for moves $u, u'$ implies $(c', \gamma) = (c'', \gamma')$. A subset of a frame set is a frame set, and the frame products of its terms are integral.

Lean: `New.Filling.IsFrameSet`, `New.Filling.IsFrameSet.mono`, `New.Filling.IsFrameSet.isIntegral_frameProducts` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

### The rounds

Let $B$ be a frame set whose terms all have cell rank $j$. Each round fixes one more datum.

**Lemma (Products and shared vectors).** The terms of $B$ have at most $b^{270n^3f}$ matrices $Z$. The shared vectors are integral, and there are at most $b^{366n^4f}$ of them.

Lean: `New.Filling.IsFrameSet.encard_range_frameProducts_le`, `New.Filling.isIntegral_sharedVectors`, `New.Filling.IsFrameSet.encard_range_sharedVectors_le` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* The entries are algebraic integers with absolute values at most $R = b^{134n}$, or $R = b^{182n^2}$ for the shared vectors ([shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves)). Embed the matrices in $\mathbb C^{\text{entries} \times \text{places}}$, a real space of dimension $2f$ times the number of entries. The images lie in a ball of radius $R$, and two different images are at distance at least $1$, by rigidity. A volume count (`New.Filling.encard_le_of_isIntegral_norm_le`, from [the anatomy of a term](/chapter/anatomy-of-a-term/)) gives at most $(1 + 2R)^{2f}$ values for each entry. With $1 + 2b^m \leq b^{m+1}$ for $b \geq 3$, there are $n^2$ entries of $Z$, giving $b^{135n\cdot 2n^2f} = b^{270n^3f}$. There are $\varrho n$ shared vector entries, giving $b^{183n^2\cdot 2\varrho nf} \leq b^{366n^4f}$. $\square$

**Lemma (The part in $A$).** Suppose all terms of $B$ have the matrix $Z$, and after moves $u_p$ all frames have one part in $X_0$. Let $d' = S.\texttt{frameModulus}\,j\,Z$. If they also have the same shared vectors, then $|B| \leq [d']^{n\varrho}$. Without this condition, $|B| \leq b^{366n^4f}[d']^{n\varrho}$.

Lean: `New.Filling.IsFrameSet.encard_le_of_sharedVectors_eq`, `New.Filling.IsFrameSet.encard_le_of_framePartX₀_eq` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* Colour each term by the rows $e_a$ of its moved frame in the lattice basis, modulo $d'$. These are $\varrho \times n$ integral entries, so there are $[d']^{n\varrho}$ colours (part (2) of the colouring lemma). In one colour the moved frames agree outside $A$ and differ in $A$ by $d'X$ with $X$ integral. By the theorem on moves from congruences of [shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves), the frames differ by a move, so the frame set has one element. The second bound adds a colouring by the shared vectors. $\square$

**Lemma (The part in $X_0$).** Suppose all terms of $B$ have the matrix $Z$, and after moves the parts $F$ have the same products with the $r$ independent columns of $y$. Let $d = MD_j$. Then $|B| \leq [d]^{ln}\cdot b^{366n^4f}[d']^{n\varrho}$.

Lean: `New.Filling.IsFrameSet.encard_le_of_conjTranspose_mul_eq` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* The columns of $F(u_p\gamma_p) - F(u_{p_0}\gamma_{p_0})$ are orthogonal to $y$ and lie in $\Lambda \cap X_0$. So they lie in $P$. Colour the terms by these $n$ columns modulo $dP$: there are $[d]^{ln}$ colours. In one colour the parts are congruent modulo $d(\Lambda \cap X_0)$. By part (3) of the lemma on moves, a further move gives all of them one part in $X_0$. The last lemma ends the proof. $\square$

**Lemma (Lifts of $L$).** Suppose all terms of $B$ have the matrix $Z$, $L \subseteq \Lambda \cap X_0$ and $L \subseteq L_\gamma$ for every term. Then $|B| \leq \operatorname{disc}(L)^{2\varrho}\cdot[d]^{ln}\cdot b^{366n^4f}[d']^{n\varrho}$.

Lean: `New.Filling.IsFrameSet.encard_le_of_le_termLattice` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* Each term has a lift $w_p$. Colour the terms by the $\varrho$ rows of $w_pa$ modulo the lattice $K$ spanned by the rows of $m^*m$. The index of $K$ is $\operatorname{disc}(L)^2$ (`submoduleIndex_gram_eq_discriminant_sq`), so there are at most $\operatorname{disc}(L)^{2\varrho}$ colours. In one colour, the lemma on lifts gives moves with $F(u_p\gamma_p)^*y = -M\Xi_0^*w_{p_1}$ for one fixed $p_1$. So the parts have the same products with $y$, and the last lemma applies. $\square$

**Theorem (Frames over a lattice).** Let $L \subseteq \Lambda \cap X_0$ be a lattice of rank $r$, with $r + l = k$ and $\operatorname{disc}(L) \leq b^{n^3f}$ (`S.discriminantBound`). Let $B$ be a frame set for $c$ whose terms each have a cell rank and satisfy $L \subseteq L_\gamma$. Then

$$|B| \leq b^{2000n^6(l+1)f}.$$

Lean: `New.Filling.IsFrameSet.encard_le` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* Colour by the cell rank: there are $\varrho + 2 \leq b^{2f}$ ranks. Then colour by $Z$: at most $b^{270n^3f}$ colours. For one rank and one $Z$, bound $[d]$ and $[d']$ by $b^{2n^3f}$, and use the last lemma:

$$|B_{j, Z}| \leq b^{2n^3\varrho f}\cdot b^{2n^3\cdot lnf}\cdot b^{366n^4f}\cdot b^{2n^3\cdot n\varrho f}.$$

The total exponent is $(2 + 270n^3 + 366n^4 + 2n^3(\varrho + ln + n\varrho))f$. As $\varrho < n$, this is at most $2000n^6(l + 1)f$. $\square$

**Corollary.** Let $t$ be a label. At most $b^{2000n^6(l+1)f}$ pairs $p = (c', \gamma)$ with `S.IsNearTermAt c t p` have $L \subseteq L_\gamma$.

Lean: `New.Filling.encard_setOf_isNearTermAt_and_le_termLattice_le` (New/Spanning/RemainingTerms/FramesOverLattice.lean).

*Proof.* The near terms at $t$ are near, lie over blocks with first class $c$ and have a cell rank. They form a frame set by the third rigidity lemma of [shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves). Apply the theorem. $\square$

**Remark (Formalization).** All counts are `Set.encard` in $\mathbb N \cup \{\infty\}$, and the bounds are `ENNReal.ofReal` of real numbers. So the theorem also shows that the set is finite. The generalised index of an idele that is not integral could be less than $1$; here $d$ and $d'$ are integral, and their indices are positive (`genIndex_pos`).
