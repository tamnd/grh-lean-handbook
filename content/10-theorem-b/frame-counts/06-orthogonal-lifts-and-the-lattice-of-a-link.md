---
title: Orthogonal lifts and the lattice of a link
lean:
  - New/Spanning/RemainingTerms/OrthogonalLifts.lean
  - New/Spanning/RemainingTerms/LinkLattice.lean
decls:
  - New.Filling.IsOrthogonalLift
  - New.Filling.HasCellRank.exists_isotropic_inter_vector
  - New.Filling.exists_orthogonal_lift
  - New.Filling.IsOrthogonalLift.gram_add_border
  - New.Filling.abs_norm_det_gram_eq_abs_norm_subframeMinor_sq
  - New.Filling.submoduleIndex_colLattice_dvd_preimageLattice
  - New.Filling.torsionIndex_dvd_submoduleIndex
  - New.Filling.isotropicRowsIndex_mul_dvd_submoduleIndex
  - New.Filling.IsOrthogonalLift.linkDiscSq_mul_sq_eq
  - New.Filling.exists_lifts_linkDiscSq_le
  - New.Filling.isotropicRowsIndex_mul_torsionIndex_ne_zero
  - New.Filling.maxGauge_pos
  - New.Filling.HasLevelLifts
  - New.Filling.HasLevelLifts.hasIntegralLifts
  - New.Filling.HasLevelLifts.mul
  - New.Filling.submoduleIndex_ideleM_smul_eq
  - New.Filling.submoduleIndex_inf_comap
  - New.Filling.submoduleIndex_ideleM_smul_isotropicRows_dvd
  - New.Filling.exists_basis_mulVec_mem_ideleM_smul
  - New.Filling.hasLevelLifts_of_col_mem
  - New.Filling.exists_hasLevelLifts_linkDiscSq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Orthogonal lifts and the lattice of a link

Let $\gamma$ have cell rank $j$, and put $I = A \cap \gamma A$. The *link* of $\gamma$ (`New.Filling.link γ`) is the image of $A^\perp \cap (\gamma A)^\perp$ under the map `linkMatrix γ`, which takes $t$ to the middle coordinates of $t$ and of $\gamma^{-1}t$. These notions are from [the anatomy of a term](/chapter/anatomy-of-a-term/). This section gives the link a lattice and bounds its discriminant by the gauge of $\gamma$. Let $k = h_c^{-1}\gamma h_{c'}$ be the adelic form of the term. Three lattice indices enter.

- $i_\gamma$ (`S.isotropicRowsIndex j k`) is the index, in the lattice spanned by the isotropic rows of the frame products of $k$, of the lattice spanned by the rows $a < j$. Write $i'_\gamma$ for the same index at $k^{-1}$.
- $t_\gamma$ (`S.torsionIndex k`) is the index of $\Lambda \cap A + k(\Lambda \cap A)$ in $\Lambda \cap (A + kA)$, with $\Lambda$ the standard lattice.
- The gauge is $\mathsf g^\sharp = |\operatorname{Nm}\delta_*|/(i_\gamma i'_\gamma N^f)$ (`S.minorGauge j c c' γ`). Here $\delta_*$ (`S.subframeMinor j γ`) is the minor of $Z$ on the subframe $f_0, \dots, f_{j-1}, z$.

The squared discriminant of the lattice with adelic basis $ve$ is $\operatorname{disc}(v, e) = |\operatorname{Nm}\det(v^*Qv)|\,[\det e]^2$ (`S.linkDiscSq v e`), with $Q$ the positive form `S.linkMetric` and $[\cdot]$ the generalised index. The size of `S.minorNorm j γ` is $|\operatorname{Nm}D_j|$ divided by $N^{2f}$ at $j = \varrho + 1$.

### Orthogonal lifts

**Definition.** Let $v$ have columns in the link. A matrix $u$ with columns indexed by $\{b \geq j\} \sqcup \tau$ is an *orthogonal lift* of $v$ if its columns are orthogonal to $A$ and $\gamma A$, $\texttt{linkMatrix}\,\gamma \cdot u = (0 \mid v)$, and the products of the columns with the $e^*_b$, $b \geq j$, form $(1 \mid 0)$.

Lean: `New.Filling.IsOrthogonalLift` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

**Lemma.** Let $\gamma$ have cell rank $j$ and $d$ any vector. Some vector $fx = \gamma fy$ of $I$ has $x_{\text{top}} = y_{\text{top}} = 0$ and $x_a = d_a$ for $a \geq j$.

Lean: `New.Filling.HasCellRank.exists_isotropic_inter_vector` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* If $j > \varrho$, take $x = y = 0$. Otherwise apply the norm-one pairs of $\gamma^{-1}$ to the vector $(d, 0)$. This gives $x$, $y$ with $fx = \gamma fy$ and $x_{\text{top}} = 0$. The vector $z$ has norm $-N$ and the $e_a$ are isotropic, so the norm of $fx$ is $-N|x_{\text{top}}|^2$, and that of $\gamma fy$ is $-N|y_{\text{top}}|^2$. So $y_{\text{top}} = 0$. $\square$

**Lemma.** If $\gamma$ has cell rank $j$ and the columns of $v$ span the link, then $v$ has an orthogonal lift.

Lean: `New.Filling.exists_orthogonal_lift` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* The three conditions form one linear system. Solve it column by column. For a column $b$, the column of $(0 \mid v)$ is in the link, so some $t$ is orthogonal to $A$ and $\gamma A$ with the right image. Correct $t$ by a vector of $I$ from the last lemma, which fixes the coordinates at the $e^*_b$, $b \geq j$. A vector of $I$ is orthogonal to $A$ and $\gamma A$ and has image $0$ in the link. $\square$

**Lemma (Isometry).** Let $u$ be an orthogonal lift of $v$ and $u_2$ its columns in $\tau$. Let $p$ be the matrix of products of $z$ and $\gamma z$ with $u_2$. Then $u_2^*Ju_2 + N^{-1}p^*p = v^*Qv$.

Lean: `New.Filling.IsOrthogonalLift.gram_add_border` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* On vectors orthogonal to $A$ and $\gamma A$, the form is $v^*\,\mathrm{diag}(\tfrac12T, \tfrac12T)\,v$ for the image $v$ (`gram_linkMatrix_mul`, with the scalars $\pm\tfrac12$). The products with $z$ and $\gamma z$ are the $z$-rows of $T$ applied to $v$. Add the two parts. This gives the definition of $Q$. $\square$

**Lemma.** Take the Gram matrix of the vectors $e_a$, $\gamma e_a$ ($a < j$), $z$, $\gamma z$, and add $N$ to the diagonal entries of $z$ and $\gamma z$. The norm of its determinant has absolute value $|\operatorname{Nm}\delta_*|^2$.

Lean: `New.Filling.abs_norm_det_gram_eq_abs_norm_subframeMinor_sq` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* The Gram matrix of $(f, \gamma f)$ is $\begin{pmatrix}-N\epsilon & Z\\ Z^* & -N\epsilon\end{pmatrix}$, with $\epsilon$ the unit at the top entry. Adding $N$ kills the diagonal blocks. Reorder the vectors list by list and exchange the two halves. The matrix becomes $\begin{pmatrix}C^* & 0\\0 & C\end{pmatrix}$, with $C$ the submatrix of $Z$ on the subframe, and $\det C = \delta_*$. The sign of the permutation has norm of absolute value $1$. $\square$

### The index chain

**Lemma.** Let $X$ and $P$ be matrices over $\mathbb A_f$ with the columns of $P$ in the span of the columns of $X$. Then the index of $\operatorname{col}(X)$ in the integral vectors of $\operatorname{span}P$ divides the index of the integral vectors in $\{y : Xy \text{ integral}\}$.

Lean: `New.Filling.submoduleIndex_colLattice_dvd_preimageLattice` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* The map $y \mapsto Xy$ carries the second pair of lattices onto a pair that contains the first. $\square$

Let $(\iota, B, q)$ be a basis of $(\Lambda \cap I^\perp)/(\Lambda \cap I)$ (`IsQuotientBasis`), with $\iota$ a basis of $\Lambda \cap I$ in the lattice of the $e_a$, $ke_a$, and $q$ the map to classes.

**Lemma.** (1) $t_\gamma$ divides the index of the classes $qe_a$, $qke_a$ in the integral vectors of their span. (2) If the classes with $a < j$ span the classes of all $e_a$, $ke_a$, then $i_\gamma i'_\gamma t_\gamma$ divides the index of the integral vectors in the lattice of the coefficient vectors $y$ with $(q \cdot \texttt{listPair}\,j\,k)\,y$ integral.

Lean: `New.Filling.torsionIndex_dvd_submoduleIndex`, `New.Filling.isotropicRowsIndex_mul_dvd_submoduleIndex` (New/Spanning/RemainingTerms/OrthogonalLifts.lean).

*Proof.* (1) A vector in the span of the $e_a$, $ke_a$ differs from the representative of its class by a vector of $I$, and this correction lies in the lattice of the $e_a$, $ke_a$. So the class map induces a surjection from the pair defining $t_\gamma$ onto a sublattice pair of the given one. (2) Use the chain $L_1 \subseteq L_2 \subseteq L_3 \subseteq L_4$. Here $L_1$ is spanned by the classes with $a < j$, $L_2$ adds the classes of all $e_a$, $L_3$ adds those of all $ke_a$, and $L_4$ is the integral vectors of the span. The products with the frame of $k$ are defined on classes, and they carry $L_2/L_1$ onto the pair defining $i_\gamma$; the products with the frame of $k^{-1}$ do the same for $L_3/L_2$ and $i'_\gamma$. Part (1) handles $L_4/L_3$. The indices multiply along the chain, and the first lemma of this part ends the proof. $\square$

### Jacobi's identity and the first bound

**Lemma.** Let $u$ be an orthogonal lift of $v$ with integral frame products, and let the classes of the lifts of $ve$ form a primitive matrix. Let $F = q \cdot \texttt{listPair}\,j\,k$ and $\ell$ the index of the integral vectors in the lattice of $y$ with $Fy$ integral. Then

$$\operatorname{disc}(v, e)\cdot\ell^2 = \texttt{minorNorm}(j, \gamma)^2,$$

and the columns of $F$ span the classes of all $e_a$, $ke_a$.

Lean: `New.Filling.IsOrthogonalLift.linkDiscSq_mul_sq_eq` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* The quotient $(\Lambda \cap I^\perp)/(\Lambda \cap I)$ is unimodular. Adjoin two vectors $z'$, $z''$ of norm $N$, and consider the isotropic lists $(e_a, z + z')$ and $(\gamma e_a, \gamma z + z'')$, $a < j$. The lifts of $ve$ are orthogonal to these lists. Jacobi's identity `New.genIndex_det_orthogonal_mul_submoduleIndex_sq`, stated in [the other tools](/chapter/fitting-ideals/), compares the two Gram determinants: the one of the lifts with border $N^{-1}p^*p$, times $\ell^2$, times a power of $[N]$, is the determinant of the last lemma of the first part. The isometry lemma turns the first determinant into $\det(v^*Qv)\,[\det e]^2$. The last lemma of the first part gives $|\operatorname{Nm}\delta_*|^2$, and `HasCellRank.abs_norm_subframeMinor` gives the power of $N$. The rank count $|\mu| = 2|\{a < j\}| + |\tau|$ makes the lists span a complement of the lifts. $\square$

**Lemma.** Let $\gamma$ be a term over $(c, s, c')$ of cell rank $j$, and let the columns of $v$ be a basis of the link. Put $w = i_\gamma i'_\gamma t_\gamma$. Then some invertible $e$ over $\mathbb A_f$ makes the columns of $ve$ have integral lifts, $\operatorname{disc}(v, e)\,w^2 \leq \texttt{minorNorm}(j, \gamma)^2$, and $w \neq 0$.

Lean: `New.Filling.exists_lifts_linkDiscSq_le` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* Choose an orthogonal lift $u$. Pass to the quotient basis of $(\Lambda \cap I^\perp)/(\Lambda \cap I)$. Take for $ve$ the lattice of the vectors whose lifts have integral classes; its class matrix is primitive. The last lemma gives $\operatorname{disc}(v, e)\ell^2 = \texttt{minorNorm}^2$, and the spanning claim lets the index chain give $w \mid \ell$. The minor is nonzero (`HasCellRank.minorNorm_pos`), so $\ell \neq 0$. Then $w \neq 0$ and $w \leq \ell$. $\square$

**Corollary.** For a term of cell rank $j$, the indices $i_\gamma$, $i'_\gamma$ and $t_\gamma$ are positive, and the gauge `S.maxGauge j c c' γ` is positive.

Lean: `New.Filling.isotropicRowsIndex_mul_torsionIndex_ne_zero`, `New.Filling.isotropicRowsIndex_pos`, `New.Filling.isotropicRowsIndex_inv_pos`, `New.Filling.torsionIndex_pos`, `New.Filling.maxGauge_pos` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* Apply the last lemma to a basis of the link. The gauge is at least $\mathsf g^\sharp = N^f\,\texttt{minorNorm}/(i_\gamma i'_\gamma)$ (`HasCellRank.minorGauge_eq`), which is positive. $\square$

**Remark (Formalization).** `submoduleIndex` is a natural number, and it is $0$ when the index is infinite. So a divisibility $w \mid \ell$ alone says nothing when $\ell = 0$. The proofs above show $\ell \neq 0$ before they use it.

### The level lattice

**Definition.** The columns of $m$ have *level lifts* (`HasLevelLifts c γ m`) if $m$ is the image in the link of integral vectors of the lattice of $c$, orthogonal to $A$ and $\gamma A$, whose parts in $A$ are divisible by $M$. These columns span the lattice $L^+_\gamma$.

Lean: `New.Filling.HasLevelLifts`, `New.Filling.HasLevelLifts.hasIntegralLifts`, `New.Filling.HasLevelLifts.mul`, `New.Filling.HasLevelLifts.submatrix` (New/Spanning/RemainingTerms/LinkLattice.lean).

Level lifts are integral lifts, and they stay level lifts under integral right multiplication and under a choice of columns. The proofs unfold the definition.

**Lemma.** Let $L' \leq L$ with finite index. Then $[L : ML] = [L' : ML']$. For submodules $L_1, L_2, L_3$, the index of $L_2 \cap L_3$ in $L_1$ is the index of $L_3$ in $L_1 \cap L_2$ times the index of $L_2$ in $L_1$. If $L_1 \leq L_2$, the index in $L_1$ of $L_2 \cap f^{-1}L$ is the index of $L$ in $f(L_1)$.

Lean: `New.Filling.submoduleIndex_ideleM_smul_eq`, `New.Filling.submoduleIndex_inf`, `New.Filling.submoduleIndex_inf_of_le`, `New.Filling.submoduleIndex_inf_comap` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* For the first claim, both $[L : ML]\,[ML : ML']$ and $[L : L']\,[L' : ML']$ equal $[L : ML']$, and $[ML : ML'] = [L : L']$ because $M$ is a unit of $\mathbb A_f$. Cancel $[L : L'] \neq 0$. The other two claims are the tower law for indices and the isomorphism theorem. $\square$

**Lemma.** Let $P$ be the matrix whose column $a$ holds the products of $e_a$ with the frame of $k$, and $L$ the lattice of its columns. Then $[L : ML]$ divides $M^{2if}$, with $i = \min(\varrho, j)$. For integral $m$ there is an invertible integral $B$ with $Pm\,b \in ML$ for each column $b$ of $B$ and $[\det B] \leq M^{2if}$.

Lean: `New.Filling.submoduleIndex_ideleM_smul_isotropicRows_dvd`, `New.Filling.exists_basis_mulVec_mem_ideleM_smul` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* The sublattice $L_j$ spanned by the columns $a < j$ has finite index in $L$ and at most $i$ generators. By the last lemma $[L : ML] = [L_j : ML_j]$, which divides $[\hat{\mathcal O}^i : M\hat{\mathcal O}^i] = M^{2if}$, since $[\mathcal O_E : M\mathcal O_E] = M^{2f}$. For the second claim, let $K$ be the integral $x$ with $Pmx \in ML$. By the index lemmas, $[\hat{\mathcal O}^\tau : K]$ divides $[L : ML]$. So it is finite and at most $M^{2if}$, and $K$ has a basis $B$ (`exists_colLattice_eq_of_submoduleIndex_ne_zero`) with $[\det B] = [\hat{\mathcal O}^\tau : K]$ (`submoduleIndex_colLattice_intVectors`). $\square$

**Lemma.** Let the columns of $tw$ be integral vectors of the lattice of $c$ orthogonal to $A$ and $\gamma A$. If the part in $A$ of each has the same products with the frame of $\gamma$ as a vector of $M(\Lambda \cap A)$, then the images in the link have level lifts.

Lean: `New.Filling.hasLevelLifts_of_col_mem` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* The difference of the two parts in $A$ has zero products with the isotropic rows. So it lies in $I$ (`IsOrthogonalLift.eq_mul_of_isotropicRows_mul_eq_zero`). Subtract it. A vector of $I$ is orthogonal to $A$ and $\gamma A$ and has image $0$ in the link. $\square$

**Theorem (The lattice of a link).** Let $\gamma$ be a term over $(c, s, c')$ of cell rank $j$, and let the columns of $v$ be a basis of its link. For some invertible $e$ over $\mathbb A_f$ the columns of $ve$ have level lifts, and

$$t_\gamma^2\,\operatorname{disc}(v, e) \leq \Bigl(\frac{M^{2if}\,\mathsf g^\sharp}{N^f}\Bigr)^2,\qquad i = \min(\varrho, j).$$

Lean: `New.Filling.exists_hasLevelLifts_linkDiscSq_le` (New/Spanning/RemainingTerms/LinkLattice.lean).

*Proof.* Take $e$ and the integral lifts $tw$ from the first bound, and let $m$ be their part in $A$. Take $B$ from the last but one lemma, and replace $e$ by $eB$. The columns of $veB$ have level lifts by the last lemma. Then $\operatorname{disc}(v, eB) = \operatorname{disc}(v, e)[\det B]^2 \leq \operatorname{disc}(v, e)M^{4if}$. With $w = i_\gamma i'_\gamma t_\gamma$,

$$t_\gamma^2\operatorname{disc}(v, eB) \leq \frac{M^{4if}\operatorname{disc}(v, e)w^2}{(i_\gamma i'_\gamma)^2} \leq \frac{M^{4if}\,\texttt{minorNorm}^2}{(i_\gamma i'_\gamma)^2} = \Bigl(\frac{M^{2if}\mathsf g^\sharp}{N^f}\Bigr)^2,$$

by `HasCellRank.minorGauge_eq`. $\square$
