---
title: Reduced groups and the structure of a term
lean:
  - New/Spanning/Unfolding/ReducedGroups.lean
  - New/Spanning/Unfolding/TermStructure.lean
decls:
  - New.Filling.mem_reducedImage_besselU
  - New.Filling.mem_reducedImage_iff_forall_place
  - New.Filling.card_reducedImage_besselU
  - New.Filling.exists_mulEquiv_reducedImage_besselH
  - New.Filling.relIndex_comap_principalLevel
  - New.Filling.relIndex_sourceLevel
  - New.Filling.disjoint_reducedImage_besselU_besselH
  - New.Filling.mem_reducedImage_besselS
  - New.Filling.reducedImage_besselS_le_normalizer
  - New.Filling.card_reducedImage_besselS
  - New.Filling.HasCellRank.flagSpan_one_sup_commonIsotropic
  - New.Filling.HasCellRank.flagSpan_coe_sup_commonIsotropic
  - New.Filling.CharsAgree.disjoint_flagSpan_one
  - New.Filling.CharsAgree.disjoint_flagSpan_coe_commonIsotropic
  - New.Filling.CharsAgree.add_finrank_commonIsotropic_eq
  - New.Filling.CharsAgree.hasCellRank_of_add_finrank_eq
  - New.Filling.commonIsotropic_besselU_mul
  - New.Filling.finrank_commonIsotropic_besselU_mul
  - New.Filling.charsAgree_mul_mul_iff_of_mem_besselU
  - New.Filling.isStable_remainingTerms
  - New.NormOnePairOccursFrom.notMem_remainingTerms
  - New.Filling.CharsAgree.normOnePairOccursFrom_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Reduced groups and the structure of a term

This section has two parts. The first counts the reductions $\bar{\mathsf{U}}$, $\bar{\mathsf{H}}$ and $\bar R$ of the integral points of the Bessel groups $\mathsf{U}$, $\mathsf{H}$ and $R_0 = \mathsf{U}\rtimes\mathsf{H}$ at the chosen places. The second shows that the cell rank $j$ of a term $\gamma$ with agreeing characters and vanishing discriminant is $\varrho - \operatorname{rk}I_\gamma$, where $I_\gamma = A \cap \gamma A$ and $A = \langle e_1, \ldots, e_\varrho\rangle$. It then defines the set $\Gamma^*$ of the terms that remain for the second moment.

For a subgroup $B$ of the finite adelic group, $\bar B$ is the image of $B \cap K$ under the reduction at the chosen places ([Definition](/decl/New.Filling.reducedImage/)).

### The reduced groups

**Lemma (Reduced groups are products).** Let $B$ consist of the elements that agree with $1$ at the entries $(a, b)$ of a fixed set. Then $s \in \bar B$ if and only if each component $s_{i,w}$ is the component at $w$ of some element of $\bar B$. In particular $s \in \bar{\mathsf{U}}$ if and only if each $s_{i,w}$ is block upper unitriangular for the levels of the Bessel basis.

Lean: `New.Filling.mem_reducedImage_iff_forall_place`, `New.Filling.mem_reducedImage_besselU` (New/Spanning/Unfolding/ReducedGroups.lean).

*Proof.* It suffices to treat an element with one component $s_{i,w}$ and $1$ elsewhere. This component is the reduction of some $k \in B$, the image of a unitary $g$ over $\hat{\mathcal{O}}$. Replace $g$ by $1$ away from $w$ and its conjugate. The result is still unitary and lies in $B$, since the set of entries is fixed. For $\mathsf{U}$, lift the free entries of each $s_{i,w}$ to $\hat{\mathcal{O}}$, and complete the lift $u$ by its inverse adjoint at the conjugate place. Residues may be prescribed at all places above $M$ at once ([Lemma](/decl/New.Filling.exists_reduceAboveM_eq/)), so some integral $k \in \mathsf{U}$ reduces to $s$. $\square$

**Theorem (The order of the unipotent reduction).** $|\bar{\mathsf{U}}| = M^{f\varrho(2k + 2\varrho + 1)}$, where $k = \dim X_0$ and $f$ is the number of infinite places.

Lean: `New.Filling.card_reducedImage_besselU` (New/Spanning/Unfolding/ReducedGroups.lean).

*Proof.* By the lemma, $\bar{\mathsf{U}}$ is the product over $i \in \{0, 1\}$ and the $f$ chosen places $w$ of index $i$ of the unitriangular groups over $\mathbb{F}_w$. Such a group has $d = \varrho(2k + 2\varrho + 1)$ free entries, and $|\mathbb{F}_w| = p_i$. So the order is $\prod_i p_i^{fd} = M^{fd}$. $\square$

**Theorem (The Levi reduction and its index).** $\bar{\mathsf{H}}$ is isomorphic to $\prod_w\mathrm{GL}_k(\mathbb{F}_w)$, compatibly with reduction. The group of $k$ with $\iota(k)$ in the principal level has index $|\bar{\mathsf{H}}|$ in the group of $k$ with $\iota(k) \in K$. For admissible $S$, the source level has the same index $|\bar{\mathsf{H}}|$.

Lean: `New.Filling.exists_mulEquiv_reducedImage_besselH`, `New.Filling.relIndex_comap_principalLevel`, `New.Filling.relIndex_sourceLevel` (New/Spanning/Unfolding/ReducedGroups.lean).

*Proof.* The reduction of $\iota(k)$ and the entrywise reduction of $k$ are two surjective maps with the same kernel, by [the lemma on the image of the small group](/chapter/poincare-series/#climbing-the-flags). So their targets are isomorphic. The subgroup of the principal level is the kernel of the reduction, whose image is $\bar{\mathsf{H}}$. So its index is $|\bar{\mathsf{H}}|$. For admissible $S$, the source level is this kernel by a field of `IsAdmissible` ([Lemma](/decl/New.Filling.IsAdmissible.sourceLevel_eq/)). $\square$

**Theorem (The Bessel reduction).** $\bar{\mathsf{U}} \cap \bar{\mathsf{H}} = 1$. Every $s \in \bar R$ is $uh$ with $u \in \bar{\mathsf{U}}$ and $h \in \bar{\mathsf{H}}$. $\bar R$ normalizes $\bar{\mathsf{U}}$. So $|\bar R| = |\bar{\mathsf{H}}|\cdot|\bar{\mathsf{U}}|$.

Lean: `New.Filling.disjoint_reducedImage_besselU_besselH`, `New.Filling.mem_reducedImage_besselS`, `New.Filling.reducedImage_besselS_le_normalizer`, `New.Filling.card_reducedImage_besselS` (New/Spanning/Unfolding/ReducedGroups.lean).

*Proof.* If $\bar u = \bar h$, then $u^{-1}h$ is congruent to $1$. If $uh$ lies in a level of the unitary group with $u \in \mathsf{U}$ and $h \in \mathsf{H}$, then so does $h$, because $h$ is the block diagonal part of $uh$ ([Lemma](/decl/New.mem_unitaryLevel_of_besselU_mul/)). So $h$ is congruent to $1$. With the level of integral points, the same lemma shows that an integral element $uh$ of $R_0$ has integral factors. $R_0$ normalizes $\mathsf{U}$ ([Lemma](/decl/New.besselS_le_normalizer_besselU/)), and reduction is a homomorphism. Multiplication is then a bijection from $\bar{\mathsf{U}}\times\bar{\mathsf{H}}$ onto $\bar R$. $\square$

### The cell rank and the common isotropic space

In this part $E$ contains a primitive root of unity of order $5040$, as in Lean. $A_{\leq j}$ is the span of the first $j$ frame vectors, and $\gamma A_{\leq j}$ the span of their images.

**Lemma (Two decompositions).** Let the discriminant of $\gamma$ vanish and let $\gamma$ have cell rank $j$. Then $A = A_{\leq j} + I_\gamma$ and $\gamma A = \gamma A_{\leq j} + I_\gamma$. If the characters of $\gamma$ agree, then $A_{\leq j}$ meets the span of $\gamma f$ only in $0$, and $\gamma A_{\leq j} \cap I_\gamma = 0$.

Lean: `New.Filling.HasCellRank.flagSpan_one_sup_commonIsotropic`, `New.Filling.HasCellRank.flagSpan_coe_sup_commonIsotropic`, `New.Filling.CharsAgree.disjoint_flagSpan_one`, `New.Filling.CharsAgree.disjoint_flagSpan_coe_commonIsotropic` (New/Spanning/Unfolding/TermStructure.lean).

*Proof.* By the cell rank, for each index $a$ with $j \leq a < \varrho$ a vector $fx = \gamma fy$ has top index $a$ and $x_a = \zeta \neq 0$. Its coefficient at $z$ is $0$, so it lies in $A \cap \gamma A = I_\gamma$. So $e_a$ lies in the span of $e_b$ for $b < a$ and $I_\gamma$. Induction from $a = j$ gives $A = A_{\leq j} + I_\gamma$. The pair condition holds for $\gamma^{-1}$ ([Lemma](/decl/New.NormOnePairOccursFrom.inv/)). Applying $\gamma$ to its decomposition gives the second claim. For the disjointness, $j$ is the least index of the pair condition ([the cell rank](/chapter/anatomy-of-a-term/#cells-and-the-discriminant)). A nonzero $fx$ with $x$ supported below $j$ that lies in the span of $\gamma f$ is a common vector. By [the lemma on common vectors](/chapter/poincare-series/#climbing-the-flags), $x_l \neq 0$ for some $l \geq j$, which is false. The second disjointness is the same argument for $\gamma^{-1}$. $\square$

**Theorem (The cell rank is the corank of $I_\gamma$).** Let the characters of $\gamma$ agree and its discriminant vanish.

1. If $\gamma$ has cell rank $j$, then $j + \operatorname{rk}I_\gamma = \varrho$.
2. If $j + \operatorname{rk}I_\gamma = \varrho$, then $\gamma$ has cell rank $j$.

Lean: `New.Filling.CharsAgree.add_finrank_commonIsotropic_eq`, `New.Filling.CharsAgree.hasCellRank_of_add_finrank_eq` (New/Spanning/Unfolding/TermStructure.lean).

*Proof.* For part 1, $\gamma A = \gamma A_{\leq j} + I_\gamma$ with trivial intersection. The ranks are $\varrho$, $j$ and $\operatorname{rk}I_\gamma$. For part 2, $\gamma$ has some cell rank $i$ by [the theorem of the climb](/chapter/poincare-series/#climbing-the-flags), and part 1 gives $i = \varrho - \operatorname{rk}I_\gamma = j$. $\square$

So the cell rank of such a term is unique, and depends only on $I_\gamma$.

### The action of the unipotent group on terms

**Lemma (Double cosets).** Let $u, u' \in \mathsf{U}$ be rational. Then $I_{u\gamma u'} = uI_\gamma$, so $\operatorname{rk}I_{u\gamma u'} = \operatorname{rk}I_\gamma$. The characters of $u\gamma u'$ agree if and only if those of $\gamma$ agree.

Lean: `New.Filling.commonIsotropic_besselU_mul`, `New.Filling.finrank_commonIsotropic_besselU_mul`, `New.Filling.charsAgree_mul_mul_iff_of_mem_besselU` (New/Spanning/Unfolding/TermStructure.lean).

*Proof.* $\mathsf{U}$ maps $A$ onto itself. So $A \cap u\gamma u'A = uA \cap u\gamma A = u(A \cap \gamma A)$. On rational points of $\mathsf{U}$ the character $\chi$ is multiplicative and invariant under conjugation ([Lemma](/decl/New.Filling.unipotentChar_ratToFin_mul/), [Lemma](/decl/New.Filling.unipotentChar_ratToFin_conj/)). If $v(u\gamma u') = (u\gamma u')v'$, then $(u^{-1}vu)\gamma = \gamma(u'v'u'^{-1})$, and the two pairs have the same character values. $\square$

### The remaining terms

The set $\Gamma^*$ of *remaining terms* consists of the rational $\gamma$ with nonzero discriminant, or with agreeing characters, zero discriminant and $A \neq \gamma A$ ([Definition](/decl/New.Filling.remainingTerms/)).

**Theorem (The remaining terms).**

1. $\Gamma^*$ is stable.
2. If a norm one pair occurs for $\gamma$ from the index $0$ on, then $\gamma \notin \Gamma^*$.
3. If the characters of $\gamma$ agree and $\gamma \notin \Gamma^*$, then a norm one pair occurs for $\gamma$ from the index $0$ on.

Lean: `New.Filling.isStable_remainingTerms`, `New.NormOnePairOccursFrom.notMem_remainingTerms`, `New.Filling.CharsAgree.normOnePairOccursFrom_zero` (New/Spanning/Unfolding/TermStructure.lean).

*Proof.* For part 1, the discriminant is invariant under $\gamma \mapsto u^{-1}\gamma u'$ ([Lemma](/decl/New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU/)). The lemma on double cosets gives the other two conditions, since $A = \gamma A$ exactly when $\operatorname{rk}I_\gamma = \varrho$. For part 2, the pair at the top gives a common vector with $y \neq 0$, so the discriminant is $0$ ([Lemma](/decl/New.Filling.termDisc_eq_zero_iff_exists/)). The decompositions with $j = 0$ give $A = I_\gamma = \gamma A$. For part 3, $\gamma \notin \Gamma^*$ and agreement give a zero discriminant and $A = \gamma A$, so $\operatorname{rk}I_\gamma = \varrho$. The theorem on the corank with $j = 0$ gives cell rank $0$. $\square$

So the terms with agreeing characters split in two kinds. The terms of $\Gamma^*$ are estimated in [the remaining terms](/chapter/remaining-terms/). The others with agreeing characters have cell rank $0$ and map $A$ onto $A$.
