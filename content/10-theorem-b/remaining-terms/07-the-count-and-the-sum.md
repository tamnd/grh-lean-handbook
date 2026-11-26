---
title: The count and the sum
lean:
  - New/Spanning/RemainingTerms/Count.lean
  - New/Spanning/RemainingTerms/Sum.lean
decls:
  - New.Filling.tsum_le_tsum_mul_of_encard_le
  - New.Filling.exists_isLabelledPair_of_isNearPairOverAgreeingBlock
  - New.Filling.sum_pairDiscriminant_inv_le_tsum
  - New.Filling.sum_pairDiscriminant_inv_le
  - New.Filling.IsNearPairOverAgreeingBlock.corank_le_and_pairDiscriminant_le
  - New.Filling.IsNearPairOverAgreeingBlock.ofReal_termSize_mul_le
  - New.Filling.sum_termSize_mul_le
  - New.Filling.pow_mul_mainSecondMoment_div_le
  - New.Filling.sum_termSize_mul_not_inSameLinkClass_le
  - New.Filling.sum_termSize_mul_inSameLinkClass_le
  - New.Filling.enorm_amplitudeSum_mul_le
  - New.Filling.enorm_amplitudeSum_sq_le
  - New.Filling.secondMoment_remainingTerms_le
  - New.Filling.linkSecondMoment_le_of_le_meetNorm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The count and the sum

This section joins the three parts of the chapter. [The size of a block](/chapter/remaining-terms/#the-size-of-a-block) bounds a block by a sum of sizes, one for each near representative. [The gain](/chapter/remaining-terms/#the-gain) bounds the discriminant $d_{12}$ of the common lattice of two terms by their gauges. [Lattices of given corank](/chapter/remaining-terms/#lattices-of-given-corank) sums $d^{-k}$ over lattices. Here we count the pairs that give one lattice, add the products of the sizes, and prove the two theorems of the chapter.

Throughout, $S$ is admissible over a CM field $E$ with a primitive root of unity of order $5040$. The notation is that of the earlier sections: $\tau = b^{kf/4}$, $H = b^{n^3f}$, the gauge $\mathsf{g}^*(\gamma) = \operatorname{levelGauge}(\operatorname{cellRank}\gamma, c, c', \gamma)$, the corank $c^+$ of the links, and $n_p = \#\bar R_0\cdot\#\mathrm{Classes}/N^{kf}$ (`pairCountScale`), where $\bar R_0$ is the set of labels. The size of a term is

$$\operatorname{termSize}(c, c', \gamma) = \tau^2\Big(\frac{\mathcal{D}_j}{n_p\,\mathsf{g}^*(\gamma)^k}\Big)^{1/2},\qquad j = \operatorname{cellRank}\gamma,$$

with $\mathcal{D}_j = \mathcal{D}_{\mathrm{main}}$ if $j = \varrho + 1$ and $\mathcal{D}_j = \tau^{-16}\mathcal{D}_{\mathrm{id}}$ otherwise. A near pair over $c, c'$ is a pair $(\gamma, \gamma')$ of near representatives with cell ranks that lie over one block $(c, s, c')$ with $s$ agreeing (`IsNearPairOverAgreeingBlock`). Its common lattice $L_{12}$ has the corank $l = k - \dim\operatorname{commonLink}(\gamma, \gamma')$.

### Counting pairs

The count rests on a general principle: if each element of a set $I$ is sent to some $y$ with the same weight, and each $y$ receives at most $x$ elements, then the weights on $I$ add up to at most $x$ times the weights of the $y$.

**Lemma (Fibres of a relation).** Let $v: I \to [0, \infty]$, $w: Y \to [0, \infty]$, $x \in [0, \infty]$ and $R \subset I \times Y$. Suppose that every $i$ has some $y$ with $R(i, y)$ and $v(i) = w(y)$, and that $\#\{i : R(i, y)\} \leq x$ for every $y$. Then $\sum_iv(i) \leq x\sum_yw(y)$.

Lean: `New.Filling.tsum_le_tsum_mul_of_encard_le` (New/Spanning/RemainingTerms/Count.lean).

*Proof.* Choose $y(i)$ for each $i$. Sort the sum over $i$ by the value of $y(i)$. The fibre over $y$ lies in $\{i : R(i, y)\}$, it has at most $x$ elements, and each of its elements has the weight $w(y)$. $\square$

**Lemma (A near pair has a label).** Let $(\gamma, \gamma')$ be a near pair over $c, c'$. There is a label $t \in \bar R_0$ such that both $(c', \gamma)$ and $(c', \gamma')$ are near terms of label $t$, the common lattice $L_{12}$ lies in $L_\gamma$, in $L_{\gamma'}$ and in $\Lambda_c \cap X_0$, and $L_{12}$ is a lattice of rank $\dim\operatorname{commonLink}(\gamma, \gamma')$.

Lean: `New.Filling.exists_isLabelledPair_of_isNearPairOverAgreeingBlock` (New/Spanning/RemainingTerms/Count.lean).

*Proof.* Take for $t$ the image of $s$ in the quotient that defines the labels. Both terms lie over $(c, s, c')$, so both have this label. The common lattice is by definition $\Lambda_{\operatorname{commonLink}} \cap L_\gamma \cap L_{\gamma'}$, and $L_\gamma \subset \Lambda_c \cap X_0$. The rank is [Lemma (The common lattice)](/chapter/remaining-terms/#the-gain). $\square$

The near pairs of corank $l$ and discriminant at most $H$ over $c, c'$ form the set $P_l(c, c')$ ([Definition](/decl/New.Filling.boundedDiscNearPairs/)).

**Lemma (Pairs over one class).** Let $l \leq n^3$ and $r + l = k$. For every class $c$,

$$\sum_{c'}\ \sum_{(\gamma, \gamma') \in P_l(c, c')} d_{12}^{-k} \leq \#\bar R_0\cdot\Big(\sum_{L} (\operatorname{disc}_rL)^{-k}\Big)\cdot\tau,$$

where $L$ runs over the lattices $L \subset \Lambda_c \cap X_0$ of rank $r$ with $\operatorname{disc}_rL \leq H$.

Lean: `New.Filling.sum_pairDiscriminant_inv_le_tsum` (New/Spanning/RemainingTerms/Count.lean).

*Proof.* Apply the lemma on fibres. Let $I$ be the set of triples $(c', \gamma, \gamma')$ with $(\gamma, \gamma') \in P_l(c, c')$, and let $Y$ be the set of pairs $(t, L)$ of a label and a lattice as above, with the weight $(\operatorname{disc}_rL)^{-k}$. Relate $(c', \gamma, \gamma')$ to $(t, L)$ if both $(c', \gamma)$ and $(c', \gamma')$ lie in the set $B(t, L)$ of near terms of label $t$ with $L \subset L_\gamma$. By the previous lemma each triple is related to $(t, L_{12})$, and the rank of $L_{12}$ is $k - l = r$, so the weights agree. The map $(c', \gamma, \gamma') \mapsto ((c', \gamma), (c', \gamma'))$ is injective, so the fibre over $(t, L)$ has at most $\#B(t, L)^2$ elements. [The chapter on frame counts](/chapter/frame-counts/) proves $\#B(t, L) \leq b^{2000n^6(l+1)f}$ ([Theorem](/decl/New.Filling.encard_setOf_isNearTermAt_and_le_termLattice_le/)). For $l \leq n^3$ we have $2\cdot2000n^6(l+1) \leq 4000n^6(n^3 + 1) \leq 10^5n^9$ ([Lemma](/decl/New.Filling.two_mul_count_exponent_le/)), so the square is at most $\tau$ by [Lemma](/decl/New.Filling.pow_le_tailScale/). The sum over $Y$ is $\#\bar R_0$ times the sum over $L$. $\square$

**Theorem (Count).** Let $l \leq n^3$. Then

$$\sum_{c, c'}\ \sum_{(\gamma, \gamma') \in P_l(c, c')} d_{12}^{-k} \leq \tau^{l+2}n_p.$$

Lean: `New.Filling.sum_pairDiscriminant_inv_le` (New/Spanning/RemainingTerms/Count.lean).

*Proof.* If $l > k$, no subspace of $X_0$ has corank $l$, and the sum is empty. Otherwise put $r = k - l$. Add the previous lemma over $c$ and apply the [theorem on lattices of given corank](/chapter/remaining-terms/#lattices-of-given-corank): the sum over $c$ and $L$ is at most $\#\mathrm{Classes}\cdot\tau^{l+1}/N^{kf}$. The product is $\#\bar R_0\cdot\#\mathrm{Classes}\cdot\tau^{l+2}/N^{kf} = \tau^{l+2}n_p$. $\square$

### Sizes of pairs

Every near pair is counted by the theorem, because its corank and its discriminant are small.

**Lemma (Near pairs are bounded).** Let $(\gamma, \gamma')$ be a near pair over $c, c'$. Then $1 \leq d_{12}$, the corank satisfies $k - \dim\operatorname{commonLink}(\gamma, \gamma') \leq n^3$, and $d_{12} \leq H$. So $(\gamma, \gamma') \in P_l(c, c')$ for its corank $l$.

Lean: `New.Filling.IsNearPairOverAgreeingBlock.corank_le_and_pairDiscriminant_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* The bound $1 \leq d_{12}$ is [Lemma (The common lattice)](/chapter/remaining-terms/#the-gain). Put $i = c^+$. The [Gain theorem](/chapter/remaining-terms/#the-gain) with $x = 1$ gives $d_{12}^2 \leq (2/M)^{2if}\mathsf{g}^*(\gamma)\mathsf{g}^*(\gamma')$, and each gauge is at most $H$ by [the lemma on the gauge of a near term](/chapter/remaining-terms/#the-gain). Since $2b^{18} \leq b^{19} \leq M$, we get $2/M \leq b^{-18}$, so $b^{36if}d_{12}^2 \leq H^2$, that is $b^{18if}d_{12} \leq H$. With $d_{12} \geq 1$ this gives $d_{12} \leq H$ and $18i \leq n^3$. By [Lemma (Coranks)](/chapter/remaining-terms/#the-gain), $k \leq \dim\operatorname{commonLink} + i + (j - \varrho)$ with $j - \varrho \leq 1$, so the corank is at most $i + 1 \leq n^3$, since $n = \varrho + 1 \geq 10^5$. The subspace $\operatorname{commonLink}$ lies in $X_0$, so its dimension plus the corank is $k$. $\square$

**Lemma (The product of two sizes).** Let $(\gamma, \gamma')$ be a near pair over $c, c'$ with corank $l$. Let $\eta > 0$ and $D, B$ be real numbers with $(d_{12}\eta)^2 \leq \mathsf{g}^*(\gamma)\mathsf{g}^*(\gamma')$, with $\mathcal{D}_j \leq D$ and $\mathcal{D}_{j'} \leq D$ for the two cell ranks, and with $\tau^{l+6}D\eta^{-k} \leq B$. Then

$$\operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma') \leq \frac{B}{\tau^{l+2}n_p}\,d_{12}^{-k}.$$

Lean: `New.Filling.IsNearPairOverAgreeingBlock.ofReal_termSize_mul_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Both gauges are positive ([Lemma](/decl/New.Filling.levelGauge_pos/)). By the definition, $\operatorname{termSize}^2 \leq \tau^4D/(n_p\mathsf{g}^{*k})$ for each term ([Lemma](/decl/New.Filling.termSize_sq_le/)). Multiply the two bounds and take the square root:

$$\operatorname{termSize}\cdot\operatorname{termSize}' \leq \frac{\tau^4D}{n_p(\mathsf{g}^*\mathsf{g}^{*\prime})^{k/2}} \leq \frac{\tau^4D}{n_p(d_{12}\eta)^k}.$$

This is $\tau^{l+6}D\eta^{-k}\cdot d_{12}^{-k}/(\tau^{l+2}n_p) \leq B\,d_{12}^{-k}/(\tau^{l+2}n_p)$. $\square$

**Theorem (Sum of sizes).** For all classes $c, c'$ let $P(c, c')$ be a set of near pairs over $c, c'$. Let $B \geq 0$. Suppose that each pair in $P(c, c')$ has numbers $\eta, D$ as in the previous lemma, for this $B$. Then

$$\sum_{c, c'}\ \sum_{(\gamma, \gamma') \in P(c, c')} \operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma') \leq \tau B.$$

Lean: `New.Filling.sum_termSize_mul_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Sort the pairs by the corank $l$, which is at most $n^3$ by the lemma on near pairs. A pair of corank $l$ lies in $P_l(c, c')$, and its product of sizes is at most $B\,d_{12}^{-k}/(\tau^{l+2}n_p)$. Extend the sum from $P(c, c')$ to all of $P_l(c, c')$; the terms are nonnegative. By the Count theorem, the pairs of corank $l$ contribute at most $B\tau^{l+2}n_p/(\tau^{l+2}n_p) = B$. There are $n^3 + 1$ values of $l$, and $n^3 + 1 \leq 2b^3 \leq b^4 \leq \tau$ ([Lemma](/decl/New.Filling.cube_add_one_le_tailScale/)). $\square$

The factor $\tau^{l+6}$ in the hypothesis pays for all the losses: $\tau^4$ from the two sizes, $\tau^{l+2}$ from the count, and $\tau$ from the number of coranks is paid by the conclusion.

### Pairs with different links

Two terms lie in the same link class if $\mathsf{g}(\gamma) \neq 0$, $\mathsf{g}(\gamma') \neq 0$ and $\operatorname{link}\gamma = \operatorname{link}\gamma'$ ([Definition](/decl/New.Filling.InSameLinkClass/)). All other pairs are small. The gain for them is $(M/2)^{c^+f}$ when $c^+ \geq 1$; it must pay for $\mathcal{D}_{\mathrm{main}}$, which is larger than $\mathcal{D}_{\mathrm{id}}$. Since $\mathcal{D}_{\mathrm{main}} \geq \tau^{44}\mathcal{D}_{\mathrm{id}}$, every $\mathcal{D}_j$ is at most $\mathcal{D}_{\mathrm{main}}$ ([Lemma](/decl/New.Filling.cellRankSecondMoment_le_mainSecondMoment/)).

**Lemma (One unit of gain pays).** Let $i \geq 1$ and $l \leq i + 1$. Then

$$\frac{\tau^{l+6}\mathcal{D}_{\mathrm{main}}}{((M/2)^{if})^k} \leq \frac{\mathcal{D}_{\mathrm{id}}}{\tau^{10}}.$$

Lean: `New.Filling.pow_mul_mainSecondMoment_div_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Put $x = \tau(2/M)^{kf}$. Since $\tau \leq \tau^4 = b^{kf}$ and $2b \leq b^{19} \leq M$, we have $x \leq (2b/M)^{kf} \leq 1$. The left side is at most $\tau^{i+7}\mathcal{D}_{\mathrm{main}}(2/M)^{ikf} = \tau^7x^i\mathcal{D}_{\mathrm{main}} \leq \tau^7x\mathcal{D}_{\mathrm{main}}$. The admissible data satisfy $\mathcal{D}_{\mathrm{main}} \leq (M/b^6)^{kf}\mathcal{D}_{\mathrm{id}}$ (the field `mainSecondMoment_le` of `IsAdmissible`). So the left side is at most

$$\tau^8(2/M)^{kf}(M/b^6)^{kf}\mathcal{D}_{\mathrm{id}} = \tau^8(2/b^6)^{kf}\mathcal{D}_{\mathrm{id}} \leq \tau^8b^{-5kf}\mathcal{D}_{\mathrm{id}} = \tau^{-12}\mathcal{D}_{\mathrm{id}} \leq \tau^{-10}\mathcal{D}_{\mathrm{id}}. \quad\square$$

**Theorem (Pairs not in one link class).** Let $A(c, c')$ be the set of near pairs over $c, c'$ that do not lie in the same link class. Then

$$\sum_{c, c'}\ \sum_{(\gamma, \gamma') \in A(c, c')} \operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma') \leq b^{-kf}\mathcal{D}_{\mathrm{id}}.$$

Lean: `New.Filling.sum_termSize_mul_not_inSameLinkClass_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Apply the theorem on the sum of sizes with $B = \tau^{-10}\mathcal{D}_{\mathrm{id}}$. Then $\tau B = \tau^{-9}\mathcal{D}_{\mathrm{id}} \leq \tau^{-4}\mathcal{D}_{\mathrm{id}} = b^{-kf}\mathcal{D}_{\mathrm{id}}$. It remains to find $\eta$ and $D$ for a pair $(\gamma, \gamma')$ in $A(c, c')$ with cell ranks $j, j'$. Let $i = c^+$. The Gain theorem with $x = 1$ gives $d_{12}^2 \leq (2/M)^{2if}\mathsf{g}^*\mathsf{g}^{*\prime}$, and [Lemma (Coranks)](/chapter/remaining-terms/#the-gain) gives $k \leq \dim\operatorname{commonLink} + i + (j - \varrho)$.

*Case $i = 0$.* The links are equal. By Lemma (Coranks), $\mathsf{g}(\gamma) = 0$ if and only if $\mathsf{g}(\gamma') = 0$. Since the pair is not in one link class, both vanish. A term with a cell rank has $\mathsf{g} \neq 0$ exactly in the top cell, so $j, j' \leq \varrho$. Then $j - \varrho = 0$ in $\mathbb{N}$, and the corank is $l = 0$. Take $\eta = 1$ and $D = \tau^{-16}\mathcal{D}_{\mathrm{id}}$, which is $\mathcal{D}_j = \mathcal{D}_{j'}$. The gain is $d_{12}^2 \leq \mathsf{g}^*\mathsf{g}^{*\prime}$, and $\tau^{0+6}D = \tau^{-10}\mathcal{D}_{\mathrm{id}} = B$.

*Case $i \geq 1$.* Take $\eta = (M/2)^{if}$ and $D = \mathcal{D}_{\mathrm{main}}$. Then $(d_{12}\eta)^2 \leq (2/M)^{2if}(M/2)^{2if}\mathsf{g}^*\mathsf{g}^{*\prime} = \mathsf{g}^*\mathsf{g}^{*\prime}$. Since $j - \varrho \leq 1$, the corank is $l \leq i + 1$, and the previous lemma gives $\tau^{l+6}D\eta^{-k} \leq B$. $\square$

The case $i = 0$ shows why the terms with $\mathsf{g} = 0$ cost nothing: they lie below the top cell, where the second moment carries the factor $\tau^{-16}$, and that factor pays for the count without a gain.

### Pairs with one link

For a pair in one link class, $c^+ = 0$ and there is no gain from the links. The gain comes from the places at which the block meets.

**Theorem (Pairs in one link class).** Let $z \neq 0$ be a natural number. Let $C(c, c')$ be the set of near pairs $(\gamma, \gamma')$ over $c, c'$ that lie in the same link class and such that $\gamma$ lies over a block $(c, s, c')$ with $z \leq \operatorname{meetNorm}(s)$. Then

$$\sum_{c, c'}\ \sum_{(\gamma, \gamma') \in C(c, c')} \operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma') \leq \Big(\frac{b^{2f}}{z}\Big)^k\mathcal{D}_{\mathrm{main}}.$$

Lean: `New.Filling.sum_termSize_mul_inSameLinkClass_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Apply the theorem on the sum of sizes with $B = \tau^7\mathcal{D}_{\mathrm{main}}/z^k$. Then $\tau B = \tau^8\mathcal{D}_{\mathrm{main}}/z^k = (b^{2f}/z)^k\mathcal{D}_{\mathrm{main}}$, since $\tau^8 = b^{2kf}$. Let $(\gamma, \gamma') \in C(c, c')$. The pair lies over a block $(c, s, c')$ with $s$ agreeing. A term determines the reduction of its block ([Lemma](/decl/New.Filling.eq_of_mem_termsOver/)), so this $s$ is the one with $z \leq \operatorname{meetNorm}(s)$. The links are equal, so $c^+ = 0$, and $\mathsf{g}(\gamma) \neq 0$, so $\gamma$ lies in the top cell $j = \varrho + 1$. So the Gain theorem with $x = z$ gives $x^\flat = z$ and $(d_{12}z)^2 \leq \mathsf{g}^*\mathsf{g}^{*\prime}$. Take $\eta = z$ and $D = \mathcal{D}_{\mathrm{main}}$. By Lemma (Coranks), $k \leq \dim\operatorname{commonLink} + 0 + 1$, so $l \leq 1$ and $\tau^{l+6}D/z^k \leq \tau^7\mathcal{D}_{\mathrm{main}}/z^k = B$. $\square$

### Proof of the two theorems

A block is split into pieces: one piece for each link $\Lambda$, which contains the terms with $\mathsf{g} \neq 0$ and link $\Lambda$, and one more piece for the terms with $\mathsf{g} = 0$ ([Definition](/decl/New.Filling.piece/)). The piece of a term is invariant under the rational unipotent elements on both sides, so the part of a stable set in one piece is stable ([Lemma](/decl/New.Filling.IsStable.inter_piece/)).

**Lemma (Product of two blocks).** Let $T, T' \subset \Gamma^*$ be stable. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\|\,\|\mathcal{A}^\flat_{T'}(c, s, c')\| \leq \sum_{\gamma \in \mathcal{R}_T(c, s, c')}\ \sum_{\gamma' \in \mathcal{R}_{T'}(c, s, c')} \nu^2\operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma').$$

Lean: `New.Filling.enorm_amplitudeSum_mul_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Multiply the bounds of the [Size theorem](/chapter/remaining-terms/#the-size-of-a-block) for $T$ and $T'$, and expand the product of the two sums. $\square$

**Lemma (Square of a block).** Let $T \subset \Gamma^*$ be stable. Then

$$\|\mathcal{A}^\flat_T(c, s, c')\|^2 \leq \sum_\Lambda\|\mathcal{A}^\flat_{T \cap \{\mathsf{g} \neq 0\} \cap \operatorname{link}^{-1}(\Lambda)}(c, s, c')\|^2 + \nu^2\sum_{(\gamma, \gamma')}\operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma'),$$

where the last sum is over the pairs of near representatives of $T$ over $(c, s, c')$ that do not lie in the same link class.

Lean: `New.Filling.enorm_amplitudeSum_sq_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Write $a_\kappa$ for the norm of the block of the piece $\kappa$ of $T$. By the [lemma on fibres](/chapter/remaining-terms/#the-size-of-a-block), $\|\mathcal{A}^\flat_T\| \leq \sum_\kappa a_\kappa$, so $\|\mathcal{A}^\flat_T\|^2 \leq \sum_{(\kappa, \kappa')}a_\kappa a_{\kappa'}$. The diagonal pairs $(\Lambda, \Lambda)$ of two links give the first sum. For any other pair $(\kappa, \kappa')$, the product of two blocks bounds $a_\kappa a_{\kappa'}$ by $\nu^2$ times the products of sizes over the near representatives $\gamma$ of the piece $\kappa$ and $\gamma'$ of the piece $\kappa'$. Such a pair does not lie in one link class: either a term has $\mathsf{g} = 0$, or the links differ. This includes the pair of pieces $(\mathsf{g} = 0, \mathsf{g} = 0)$. A term determines its piece, so different $(\kappa, \kappa')$ give different pairs $(\gamma, \gamma')$, and the sum over all off diagonal $(\kappa, \kappa')$ is at most the last sum. $\square$

**Theorem (Remaining terms, reduction to one link).** Let $\Omega \subset \bar G$ and $w \geq 0$. Suppose that

$$\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq w\nu^2.$$

Then

$$\mathsf{E}(\mathcal{A}^\flat_{\Gamma^*}, \Omega) \leq w + \frac{\mathcal{D}_{\mathrm{id}}}{b^{kf}}.$$

Lean: `New.Filling.secondMoment_remainingTerms_le` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* Multiply by $\nu^2 > 0$; it suffices to show $\sum_{c, c'}\sum_{s \in \Omega}\|\mathcal{A}^\flat_{\Gamma^*}(c, s, c')\|^2 \leq (w + b^{-kf}\mathcal{D}_{\mathrm{id}})\nu^2$. The set $\Gamma^*$ is stable ([Lemma](/decl/New.Filling.isStable_remainingTerms/)). Apply the square of a block to each $(c, s, c')$ with $T = \Gamma^*$. Every $\gamma$ with $\mathsf{g}(\gamma) \neq 0$ lies in $\Gamma^*$, so $\Gamma^* \cap \{\mathsf{g} \neq 0\} = \{\mathsf{g} \neq 0\}$. So the first sums, added over $c, c'$ and $s \in \Omega$, give $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq w\nu^2$.

The second sums are over pairs of near representatives over $(c, s, c')$. Two near representatives over one block form a near pair ([Lemma](/decl/New.Filling.isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver/)). A term determines the reduction $s$ of its block, so for fixed $c, c'$ a pair occurs for at most one $s$. So, for fixed $c, c'$, the sum over $s \in \Omega$ of the second sums is at most the sum over all near pairs over $c, c'$ not in one link class. By the theorem on pairs not in one link class, the total over $c, c'$ is at most $b^{-kf}\mathcal{D}_{\mathrm{id}}$. Together the sum is at most $w\nu^2 + \nu^2b^{-kf}\mathcal{D}_{\mathrm{id}}$. $\square$

**Theorem (Remaining terms, one link at a time).** Let $\Omega \subset \bar G$, and let $z \neq 0$ be a natural number with $z \leq \operatorname{meetNorm}(s)$ for every $s \in \Omega$. Then

$$\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq \Big(\frac{b^{2f}}{z}\Big)^k\mathcal{D}_{\mathrm{main}}\,\nu^2.$$

Lean: `New.Filling.linkSecondMoment_le_of_le_meetNorm` (New/Spanning/RemainingTerms/Sum.lean).

*Proof.* For a link $\Lambda$ let $T_\Lambda = \{\gamma : \mathsf{g}(\gamma) \neq 0,\ \operatorname{link}\gamma = \Lambda\}$. It lies in $\Gamma^*$. It is stable, because $\mathsf{g}$ and the link do not change when $\gamma$ is replaced by $u^{-1}\gamma u'$ for rational $u, u'$ in the Bessel unipotent group ([Lemma](/decl/New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU/) and [Lemma](/decl/New.Filling.link_inv_mul_mul_of_mem_besselU/)). The product of two blocks with $T = T' = T_\Lambda$ gives

$$\|\mathcal{A}^\flat_{T_\Lambda}(c, s, c')\|^2 \leq \nu^2\sum_{\gamma, \gamma' \in \mathcal{R}_{T_\Lambda}(c, s, c')}\operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma').$$

A pair $(\gamma, \gamma')$ here is a near pair, both terms have $\mathsf{g} \neq 0$ and the link $\Lambda$, and $\gamma$ lies over $(c, s, c')$ with $z \leq \operatorname{meetNorm}(s)$ since $s \in \Omega$. So the pair lies in $C(c, c')$. The pair determines $s$, since a term determines its block, and it determines $\Lambda = \operatorname{link}\gamma$. So the sum over $s \in \Omega$ and $\Lambda$ is at most the sum over $C(c, c')$. The theorem on pairs in one link class finishes the proof. $\square$

**Remark (Formalization).** All sums over pairs, links and reductions are taken in $[0, \infty]$, so no summability is needed, and the sizes enter as $\operatorname{ofReal}$ of the real products. The cell rank is defined by `Classical.epsilon` and is an unspecified index for a term with no cell rank; all terms that are summed here are near representatives, which have a cell rank by definition, so the junk value never enters. The hypothesis $z \neq 0$ is needed: in Lean $b^{2f}/0 = 0$, so without it the second theorem would assert $\mathsf{L} = 0$. The number $\nu$ is positive, so the division by $\nu^2$ in $\mathsf{E}$ is a true division.

**Example.** Take $\Omega$ to be all reductions with $\operatorname{meetNorm}(s) \geq z$, and combine the two theorems with $w = (b^{2f}/z)^k\mathcal{D}_{\mathrm{main}}$. The result is $\mathsf{E}(\mathcal{A}^\flat_{\Gamma^*}, \Omega) \leq (b^{2f}/z)^k\mathcal{D}_{\mathrm{main}} + b^{-kf}\mathcal{D}_{\mathrm{id}}$. Since $\mathcal{D}_{\mathrm{main}}$ can be as large as $(M/b^6)^{kf}\mathcal{D}_{\mathrm{id}}$, the first term is small against $\mathcal{D}_{\mathrm{id}}$ only if $z$ is larger than about $(M/b^4)^f$.
