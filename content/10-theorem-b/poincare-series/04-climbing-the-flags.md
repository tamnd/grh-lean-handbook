---
title: Climbing the flags
lean:
  - New/Spanning/Unfolding/Climbing.lean
decls:
  - New.Filling.inclHFin_mem_latticeStabilizer_iff
  - New.Filling.reduction_inclHFin_eq_one_iff
  - New.Filling.classSum_sourceLevel_eq_sum
  - New.Filling.card_resField_eq_levelPrime
  - New.Filling.tsum_indicator_smul_eq_tsum_stabilizer
  - New.Filling.integral_besselKernel_eq_zero_of_not_charsAgree
  - New.Filling.amplitudeSum_eq_zero_of_not_charsAgree
  - New.PairOccursInColumnsAt
  - New.IsTopIndex
  - New.exists_isTopIndex
  - New.IsTopIndex.ne_zero_or_ne_zero
  - New.PairOccursInColumnsAt.of_le
  - New.pairOccursInColumnsAt_of_forall_mul_vecMul_eq
  - New.dotProduct_cons_zero_init
  - New.Filling.pairOccursAt_succ
  - New.Filling.CharsAgree.pairOccursAt_mono
  - New.Filling.CharsAgree.mul_star_eq_of_pairOccursAt
  - New.Filling.CharsAgree.mul_star_eq_of_isTopIndex
  - New.Filling.CharsAgree.mul_star_ne_zero_of_isTopIndex
  - New.Filling.CharsAgree.exists_isTopIndex_apply_eq
  - New.Filling.CharsAgree.exists_coords_ne_zero_of_common_vector
  - New.Filling.CharsAgree.leadingMinor_ne_zero
  - New.Filling.CharsAgree.exists_hasCellRank
  - New.Filling.MeetsAt
  - New.Filling.meetNorm
  - New.Filling.one_le_meetNorm
  - New.Filling.prod_le_meetNorm
  - New.Filling.vectorFixer
  - New.Filling.reducedImage_besselH_le_vectorFixer
  - New.Filling.reducedImage_besselH_le_fixer
  - New.Filling.exists_eichler_mem_latticeStabilizer
  - New.Filling.vecMul_frameImage_dotProduct_cons_init_eq_of_agrees
  - New.Filling.pairOccursInColumnsAt_succ_of_agree
  - New.Filling.exists_pairOccursInColumnsAt_top_of_meetsAt
  - New.Filling.meetNorm_le_genIndex_star
  - New.Filling.reduceAboveM_det_eq_zero_of_meetsAt
  - New.Filling.meetNorm_le_genIndex_det
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Climbing the flags

This section proves two things. First, a block over a stable set of terms whose characters never agree is $0$. Second, a term whose characters agree climbs: a vector common to the flags of the frame $f$ and of $\gamma f$ can be moved up both flags with the same two coefficients. At the top the two coefficients have the same norm. This gives the cell rank of [the anatomy of a term](/chapter/anatomy-of-a-term/#cells-and-the-discriminant). The same climb works modulo a place above $M$, and it bounds the norm of the places where a reduction meets its frame.

The frame is $f = (e_1, \ldots, e_\varrho, z)$, with indices $0, \ldots, \varrho$. The last index $\varrho$ is called the top. A *common vector* is a pair of coordinate vectors $x, y$ with $fx = \gamma fy$ ([Definition](/decl/New.PairOccursAt/)).

### The lattice stabilizer and the classes

These four facts are used in [Bessel functions at a real place](/chapter/bessel-real-place/#the-bessel-system-of-the-data).

**Lemma (The image of the small group).** Let $k$ be a finite adelic unitary matrix for the identity form on $X_0$, and $\iota(k)$ its image in the unitary group of $V$, in the lattice basis. Then $\iota(k) \in K$ if and only if $k$ is integral and its row $k_0$ is congruent to the row of $1$ modulo $\pi_N$. If $\iota(k) \in K$, then for each chosen place $w$ the reduction of $\iota(k)$ modulo $w$ is $1$ if and only if the reduction of $k$ is $1$.

Lean: `New.Filling.inclHFin_mem_latticeStabilizer_iff`, `New.Filling.reduction_inclHFin_eq_one_iff` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* An isometry $x$ of a unimodular form lies in $K$ if and only if $x - 1$ is integral. The matrix $\iota(k) - 1$ is $0$ outside one block, and there it is $P\,(k - 1)D$, where the columns of $P$ are the basis vectors of $X_0$ in the lattice basis of $X_0 \oplus \langle z\rangle$ and $D$ is the diagonal matrix with $\bar\pi_N^{-1}$ at $k_0$. The product $Pl$ is integral if and only if $l$ is integral and row $k_0$ of $l$ is divisible by $\pi_N$. At each place $\pi_N$ or $\bar\pi_N$ is a unit. So the condition says that $(k-1)$, with row $k_0$ divided by $\pi_N$ and column $k_0$ by $\bar\pi_N$, is integral. That is the congruence condition. For the reduction, $w$ has norm $p_i \neq N$, so $\pi_N$ and $\bar\pi_N$ are units at $w$, and the extra row of $P$ repeats row $k_0$. $\square$

**Lemma (Class sums and residue fields).** The class sum at the source level, weighted by the inverse orders of the stabilizers, is the plain sum $\sum_c F(h_c)$. The residue field at a chosen place of index $i$ has $p_i$ elements.

Lean: `New.Filling.classSum_sourceLevel_eq_sum`, `New.Filling.card_resField_eq_levelPrime` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* At the source level the stabilizers are trivial ([the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block)). A chosen place has norm $p_i$. $\square$

### Characters that do not agree

**Lemma (Sums over representatives).** Let $H$ act on $X$, and let $a(x)\cdot x$ be the chosen representative of the orbit of $x$. Then $\sum_{u \in H}\mathbf{1}[u x \text{ is a representative}]\,F(ux, u) = \sum_{u \in \operatorname{Stab}(a(x)x)}F(a(x)x, u\,a(x))$.

Lean: `New.Filling.tsum_indicator_smul_eq_tsum_stabilizer` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* $ux$ is a representative exactly when $ux = a(x)x$, that is when $u\,a(x)^{-1}$ fixes $a(x)x$. $\square$

**Lemma (One term with characters that do not agree).** Let $\gamma$ be rational and suppose its characters do not agree. Let $\Gamma$ be the image at the infinite places of the stabilizer in $\mathsf{U}_c(M)$ of the coset $\gamma\,\mathsf{U}_{c'}(M)$. Let $\Gamma$ be discrete and $\beta$ a cutoff for $\Gamma$. Then, for both sides,

$$\int\beta(y)\,K(\gamma, y)\,dy = 0.$$

Lean: `New.Filling.integral_besselKernel_eq_zero_of_not_charsAgree` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* There are rational $u, u' \in \mathsf{U}$ with $u\gamma = \gamma u'$ and $\chi(u) \neq \chi(u')$ ([Definition](/decl/New.Filling.CharsAgree/)). For $k \in \mathsf{U}_c(M)$ that fixes the coset, $\gamma^{-1}k\gamma \in \mathsf{U}_{c'}(M)$. The invariance under the group of a class then gives $K(\gamma, ky) = K(\gamma, y)$. So $K(\gamma, \cdot)$ is invariant under $\Gamma$, and $\int\beta K$ is the integral of $K$ over $\Gamma\backslash G_\infty$. The kernel lemma of [the previous section](/chapter/poincare-series/#moving-blocks) gives $K(\gamma, uy) = \chi(u)^{-1}\chi(u')K(\gamma, y)$, since $u\gamma u'^{-1} = \gamma$. The factor has modulus $1$ and is not $1$. The kernel is continuous. An invariant continuous function that a left translation multiplies by such a factor has integral $0$ over the quotient ([Lemma](/decl/New.integral_quotMeasure_eq_zero_of_twist/), [reduction theory](/chapter/reduction-theory/)). $\square$

**Theorem (Blocks without agreeing characters vanish).** Let $S$ be admissible, $E$ contain a primitive root of unity of order $5040$, and $T$ be stable. If no $\gamma \in T$ has agreeing characters, then $\mathcal{A}(c, s, c') = 0$ for all $c, s, c'$ and both sides.

Lean: `New.Filling.amplitudeSum_eq_zero_of_not_charsAgree` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Choose for each coset $x \in G(E)/\mathsf{U}_{c'}(M)$ a cutoff $\varphi_x$ for the stabilizer of $x$ in $\mathsf{U}_c(M)$, with $\sum_{u \in \operatorname{Stab}(x)}\varphi_x(uy) = 1$ ([Lemma](/decl/New.Filling.exists_cutoff_classUnipotent/)). Choose a representative $a(x)x$ of each orbit of $\mathsf{U}_c(M)$ on these cosets. Put

$$\mathrm{wt}(\gamma, y) = \beta_{c'}(\gamma^{-1}y)\cdot\mathbf{1}[\gamma\,\mathsf{U}_{c'}(M) \text{ is a representative}]\cdot\varphi_\gamma(y).$$

Its orbit sum under $(u, u')$ is $1$. The sum over $u'$ of $\beta_{c'}(u'\gamma^{-1}u^{-1}uy)$ is $1$. The sum over $u$ that remains is $1$ by the lemma on sums over representatives and the choice of $\varphi$. The change of weight gives $\mathcal{A}(c, s, c') = \sum_\gamma\int\mathrm{wt}(\gamma, y)K(\gamma, y)\,dy$. Each term is a constant times $\int\varphi_\gamma K(\gamma, \cdot)$, which is $0$ by the lemma on one term. $\square$

### Common vectors of two flags

Let $P, P'$ be matrices over a field with columns $0, \ldots, n$. A pair $(\mu, \mu')$ *occurs at* $j$ if some vector lies in the spans of the columns of index at most $j$ of $P$ and of $P'$, with coefficients $\mu$ and $\mu'$ at $j$ ([Definition](/decl/New.PairOccursInColumnsAt/)). For coordinates $x, y$, an index $j$ is the *top index* if $x, y$ vanish above $j$ and $j$ is the least such index ([Definition](/decl/New.IsTopIndex/)).

**Lemma (Top indices).** Every pair $x, y$ has a top index $j$. If $x \neq 0$, then $x_j \neq 0$ or $y_j \neq 0$.

Lean: `New.exists_isTopIndex`, `New.IsTopIndex.ne_zero_or_ne_zero` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Above the top index there are no nonzero entries. If $x \neq 0$ and both $x_j, y_j$ were $0$, then $j \neq 0$ and $j - 1$ would also bound the support. $\square$

**Lemma (Steps give all heights).** If every pair that occurs at an index occurs at the next index, then a pair that occurs at $j$ occurs at every $l \geq j$.

Lean: `New.PairOccursInColumnsAt.of_le` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Induction on $l$. $\square$

**Lemma (Duality).** Suppose that every linear form $m$ that kills the columns of index below $j$ of $P$ and of $P'$ satisfies $\mu\,m(P_j) = \mu'\,m(P'_j)$. Then $(\mu, \mu')$ occurs at $j$.

Lean: `New.pairOccursInColumnsAt_of_forall_mul_vecMul_eq` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Let $A$ be the span of the columns below $j$ of $P$ and $P'$. The vector $\mu P_j - \mu' P'_j$ is killed by every form that kills $A$, so it lies in $A$. Write it as $Pa - P'a'$ with $a, a'$ supported below $j$. Then $P(\mu e_j - a) = P'(\mu' e_j - a')$. $\square$

**Lemma (The shift).** Let $m$ vanish on the columns of index at most $i$, and $x$ vanish above $i$. Write $x^{\uparrow}$ for $x$ moved up by one index, with $0$ at index $0$. Then $m(Px^{\uparrow}) = x_i\,m(P_{i+1})$.

Lean: `New.dotProduct_cons_zero_init` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* $Px^{\uparrow} = \sum_bx_bP_{b+1}$, and only $b = i$ survives. $\square$

### The climb

**Theorem (One step up).** Let the characters of $\gamma$ agree. If $(\mu, \mu')$ occurs at $j < \varrho$ for $f$ and $\gamma f$, it occurs at $j + 1$.

Lean: `New.Filling.pairOccursAt_succ` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Let $fx = \gamma fy$ with $x, y$ zero above $j$ and $x_j = \mu$, $y_j = \mu'$. By duality it suffices to show $\mu\,m(f_{j+1}) = \mu'\,m(\gamma f_{j+1})$ for each form $m$ that kills $f_b$ and $\gamma f_b$ for $b \leq j$. By the shift lemma, this says $m(fx^{\uparrow}) = m(\gamma fy^{\uparrow})$. Two elements of $E$ are equal if $\psi_f$ agrees on all their multiples by $t \in E$, since $\psi_f$ is nontrivial and $E$ is dense in the finite adeles. So fix $t \in E$.

Let $v$ represent the form $m\gamma$ through the hermitian form, so that $\gamma v$ represents $m$. Put $r = M\delta_E(-t)$. The Eichler map along $r$ times the vector $fx$, with the form $m$, is an element $u \in \mathsf{U}$, and the sum of its entries at the simple roots is $r\,m(fx^{\uparrow})$ ([Lemma](/decl/New.exists_mem_besselU_eq_eichlerMap/), [the level structure](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data)). In the same way the Eichler map along $r\,fy$ with the form $m\gamma$ is $w \in \mathsf{U}$, with sum $r\,m(\gamma fy^{\uparrow})$. Since $fx = \gamma fy$ and $\gamma$ is an isometry, $u\gamma = \gamma w$. As the characters agree, $\chi(u) = \chi(w)$. By the definition of $\chi$ through the self dual character and the factor $M^{-1}$, $\chi(u) = \psi_f(t\,m(fx^{\uparrow}))$ and $\chi(w) = \psi_f(t\,m(\gamma fy^{\uparrow}))$. $\square$

**Corollary (The climb).** Let the characters of $\gamma$ agree, and let $(\mu, \mu')$ occur at $j$.

1. It occurs at every $l \geq j$.
2. $\mu\bar\mu = \mu'\bar\mu'$.
3. If $fx = \gamma fy$ with $x \neq 0$ and top index $j$, then $x_j\bar x_j = y_j\bar y_j \neq 0$, and for every $l \geq j$ some common vector has top index $l$ and the coefficients $x_j, y_j$ at $l$.

Lean: `New.Filling.CharsAgree.pairOccursAt_mono`, `New.Filling.CharsAgree.mul_star_eq_of_pairOccursAt`, `New.Filling.CharsAgree.mul_star_eq_of_isTopIndex`, `New.Filling.CharsAgree.mul_star_ne_zero_of_isTopIndex`, `New.Filling.CharsAgree.exists_isTopIndex_apply_eq` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Part 1 is the step lemma with the lemma on steps. For part 2 climb to the top. There $fx = \gamma fy$ with $x_\varrho = \mu$, $y_\varrho = \mu'$. The vector has norm $-N x_\varrho\bar x_\varrho$ in $f$ and $-N y_\varrho\bar y_\varrho$ in $\gamma f$, since $\gamma$ is an isometry ([Lemma](/decl/New.Filling.star_mul_last_eq_of_frameImage_eq/)). For part 3, $(x_j, y_j)$ occurs at $j$, so part 2 gives the equality. One of $x_j, y_j$ is nonzero by the lemma on top indices, so the common norm is nonzero. Then both are nonzero, and part 1 gives the vectors at $l$. $\square$

### The cell rank

**Lemma (Common vectors reach the cell).** Let the characters of $\gamma$ agree, and let $j$ be the least index from which a norm one pair $(\zeta, 1)$ occurs at all indices ([Definition](/decl/New.NormOnePairOccursFrom/)). If $fx = \gamma fy$ with $x \neq 0$, then $x_l \neq 0$ and $y_l \neq 0$ for some $l \geq j$.

Lean: `New.Filling.CharsAgree.exists_coords_ne_zero_of_common_vector` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Let $l$ be the top index. By the climb, $x_l\bar x_l = y_l\bar y_l \neq 0$. Put $\zeta = y_l^{-1}x_l$. Dividing by $y_l$ shows that $(\zeta, 1)$ occurs at $l$, and by part 2 of the climb $\zeta\bar\zeta = 1$. By part 1 it occurs at all indices from $l$ on. By the choice of $j$, $j \leq l$. $\square$

**Lemma (The leading minor).** Under the same hypotheses, if $j \leq \varrho$, then the leading minor of order $j$ of the matrix $(h(f_a, \gamma f_b))_{a,b}$ is nonzero.

Lean: `New.Filling.CharsAgree.leadingMinor_ne_zero` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Suppose the minor is $0$. Then some $y \neq 0$, zero from $j$ on, has $h(f_a, \gamma fy) = 0$ for $a < j$. For $a \geq j$ the same holds. The pair condition holds for $\gamma^{-1}$ from $j$ on ([Lemma](/decl/New.NormOnePairOccursFrom.inv/)). So for each $w$ there are $X, Y$ with $fX = \gamma^{-1}fY$ and $X_a = \bar w_a$ for $a \geq j$ ([Lemma](/decl/New.Filling.exists_frameImage_eq_of_normOnePairOccursFrom/)). The pairing of $fX$ with $\gamma fy$ is $-N\bar Y_\varrho y_\varrho$ ([Lemma](/decl/New.Filling.frameProducts_mulVec_of_frameImage_eq/)), which is $0$ because $y_\varrho = 0$. Expanding it in $X$, the rows below $j$ give $0$ and the rows from $j$ on give $\sum_{a \geq j}w_a\,h(f_a, \gamma fy)$. As $w$ is arbitrary, $\gamma fy$ is orthogonal to the whole frame. Then $\gamma fy = fx$ for some $x$ ([Lemma](/decl/New.Filling.exists_frameImage_eq_of_frameProducts_mulVec_eq_zero/)), and $x \neq 0$ because $y \neq 0$. The lemma on common vectors gives $l \geq j$ with $y_l \neq 0$. This contradicts $y_l = 0$. $\square$

**Theorem (Agreeing characters give a cell rank).** Let the characters of $\gamma$ agree and let the discriminant of $\gamma$ vanish. Then $\gamma$ has a cell rank $j \leq \varrho$.

Lean: `New.Filling.CharsAgree.exists_hasCellRank` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* The pair condition from $\varrho + 1$ on is empty, so it holds, and there is a least $j$ with the pair condition. The discriminant vanishes, so $f$ and $\gamma f$ share a nonzero vector ([Lemma](/decl/New.Filling.termDisc_eq_zero_iff_exists/)). The lemma on common vectors gives $l \geq j$ with $l \leq \varrho$, so $j \leq \varrho$. The leading minor lemma gives the second condition of a cell rank. The third, $\varrho < j \Leftrightarrow$ the discriminant is nonzero, holds since both sides are false. $\square$

[The anatomy of a term](/chapter/anatomy-of-a-term/#cells-and-the-discriminant) uses this theorem.

### The climb modulo a place above M

A place above $M$ is a chosen place $w$ with a flag that says whether to conjugate. The element $s \in \bar G$ acts modulo this place by its component at $w$, or by the inverse adjoint of it. $s$ *meets* at the place if the span of $f$ and its image under $s$ share a nonzero vector there. The *meet norm* of $s$ is the product of the norms $p_i$ of the places where $s$ meets ([Definition](/decl/New.Filling.MeetsAt/), [Definition](/decl/New.Filling.meetNorm/)).

**Lemma (The meet norm).** $1 \leq \operatorname{meetNorm}(s)$. If $s$ meets at every place of a set $A$, then $\prod_{p \in A}N(p) \leq \operatorname{meetNorm}(s)$. The reduction of the Bessel group $\mathsf{H}$, the unitary group of $X_0$, fixes every nonzero vector of the span of $f$ modulo every place above $M$.

Lean: `New.Filling.one_le_meetNorm`, `New.Filling.prod_le_meetNorm`, `New.Filling.vectorFixer`, `New.Filling.reducedImage_besselH_le_vectorFixer`, `New.Filling.reducedImage_besselH_le_fixer` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* The norms are primes, so they are at least $1$, and a subproduct is at most the product. $\mathsf{H}$ fixes the basis vectors outside $X_0$, which span the frame, and its inverse adjoint fixes the forms that they define. $\square$

**Lemma (Eichler maps in the lattice stabilizer).** Let $x$ be integral coordinates that vanish from $a$ on, $m$ an integral form that kills the frame vectors below $a$, and $r$ integral. Then some $u \in K \cap \mathsf{U}$ has simple root sum $r\,m(fx^{\uparrow})$. Modulo each place above $M$ where $\bar x$ vanishes, $u$ is $1 + r\,(fx)\,m$.

Lean: `New.Filling.exists_eichler_mem_latticeStabilizer` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* Take the Eichler map of [the level structure](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data) over the integral adeles. Its correction term is a multiple of $\bar x$, which vanishes at the place. $\square$

**Theorem (One step up modulo a place).** Let $k \in K$ and let its reduction agree ([Definition](/decl/New.Filling.Agrees/)). Work modulo a place above $M$, and write $\gamma$ for the matrix of $k$ there.

1. If $fx = \gamma fy$, with $x, y$ zero from $a$ on, and $m$ kills $f_b$ and $\gamma f_b$ for $b < a$, then $m(fx^{\uparrow}) = m(\gamma fy^{\uparrow})$.
2. A pair that occurs at $j < \varrho$ occurs at $j + 1$.
3. If $k$ meets at the place, some pair $(\mu, \mu')$, not both $0$, occurs at the top.

Lean: `New.Filling.vecMul_frameImage_dotProduct_cons_init_eq_of_agrees`, `New.Filling.pairOccursInColumnsAt_succ_of_agree`, `New.Filling.exists_pairOccursInColumnsAt_top_of_meetsAt` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* For part 1, lift $x$, $y$ and $m$ to integral adeles that vanish at the other places above $M$. It suffices that $M$ divides the difference $\Delta$ of the lifts. As $\hat{\mathcal{O}}$ is self dual for the character, it suffices that $\psi(M^{-1}r\Delta) = 1$ for every integral $r$. The lemma on Eichler maps gives $u$ along $x$ with the form $m$ and $u'$ along $y$ with the form $m\gamma$. Modulo the place, $u\gamma = \gamma + r(fx)(m\gamma) = \gamma u'$. Modulo the other places, both are $1$. So $\bar u\bar k = \bar k\bar u'$, and agreement gives $\chi(u) = \chi(u')$, which is $\psi(M^{-1}r\Delta) = 1$. Part 2 follows from part 1 by duality and the shift lemma, as in the rational case. For part 3, take a shared vector, its top index $j$, and climb from $j$ to the top by part 2. $\square$

**Theorem (The meet norm and an index).** Let $k \in K$ with agreeing reduction.

1. Let $\delta$ be integral with $\bar\delta$ a unit in the finite adeles, and let $\delta$ vanish modulo each place above $M$ where $k$ meets. Then $\operatorname{meetNorm}(\bar k) \leq [\hat{\mathcal{O}} : \bar\delta\hat{\mathcal{O}}]$.
2. Let $t$ be an integral matrix with two columns and $P = (f \mid kf)^*t$. Suppose all rows of $P$ vanish except the two at the top of $f$ and of $kf$, and that the determinant $d$ of these two rows is a unit of the finite adeles. Then $d$ vanishes modulo each meeting place, and $\operatorname{meetNorm}(\bar k) \leq \operatorname{genIndex}(d)$.

Lean: `New.Filling.meetNorm_le_genIndex_star`, `New.Filling.reduceAboveM_det_eq_zero_of_meetsAt`, `New.Filling.meetNorm_le_genIndex_det` (New/Spanning/Unfolding/Climbing.lean).

*Proof.* For part 1, the index is the order of $\hat{\mathcal{O}}/\delta$. Reduction maps $\hat{\mathcal{O}}$ onto the product of the residue fields at the meeting places, by the Chinese remainder theorem, and kills $\delta$. So the order of the product, which is the meet norm, is at most the index. For part 2, take a pair not both $0$ that occurs at the top modulo a meeting place, with $fx = \bar kfy$. Then $P^*$ kills $(x, -y)$ there. Only the two top columns of $P^*$ are nonzero. If $d$ did not vanish there, then $x_\varrho = y_\varrho = 0$, which is false. So part 1 applies to $d$. $\square$

**Remark (Formalization).** `genIndex` is a multiplicative character that is $0$ on elements that are not units. The unit hypotheses of the last theorem are what make the bound true and not a junk inequality. The chosen lifts and representatives in the proofs do not appear in the statements.
