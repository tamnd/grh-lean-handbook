---
title: Hilbert-Schmidt norms and near isometries
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
decls:
  - New.hilbertSchmidtVector
  - New.hilbertSchmidtNorm
  - New.inner_hilbertSchmidtVector
  - New.hilbertSchmidtNorm_sq_eq_sum
  - New.hilbertSchmidtNorm_le_of_norm_le
  - New.orthoProj
  - New.hilbertSchmidtNorm_orthoProj_sq
  - New.hilbertSchmidtNorm_comp_orthoProj_le
  - New.hilbertSchmidtNorm_orthoProj_comp_sq
  - New.IsNearIsometry
  - New.isNearIsometry_of_hilbertSchmidtNorm_le
  - New.IsNearIsometry.mono
  - New.IsNearIsometry.finrank_range_pos
  - New.IsNearIsometry.proj_comp
  - New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hilbert-Schmidt norms and near isometries

This section defines the Hilbert-Schmidt norm in the form that the source uses, and the near isometry in mean square. It proves the rules of computation that the next two sections need, and three rules that [the chapter on moments](/chapter/moments/) uses to show that the good part $e_0P$ of the scaled Poincaré map is a near isometry with the error $5b^{-4}$. Throughout, $S$, $T$ and $T'$ are finite-dimensional complex inner product spaces. The inner product is linear in the second argument and conjugate-linear in the first, as in Mathlib.

### The Hilbert-Schmidt norm

For a linear map $A : S \to T$ the Hilbert-Schmidt norm is $\|A\| = \operatorname{tr}(A^*A)^{1/2}$. The source defines it through one vector, so that the Cauchy-Schwarz inequality for maps is the Cauchy-Schwarz inequality of a Hilbert space.

**Definition (Hilbert-Schmidt vector).** Let $(b_i)_{i < \dim S}$ be the standard orthonormal basis of $S$, a basis fixed once for all. The *Hilbert-Schmidt vector* of $A : S \to T$ is the vector $(A b_i)_i$ of the orthogonal sum $\bigoplus_{i < \dim S} T$. The map $A \mapsto (Ab_i)_i$ is linear.

Lean: `New.hilbertSchmidtVector` (New/Spanning/SecondMoment/FewTranslates.lean).

**Definition (Hilbert-Schmidt norm).** The *Hilbert-Schmidt norm* $\|A\|$ of $A : S \to T$ is the norm of its Hilbert-Schmidt vector, $\|A\|^2 = \sum_i \|Ab_i\|^2$.

Lean: `New.hilbertSchmidtNorm`, `New.hilbertSchmidtNorm_nonneg` (New/Spanning/SecondMoment/FewTranslates.lean).

In this chapter $\|A\|$ always means the Hilbert-Schmidt norm of a map. The operator norm, where it appears, is written $\|A\|_{\mathrm{op}}$.

**Lemma (The trace form).** For $A, B : S \to T$, the inner product of the Hilbert-Schmidt vectors of $A$ and $B$ is $\operatorname{tr}(A^*B)$. In particular $\|A\|^2 = \operatorname{tr}(A^*A)$.

Lean: `New.inner_hilbertSchmidtVector`, `New.hilbertSchmidtNorm_sq_eq_trace` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* The trace of an operator $X$ on $S$ is $\sum_i \langle b_i, Xb_i\rangle$ for any orthonormal basis. Take $X = A^*B$: $\langle b_i, A^*Bb_i\rangle = \langle Ab_i, Bb_i\rangle$, and the sum over $i$ is the inner product in $\bigoplus_i T$. $\square$

We write $\langle A, B\rangle_{\mathrm{HS}} = \operatorname{tr}(A^*B)$ for this inner product of maps.

**Lemma (Independence of the basis).** For every orthonormal basis $(e_i)$ of $S$, $\|A\|^2 = \sum_i\|Ae_i\|^2$. For orthonormal bases $(e_i)$ of $S$ and $(f_j)$ of $T$, $\|A\|^2 = \sum_{i, j}|\langle Ae_i, f_j\rangle|^2$. The adjoint has the same norm: $\|A^*\| = \|A\|$.

Lean: `New.hilbertSchmidtNorm_sq_eq_sum`, `New.hilbertSchmidtNorm_sq_eq_sum_entries`, `New.hilbertSchmidtNorm_adjoint` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* The trace does not depend on the basis, so the trace form gives the first formula. Expand $\|Ae_i\|^2$ in the basis $(f_j)$ for the second. For the third, $\operatorname{tr}(AA^*) = \operatorname{tr}(A^*A)$. $\square$

**Remark (Formalization).** The Hilbert-Schmidt vector depends on the basis that Mathlib fixes for $S$, and a different basis gives a different vector. Its norm, and the inner product of two such vectors, do not depend on the basis, by the two lemmas above. Every statement of this volume uses only the norm and the inner product. So the choice has no effect on any statement.

**Lemma (Comparison).** Let $A : S \to T$ and $B : S \to T'$ with $\|Ax\| \leq \|Bx\|$ for all $x \in S$. Then $\|A\| \leq \|B\|$.

Lean: `New.hilbertSchmidtNorm_le_of_norm_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Compare $\sum_i\|Ab_i\|^2$ and $\sum_i\|Bb_i\|^2$ term by term. $\square$

The two maps may have different targets. This is used below when one side is a map into $T$ and the other a map into a subspace.

### Orthogonal projections

**Definition (Orthogonal projection).** For a subspace $U$ of $S$, $\mathrm{pr}_U : S \to S$ is the orthogonal projection onto $U$, as a linear map of $S$ to itself.

Lean: `New.orthoProj`, `New.adjoint_orthoProj`, `New.orthoProj_comp_self` (New/Spanning/SecondMoment/FewTranslates.lean).

The projection is self-adjoint and idempotent. A linear map $p$ of $S$ with $p^2 = p$ and $p^* = p$ is called a *symmetric projection*. It is the orthogonal projection onto its range. For a symmetric projection $p$ and every $y$, the vectors $py$ and $(1 - p)y$ are orthogonal, so $\|y\|^2 = \|py\|^2 + \|(1 - p)y\|^2$ (`New.norm_sq_eq_add_of_isSymmetricProjection`).

**Lemma (Projections and norms).** Let $U \subseteq S$ and $W \subseteq T$ be subspaces, and let $A : S \to T$.

1. $\|\mathrm{pr}_U\|^2 = \dim U$.
2. $\|A\,\mathrm{pr}_U\| \leq \|A\|$.
3. $\|\mathrm{pr}_W A\|^2 = \operatorname{Re}\langle \mathrm{pr}_W, AA^*\rangle_{\mathrm{HS}}$.

Lean: `New.hilbertSchmidtNorm_orthoProj_sq`, `New.hilbertSchmidtNorm_comp_orthoProj_le`, `New.hilbertSchmidtNorm_orthoProj_comp_sq` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* (1) $\|\mathrm{pr}_U\|^2 = \operatorname{tr}(\mathrm{pr}_U^*\mathrm{pr}_U) = \operatorname{tr}(\mathrm{pr}_U)$, and the trace of a projection is the dimension of its range. (2) Pass to adjoints: $\|A\,\mathrm{pr}_U\| = \|\mathrm{pr}_U A^*\|$, and $\|\mathrm{pr}_U A^*x\| \leq \|A^*x\|$ for every $x$, so the comparison lemma applies. (3) $\|\mathrm{pr}_W A\|^2 = \operatorname{tr}(A^*\mathrm{pr}_W A) = \operatorname{tr}(\mathrm{pr}_W AA^*) = \langle\mathrm{pr}_W, AA^*\rangle_{\mathrm{HS}}$, since $\mathrm{pr}_W^* = \mathrm{pr}_W = \mathrm{pr}_W^2$. The value is real, so it equals its real part. $\square$

Formula (3) is the key to the next section. It turns the norm of $\mathrm{pr}_W A$, which is quadratic in $A$, into a pairing of $\mathrm{pr}_W$ with $AA^*$, which is linear in $AA^*$. A sum over translates of $A$ then becomes one pairing with a sum.

### The near isometry in mean square

**Definition (Near isometry in mean square).** Let $A : S \to T$ and $\varepsilon \in \mathbb{R}$. The map $A$ is a *near isometry with the error* $\varepsilon$ if for every subspace $U$ of $S$

$$\dim U - \varepsilon\dim S \leq \|A\,\mathrm{pr}_U\|^2.$$

Lean: `New.IsNearIsometry` (New/Spanning/SecondMoment/FewTranslates.lean).

For an isometry, $\|A\,\mathrm{pr}_U\|^2 = \|\mathrm{pr}_U\|^2 = \dim U$, so it is a near isometry with the error $0$. The definition allows any real $\varepsilon$. For $S \neq 0$ the subspace $U = 0$ gives $-\varepsilon\dim S \leq 0$, so a near isometry has $\varepsilon \geq 0$. The source uses only $\varepsilon \geq 0$.

The word "near isometry" usually means a bound $(1 - \delta)\|x\| \leq \|Ax\| \leq (1 + \delta)\|x\|$ for all $x$, as in the theory of restricted isometries. The notion of the source is different in two ways. It is a lower bound only. It is also an average over the dimensions, not a bound for each vector. The next remark makes this exact.

**Remark (The near isometry and the singular values).** Let $\sigma_1^2, \dots, \sigma_{\dim S}^2$ be the eigenvalues of $A^*A$, with orthonormal eigenvectors $v_1, \dots, v_{\dim S}$. Then $A$ is a near isometry with the error $\varepsilon$ if and only if

$$\sum_{i}\max(0,\ 1 - \sigma_i^2) \leq \varepsilon\dim S.$$

*Proof.* Put $M = 1 - A^*A$, a self-adjoint operator with eigenvalues $\mu_i = 1 - \sigma_i^2$. For a subspace $U$, $\dim U - \|A\,\mathrm{pr}_U\|^2 = \operatorname{tr}(\mathrm{pr}_U M\,\mathrm{pr}_U) = \sum_i \mu_i\|\mathrm{pr}_U v_i\|^2$. As $0 \leq \|\mathrm{pr}_U v_i\|^2 \leq 1$, this is at most $\sum_i\max(0, \mu_i)$. The span of the $v_i$ with $\mu_i > 0$ attains this value. So the supremum over $U$ of $\dim U - \|A\,\mathrm{pr}_U\|^2$ is $\sum_i\max(0, \mu_i)$. This is Ky Fan's maximum principle for the sum of the positive eigenvalues. $\square$

So the near isometry with the error $\varepsilon$ says that the singular values of $A$ below $1$ have a total deficit of at most $\varepsilon\dim S$. It has three consequences.

1. A lower bound $\|Ax\|^2 \geq (1 - \delta)\|x\|^2$ for all $x$ gives the near isometry with the error $\delta$. The converse fails: the error $\varepsilon$ allows a kernel of dimension up to $\varepsilon\dim S$.
2. The kernel of $A$ has dimension at most $\varepsilon\dim S$. Take $U = \ker A$.
3. The singular values above $1$ do not count. A map with a large norm is a near isometry if it is large on almost all directions.

**Remark (Formalization).** Finding F-059 of the register asks for a comparison with the operator notion. The remark above gives it. The spread argument of the next section uses the definition on one subspace only, the preimage $U$ of a subspace $W$ of the target, and it needs exactly a lower bound for $\dim U$ in terms of $\|A\,\mathrm{pr}_U\|^2$. A bound in the operator norm would give this, but the source cannot prove one for the Poincaré map. Its bound for the identity terms is $\|P^*P - 1\|^2 \leq b^{-12}\dim S$ in the Hilbert-Schmidt norm ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le/)). This gives only $\|P^*P - 1\|_{\mathrm{op}} \leq b^{-6}(\dim S)^{1/2}$, which is large. The mean square notion is the one that this bound controls.

### Rules for near isometries

**Lemma (From a defect in Hilbert-Schmidt norm).** Let $\varepsilon \geq 0$ and $A : S \to T$ with $\|A^*A - 1\|^2 \leq \varepsilon^2\dim S$. Then $A$ is a near isometry with the error $\varepsilon$.

Lean: `New.isNearIsometry_of_hilbertSchmidtNorm_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $U \subseteq S$ and $p = \mathrm{pr}_U$. By the lemma on projections, applied to $A^*$ with $p^* = p$, $\|Ap\|^2 = \operatorname{Re}\langle p, A^*A\rangle_{\mathrm{HS}}$, and in the same way $\dim U = \operatorname{Re}\langle p, 1\rangle_{\mathrm{HS}}$. So

$$\|Ap\|^2 - \dim U = \operatorname{Re}\langle p, A^*A - 1\rangle_{\mathrm{HS}} \geq -\|p\|\,\|A^*A - 1\| \geq -(\dim S)^{1/2}\cdot\varepsilon(\dim S)^{1/2},$$

by the Cauchy-Schwarz inequality and $\|p\|^2 = \dim U \leq \dim S$. $\square$

The loss is from $\varepsilon^2$ to $\varepsilon$. In the source, $\|P^*P - 1\|^2 \leq b^{-12}\dim S \leq (b^{-4})^2\dim S$, so $P$ is a near isometry with the error $b^{-4}$. The bound $b^{-12}$ is stronger than this use needs.

**Lemma (Monotonicity).** A near isometry with the error $\varepsilon$ is a near isometry with every error $\varepsilon' \geq \varepsilon$.

Lean: `New.IsNearIsometry.mono` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* $\dim U - \varepsilon'\dim S \leq \dim U - \varepsilon\dim S$. $\square$

**Lemma (The range is not zero).** Let $S \neq 0$, let $\mathrm{pr}_0$ be any linear map of $T$ to itself, and let $B : S \to T$. If $\mathrm{pr}_0B$ is a near isometry with an error $\varepsilon < 1$, then $\dim\mathrm{range}(\mathrm{pr}_0) > 0$.

Lean: `New.IsNearIsometry.finrank_range_pos` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* If the range is $0$, then $\mathrm{pr}_0 = 0$, and the definition with $U = S$ reads $(1 - \varepsilon)\dim S \leq 0$. This is false for $\dim S > 0$ and $\varepsilon < 1$. $\square$

This lemma gives $d_T > 0$ in Theorem B ([Theorem](/decl/New.Data.finrank_targetForms_ne_zero/)). The map $\mathrm{pr}_0$ need not be a projection here.

**Lemma (Composition with a projection).** Let $A : S \to T$ be a near isometry with the error $\varepsilon$, and let $\mathrm{pr}$ be a symmetric projection of $T$ with $\|(1 - \mathrm{pr})A\|^2 \leq \delta\dim S$. Then $\mathrm{pr}\,A$ is a near isometry with the error $\varepsilon + \delta$.

Lean: `New.IsNearIsometry.proj_comp` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $U \subseteq S$. Apply $\|y\|^2 = \|\mathrm{pr}\,y\|^2 + \|(1 - \mathrm{pr})y\|^2$ to $y = A\,\mathrm{pr}_U b_i$ and sum over $i$:

$$\|A\,\mathrm{pr}_U\|^2 = \|\mathrm{pr}\,A\,\mathrm{pr}_U\|^2 + \|(1 - \mathrm{pr})A\,\mathrm{pr}_U\|^2.$$

The last term is at most $\|(1 - \mathrm{pr})A\|^2 \leq \delta\dim S$, by the lemma on projections. The first side is at least $\dim U - \varepsilon\dim S$. $\square$

**Lemma (Two projections).** Let $p$ be a symmetric projection of $T$, let $q$ be any linear map of $T$ to itself, and let $A : S \to T$. Then

$$\|(1 - pq)A\|^2 \leq \|(1 - p)A\|^2 + \|(1 - q)A\|^2.$$

Lean: `New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* It is enough to prove $\|(1 - pq)y\|^2 \leq \|(1 - p)y\|^2 + \|(1 - q)y\|^2$ for each vector $y = Ab_i$, and then to sum over $i$. Since $p^2 = p$, $p(1 - pq) = p(1 - q)$ and $(1 - p)(1 - pq) = 1 - p$. So the orthogonal splitting by $p$ gives

$$\|(1 - pq)y\|^2 = \|p(1 - q)y\|^2 + \|(1 - p)y\|^2 \leq \|(1 - q)y\|^2 + \|(1 - p)y\|^2,$$

since $p$ does not increase norms. $\square$

The two rules give the near isometry of the good part. In the source, $e_0$ acts as the product $e_{p_0}e_{p_1}$ of two commuting symmetric projections, one for each level prime. [The chapter on moments](/chapter/moments/) proves $\|(1 - e_{p_i})P\|^2 \leq 2b^{-4}\dim S$ for $i = 0, 1$ from [the rarity of bad types](/decl/New.Data.bad_types_rare/). By the rule for two projections, $\|(1 - e_0)P\|^2 \leq 4b^{-4}\dim S$. By the rule for composition, $e_0P$ is a near isometry with the error $b^{-4} + 4b^{-4} = 5b^{-4}$. This is [the theorem on good forms](/decl/New.Data.isNearIsometry_e₀_comp_scaledPoincare/).

**Example.** Let $S = T = \mathbb{C}^2$, let $A$ be the projection onto the first coordinate, and $U = S$. Then $\|A\,\mathrm{pr}_U\|^2 = 1 = \dim U - \frac{1}{2}\dim S$. On a line $U$ at the angle $\theta$ to the first axis, $\|A\,\mathrm{pr}_U\|^2 = \cos^2\theta \geq 1 - \frac{1}{2}\cdot 2$. So $A$ is a near isometry with the error $\frac{1}{2}$, and with no smaller error, in agreement with the remark on singular values: the deficits are $0$ and $1$, with sum $1 = \frac{1}{2}\dim S$. The map has a kernel, so it is not a near isometry for any $\delta < 1$ in the operator sense.
