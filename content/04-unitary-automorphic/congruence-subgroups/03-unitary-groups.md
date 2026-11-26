---
title: Unitary groups as topological groups
lean:
  - Lib/General/Groups/CongruenceSubgroups.lean
decls:
  - New.U.coe_inv
  - New.U.form_mulVec_mulVec
  - New.U.map
  - New.U.mem_range_map
  - New.U.conj
  - New.U.det
  - New.isClosed_U
  - New.U.isClosedEmbedding_coe
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Unitary groups as topological groups

This section proves the facts about the unitary group $\mathrm{U}(J)$ of a matrix that the rest of the source uses without comment. The group is functorial in the ring, it changes by conjugation when the form changes by a change of basis, it has a determinant with values in the norm one elements, and it is a closed subgroup of the matrices. The last fact has one consequence that matters for integration: the complex unitary group of a definite form is compact, so its Haar measure is finite and every continuous function on it is integrable.

### The group and its inverse

Let $R$ be a commutative ring with an involution $x \mapsto \bar x$, and let $J$ be an $n \times n$ matrix over $R$. Write $g^* = \bar g^{\,t}$. The [unitary group](/decl/New.U/) is
$$\mathrm{U}(J) = \{ g \in \mathrm{GL}_n(R) : g^* J g = J \}.$$
The source does not ask $J$ to be hermitian or invertible in the definition. It adds these conditions in the lemmas that need them. For a family of signs $\varepsilon$, the group of the sign matrix $\mathrm{diag}(\varepsilon)$ is written [$\mathrm{U}_\varepsilon$](/decl/New.USign/).

In a unitary group the inverse is given by a formula, and this formula is the source of all the topological facts below.

**Lemma.** Let $g \in \mathrm{U}(J)$. Then $J g^{-1} = g^* J$. If $J^2 = 1$, then $g^{-1} = J g^* J$. In particular, if $J = 1$, then $g^{-1} = g^*$.

Lean: `New.U.coe_inv` (Lib/General/Groups/CongruenceSubgroups.lean). The first identity is `New.U.form_mul_inv_eq` and the case $J = 1$ is `New.U.inv_val_eq_conjTranspose`.

*Proof.* Multiply $g^* J g = J$ on the right by $g^{-1}$. This gives $g^* J = J g^{-1}$. If $J^2 = 1$, multiply on the left by $J$. $\square$

**Lemma.** Let $g \in \mathrm{U}(J)$ and let $x, y \in R^n$. Then $(gx)^* J (gy) = x^* J y$.

Lean: `New.U.form_mulVec_mulVec` (Lib/General/Groups/CongruenceSubgroups.lean). The form with matrices in place of vectors is `New.U.gram_invariant`.

*Proof.* The left side is $x^* (g^* J g) y$. $\square$

So $\mathrm{U}(J)$ is the isometry group of the sesquilinear form $h(x, y) = x^* J y$ on $R^n$. When $J$ is hermitian, $h$ is a hermitian form in the sense of [the hermitian spaces](/chapter/adeles-hermitian-spaces/).

### Change of ring and change of form

**Definition (Change of ring).** Let $f : R \to S$ be a ring homomorphism with $f(\bar x) = \overline{f(x)}$ for all $x$, and let $J'$ be the matrix $f(J)$ over $S$. The homomorphism $\mathrm{U}(J) \to \mathrm{U}(J')$ applies $f$ to each entry.

Lean: `New.U.map` (Lib/General/Groups/CongruenceSubgroups.lean). It is continuous if $f$ is (`New.U.continuous_map`).

The image of $g$ lies in $\mathrm{U}(J')$ because $f(g)^* f(J) f(g) = f(g^* J g) = f(J)$. The model case is the inclusion of a CM field $E$ into its completion $E_v$, or into the adeles. The next lemma says when an element of the larger group comes from the smaller one.

**Lemma.** Let $f : R \to S$ be an injective ring homomorphism that commutes with the involutions. Let $J$ be invertible over $R$, and let $J' = f(J)$. Let $g \in \mathrm{U}(J')$, and let $M$ be a matrix over $R$ with $f(M) = g$. Then there is $k \in \mathrm{U}(J)$ with matrix $M$ whose image is $g$.

Lean: `New.U.mem_range_map` (Lib/General/Groups/CongruenceSubgroups.lean). The element of $\mathrm{U}(J)$ with a given matrix is `New.U.of`.

*Proof.* The matrices $f(M^* J M)$ and $f(J)$ are both $g^* J' g = J'$. Since $f$ is injective, $M^* J M = J$. Then $\det(M^*) \det J \det M = \det J$, and $\det J$ is a unit. So $\det M$ is a unit, $M$ is invertible, and $M \in \mathrm{U}(J)$. $\square$

The hypothesis that $J$ is invertible is used only to see that $M$ is invertible. Without it, a matrix with $M^* J M = J$ need not be invertible: take $J = 0$.

**Definition (Change of form).** Let $x \in \mathrm{GL}_n(R)$ with $x^* J x = J'$. The isomorphism $\mathrm{U}(J') \to \mathrm{U}(J)$ is $g \mapsto x g x^{-1}$.

Lean: `New.U.conj` (Lib/General/Groups/CongruenceSubgroups.lean).

The map is well defined: for $g \in \mathrm{U}(J')$,
$$(x g x^{-1})^* J (x g x^{-1}) = (x^{-1})^* g^* (x^* J x) g x^{-1} = (x^{-1})^* (g^* J' g) x^{-1} = (x^{-1})^* J' x^{-1} = J.$$
The inverse map is $g \mapsto x^{-1} g x$. So isometric forms have isomorphic unitary groups, and the source can move between a Gram matrix adapted to a Witt decomposition and a diagonal one.

### The determinant

Let $\mathrm{U}_1(R) = \{ u \in R : \bar u u = 1 \}$ be the group of norm one elements.

**Definition (Determinant).** Let $\det J$ be a unit of $R$. The determinant is the homomorphism $\mathrm{U}(J) \to \mathrm{U}_1(R)$, $g \mapsto \det g$.

Lean: `New.U.det` (Lib/General/Groups/CongruenceSubgroups.lean).

The value lies in $\mathrm{U}_1(R)$. Take determinants in $g^* J g = J$. This gives $\overline{\det g} \det J \det g = \det J$. Since $\det J$ is a unit, $\overline{\det g}\det g = 1$. The kernel is the special unitary group. For $R = \mathbb{C}$ and $J = 1$, the determinant maps $\mathrm{U}(n)$ onto the circle.

### Closedness and compactness

Let $R$ be a topological ring with a continuous involution. The group $\mathrm{GL}_n(R)$ carries the topology of units: the coarsest topology for which $g \mapsto g$ and $g \mapsto g^{-1}$ are continuous maps to the matrices. In general this topology is finer than the topology of a subspace of the matrices. For the finite adeles and $n = 1$, the units $\mathbb{A}_f^\times$ carry the restricted product topology, and inversion is not continuous for the subspace topology. For unitary groups the two topologies agree, because the inverse is a continuous function of the matrix.

**Lemma.** Let $R$ be a Hausdorff topological commutative ring with a continuous involution. Then $\mathrm{U}(J)$ is closed in $\mathrm{GL}_n(R)$.

Lean: `New.isClosed_U` (Lib/General/Groups/CongruenceSubgroups.lean).

*Proof.* The map $g \mapsto g^* J g$ is continuous on $\mathrm{GL}_n(R)$, and $R$ is Hausdorff. So the set where it equals the constant $J$ is closed. $\square$

**Lemma.** Let $R$ be as in the last lemma, and let $J$ be an invertible matrix. Then the map $\mathrm{U}(J) \to M_n(R)$, $g \mapsto g$, is a closed embedding.

Lean: `New.U.isClosedEmbedding_coe` (Lib/General/Groups/CongruenceSubgroups.lean).

*Proof.* The map $\mathrm{GL}_n(R) \to M_n(R) \times M_n(R)^{\mathrm{op}}$, $g \mapsto (g, g^{-1})$, is a closed embedding. This is the definition of the topology of units, and its image is the closed set of pairs with product $1$. Restrict it to the closed subgroup $\mathrm{U}(J)$. On $\mathrm{U}(J)$ the second coordinate is $J^{-1} g^* J$ by the first lemma, a continuous function of $g$. So the map $g \mapsto (g, g^{-1})$ factors as $g \mapsto g$ followed by the graph $M \mapsto (M, J^{-1} M^* J)$ of a continuous function, which is an embedding. A map whose composite with an embedding is a closed embedding is itself a closed embedding. $\square$

**Proposition.** The complex unitary group $\mathrm{U}(1) = \mathrm{U}(n)$ is compact. So is the group $\mathrm{U}_\varepsilon$ of the sign matrix with all signs $+1$.

Lean: two anonymous instances in Lib/General/Groups/CongruenceSubgroups.lean, proved from `New.U.isClosedEmbedding_coe` and `New.U_one_mem_unitaryGroup`.

*Proof.* Let $g \in \mathrm{U}(1)$. Then $g^* g = 1$, so each column of $g$ is a unit vector, and every entry has absolute value at most $1$. So $\mathrm{U}(1)$ is the preimage, under the closed embedding of the last lemma, of the compact set of matrices with entries in the closed unit disc. A closed embedding is proper, so the preimage of a compact set is compact. The sign matrix with all signs $+1$ is the identity matrix. $\square$

The source also gives $\mathrm{U}(J)$ the structures that integration needs. If $R$ is locally compact, so is $\mathrm{U}(J)$, as a closed subset of a locally compact space. If $R$ is Polish, so is $\mathrm{U}(J)$. A subgroup cut out by asking some entries to equal those of the identity is [closed](/decl/New.isClosed_of_entries_eq_one/).

**Remark (Formalization).** The source makes these structures global instances. The file declares, for every ring of the right kind, a Polish structure on the units, the product measurable structure and the product measure on matrices, the Borel structure on units, and the Polish, locally compact and compact structures on unitary groups. A global instance applies in every file that imports this one. Mathlib also has instances on matrices, and two instances for one structure can differ. The research notes of this book list these instances among the points to check. The question whether a global instance creates such a diamond is open (Q-62 of [the register of findings](/chapter/register-of-findings/)). The row F-023 of the register lists global instances of other files, and not these. No instance adds an axiom. An instance can only decide which of two structures a later statement means. For the measure on matrices the product measure is the natural choice, and the source proves that it is an additive Haar measure (`New.isAddHaarMeasure_pi`).
