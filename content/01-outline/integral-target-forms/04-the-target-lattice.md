---
title: The target lattice
lean:
  - New/Reduction/IntegralTargetForms.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
  - New/UpperBound/Objects/LiftChains.lean
  - New/Reduction/Lattices/TwistedLattice.lean
decls:
  - New.LevelPlaces.LevelForm.integralForms
  - New.PrimePadicIso.norm_place
  - New.gramForm_mem_embValRing
  - New.LevelPlaces.LevelForm.inner_eq_stdClassSum
  - New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one
  - New.Data.classAut_eq_bot_of_le_levelOf_chosenPlace
  - New.Data.classAut_eq_bot_of_le_chosenLevel
  - New.Data.levelOf_lastResidueLevel_le_chosenLevel
  - New.Data.classAut_lastResidueLevel_eq_bot
  - New.Data.targetLattice
  - New.Data.mem_integralVectors_targetLattice
  - New.LevelPlaces.LevelForm.inner_eq_valueCoord
  - New.LevelPlaces.LevelForm.normSqAt_eq_re_valueCoord
  - New.Data.normSqAt_targetLattice
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The target lattice

A twisted lattice in the sense of [twisted lattices](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume) has a map $\Theta_\xi$ for each twist, a relation "$\xi$ is allowed at $\ell$", modules of integral vectors, coordinates with a rational Gram matrix for the trivial twist, and two axioms. The first axiom says that integral vectors at $\bar\iota$ and at $\iota$ pair integrally at $\iota$, for allowed twists. The second says that the coordinates compute the inner product. This section supplies the parts for the maps $\Theta_\vartheta$ of Section 3 and proves the two axioms.

### Integral forms

Fix a prime $\ell$ and an isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. The source turns $\iota$ into an embedding $\mathbb{C} \to \mathbb{C}_\ell$, the *place* of $\iota$, by composition with the inclusion $\bar{\mathbb{Q}}_\ell \subset \mathbb{C}_\ell$ (`New.PrimePadicIso.place`).

**Lemma (The place has the same absolute value).** For every $x \in \mathbb{C}$, the absolute value of the image of $x$ under the place of $\iota$ equals $|\iota(x)|$.

Lean: `New.PrimePadicIso.norm_place` (New/Reduction/Lattices/TwistedLattice.lean).

Let $\varphi$ be a form of a level on the standard definite space of rank $n$, with values in the Weyl module of weight $(\kappa, e)$. For $g \in G_f$ and a value $\xi = \varphi(g)$, the *gauge* of $\xi$ at $g$ is the largest $\ell$-adic absolute value of a coordinate of $g^{-1} \cdot \iota(\xi)$. Here $g^{-1}$ acts in the weight $(\kappa, e)$ through its components at the places above $\ell$, read in $\mathbb{C}_\ell$ by the place of $\iota$ (`New.weylGauge`).

**Definition (Integral forms).** The forms integral at $\iota$ are the forms $\varphi$ such that the gauge of $\varphi(g)$ at $g$ is at most $1$ for every $g \in G_f$. They form a module over the valuation ring of $\iota$.

Lean: `New.LevelPlaces.LevelForm.integralForms` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

The source tests the condition at every $g \in G_f$, not only at the representatives of the classes.

### The pairing of two integral values

The Weyl module has a Gram matrix $G$ with integer entries, positive definite, such that the matrix of $a$ and the matrix of its transpose are adjoint for $G$: $G\rho(a) = \rho(a^{\mathsf{T}})^{\mathsf{T}} G$ (`New.weylGramOver_mul_weylRep`). The Gram pairing of two values is $\langle u, v \rangle_G = \bar u^{\mathsf{T}} G v$ (`New.gramForm`).

**Lemma (Integral values pair integrally).** Let $u$ have gauge at most $1$ at $g$ for the place of $\bar\iota$, and $v$ have gauge at most $1$ at $g$ for the place of $\iota$. Then $\langle u, v \rangle_G$ lies in the valuation ring of $\iota$.

Lean: `New.gramForm_mem_embValRing` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Let $a$ be the family of the components of $g$ at the embeddings that $\iota$ induces. Since $g$ is unitary, the components of $g^{-1}$ at the embeddings induced by $\bar\iota$ are the transposes (`New.map_inv_weightEmbedding_comp_conj`). Put
$$x = \rho(a^{\mathsf{T}})\, \bar\iota(u), \qquad y = \rho(a)^{-1}\, \iota(v).$$
By the hypotheses, $x$ and $y$ have integral coordinates. By the adjointness of $G$,
$$x^{\mathsf{T}} G\, y = \bar\iota(u)^{\mathsf{T}}\, \rho(a^{\mathsf{T}})^{\mathsf{T}} G\, \rho(a)^{-1}\, \iota(v) = \bar\iota(u)^{\mathsf{T}}\, G \rho(a) \rho(a)^{-1}\, \iota(v) = \bar\iota(u)^{\mathsf{T}} G\, \iota(v).$$
The right side is the image of $\langle u, v\rangle_G$ under the place of $\iota$, since $G$ has integer entries, and the left side is integral. $\square$

### The inner product as a class sum

**Lemma (The inner product is a class sum).** For two forms $\varphi, \varphi'$ of level $K_H$,
$$\langle \varphi, \varphi' \rangle = \sum_{c \in \Gamma\backslash G_f / K_H} \frac{\langle \varphi(g_c), \varphi'(g_c) \rangle_G}{\#\Gamma_{g_c}},$$
where $\Gamma$ is the group of rational points and $\Gamma_g = \Gamma \cap g K_H g^{-1}$.

Lean: `New.LevelPlaces.LevelForm.inner_eq_stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Remark (Formalization).** The source defines the inner product on forms of a level as the index of the level in $K_0$ times an integral over $\Gamma \backslash G_f$ of the Gram pairing. The lemma above is a theorem in the source. The lattice uses only the class sum, so the normalization of the measure does not matter for it.

**Lemma (Integrality of the pairing).** Let $A$ be a natural number divisible by $\#\Gamma_g$ for every $g$. If $\varphi$ is integral at $\bar\iota$ and $\varphi'$ is integral at $\iota$, then $|\iota(A \langle\varphi, \varphi'\rangle)| \leq 1$.

Lean: `New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Write the inner product as the class sum. Each numerator $\langle \varphi(g_c), \varphi'(g_c) \rangle_G$ is integral at $\iota$ by the lemma on integral values. The number $A/\#\Gamma_{g_c}$ is an integer. So $A$ times the class sum is a finite sum of integral numbers. $\square$

With $A = 1$ it gives the first axiom of a twisted lattice, provided that all stabilisers are trivial.

### The stabilisers are trivial

The next results apply Minkowski's lemma of Section 2 to the data. There are $f$ chosen places above $p_i$, each of norm $p_i$, and $[E : \mathbb{Q}] = 2f$.

**Theorem (Trivial stabilisers at the chosen places above $p_i$).** Let $i \in \{0, 1\}$. Let $K$ be a subgroup of the integral points of $G_f$ on an index set of at most $4 n_m$ elements whose elements reduce to $1$ at the chosen places above $p_i$. Then for every $g$ the stabiliser $\Gamma \cap g K g^{-1}$ is trivial.

Lean: `New.Data.classAut_eq_bot_of_le_levelOf_chosenPlace` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* The lemma of Section 2 asks that $(2n)^{[E:\mathbb{Q}]}$ is less than the product of the norms of the places. Let $n$ be the size of the index set. Then
$$(2n)^{[E:\mathbb{Q}]} \leq \big((8 n_m)^2\big)^{f} < p_i^{f} = \prod_{w \text{ chosen above } p_i} q_w.$$
The first step uses $n \leq 4 n_m$, and the second uses $(8 n_m)^2 < p_i$, which follows from the sizes of the data. $\square$

The inequality $(8 n_m)^2 < p_i$ has much room, since $p_i \geq b^{10}$ by [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).

**Corollary (Trivial stabilisers in the chosen level).** Let $K$ be a subgroup of the chosen level, the integral elements that reduce to $1$ at every chosen place. If the index set has at most $2 n_m$ elements, then $\Gamma \cap g K g^{-1} = 1$ for every $g$.

Lean: `New.Data.classAut_eq_bot_of_le_chosenLevel` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* The chosen level lies in the group of elements that reduce to $1$ at the chosen places above $p_0$. Apply the theorem with $i = 0$, since $2 n_m \leq 4 n_m$. $\square$

**Lemma (The last level lies in the chosen level).** For every tame character $\vartheta$, the level $J_m(\vartheta)$ on $Y_m$ lies in the chosen level.

Lean: `New.Data.levelOf_lastResidueLevel_le_chosenLevel` (New/Reduction/IntegralTargetForms.lean).

*Proof.* An element of $J_m(\vartheta)$ is integral, and its reduction lies in the last residue level. The last residue level is $1$ at every chosen place. $\square$

**Corollary (The forms on $Y_m$ have trivial stabilisers).** For every tame character $\vartheta$ and every $g$, the stabiliser $\Gamma \cap g J_m(\vartheta) g^{-1}$ is trivial.

Lean: `New.Data.classAut_lastResidueLevel_eq_bot` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The rank of $Y_m$ is at most $n_m \leq 2 n_m$ by the lemma on ranks in Section 3. Apply the corollary on the chosen level with the last lemma. $\square$

**Remark (Formalization).** The places of $Q$ play no part here. The level at $Q$ is only block upper triangular, which is too large for Minkowski's lemma. The chosen places above $p_0$ alone make the stabilisers trivial, and this holds for every tame character at once. The factors $2$ and $4$ in the bounds on the index sets leave room for other uses of the same lemmas (New/OneLift/ComparisonOperator/GluingMaps.lean).

### The definition

**Definition (The target lattice).** The target lattice is the twisted lattice on $T$ with the $m$-fold twists as twists, and with these parts.

1. The space for $\vartheta$ is the space of forms on $Y_m$ with the level places of $\vartheta$, the last residue level, the last level character and the weight (`D.columnsY`, `D.lastEntry D.m`).
2. The map for $\vartheta$ is $\Theta_\vartheta$.
3. The twist $\vartheta$ is allowed at $\ell$ if $\ell$ is prime to $\mathrm{Nm}\,Q$.
4. The integral vectors at $\iota$ in the space for $\vartheta$ are the forms integral at the place of $\iota$.
5. The coordinates on the space for the trivial twist are the values $\varphi(g_c)$ at the representatives $g_c$ of the classes, in the standard basis of the Weyl module. The index set is the product of the set of classes and the basis of the Weyl module.
6. The Gram matrix in these coordinates is the block matrix $1 \otimes G$, one block $G$ for each class. It has rational entries, and it is positive definite (`New.LevelPlaces.LevelForm.posDef_valueMetric`).

Lean: `New.Data.targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof of the first axiom.* Let $\varphi$ be integral at $\bar\iota$ and $\varphi'$ integral at $\iota$, in the space for $\vartheta$. All stabilisers $\Gamma \cap g J_m(\vartheta) g^{-1}$ are trivial, so the lemma on the integrality of the pairing applies with $A = 1$. The lemma on the place turns its conclusion into $|\iota\langle\varphi, \varphi'\rangle| \leq 1$. $\square$

*Proof of the second axiom.* This is the next lemma on coordinates, for the trivial twist. $\square$

**Remark (Formalization).** The proof of the first axiom does not use the hypothesis that $\vartheta$ is allowed at $\ell$. The pairing is integral for every $m$-fold twist and every $\iota$. The relation "allowed" matters for the integral vectors, which are tested only through the allowed twists. The trivial twist is allowed at every prime.

### The integral vectors

**Lemma (Integral target forms).** A target form $y$ is an integral vector of the target lattice at $\iota \mid \ell$ if and only if $\Theta_\vartheta y$ is integral at the place of $\iota$ for every $m$-fold twist $\vartheta$ with $\mathrm{Nm}\,Q$ prime to $\ell$.

Lean: `New.Data.mem_integralVectors_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The integral vectors of a twisted lattice at $\iota$ are the $y$ such that $\Theta_\xi y$ is integral at $\iota$ for every twist $\xi$ allowed at the prime of $\iota$ (`New.TwistedLattice.mem_integralVectors`). Insert the parts of the definition. $\square$

There are infinitely many $m$-fold twists, so an integral target form satisfies infinitely many conditions at each $\iota$. The source does not claim that the integral vectors form a lattice of full rank in $T$, and the lower bound does not need this.

### Coordinates and norms

**Lemma (Coordinates of a form).** Let all stabilisers $\Gamma \cap g K_H g^{-1}$ be trivial. Then for two forms $\varphi, \varphi'$ of level $K_H$,
$$\langle \varphi, \varphi' \rangle = \overline{v(\varphi)}^{\mathsf{T}} (1 \otimes G)\, v(\varphi'),$$
where $v(\varphi)$ is the vector of the coordinates of the values $\varphi(g_c)$.

Lean: `New.LevelPlaces.LevelForm.inner_eq_valueCoord` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Each weight $1/\#\Gamma_{g_c}$ of the class sum is $1$. $\square$

For $\sigma \in \mathrm{Aut}(\mathbb{C})$, the squared norm $\|\varphi\|_\sigma^2$ of a form is the class sum of the squared Gram norms of the vectors $\sigma(\varphi(g))$ (`New.LevelPlaces.LevelForm.normSqAt`).

**Lemma (Conjugate norms in coordinates).** Let all stabilisers be trivial. Then $\|\varphi\|_\sigma^2$ is the real part of $\overline{\sigma v(\varphi)}^{\mathsf{T}} (1 \otimes G)\, \sigma v(\varphi)$, where $\sigma v(\varphi)$ is the vector $v(\varphi)$ with $\sigma$ applied to each entry.

Lean: `New.LevelPlaces.LevelForm.normSqAt_eq_re_valueCoord` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

In a twisted lattice the squared norm of $y$ at $\sigma$ is defined by the rational Gram matrix on the conjugated coordinates of $\Theta_1 y$. For the target lattice this is the conjugate norm of the lift.

**Lemma (Norms in the target lattice).** For every target form $y$ and every $\sigma \in \mathrm{Aut}(\mathbb{C})$, the squared norm of $y$ at $\sigma$ in the target lattice equals $\|\Theta_1 y\|_\sigma^2$.

Lean: `New.Data.normSqAt_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* Apply the lemma on conjugate norms to $\varphi = \Theta_1 y$. Its hypothesis holds by the corollary on the stabilisers of the forms on $Y_m$. $\square$

**Remark (Formalization).** The coordinates use a representative $g_c$ of each class, which the source takes by `Quot.out`. So the coordinate map depends on an arbitrary choice. The inner product and the conjugate norms do not, since they are class sums of functions that are invariant under the level. The Gram matrix $1 \otimes G$ is declared rational, and in fact it has integer entries. Only the target for the trivial twist has coordinates.
