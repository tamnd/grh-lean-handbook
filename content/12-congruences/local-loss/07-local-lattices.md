---
title: Local lattices
lean:
  - New/Congruences/LocalLoss/LocalLattices.lean
decls:
  - New.Selmer.isTameType_of_roots
  - New.Selmer.localLattice
  - New.Selmer.IsLatticeIn.exists_equivariant_embedding
  - New.Selmer.IsLatticeIn.isAdmissible_localLattice
  - New.Selmer.IsLatticeIn.isKilledBy_localLattice
  - New.Selmer.IsConjSelfDualOfLevel.eq_one_of_mem_inertiaAbove
  - New.Selmer.complexEmbeddingAt
  - New.Selmer.crystallinityFilter
  - New.Selmer.KillsAboveM
  - New.Selmer.jumpSetAt
  - New.Selmer.IsConjSelfDualOfLevel.hasJumps_localLattice
  - New.Selmer.IsConjSelfDualOfLevel.inClass_localLattice
  - New.Selmer.hasJumps_and_inClass_localLattice
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Local lattices

The main theorem of [Section 6](/chapter/local-loss/#the-defect-at-a-place-above) is a statement on lattices with an action of a local group $\Gamma$. The argument has global objects: an $\ell$-adic representation $R$ of the absolute Galois group $G_E$ of $E$, and a lattice $u : G_E \to M_n(O)$ in $R$. This section restricts $u$ to the decomposition group at a place $w$ of $E$ above $\ell$, and shows that the result lies in an explicit class $\mathrm{InClass}(F, K, U)$. It also gives a criterion for the tame type of a class of polynomials.

The global objects are those of the Selmer hypotheses in [main summands](/chapter/main-summands/): $R$ is conjugate self-dual of level $S$ with jumps $\tau(\sigma)$ at the complex embeddings $\sigma$, and $u$ is a lattice in $R$, that is, $u$ is conjugate to $R$ over $\bar{\mathbb{Q}}_\ell$. An isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ is fixed.

### Tame types from roots of unity

**Lemma (Tame type from roots).** Let $M$ be a multiset of at most $N$ elements of $\bar{\mathbb{Q}}_\ell$. Suppose each $y \in M$ satisfies $y^{\ell^a - 1} = 1$ for some $a \in [1, r]$. Let $K$ be a property of polynomials over $O$ that holds for every $Q$ that vanishes at all $y \in M$. Then $K$ is of tame type $(\ell, r, Nr)$.

Lean: `New.Selmer.isTameType_of_roots` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* Put $e' = \mathrm{lcm}\{\ell^a - 1 : 1 \leq a \leq r\}$. Each $y \in M$ has $y^{\ell^a - 1} = 1$ with $\ell^a - 1 \mid e'$, so $X^{e'} - 1$ vanishes at $y$, and $K(X^{e'} - 1)$ holds. For the second condition, $y$ is the Teichmüller lift of an element of $\mathbb{F}_{\ell^a}^\times$. So $y$ lies in the image of $W(\mathbb{F}_{\ell^a})$, which has rank $a$ over $\mathbb{Z}_\ell$. Its minimal polynomial $\mu_y$ over $\mathbb{Z}_\ell$ is monic of degree at most $a \leq r$. Put $q = \prod_{y \in M} \mu_y$. It is monic of degree at most $\#M \cdot r \leq Nr$, and its image in $O[X]$ vanishes at every $y \in M$. So $K(q)$ holds. $\square$

The source uses this lemma in [the denominator bound](/chapter/denominator-bound/) to show that the classes at the level primes are tame, with $M$ the eigenvalues of an inertia element.

### Restriction to a place

**Definition (Local lattice).** For $\rho : G_E \to M_m(O)$ and a place $w$ of $E$ above $\ell$, the *local lattice* of $\rho$ at $w$ is the matrix lattice of $\rho$ restricted to the decomposition group $G_w$ of the chosen place of $\bar{E}$ over $w$.

Lean: `New.Selmer.localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

**Lemma (An equivariant embedding).** Let $u$ be a lattice in $R$. There are a $\mathbb{Z}_\ell$-linear map $F : O^n \to \bar{\mathbb{Q}}_\ell^n$ and a basis $b$ of $\bar{\mathbb{Q}}_\ell^n$ such that $F$ is injective, $F(ax) = a F(x)$ for $a \in O$, $F$ sends the standard basis to $b$, and $F(u(g)x) = R(g)F(x)$ for all $g \in G_E$.

Lean: `New.Selmer.IsLatticeIn.exists_equivariant_embedding` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* Since $u$ is a lattice in $R$, there is $B \in \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ with $R(g) = B u(g) B^{-1}$. Let $F$ be the inclusion $O^n \subset \bar{\mathbb{Q}}_\ell^n$ followed by $x \mapsto Bx$, and $b$ the columns of $B$. Then $F(u(g)x) = Bu(g)x = R(g)Bx$. $\square$

The two local properties of the class pass from $R$ to $u$ along $F$, since $F$ is injective and equivariant.

**Lemma (Admissibility of the local lattice).** Let $u$ be a lattice in $R$, $w$ a place above $\ell$, and $\mathcal{F}$ a filter on $G_w$ with $\mathrm{nearOne} \leq \mathcal{F}$. If $R$ restricted to $G_w$ is admissible along $\mathcal{F}$, so is the local lattice of $u$ at $w$.

Lean: `New.Selmer.IsLatticeIn.isAdmissible_localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

**Lemma (Polynomials of the local lattice).** Let $u$ be a lattice in $R$, $w$ a place above $\ell$, $(s, m)$ a Weil pair with $s \in G_w$, and $Q \in O[X]$. If $Q$, read in $\bar{\mathbb{Q}}_\ell[X]$, kills $(s, m)$ on $R$ at $w$, then $Q$ kills $(s, m)$ on the local lattice of $u$ at $w$.

Lean: `New.Selmer.IsLatticeIn.isKilledBy_localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof of both.* Admissibility and the killing of a Weil pair pass along a family of jointly injective equivariant maps, by the results of [period rings](/chapter/period-rings/). Here the family is the single map $F$ of the previous lemma. $\square$

**Lemma (Trivial on inertia away from the level).** Let $R$ be conjugate self-dual of level $S$. Let $v$ be a finite place of $E$ outside $S$, not above $\ell$ and not above $p_0$ or $p_1$. Then $R(g) = 1$ for every $g$ in an inertia group above $v$.

Lean: `New.Selmer.IsConjSelfDualOfLevel.eq_one_of_mem_inertiaAbove` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* At such a place the local conditions of the level say that $R$ is good at $v$. As $\ell$ is a unit at $v$, good means unramified, so $R$ is trivial on inertia. $\square$

### The class at a place

**Definition (Embedding, filter, polynomials and jumps at a place).** Let $w$ be a place of $E$ above $\ell$, and $e_w : E \to \bar{\mathbb{Q}}_\ell$ the embedding of the local chart at $w$.

1. For $g \in G_\ell$, $\sigma_{w,g} = \sigma_{e_w, g}$ is the complex embedding $\iota^{-1} \circ g^{-1} \circ e_w$.
2. The *crystallinity filter* at $w$ is $\bot$ if $w$ lies above $p_0$ or $p_1$, and $\top$ otherwise.
3. $\mathrm{KillsAboveM}(\mathcal{R}, w, s, Q)$ says that $w$ lies above $p_0$ or $p_1$, and $Q$ kills $(s, 0)$ on every $R \in \mathcal{R}$ at $w$.
4. $U_w(\gamma)$ is the set of members of $\tau(\sigma_{w, g})$ for a chosen $g$ with $c_g = \gamma$.

Lean: `New.Selmer.complexEmbeddingAt`, `New.Selmer.crystallinityFilter`, `New.Selmer.KillsAboveM`, `New.Selmer.jumpSetAt` (New/Congruences/LocalLoss/LocalLattices.lean).

Admissibility along $\mathrm{nearOne} \sqcup \bot = \mathrm{nearOne}$ is potential crystallinity, and along $\mathrm{nearOne} \sqcup \top = \top$ it is crystallinity.

**Theorem (Jumps of the local lattice).** Let $R$ be conjugate self-dual of level $S$ with jumps $\tau$, $u$ a lattice in $R$, $w$ a place above $\ell$ and $g \in G_\ell$. Then the local lattice of $u$ at $w$ has, at $c_g$, the jumps $\tau(\sigma_{w,g})$ with multiplicity.

Lean: `New.Selmer.IsConjSelfDualOfLevel.hasJumps_localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* The local conditions of the level give the jumps of $R$ at $w$, read at $\sigma_{w,g}$ through $\iota$. The map $F$ is equivariant and sends a basis of $O^n$ to a basis of $\bar{\mathbb{Q}}_\ell^n$, so $\bar{\mathbb{Q}}_\ell \otimes_O O^n \cong \bar{\mathbb{Q}}_\ell^n$ as representations. Jumps do not change under extension of scalars from $O$ to $\bar{\mathbb{Q}}_\ell$. Last, $c_g$ is the restriction to $O$ of the map that reads $\bar{\mathbb{Q}}_\ell$ in $\mathbb{C}_\ell$ through $g$. $\square$

**Theorem (The local lattice is in the class).** Let $R$ be conjugate self-dual of level $S$ with jumps $\tau$, $R \in \mathcal{R}$, $u$ a lattice in $R$ and $w$ a place above $\ell$. Then the local lattice of $u$ at $w$ lies in
$$\mathrm{InClass}\big(\mathrm{crystallinityFilter}(w),\ \mathrm{KillsAboveM}(\mathcal{R}, w),\ U_w\big).$$

Lean: `New.Selmer.IsConjSelfDualOfLevel.inClass_localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* There are three conditions.

1. Admissibility. The local conditions at $w$ say that $R$ is potentially crystalline at $w$, and crystalline if $w$ is not above $p_0 p_1$. By the remark after the definition, $R$ is admissible along $\mathrm{nearOne} \sqcup \mathrm{crystallinityFilter}(w)$. The lemma on admissibility passes this to $u$.
2. Jumps. Let $i$ be a jump of nonzero multiplicity at $\gamma$, and let $g$ be the chosen element with $c_g = \gamma$. By the previous theorem the multiplicity of $i$ is its count in $\tau(\sigma_{w,g})$. So $i \in U_w(\gamma)$.
3. Polynomials. If $\mathrm{KillsAboveM}(\mathcal{R}, w, s, Q)$ and $s$ is in inertia, then $Q$ kills $(s, 0)$ on $R$, as $R \in \mathcal{R}$. The lemma on polynomials passes this to $u$. $\square$

**Corollary (Jumps and class).** Under the same hypotheses, the local lattice of $u$ at $w$ has the jumps $\tau(\sigma_{w,g})$ at every $c_g$, and lies in the class of the theorem.

Lean: `New.Selmer.hasJumps_and_inClass_localLattice` (New/Congruences/LocalLoss/LocalLattices.lean).

*Proof.* Combine the two theorems. $\square$

**Remark (Formalization).** The embedding $e_w$ comes from the local chart at $w$, which the source chooses (finding F-044). Every statement of this section holds for every choice, but the jumps $\tau(\sigma_{w,g})$ and the sets $U_w$ depend on it through $\sigma_{w,g}$. The set $U_w(\gamma)$ also uses a chosen $g$ with $c_g = \gamma$; by the theorem on jumps the multiset $\tau(\sigma_{w,g})$ does not depend on this choice. The class is the same for every $R \in \mathcal{R}$ only through $\mathrm{KillsAboveM}$, which quantifies over all of $\mathcal{R}$. This is what lets one class serve for all members of a family.
