---
title: The target forms and the chain
lean:
  - New/UpperBound/Objects/Rows.lean
  - New/UpperBound/Objects/RowChain.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
  - New/Determinant/Chain/NormOfChain.lean
  - New/Determinant/Chain/ChainNorms.lean
  - New/Reduction/ShortAndEnough.lean
decls:
  - New.Data.card_Y_le
  - New.Data.spaceY
  - New.Data.isStd_spaceY_of_le
  - New.Data.goodForms
  - New.Data.targetForms
  - New.Data.targetDim_pos
  - New.Data.TameChar.normQ
  - New.Data.MFoldTwist
  - New.Data.levelPlaces
  - New.Data.lastResidueLevel
  - New.Data.lastLevelChar
  - New.LevelPlaces.LevelForm
  - New.Data.lowerChainAtLevel
  - New.Data.Θ
  - New.Data.lowerChainAtLevel_injective
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The target forms and the chain

This section states the objects that the target lattice is made of. They are the space $T$ of target forms, the twists, the level and character of the last space, and the chain of lifts $\Theta_\vartheta$. Volume 9 constructs them in [the objects of the upper bound](/chapter/upper-bound-objects/), and this section gives each one with the properties that the lattice needs. All sizes are rows of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).

### The spaces of the chain

The chain runs through hermitian spaces $Y_0, Y_1, \dots, Y_m$ over the CM field $E$ of the data. The basis of $Y_j$ is indexed by a set of $r$ row indices followed by $j$ blocks of $t$ indices each. So $Y_j$ has rank $r + jt$.

**Lemma (Ranks of the spaces).** For $j \leq m$, the rank of $Y_j$ is at most $n_m = k + m(t+1)$.

Lean: `New.Data.card_Y_le` (New/UpperBound/Objects/Rows.lean).

*Proof.* The rank is $r + jt \leq r + mt$. Since $k = r + 1 - m$, we have $n_m = r + 1 + mt$. So the rank is at most $n_m - 1$. $\square$

The last space $Y_m$ has rank exactly $n_m - 1$. This number enters the bound on the stabilisers in Section 4.

**Definition (The spaces $Y_j$).** For each $j$, the hermitian space $Y_j$ with its lattice is a space on the index set of rank $r + jt$ with signs fixed by the data. The source takes it from an existence lemma by `choose`.

Lean: `New.Data.spaceY` (New/UpperBound/Objects/Rows.lean).

**Lemma (The last spaces are standard).** For $j \geq m$, the space $Y_j$ is standard: all its signs are $+1$ and its point is $1$.

Lean: `New.Data.isStd_spaceY_of_le` (New/UpperBound/Objects/Rows.lean).

For $j < m$ the source states the Gram matrix of $Y_j$ (`New.Data.spaceY_gram_eq`), and these spaces are indefinite.

**Remark (Formalization).** The spaces $Y_j$ are objects chosen by `choose`. The source uses only the properties of the existence lemma (`New.Data.exists_spaceY_xFin_eq`). The forms of the lattice live on the standard definite space with index set $Y_m$, and this space does not depend on the choice, since $Y_m$ is standard.

### The target forms

Let $\mathsf{G} = \prod_w \mathrm{GL}_r(\mathbb{F}_w)$ be the product of the general linear groups over the residue fields $\mathbb{F}_w$ of the chosen places $w$ above the two level primes $p_0$ and $p_1$. For a hermitian space $V$ of the data, the *principal forms* on $V$ are the automorphic forms on $U(V)$ of a fixed parameter $\varsigma$ that are fixed by the principal level at the chosen places. The group $\mathsf{G}$ acts on them through integral lifts of its elements. The source fixes an element $e_0$ of the group algebra $\mathbb{C}[\mathsf{G}]$, a sum of idempotents over a set of good families.

**Definition (Good forms).** The good forms on $V$ are the image of $e_0$ acting on the principal forms on $V$.

Lean: `New.Data.goodForms` (New/UpperBound/Objects/Rows.lean).

**Definition (Target forms).** The target forms are the good forms on $Y_0$. Their space is $T$, and $d_T = \dim_{\mathbb{C}} T$.

Lean: `New.Data.targetForms` (New/UpperBound/Objects/Rows.lean).

The space $T$ is a subspace of the forms on $U(Y_0)$, and it has their Petersson inner product. The volume of Section 5 uses it. The space $Y_0$ is indefinite, so the model case of Section 2 does not apply to forms on it.

**Lemma (The target is not zero).** $d_T > 0$.

Lean: `New.Data.targetDim_pos` (New/Reduction/ShortAndEnough.lean).

The source proves it from the spanning theorem of Volume 10 (`New.Data.finrank_targetForms_ne_zero`). The lattice does not need this fact, but the main inequality does.

### Twists

A *tame character* $\vartheta$ is an automorphic character of $U(1)(\mathbb{A}_E)$ of weight $0$ with a finite set $Q$ of finite places, its modulus, and a character $\psi_w$ of $\mathbb{F}_w^\times$ for each finite place $w$. The tame part $\psi_w$ is trivial outside $Q$. [Characters and twists](/chapter/fields-places-twists/#characters-twists-and-m-fold-twists) states these objects in full.

**Definition (Norm of the modulus).** The norm of the modulus of $\vartheta$ is $\mathrm{Nm}\,Q = \prod_{w \in Q} q_w$.

Lean: `New.Data.TameChar.normQ` (New/Reduction/Data/LevelAndTwists.lean).

**Definition ($m$-fold twist).** An $m$-fold twist is a tame character $\vartheta$ such that $\psi_w^n \neq 1$ for every $w \in Q$ and every $1 \leq n \leq m$.

Lean: `New.Data.MFoldTwist` (New/Reduction/Data/LevelAndTwists.lean).

The trivial twist $1$ has $Q = \emptyset$, so it is an $m$-fold twist. The $m$-fold twists are the twists of the target lattice. The condition on the powers makes the power $\vartheta^j$ used by lift $j$ nontrivial at every place of $Q$.

### The level and the character on the last space

**Definition (Level places).** The level places of $\vartheta$ are the chosen places above $p_0$ and $p_1$, indexed by pairs $(i, w)$ with $w$ a chosen place above $p_i$, together with the places of $Q$.

Lean: `New.Data.levelPlaces` (New/UpperBound/Objects/Rows.lean).

The basis of $Y_m$ falls into $m + 1$ blocks: the $r$ row indices and $m$ blocks of $t$ indices. A matrix is *block upper triangular* if it is upper triangular for this partition.

**Definition (Last residue level).** The last residue level of $\vartheta$ is the subgroup of $\prod_x \mathrm{GL}(Y_m \bmod w_x)$, over the level places $w_x$, of the families that are $1$ at the chosen places and block upper triangular at the places of $Q$.

Lean: `New.Data.lastResidueLevel` (New/UpperBound/Objects/RowChain.lean).

The level $J_m(\vartheta)$ on $Y_m$ is the group of elements of $K_0$, the stabiliser of the standard lattice, whose reductions at the level places lie in the last residue level (`New.Data.lastLevel`). For the trivial twist, $J_m(1)$ is the group of integral elements that reduce to $1$ at every chosen place.

**Definition (Last level character).** The character of the last residue level is
$$k \longmapsto \prod_{w} \prod_{l < m} \psi_{l,w}\big(\det k_w^{(l+1)}\big),$$
where $w$ runs over the level places, $k_w^{(l+1)}$ is the diagonal block $l + 1$ of the component $k_w$, and $\psi_l$ is the tame part of the character of lift $l + 1$.

Lean: `New.Data.lastLevelChar` (New/UpperBound/Objects/RowChain.lean).

The character is trivial at the chosen places.

**Definition (Forms of a level).** Let $S$ be a system of level places, $H$ a subgroup of the product of the groups $\mathrm{GL}_n$ over the residue fields of these places, $\chi$ a character of $H$ and $(\kappa, e)$ a weight. A form of level $H$ and character $\chi$ is an algebraic form of weight $(\kappa, e)$ on the standard definite space of rank $n$ on which the level $K_H$, the elements of $K_0$ with reductions in $H$, acts through $\chi$ composed with the reduction.

Lean: `New.LevelPlaces.LevelForm` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

An algebraic form here is a function $\varphi$ on $G_f$ with values in the Weyl module $W_\kappa$, such that $\varphi(\gamma g) = \rho(\gamma)\varphi(g)$ for rational $\gamma$. The space of forms of a level is the space of the model case of Section 2 with vector values.

### The chain of lifts

For each $j < m$ there is a lift from forms on $Y_j$ to forms on $Y_{j+1}$: the theta lift with the character $\mu^0_{j+1}\vartheta^{j+1}$ and a datum fixed by the source, times the index in $K_0$ of a level `New.Data.levelY` (`New.Data.liftY`). The composite of the $m$ lifts, read on the definite space $Y_m$, is the map $\iota_\vartheta$ (`New.Data.lowerChain`). Its values have level $J_m(\vartheta)$ and the last level character (`New.Data.lowerChain_mem_levelSpace`).

**Definition (The chain at its level).** The map $\iota_\vartheta$ from the principal forms on $Y_0$ to the forms on $Y_m$ of level $J_m(\vartheta)$, of character the last level character and of weight (`D.columnsY`, `D.lastEntry D.m`).

Lean: `New.Data.lowerChainAtLevel` (New/UpperBound/Objects/RowChain.lean).

**Definition (The maps $\Theta_\vartheta$).** For an $m$-fold twist $\vartheta$, $\Theta_\vartheta$ is the restriction of $\iota_\vartheta$ to the target forms.

Lean: `New.Data.Θ` (New/Determinant/Chain/NormOfChain.lean).

The space $\mathcal{A}_\vartheta$ of values of $\Theta_\vartheta$ depends on $\vartheta$ through its level places, its level and its character.

**Theorem (The chain is injective).** For every $m$-fold twist $\vartheta$, the map $\iota_\vartheta$ is injective on the principal forms on $Y_0$.

Lean: `New.Data.lowerChainAtLevel_injective` (New/Determinant/Chain/ChainNorms.lean).

Volume 11 proves this in [the chain determinant](/chapter/chain-determinant/). The source writes the squared norm of $\iota_\vartheta y$ as a weighted chain of inner products, and a triangle structure of the lifts shows that the chain vanishes only if $y = 0$.

**Remark (Formalization).** The injectivity holds on all principal forms, not only on the target forms. The target lattice needs it on $T$, and it gets it by composition with the inclusion of $T$. The structure of a twisted lattice does not contain injectivity. The source proves it as a separate lemma (Section 5) and gives it to the lower bound as a hypothesis.
