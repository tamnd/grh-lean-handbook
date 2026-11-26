---
title: The auxiliary places and the base level
lean:
  - New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean
  - New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean
decls:
  - New.Selmer.invAvatar_eq_of_isTameExponent
  - New.Selmer.isSplit_twistPlace
  - New.Selmer.HasTwistParahoricType
  - New.Selmer.natCast_notMem_of_mem_conjClosure
  - New.Selmer.isFiniteTypeAt_and_polyKillsAt_of_mem_conjClosure
  - New.Selmer.normalisedRep_quadratic_on_inertia
  - New.Selmer.normalisedJumps
  - New.Selmer.normalisedJumps_eq_range_add_map
  - New.Selmer.chosenGroupOrder_nsmul_typeProjection_mem_ellIntegralForms
  - New.Selmer.IsFormOfType
  - New.Selmer.IsFormOfType.isRepOfType_normalisedRep
  - New.Selmer.exists_baseLevel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The auxiliary places and the base level

Ribet's method works at a level with extra places: the modulus $Q$ of a twist $\vartheta$. This section gives the local shape of the normalized representations at $Q$ and puts the forms of a lift setting into base data. Base data, its forms of a level and its integral forms are in [building the representations](/chapter/building-representations/). The set $Q$ is *auxiliary* for the bad places, those above $\ell p_0 p_1 N$: its places have prime norm, they and their conjugates are not bad, and no conjugate of a place of $Q$ is in $Q$ ([tied traces and even classes](/chapter/tied-traces/)).

### Inertia at the auxiliary places

**Lemma.** Every twist place of a descent pair is split. If $Q$ is auxiliary, no place of $Q$ or of its conjugate divides $\ell$.

Lean: `New.Selmer.isSplit_twistPlace`, `New.Selmer.natCast_notMem_of_mem_conjClosure` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* A twist place is a split place by the definition of a descent pair. The places above $\ell$ are bad. $\square$

**Lemma (The inverse avatar on inertia).** Let $w \in Q$ with $\bar w \neq w$, and let $s$ have tame exponent $a$ at $A$ over $w$. Then the avatar of $\vartheta^{-1}$ sends $s$ to $\iota(T^a(x^{-1}))$, where $x$ names $\vartheta.\mathrm{tamePart}(w)$.

Lean: `New.Selmer.invAvatar_eq_of_isTameExponent` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* This is the lemma on the label of an avatar of [avatars and conjugate self-duality](/chapter/main-summands/#avatars-and-conjugate-self-duality), for the character $\vartheta^{-1}$. Its tame part at $\bar w$ is trivial, since $\bar w \notin Q$. $\square$

**Definition (Parahoric type of the twist).** A form $f$ on the space of rank $\#n$ has the *parahoric type of $V$* at a twist place $w$ if the parahoric with blocks $\emptyset$, the complement of $r$, and $r$ acts on $f$ through $V.\mathrm{tamePart}(w)^{-1}$ of the determinant of the block $r$.

Lean: `New.Selmer.HasTwistParahoricType` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

**Theorem (Quadratic relation on inertia).** Let $(V, c)$ be a lift setting for $\vartheta$ with $Q$ auxiliary. Let $f \neq 0$ be an eigenform with Hecke polynomials $H$, of the parahoric type of $V$ at each twist place, and let $R$ be attached to $H$. Then at every $A$ over a place of $Q$ or of its conjugate, $R$ is of finite type, and $(X - a(s))(X - 1)$ kills $s$ for $s$ in inertia, where $a$ is the avatar of $\vartheta^{-1}$. The normalized representation $u = \chi \otimes R$ has $(u(g) - a(g))(u(g) - 1) = 0$ for $g$ in inertia above $Q$ and its conjugate.

Lean: `New.Selmer.isFiniteTypeAt_and_polyKillsAt_of_mem_conjClosure`, `New.Selmer.normalisedRep_quadratic_on_inertia` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* A place $w$ of $Q$ is split, not above $\ell$, and of prime norm. The local-global compatibility at split places for the parahoric type gives finite type, no monodromy, and a kill of inertia by $\prod (X - \iota\eta_b(s))$ over the block characters. The characters are $1$ on the blocks of the complement and $\vartheta.\mathrm{tamePart}(w)^{-1}$ on the block $r$, read through $T$ at the tame exponent. By the lemma on the inverse avatar, this gives the factors $X - 1$ and $X - a(s)$. At $\bar w$, use the conjugate place lemma. The normalizing character $\chi$ is trivial on inertia away from $\ell$ ([avatars and conjugate self-duality](/chapter/main-summands/#avatars-and-conjugate-self-duality)). So $u(g) = R(g)$ on inertia there. $\square$

### The jumps of the normalized representation

**Definition (Normalized jumps).** At $\sigma$, the *normalized jumps* of $V$ are the jumps of the weight of $V$ in rank $\#n$, each shifted by minus the infinity type of the character whose avatar is $\chi$.

Lean: `New.Selmer.normalisedJumps` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

**Theorem (The normalized jumps).** Let $\#n$ be even, $l = 2\lambda$ the doubled parameter that fits $V$, $-\kappa'$ the weight of the character of $V$ and $t' = \#n - \#r$. At $\sigma$ with place $v$, the normalized jumps are $0, 1, \dots, t' - 1$ and the numbers $(t' - 1 - \epsilon_\sigma(l_v(c) - 2\kappa'_v))/2$ for $c \in r$.

Lean: `New.Selmer.normalisedJumps_eq_range_add_map` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

*Proof.* The jumps are distinct and both sides have $\#n$ members, so an inclusion suffices. The jumps of the weight are the shifted Harish-Chandra parameters. The parameters on the complement of $r$ give a run of $t'$ consecutive numbers, which the shift moves to $0, \dots, t' - 1$. The parameters on $r$ give the other numbers. The sign $\epsilon_\sigma$ enters because the infinity type is $\kappa'$ on the CM type and $-\kappa'$ off it. The division is exact, since $l_v(c)$ and $t' - 1$ are both odd or both even. $\square$

### Forms of a type and base data

**Definition (Form of a type).** For labels $c$ and a set $S$ of places, a *$(c, S)$-form* is a nonzero eigenform $f$ with Hecke polynomials $H$, of the weight of $V$, that has the level and character of $V$ at the places of $V$, is fixed by the tuple idempotent of $c$, and is spherical at every $v$ with $v, \bar v \notin S \cup V.\mathrm{places}$.

Lean: `New.Selmer.IsFormOfType` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

**Theorem (Forms of a type give representations of a type).** Let $(V, c)$ be a lift setting for $\vartheta$, $Q$ auxiliary, and $S$ a set of places that are not bad. Let $f$ be a $(c, S)$-form and $R$ attached to its Hecke polynomials. Then $\chi \otimes R$ is of type $(V, c^{\mathrm{sc}}(X - 1)^{t'})$, with twist $1 - t'$, the normalized jumps, and level $\bar Q \cup Q \cup \bar S \cup S$.

Lean: `New.Selmer.IsFormOfType.isRepOfType_normalisedRep` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

*Proof.* The idempotent fixes $f \neq 0$, so it does not kill $f$, and $f$ has the product label made from $c$. The theorem on representations of a type from labels, twisted by the avatar $\chi$, gives the claim, once $f$ is spherical at the right places. A place that is neither chosen nor in the level avoids $S$ and the places of $V$, and so does its conjugate, since the places of $V$ are the chosen places and $Q$. So $f$ is spherical there. $\square$

**Lemma.** If $(V, c)$ is a lift setting and $y$ is a form integral above $\ell$, then $N_{\mathrm{ch}} \cdot e_c y$ is integral above $\ell$.

Lean: `New.Selmer.chosenGroupOrder_nsmul_typeProjection_mem_ellIntegralForms` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

*Proof.* The idempotent is a sum over the group $\prod_i \mathrm{GL}_{\#r}(k_i)$ with coefficients in $\frac{1}{|G|}\mathbb{Z}[\zeta]$. Its order $|G|$ divides $N_{\mathrm{ch}}$, since $\#r \leq D.r \leq D.r D.t$. Each group element maps integral forms to integral forms. $\square$

**Theorem (Base data of a label).** Let $(V, c)$ be a lift setting for $\vartheta$ with $Q$ auxiliary. There are jumps $J$ and base data $B$ of the weight of $V$ and constant $N_{\mathrm{ch}}$ with:

1. every form in the range of $e_c$ is a form of $B$ of empty extra level;
2. if $y$ is integral above $\ell$, so is $N_{\mathrm{ch}} \cdot e_c y$;
3. for every finite family $u$ of places that are not bad and every eigensystem $x$ of $B$ of level $u$, $\chi \otimes R_x$ is of type $(V, c^{\mathrm{sc}}(X - 1)^{t'})$ with jumps $J$ and level $\bar Q \cup Q \cup \bar u \cup u$, and it satisfies the quadratic relation on inertia above $Q$ and $\bar Q$.

Lean: `New.Selmer.exists_baseLevel` (New/Congruences/GaloisRepresentations/BaseLevelOfLabel.lean).

*Proof.* Take for $B$ the forms of the weight of $V$, with the level and character of $V$ at its places, cut out by the idempotent of $c$, and $J$ the normalized jumps. Part 1 holds because $e_c$ fixes its range and the range is in the level space. Part 2 is the lemma before. For part 3, an eigensystem of $B$ of level $u$ is a $(c, u)$-form, so the two theorems of this section apply. $\square$

**Remark (Formalization).** The base data $B$ and the jumps $J$ are given by an existential, so later chapters use only the three properties. The bound $N_{\mathrm{ch}}$ is positive, since it is the order of a finite group.
