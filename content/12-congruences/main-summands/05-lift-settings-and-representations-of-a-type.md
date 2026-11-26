---
title: Lift settings and representations of a type
lean:
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/GaloisRepresentations/AttachedRepresentations.lean
decls:
  - New.Selmer.scaledTypePoly
  - New.Selmer.IsLiftSetting
  - New.Selmer.IsLiftSetting.card_le
  - New.Selmer.IsLiftSetting.isChosen_chosenPlace
  - New.Selmer.typeProjection
  - New.Selmer.IsLiftSetting.isSymmetric_typeProjection
  - New.Selmer.IsLiftSetting.typeProjection_eq_self_of_mem_range
  - New.Selmer.IsLiftSetting.range_typeProjection_mem_invtSubmodule
  - New.Selmer.frequently_isSplit_notMem_places
  - New.Selmer.not_isRoot_one_scaleRoots_inv
  - New.Selmer.isLiftSetting_descentPair
  - New.Selmer.isLiftSetting_mainPair
  - New.Selmer.trivialLift_mem_range_typeProjection
  - New.Selmer.IsRepOfType
  - New.Selmer.prod_aroots_dvd_prod_aroots_scaleRoots_comp
  - New.Selmer.IsRepOfType.twist_avatar
  - New.Selmer.isRepOfType_of_hasProductLabel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lift settings and representations of a type

The inertia of a main summand at the chosen places above $p_0$ and $p_1$ is controlled by *labels*: polynomials over the residue fields whose roots are the tame eigenvalues. A *lift setting* is a descent pair together with labels that satisfy the conditions the later proofs need. A *representation of the type* of a lift setting is a conjugate self-dual representation whose inertia at the chosen places acts through the roots of the labels. This section defines both and proves the three ways in which they arise.

### Background

- A *label* of degree $r$ over a finite field $k$ is a monic squarefree polynomial of degree $r$ with nonzero constant term. It is *primitive* if its roots generate $\mathbb{F}_{q^r}$ and are of maximal type. A tuple $c$ of labels at the chosen places has a central idempotent $e_c$ in the group algebra of $\prod_i \mathrm{GL}(k_i)$ ([the finite general linear group](/chapter/finite-gln/)).
- The faithful character $T$ of a residue field and the name $\lambda \in k^\times$ of a character $\psi$ of $k^\times$, with $\psi = T \circ \lambda$ in the sense of [the finite general linear group](/chapter/finite-gln/).
- A descent pair $V$ has chosen places $w_i$, one tame part $V.\mathrm{tamePart}$, ranks $\#r < \#n$, and $V.\mathrm{rankDiff} = \#n - \#r$. The $j$-th descent pair of a twist $\vartheta$ and the rank-one descent pair of a main pair are in [single theta lifts](/chapter/single-theta-lifts/) and [twists and critical pairs](/chapter/twists-critical-pairs/). The good tuple families are in [the objects of the upper bound](/chapter/upper-bound-objects/).
- A representation $R$ is *labelled at $A$ by $c$ at level $f$* if every inertia element $s$ over $A$ of tame exponent $y$ at level $f$ is killed by $\prod_{x} (X - \iota(T^y(x)))$, over the roots $x$ of $c$ ([local conditions](/chapter/attached-representations/#local-conditions-kills-and-characteristic)).

### Lift settings

**Definition (Scaled type polynomial).** For a descent pair $V$ with labels $c_i$ at the chosen places $w_i$, let $\lambda_i$ name the character $V.\mathrm{tamePart}(w_i)^{-1}$. The *scaled type polynomial* at $i$ is $c_i$ with its roots multiplied by $\lambda_i$.

Lean: `New.Selmer.scaledTypePoly` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Definition (Lift setting).** A descent pair $V$ with labels $c$ is a *lift setting for the twist $\vartheta$* if:

1. the places of $V$ are the level places of $\vartheta$;
2. $V.\mathrm{tamePart} = \chi_M^{j}\,\vartheta.\mathrm{tamePart}$ for some $1 \leq j \leq m$, with $\chi_M$ the local character of the data;
3. $\#r$ and $V.\mathrm{rankDiff}$ are odd, $\#r \leq D.r$ and $V.\mathrm{rankDiff} \leq D.t$;
4. each $c_i$ is a label of degree $\#r$;
5. over each of $p_0$, $p_1$ there is a chosen place $w_i$ with ($\#r = D.r$ and $c_i$ primitive) or ($\#r = 1$ and $c_i = X - 1$);
6. $1$ is not a root of any scaled type polynomial.

Lean: `New.Selmer.IsLiftSetting` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma.** For a lift setting, $\#n \leq 2\,n_m$, where $n_m = k + m(t + 1)$, and every chosen place of $V$ is chosen for the data.

Lean: `New.Selmer.IsLiftSetting.card_le`, `New.Selmer.IsLiftSetting.isChosen_chosenPlace` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* By 3, $\#n \leq D.r + D.t$. Since $D.t = 5D.r$, this is at most $2D.t$. Since $m \geq 10^4$, $D.t \leq m D.t \leq n_m$. For the second claim, the chosen places of $V$ are those of the level places of $\vartheta$, by 1. $\square$

**Definition (Type projection).** For a descent pair $V$ with labels $c$, the *type projection* $e_c$ is the action of the tuple idempotent of $c$ on the forms on $V$.

Lean: `New.Selmer.typeProjection` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma (The type projection).** The operator $e_c$ is self-adjoint, it fixes its range, and its range is stable under the Hecke polynomial $\sum_{i \le \#n} (-x)^i q^{\binom{i}{2}} T_{w,i}$ at every split place $w$ with $w, \bar w$ off the places of $V$, for every $x \in \mathbb{C}$. Infinitely many places $w$ are split with $w, \bar w$ off the places of $V$.

Lean: `New.Selmer.IsLiftSetting.isSymmetric_typeProjection`, `New.Selmer.IsLiftSetting.typeProjection_eq_self_of_mem_range`, `New.Selmer.IsLiftSetting.range_typeProjection_mem_invtSubmodule`, `New.Selmer.frequently_isSplit_notMem_places` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* The idempotent is central and self-adjoint in the group algebra, and the action on forms is unitary. An idempotent fixes its range. Each group element acts, up to a scalar, by translation with an element trivial at $w$ and $\bar w$. Such a translation commutes with the Hecke operators at $w$. So the range of $e_c$ is stable. Places of prime norm are split and infinite in number, and only finitely many lie in the places of $V$ or their conjugates. $\square$

**Theorem (The lift settings of the lifts).** Let $1 \leq j \leq m$, let $\vartheta$ be a twist, and let $c$ be a good tuple family. Then the $j$-th descent pair of $\vartheta$ with the labels $c$ is a lift setting for $\vartheta$.

Lean: `New.Selmer.isLiftSetting_descentPair`, with `New.Selmer.not_isRoot_one_scaleRoots_inv` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Conditions 1 to 3 hold by the construction of the $j$-th descent pair. Over each of $p_0, p_1$ the labels form a good tuple: each is a label of degree $D.r$, and one is primitive. This gives 4 and 5. For 6: if $y$ is a unit and $y$ is not a root of $q$, then $1$ is not a root of $q$ with roots scaled by $y^{-1}$, since $q^{\mathrm{sc}}(y^{-1} \cdot y) = 0$ would give $q(y) = 0$. The name $\lambda$ of the tame part is a root of unity of order dividing $q_2$, and a good label vanishes at no $q_2$-th root of unity. $\square$

**Theorem (The lift settings of the main pairs).** Let $p = (\nu, z)$ be a main pair for $j$, and let $\vartheta$ be a twist. The descent pair of the lift of $\nu\vartheta$ from $\mathrm{U}(1)$ to $\mathrm{U}(2z)$, with every label equal to $X - 1$, is a lift setting for $\vartheta$. The trivial lift of this pair lies in the range of the type projection.

Lean: `New.Selmer.isLiftSetting_mainPair`, `New.Selmer.trivialLift_mem_range_typeProjection` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Here $\#r = 1$ and $\mathrm{rankDiff} = 2z - 1$, both odd, and $2z - 1 \leq 2D.r - 1 \leq D.t$. The label $X - 1$ has degree $1$, which gives 4 and 5. The scaled type polynomial is $X - \lambda$, and $\lambda = 1$ only if the tame part of $\nu$ is trivial at the place. A main pair is ramified at every chosen place. For the second claim, the label $X - 1$ belongs to the trivial character of $\mathrm{GL}_1$, so the idempotent is the mean over the group. The trivial lift is invariant, so the mean fixes it. $\square$

### Representations of a type

**Definition (Representation of a type).** Let $V$ be a descent pair with labels $c$, let $S$ be a set of places, $k \in \mathbb{N}$ and $J$ a family of jumps. A representation $R$ of rank $\#m$ is *of type $(V, c)$*, with twist $1 - k$, jumps $J$ and level $S$, if:

1. $R$ is conjugate self-dual of twist $1 - k$, level $S$ and jumps $J$;
2. at every place $A$ over a chosen place $w_i$, $R$ is labelled by $c_i$ at level $(\#r)!$.

Lean: `New.Selmer.IsRepOfType` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma (Scaled roots).** Let $\varphi : K \to L$ be multiplicative, $p \in F[X]$ and $u \in F^\times$. Then $\prod_{x} (X - \varphi(x))$ over the roots of $p$ divides $Q(\varphi(u) X)$, where $Q$ is the same product for $p$ with roots scaled by $u$.

Lean: `New.Selmer.prod_aroots_dvd_prod_aroots_scaleRoots_comp` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* The roots of the scaled polynomial are the $ux$. Factor by factor, $\varphi(u)X - \varphi(ux) = \varphi(u)(X - \varphi(x))$. $\square$

**Theorem (Twist by an avatar).** Let $(V, d)$ be a lift setting for $\vartheta$, and let $R$ be of type $(V, c)$ with twist $1 - k$, jumps $J$ and level $S$. Let $a$ be a character of the norm-one torus whose tame part $\psi$ is $1$ at every place that is not chosen. Let $\mu$ be the avatar of $y \mapsto a(y/\bar y)\upsilon(y)^{-k'}|y|^{j - k'/2}$, and let $b$ satisfy $(b - 1) + (2j - k') = k - 1$. Then $\mu \otimes R$ is of type $(V, c')$ with twist $1 - b$, level $S$, the jumps $J$ shifted by minus the infinity type of the character, and $c'_i$ equal to $c_i$ with roots scaled by the name of $\psi(w_i)$.

Lean: `New.Selmer.IsRepOfType.twist_avatar` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* *Duality.* By the theorem on avatars, $\mu(g^c)\mu(g) = \varepsilon(g)^{2j - k'}$. With $\mu(g^{-1}) = \mu(g)^{-1}$ this gives $\mathrm{tr}(\mu R)(g^c) = \varepsilon^{-1}(g)^{b - 1}\,\mathrm{tr}(\mu R)(g^{-1})$ by the choice of $b$. Continuity and the trace form pass to a twist by a continuous character. *Local conditions.* The avatar is of finite type everywhere, with one jump given by the infinity type. Off $p_0 p_1$ no place and no conjugate is chosen, so $\psi = 1$ there and the character is unramified, hence good. A twist of a representation by a character of finite type is of finite type, with the jumps added. *Labels.* Let $s$ have tame exponent $y$ at $A$ over $w_i$. The place $w_i$ is split, and $\bar w_i$ is not chosen, so $\psi(\bar w_i) = 1$. By the lemma on the label of an avatar, $s$ acts on $\mu$ by $\varphi(u)$ with $u$ the name of $\psi(w_i)$ and $\varphi = \iota \circ T^y$. It acts on $R$ through the $\varphi(x)$ for the roots $x$ of $c_i$. So it acts on $\mu R$ through the $\varphi(ux)$, the roots of $c'_i$, by the lemma on scaled roots. $\square$

**Theorem (Representations of a type from labels).** Let $(V, d)$ be a lift setting for $\vartheta$. Let $f$ be an eigenform of weight $\kappa$ on the definite unitary group of rank $\#m$, and let $R$ be attached to its Hecke polynomials $H$. Suppose:

1. at every place $v$ outside $S$ or above $\ell p_0 p_1$, other than the chosen places of $V$ and their conjugates, $f$ is spherical;
2. at each chosen place $w_i$, the type of $f$ is induced from the type with label $c_i$ of degree $\#r$ and trivial characters on blocks of sizes $t_l$.

Then $R$ is of type $(V, c')$ with twist $1 - \#m$, level $S$ and the jumps of $\kappa$ in rank $\#m$, where $c'_i = c_i (X - 1)^{\#m - \#r}$.

Lean: `New.Selmer.isRepOfType_of_hasProductLabel` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Conjugate self-duality of twist $1 - \#m$ is the theorem on attached representations. For the local conditions at $v$ over $A$ there are three cases. If $v$ is a chosen place $w_i$, the product label of hypothesis 2 gives finite type, the jumps and the label, through the local-global compatibility at labelled places ([building the representations](/chapter/building-representations/)). If $v$ is the conjugate of a chosen place, the case $w_i$ and the theorem on local conditions at the conjugate place give the clauses. Otherwise $f$ is spherical at $v$, and the standard compatibility at spherical places gives finite type, the jumps, and good reduction. For the labels, the completing characters are trivial, so their roots are $1$, and their sizes add up to $\#m - \#r$. $\square$

### The auxiliary twist

Ribet's element also uses an *auxiliary twist* $\psi$ with an auxiliary modulus $Q$ and a bound on the $\ell$-adic size of $\psi - 1$ on the tame generators. It is defined in [tied traces and even classes](/chapter/tied-traces/).
