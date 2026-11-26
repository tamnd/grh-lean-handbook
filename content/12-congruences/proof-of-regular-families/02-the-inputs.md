---
title: The inputs
lean:
  - New/Congruences/Selmer/TwistingTheorem.lean
  - New/Congruences/FirstOrder/DenominatorBound.lean
  - New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean
  - New/OneLift/HeckeValues/CentralAction.lean
decls:
  - New.Selmer.norm_inv_le_exp_of_ellVal_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The inputs

This section states the results of other chapters that the proof uses. Each one is stated exactly as the source proves it, with a link to the section that proves it. The proofs are not repeated. The inputs fall into five groups: the twisting theorem, the main summands, the bound for denominators, the lifts and their eigensystems, and some small facts. Sections 3 to 7 show where each input enters.

### The twisting theorem

The twisting theorem is the deepest input. Its proof takes [tied Selmer groups](/chapter/tied-selmer-groups/) and [the twisting theorem](/chapter/twisting-theorem/). It uses two relations: `IsAuxTwist` of [even classes and cocycles of Tate twists](/chapter/tied-traces/#even-classes-and-cocycles-of-tate-twists), and `HasDivisibleSelmerLengthLe` of [cocycles, relations and Selmer lengths](/chapter/main-summands/#cocycles-relations-and-selmer-lengths). The relation `IsMainSummandLike` is in [inertia above the level and main summand like](/chapter/main-summands/#inertia-above-the-level-and-main-summand-like).

The bad places `badPlaces D ℓ` are the finite places of $E$ that divide $\ell \cdot (M \cdot N)$, for $M$ = `D.M` the product of the two level primes $p_0$, $p_1$ and $N$ = `D.N` the level. The twist error is
$$e'_\ell = \mathrm{twistError}(\ell) = (4f + 3)\, r\, v_\ell(N_g) + (1/2)^{\ell}.$$

**Theorem (The twisting theorem).** Fix a prime $\ell$ and $\iota$. Let $I$ be a finite type, and for $i \in I$ let $R_i$ be a Galois representation with row type $r_i$, like a main summand for some $t$ and jumps $J$. Then there is an $m$-fold twist $\tau$ such that for every $1 \leq j \leq m$ the power $\xi = \tau^j$ has three properties:

1. `IsAuxTwist` (badPlaces $D$ $\ell$) $\xi.Q$ $\xi.\mathrm{invAvatar}$ $e'_\ell$;
2. for every $i$ there are $\gamma$ and $\zeta$ with `HasDivisibleSelmerLengthLe` $\xi.\mathrm{invAvatar}$ $R_i$ $\xi.Q$ $\gamma$ $\zeta$ $e'_\ell$;
3. for every ramified critical pair $p$ and every sign $s$, $\mathrm{ellVal}(\iota_\ell(p.\mathrm{ratio}(\xi, s))) \leq e'_\ell$.

Lean: `New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe` (New/Congruences/Selmer/TwistingTheorem.lean).

This is the theorem of [the twisting theorem](/chapter/twisting-theorem/#main-summands-and-the-twisting-theorem), at [line 370](lean:New/Congruences/Selmer/TwistingTheorem.lean#L370). The family $R_i$ may mix row types. This is what lets Section 5 join representations of rank $r$ and of rank one.

Here $\mathrm{ellVal}(z) = -\log_\ell \|z\|$ for $z \neq 0$ and $\mathrm{ellVal}(0) = \infty$, in $[0, \infty]$ after truncation at $0$. The third property gives a bound on norms through one small lemma of the same file.

**Lemma (From a valuation to a norm).** Let $x \in \mathbb{C}$ and $c \geq 0$ with $\mathrm{ellVal}(\iota_\ell(x)) \leq c$. Then $\|\iota_\ell(x^{-1})\| \leq \exp(c \log \ell)$.

Lean: `New.Selmer.norm_inv_le_exp_of_ellVal_le` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Since $\mathrm{ellVal}(\iota_\ell(x)) \leq c < \infty$, $\iota_\ell(x) \neq 0$ and $\|\iota_\ell(x)\| \geq \ell^{-c}$. The map $\iota_\ell$ is a ring isomorphism, so $\iota_\ell(x^{-1}) = \iota_\ell(x)^{-1}$. Then $\|\iota_\ell(x^{-1})\| \leq \ell^{c} = \exp(c \log \ell)$. $\square$

### The main summands

A main summand for a descent pair $O$ and Hecke values $z$ is a representation $R$ that is like a main summand for $t = O.\mathrm{rankDiff}$ and some jumps, and that gives the traces of the representations attached to all twisted lifts of $z$ (`New.Selmer.IsMainSummand`, [main summands from eigensystems](/chapter/main-summands/#main-summands-from-eigensystems)). Two results give main summands.

**Theorem (Main summands of the lifts).** Let $q$ be a system of Hecke eigenvalues with $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0$, where $\mathcal{G}$ is the space of good forms and $\mathcal{A}(\cdot)_q$ the eigenpart. Let $1 \leq j \leq m$. Then some $T$ with the row type $D.\mathrm{RowIndex}$ is a main summand for the $j$-th descent pair of the trivial twist `TameChar.one` and the values $(w, i) \mapsto q(w, i)$.

Lean: `New.Selmer.exists_isMainSummand_descentPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

**Theorem (Main summands from a representation of a type).** Let $(O, c)$ be a lift setting for the trivial twist and $R$ of type $(O, c)$ with twist $1 - \#r$, jumps $J$ and empty level. Suppose that $\mathrm{tr}\,R(g)$ is the limit of $\iota_\ell(b(w, 1))$ along most Frobenius elements tending to $g$, and that the jumps $u \in J_\sigma$, lowered to $u - \big((\#r - O.\mathrm{rankDiff})/2 - \epsilon_\sigma\, O.\mathrm{weight}_v\big)$, are main summand weights for $(\#r, O.\mathrm{rankDiff})$. Here $\epsilon_\sigma = \pm 1$ is the sign of $\sigma$ for the CM type and $v$ is the place of $\sigma$. Then some $T$ is a main summand for $O$ and $b$.

Lean: `New.Selmer.exists_isMainSummand_of_isRepOfType` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

Both theorems are proved in [main summands from eigensystems](/chapter/main-summands/#main-summands-from-eigensystems). The second needs a lift setting and a representation of a type ([lift settings and representations of a type](/chapter/main-summands/#lift-settings-and-representations-of-a-type)). For the main pairs these come from three more results.

**Theorem (The lift settings of the main pairs).** Let $p = (\nu, z)$ be a main pair for $j$, and let $\vartheta$ be a twist. The descent pair of the lift of $\nu\vartheta$ from $U(1)$ to $U(2z)$, with every label equal to $X - 1$, is a lift setting for $\vartheta$. The trivial lift of this pair lies in the range of the type projection.

Lean: `New.Selmer.isLiftSetting_mainPair`, `New.Selmer.trivialLift_mem_range_typeProjection` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

**Theorem (Weights of the main pairs).** Let $p$ be a main pair for $j$ with the point $p.z$ and the negative weight $c$. The single jumps $p.z - 1 - \epsilon_\sigma c_v$ are main summand weights for $(1, 2p.z - 1)$.

Lean: `New.Selmer.isMainSummandWeights_mainPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

**Lemma (Local conditions of a character).** Let $\mu$ be a continuous $\ell$-adic character whose image on the inertia group at a place $A$ is finite, and let $\rho$ be the representation of rank one that it defines. Then $\rho$ is of finite type at $A$, its only Hodge-Tate jump at $A$ is $0$ along every embedding, and $X - \mu(s)$ kills every $s$ in the sense of `PolyKillsAt`.

Lean: `New.GaloisRep.localConditions_char_of_finite_image_inertia` (Lib/PadicHodge/Characters.lean).

The lemma is at [line 993](lean:Lib/PadicHodge/Characters.lean#L993) of the library. No other chapter of the handbook states it yet. Section 3 uses it once, for $\mu = 1$.

### The bound for denominators

The bound for denominators is Ribet's method, carried to all ranks. Its proof takes [Ribet elements](/chapter/ribet-elements/), [first-order deformations](/chapter/first-order-deformations/), [tied traces](/chapter/tied-traces/), [the local loss](/chapter/local-loss/) and [from a congruence to a Selmer class](/chapter/denominator-bound/). Its form for the proof is short. A *lift generator* of $Z$ for $\vartheta$, $E$ and the bound $\mathrm{sel}$ is a form $y \in Z$ in the range of the type projection of some lift setting $c$ for $O$ and $\vartheta$ whose range lies in the image of $E$. It also has the Hecke polynomials of the lift of some values $z$, and there are a main summand $R$ for a pair $V$ and $z$, with $O.\mathrm{u1Char} = V.\mathrm{u1Char} \cdot \vartheta.\mathrm{toAutChar}$, and $\gamma$, $\zeta$ with `HasDivisibleSelmerLengthLe` $\vartheta.\mathrm{invAvatar}$ $R$ $\vartheta.Q$ $\gamma$ $\zeta$ $\mathrm{sel}$ (`New.Selmer.IsLiftGenerator`, [false lifts and lift generators](/chapter/denominator-bound/#false-lifts-and-lift-generators)).

**Theorem (The bound for denominators as `DenominatorLe`).** Fix $\ell$ and $\iota$. Let $\vartheta$ be a twist with `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $e'_\ell$. Let $O$ be a descent pair with finite row and column types, $E$ an element of the group algebra of its chosen group, and $Z$ a subspace of the forms on $O$ that lies in the span of the lift generators of $Z$ for $\vartheta$, $E$ and $e'_\ell$. Then `DenominatorLe` $\iota_\ell$ $O$ $E$ $Z$ $(\beta_\ell \log \ell)$ holds, with $\beta_\ell = \mathrm{clearingBound}(\ell)$.

Lean: `New.Selmer.denominatorLe_clearingBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

It is proved in [the bound for denominators](/chapter/denominator-bound/#the-bound-for-denominators), at [line 1321](lean:New/Congruences/FirstOrder/DenominatorBound.lean#L1321). The operator is that of `exists_operator_det_clearingBound` ([line 1246](lean:New/Congruences/FirstOrder/DenominatorBound.lean#L1246)), and its three properties are the three conditions of `DenominatorLe`. The constant $\beta_\ell$ is given in Section 6.

### The lifts and their eigensystems

**Lemma (Range of the good lift).** Let $\vartheta$ be a tame character, $1 \leq j \leq m$, and $N$ a subspace of the forms on the larger space of the pair. Suppose that $N$ contains $\Theta_{j,\vartheta}\,y$ for every good Hecke eigenform $y$ on $W_j$ such that $\Theta_{j,\vartheta}\,y$ is in the range of $e_c$ for some good tuple family $c$. Then $N$ contains the range of the good lift.

Lean: `New.Data.range_goodLift_le` (New/Determinant/Chain/NormOfChain.lean).

**Lemma (Pieces of the good idempotent).** Let $f$ be a representation of the group algebra of the chosen group and $c$ a good tuple family. Then the range of $f(e_c)$ is in the range of $f(e_0)$.

Lean: `New.Data.range_tupleIdem_le` (New/Determinant/Chain/NormOfChain.lean).

Both are in [good forms and the factorization](/chapter/chain-determinant/#good-forms-and-the-factorization).

**Theorem (Equal multiplicities, vanishing form).** If a system $q$ does not occur in the good forms of $V'$, it does not occur in those of $V$.

Lean: `New.Data.goodForms_inf_eigenPart_eq_bot_of_eq_bot` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

This is [equal traces and equal multiplicities](/chapter/equal-multiplicities/#equal-traces-and-equal-multiplicities) of Volume 10.

**Lemma (Finitely many eigensystems).** For every subspace $N$ of the forms of principal level on $V$, the set of systems $q$ with $N \cap \mathcal{A}(V)_q \neq 0$ is finite.

Lean: `New.Data.finite_setOf_inf_eigenPart_ne_bot` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

This is in [eigensystems and projectors](/chapter/equal-multiplicities/#eigensystems-and-projectors).

**Theorem (Hecke polynomials of the single lift).** Let $\vartheta$ be a tame character and $1 \leq j \leq m$. Let $y$ be a form on $W_j$ in the eigenpart of $q$. Then $\Theta_{j,\vartheta}\,y$ has the Hecke polynomials of a lift of the values $(w, i) \mapsto q(w, i)$.

Lean: `New.Data.hasLiftHeckePolynomial_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

This is in [Hecke polynomials of the lift](/chapter/single-theta-lifts/#hecke-polynomials-of-the-lift).

**Theorem (The lift settings of the lifts).** Let $1 \leq j \leq m$, let $\vartheta$ be a twist, and let $c$ be a good tuple family. Then the $j$-th descent pair of $\vartheta$ with the labels $c$ is a lift setting for $\vartheta$.

Lean: `New.Selmer.isLiftSetting_descentPair` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

This is in [lift settings and representations of a type](/chapter/main-summands/#lift-settings-and-representations-of-a-type).

**Theorem (Hecke polynomials of the lift of a character).** The lift $\varphi_X$ = `X.trivialLift` has the Hecke polynomials of a lift of the trivial system $1$.

Lean: `New.LValueData.hasLiftHeckePolynomial_trivialLift` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

This is in [Hecke polynomials of lifts](/chapter/character-lifts/#hecke-polynomials-of-lifts).

**Lemma (The trivial twist).** The trivial twist has the trivial character of $U(1)(\mathbb{A}_E)$ and the empty modulus, and the twist under the trivial $m$-fold twist is the trivial twist.

Lean: `New.Data.toAutChar_one_and_toTwist_one_and_Q_one` (New/Determinant/Twist/FitTwists.lean).

This is in [twists and their powers](/chapter/twists-critical-pairs/#twists-and-their-powers).

### The line of a main pair

**Theorem (The projection bound).** Let $Y$ be the data of a theta lift from $U(1)$, and let the projection to the line of $\varphi$ = `Y.trivialLift` have denominator at most $\exp\beta$ at $\iota$ (`DenominatorLe`, with the idempotent of the labels $X - 1$ at the chosen places). Suppose that all stabilizers of $U(1)$ at the level `Y.chosenLevel` are trivial. Let $\Xi$, $\Xi'$ be test forms. Then
$$\|\iota\langle \mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle\| \leq \exp\big(\beta + v_\ell(\#\mathrm{StdClasses}(Y.\mathrm{chosenLevel})) \log \ell\big),$$
where $\mathrm{pr}$ is the projection to the line $\mathbb{C}\varphi$.

Lean: `New.Selmer.DenominatorLe.norm_inner_starProjection_le` (New/OneLift/HeckeValues/CentralAction.lean).

It is proved in [the central action and the projection bound](/chapter/hecke-values/#the-central-action-and-the-projection-bound) of Volume 11.

### Small facts

**Lemma (The modulus is prime to the bad places).** If $I$ is a set of places that is auxiliary for `badPlaces D ℓ`, then $\ell$ and $M N$ are prime to $\prod_{w \in I} q_w$.

Lean: `New.Selmer.coprime_prod_q_of_isAuxiliary` (New/Congruences/Selmer/ClassSums.lean).

This is in [twist measures of critical pairs](/chapter/twisting-theorem/#twist-measures-of-critical-pairs).

**Lemma (Trivial stabilizers).** If $K \leq$ `D.chosenLevel` and the index type $n$ has at most $2\,n_m$ elements, then the stabilizer of every point $gK$ in the rational unitary group is trivial.

Lean: `New.Data.classAut_eq_bot_of_le_chosenLevel` (New/UpperBound/Objects/LiftChains.lean).

This is in [the target lattice](/chapter/integral-target-forms/#the-target-lattice) of Volume 1.

**Lemma (Heights from local bounds).** If reals $e_\ell$ have $\sum_{\ell \in T} e_\ell \leq c$ for every finite set $T$ of primes, and $\|\iota(y_\kappa)\| \leq \exp(e_\ell)$ for every $\kappa = (\ell, \iota)$, then the family $y$ has height at most $c$.

Lean: `New.HeightLe.of_le` (New/Reduction/Lattices/Heights.lean).

This is in [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers).

**Lemma (Comparison of sizes).** If $|F| \leq \exp l$, $\exp l' \leq G$ and $l < l'$, then $F \leq G$.

Lean: `New.Data.le_of_hasLogBound` (New/Reduction/Data/Magnitudes.lean).

The bounds $|F| \leq \exp l$ and $\exp l' \leq G$ are found by instance search, and $l < l'$ by a tactic ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)). Sections 6 and 7 use this lemma for every comparison of a constant with a scale of the data. Its sibling `New.Data.nat_le_of_hasLogBound` gives $1 \leq m$, so that $j = 1$ is a lift index, and $\#\mathrm{Unit} = 1 \leq 2 n_m$.

**Remark (Formalization).** A use of `le_of_hasLogBound` hides the comparison in the instances. The proof text shows only the two sides. To check a comparison by hand, read the instances of `HasLogUpper` and `HasLogLower` for the two sides. Section 6 writes out the two sides of each comparison.
