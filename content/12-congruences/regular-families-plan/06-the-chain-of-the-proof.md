---
title: The chain of the proof
lean:
  - New/Congruences/FitTwistsExist.lean
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean
  - New/Congruences/FirstOrder/EvenClasses.lean
  - New/Congruences/FirstOrder/DenominatorBound.lean
  - New/Congruences/Selmer/TwistingTheorem.lean
  - New/OneLift/HeckeValues/CentralAction.lean
decls:
  - New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial
  - New.Selmer.IsMainSummandLike
  - New.Selmer.HasLiftTrace
  - New.Selmer.IsMainSummand
  - New.Selmer.exists_isMainSummand_descentPair
  - New.Selmer.exists_isMainSummand_mainPair
  - New.Selmer.IsAuxTwist
  - New.Selmer.HasDivisibleSelmerLengthLe
  - New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe
  - New.Selmer.exists_mFoldTwist_selmerLengthLe_inv_ratio_le
  - New.Selmer.denominatorLe_clearingBound
  - New.Selmer.denominatorLe_range_goodLift
  - New.Selmer.denominatorLe_span_trivialLift
  - New.Selmer.DenominatorLe.norm_inner_starProjection_le
  - New.Selmer.exists_mFoldTwist_hasDenominatorsLe
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chain of the proof

This section states the steps from the twisting theorem and Ribet's method to the theorem on regular families, in the order of the top file. Each step is a declaration of the source with the hypotheses it has. The later chapters of the volume prove the steps that are not proved here.

### Step 1: finitely many eigensystems

The space of lifts changes with the twist. The Hecke eigensystems that it contains do not.

**Theorem (Splitting, pairs of rank $r$).** Let $\vartheta$ be a twist and $1 \leq j \leq m$. The range of $\mathrm{goodLift}(\vartheta, j)$ lies in the span of the forms $y$ in the range with two properties.

1. There is a tuple $c$ of labels, one polynomial over the residue field at each chosen place, such that $y$ is in the range of the projection to the type $c$, the tuple $c$ is in lift setting for the descent pair of $(\vartheta, j)$ and for $\vartheta$, and the range of the projection to the type $c$ lies in the image of $e_0$. A tuple in lift setting has labels of degree $r$, some label over each level prime is primitive, and no twisted label has the root $1$.
2. There is a system $q(w, i)$ of Hecke eigenvalues, indexed by the finite places $w$ and the numbers $i$ of the Hecke operators, such that $q$ occurs in a nonzero good form on $W_m$, and at the split places off the level the Hecke polynomial of $y$ is that of a lift of $q$.

Lean: `New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial` (New/Congruences/FitTwistsExist.lean).

*Proof.* The space of lifts is spanned by the lifts of good eigenforms on $W_j$. Let $y$ be a nonzero good eigenform on $W_j$ with the system $q$ and the type $c$. If $q$ did not occur in a good form on $W_m$, it would not occur on $W_j$ either, since the good eigenspaces for $q$ on the spaces $W_j$ vanish together. So $q$ occurs on $W_m$. The lift of $y$ has the Hecke polynomial of a lift of $q$, and the type $c$ moves to a type in lift setting for the descent pair. The lift is in the range and in the set. $\square$

The set of systems that occur in good forms on $W_m$ is finite (`New.Data.finite_setOf_inf_eigenPart_ne_bot`), since the good forms on $W_m$ form a finite dimensional space. This set does not depend on $\vartheta$ or $j$.

### Step 2: main summands

A main summand is an $\ell$-adic representation of the Galois group of $E$ that gives the traces of the representations attached to all twisted lifts of a system.

**Definition (Representations of main summand type).** A representation $R$ with the index type $n$ is *like a main summand* for $t$ and the jumps $J$ if:

1. $R$ is conjugate self-dual of twist $1 - t$, with the jumps $J$ at the complex embeddings and with empty level (`IsConjSelfDualOfLevel` $D$ $t$ $J$ $\emptyset$ $R$);
2. the jumps satisfy `IsMainSummandWeights` $D$ $(\#n)$ $t$ $J$;
3. at each place above $p_0 p_1$ prime to $\ell$, a power prime to the place kills the image of inertia, and two determinants have bounded valuation;
4. the image of a lattice spans all matrices;
5. the image contains a scalar with a prescribed cyclotomic character, and some inertia element acts by a scalar of large order modulo the maximal ideal.

Lean: `New.Selmer.IsMainSummandLike` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Definition (The trace of a lift).** For a character $\psi$, a representation $R$, an integer $t$ and a representation $u$, the relation `HasLiftTrace` $\psi$ $R$ $t$ $u$ says that
$$\mathrm{tr}\, u(g) = \psi(g)\, \mathrm{tr}\, R(g) + \sum_{e < t} \mathrm{cyc}^{-1}(g)^{e}$$
for every $g$ in the Galois group of $E$, where $\mathrm{cyc}$ is the cyclotomic character.

Lean: `New.Selmer.HasLiftTrace` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Definition (Main summands).** A representation $R$ is a *main summand* for a descent pair $O$ and Hecke values $z$ if:

1. $R$ is like a main summand for $t = O.\mathrm{rankDiff}$ and some jumps;
2. for every tame character $\vartheta$, every descent pair $V$ with $V.\mathrm{u1Char} = O.\mathrm{u1Char} \cdot \vartheta$, every form $y$ for $V$ that lifts $z$ and is an eigenform with Hecke polynomials $H$, and every representation $S$ attached to $H$, the normalized representation of $S$ has the trace of $\vartheta^{-1}$ times $R$ plus the first $V.\mathrm{rankDiff}$ powers of $\mathrm{cyc}^{-1}$ (`HasLiftTrace`).

Lean: `New.Selmer.IsMainSummand` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** The relation `Attached` $H$ $S$ (Lib/GaloisRep/Main/AttachedRepresentations.lean) is weak. It asks that $S$ is continuous with a nondegenerate trace form, and that for every $\eta > 0$ the coefficients of the characteristic polynomial of $S$ at Frobenius are within $\eta$ of $\iota_\ell(H(w))$ *for most Frobenius data*. It does not ask the equality at every unramified place. Condition 2 quantifies over every such $S$, so it is a strong condition on $R$.

**Theorem (Main summands of the lifts).** Let $q$ occur in a nonzero good form on $W_m$ and let $1 \leq j \leq m$. Then there is a representation $T$ of rank $r$ that is a main summand for the $j$-th descent pair of the trivial twist and the system $q$.

Lean: `New.Selmer.exists_isMainSummand_descentPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

**Theorem (Main summands of the main pairs).** Let $p = (\nu, z)$ be a main pair for $j$. Then there is a representation $T$ of rank one that is a main summand for the descent pair of the untwisted rank-one lift `p.lValueData` and the constant system $1$.

Lean: `New.Selmer.exists_isMainSummand_mainPair` (New/Congruences/FitTwistsExist.lean).

The first theorem is the subject of [main summands](/chapter/main-summands/). The second comes from the trivial representation of rank one, whose only jump is $0$. Its proof is in the top file.

### Step 3: the twisting theorem

**Definition (Auxiliary twists).** For finite sets $S$ and $Q$ of finite places of $E$, a character $\psi$ of the Galois group with values in $\overline{\mathbb{Q}}_\ell$, and $c \in [0, \infty]$, the relation `IsAuxTwist` $S$ $Q$ $\psi$ $c$ holds if:

1. $Q$ is auxiliary for $S$: its places have prime norm, they and their conjugates are not in $S$, and their conjugates are not in $Q$;
2. $\psi$ comes from the norm-one torus with the modulus $Q$, and no place of $Q$ lies above $\ell$ (`IsFromU1`);
3. for some tame generators $\sigma_w$ at the places $w$ of $Q$, $\sum_{w \in Q} \mathrm{ellVal}(\psi(\sigma_w) - 1) \leq c$.

Lean: `New.Selmer.IsAuxTwist` (New/Congruences/FirstOrder/EvenClasses.lean).

**Definition (Short Selmer groups).** For a character $\psi$, a representation $R$, a set $Q$, an element $\gamma$ of the Galois group, a scalar $\zeta$ and $\mathrm{sel} \in [0, \infty]$, the relation `HasDivisibleSelmerLengthLe` $\psi$ $R$ $Q$ $\gamma$ $\zeta$ $\mathrm{sel}$ holds if, for all large coefficient rings $O$, there are models $u$, $\psi'$, $\zeta'$ of $R$, $\psi$, $\zeta$ over $O$ such that:

1. $\gamma$ acts on the lattice $\psi' u$ by the scalar $\zeta'$, $\zeta' - 1$ is a unit, and $\gamma$ lies in an inertia group away from $\ell$ (`IsTwistedLattice`);
2. the Selmer group of $\psi' u$ with coefficients in $\mathrm{Frac}(O)/O$ has length at most $\mathrm{sel}$, where $O/\ell$ has length $1$. The Selmer group is formed by the continuous cocycles that are unramified off $\ell p_0 p_1$, $Q$ and $\overline{Q}$, crystalline above $\ell$, and zero at $\gamma$.

Lean: `New.Selmer.HasDivisibleSelmerLengthLe` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** Two points of this definition differ from the usual form. First, "for all large coefficient rings" is the filter `Filter.atTop` on the coefficient rings, so the bound holds eventually, not for one fixed ring. Second, the Selmer group is a group of cocycles that vanish at $\gamma$, not a group of cohomology classes. Since $\gamma$ acts by $\zeta'$ and $\zeta' - 1$ is a unit, each class has exactly one cocycle that vanishes at $\gamma$: a coboundary $g \mapsto (g - 1)v$ vanishes at $\gamma$ only if $(\zeta' - 1)v = 0$, so only if $v = 0$. So the cocycles that vanish at $\gamma$ stand for the classes.

**Theorem (The twisting theorem).** Fix $\ell$ and $\iota$. Let $I$ be a finite type, and let $R_i$, for $i \in I$, be representations, each like a main summand for some $t$ and $J$. Then there is an $m$-fold twist $\tau$ such that, for every $1 \leq j \leq m$, the power $\xi = \tau^j$ has three properties:

1. `IsAuxTwist` (badPlaces $D$ $\ell$) $\xi.Q$ $\xi.\mathrm{invAvatar}$ $e'_\ell$;
2. for every $i$ there are $\gamma$ and $\zeta$ with `HasDivisibleSelmerLengthLe` $\xi.\mathrm{invAvatar}$ $R_i$ $\xi.Q$ $\gamma$ $\zeta$ $e'_\ell$;
3. for every ramified critical pair $p$ and every sign $s$, $\mathrm{ellVal}(\iota_\ell(p.\mathrm{ratio}(\xi, s))) \leq e'_\ell$.

Lean: `New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe` (New/Congruences/Selmer/TwistingTheorem.lean).

The bad places are those that divide $\ell p_0 p_1 N$. The proof is the subject of [tied Selmer groups](/chapter/tied-selmer-groups/) and [the twisting theorem](/chapter/twisting-theorem/). The relation to the literature that the source gives in this file names Mazur and Rubin, *Diophantine stability* (2018), Kriz and Nordentoft, *Horizontal p-adic L-functions* (2023), and Hida, *Non-vanishing modulo p of Hecke L-values* (2004), as related work on twists that make Selmer groups short or keep $L$-values barely divisible.

**Theorem (The twisting theorem for two families).** Let $A$ and $B$ be finite types, and let $R_a$, $a \in A$, have rank $r$ and $R'_b$, $b \in B$, have rank one, each like a main summand for some $t$ and $J$. Then there is an $m$-fold twist $\tau$ such that, for every $1 \leq j \leq m$, with $\vartheta = \tau^j$:

1. `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $e'_\ell$;
2. every $R_a$ and every $R'_b$ has a short Selmer group, as in the twisting theorem, with the bound $e'_\ell$;
3. for every ramified critical pair $p$ and every sign $s$, $\|\iota_\ell(p.\mathrm{ratio}(\vartheta, s)^{-1})\| \leq \exp(e'_\ell \log \ell)$.

Lean: `New.Selmer.exists_mFoldTwist_selmerLengthLe_inv_ratio_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Join the two families into one family over $A \oplus B$. The index type is the rows of the data on the left summand and the one-point type on the right (`SummandCoordIndex`). The twisting theorem gives $\tau$. Conditions 1 and 2 are its first two conditions. For condition 3, $\mathrm{ellVal}(x) \leq e$ means that $x \neq 0$ and $\|x\| \geq \ell^{-e}$. Then $\|x^{-1}\| \leq \ell^{e} = \exp(e \log \ell)$. $\square$

### Step 4: Ribet's method for each space

**Theorem (The bound for denominators as `DenominatorLe`).** Let $\vartheta$ be a twist with `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $e'_\ell$, and let $Z$ lie in the span of the lift generators for the bound $e'_\ell$. Then `DenominatorLe` $\iota_\ell$ $O$ $E$ $Z$ $(\beta_\ell \log \ell)$ holds, with $\beta_\ell = \mathrm{clearingBound}(\ell)$.

Lean: `New.Selmer.denominatorLe_clearingBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Take $\Lambda$ from the operator form of Section 4. Its three conditions are the three clauses of `DenominatorLe`. $\square$

**Theorem (Denominator for the space of lifts).** Let $\vartheta$ satisfy `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $e'_\ell$, and let $1 \leq j \leq m$. Suppose that every system $q$ that occurs in a nonzero good form on $W_m$ has a main summand $R$ for the $j$-th descent pair of the trivial twist, with `HasDivisibleSelmerLengthLe` $\vartheta.\mathrm{invAvatar}$ $R$ $\vartheta.Q$ $\gamma$ $\zeta$ $e'_\ell$ for some $\gamma$, $\zeta$. Then `DenominatorLe` holds for the descent pair of $(\vartheta, j)$, the idempotent $e_0$, the range of $\mathrm{goodLift}(\vartheta, j)$ and the constant $\beta_\ell \log \ell$.

Lean: `New.Selmer.denominatorLe_range_goodLift` (New/Congruences/FitTwistsExist.lean).

*Proof.* The characters satisfy $O.\mathrm{u1Char} = V.\mathrm{u1Char} \cdot \vartheta$, for $O$ the descent pair of $(\vartheta, j)$ and $V$ that of the trivial twist. By Step 1, the range lies in the span of forms $y$ with a type in lift setting and a system $q$ that occurs on $W_m$. With the main summand $R$ of $q$, each such $y$ is a lift generator. The previous theorem applies. $\square$

**Theorem (Denominator for the line of a main pair).** Let $\vartheta$ satisfy `IsAuxTwist` as above, let $p$ be a main pair for $j$, and let $R$ be a main summand for the untwisted rank-one lift of $p$ and the system $1$, with a short Selmer group for $\vartheta^{-1}$ and the bound $e'_\ell$. Then `DenominatorLe` holds for the descent pair of `p.lValueData` at $\vartheta$, the idempotent of the labels $X - 1$ at the chosen places, the line $\mathbb{C}\,\varphi$ of the lift $\varphi$ = `trivialLift`, and the constant $\beta_\ell \log \ell$.

Lean: `New.Selmer.denominatorLe_span_trivialLift` (New/Congruences/FitTwistsExist.lean).

*Proof.* The line is spanned by $\varphi$, and $\varphi$ is a lift generator: it has the labels $X - 1$, which are in lift setting for a main pair, it lifts the system $1$, and $R$ is its main summand. The theorem on `DenominatorLe` applies. $\square$

**Remark (Formalization).** The statement uses `open scoped Classical` to form the idempotent of the labels. The proof that $\varphi$ is in the range of the projection to the type uses `convert`, since the two instances of decidable equality on the index type agree only as propositions.

**Theorem (From the line to inner products).** Let $Y$ be data for a theta lift from $U(1)$, and let the projection to the line of $\varphi$ = `Y.trivialLift` have denominator at most $\exp \beta$ (`DenominatorLe`, with the idempotent of the labels $X - 1$). Suppose all stabilizers of $U(1)$ at the chosen level are trivial. Let $\Xi$, $\Xi'$ be test forms. Then $\|\iota\langle \mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle\|$ is at most $\exp \beta$ times the $\ell$-part of the class number $h_{\mathrm{std}}$ of $U(1)$ at that level.

Lean: `New.Selmer.DenominatorLe.norm_inner_starProjection_le` (New/OneLift/HeckeValues/CentralAction.lean).

This theorem is in Volume 11. It is the reason for the term $v_\ell(h_{\mathrm{std}}) \log \ell$ in the constant of Section 3.

### Step 5: one prime

**Theorem (A twist with few congruences at one prime).** For a prime $\ell$ and $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$, there is an $m$-fold twist $\tau$ such that:

1. $\ell$ is prime to $\mathrm{Nm}\,Q$ of $\tau$;
2. for every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s$, $\|\iota(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e'_\ell \log \ell)$;
3. for every $1 \leq j \leq m$, the twist $\tau^j$ has denominators at most $\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$ at $\iota$ (`HasDenominatorsLe`).

Lean: `New.Selmer.exists_mFoldTwist_hasDenominatorsLe` (New/Congruences/FitTwistsExist.lean).

*Proof.* Let $\mathcal{S}$ be the finite set of systems that occur in nonzero good forms on $W_m$. For each pair $(j, q)$ with $q \in \mathcal{S}$, choose a main summand $R_{j,q}$ by Step 2. For each main pair, choose a main summand $R'_p$ of rank one. These are finitely many representations, each like a main summand. The twisting theorem for two families gives $\tau$, and for every $j$ it gives the auxiliary condition, short Selmer groups for all $R_{j,q}$ and $R'_p$, and condition 2.

For condition 1, the modulus of $\tau^1$ is auxiliary for the bad places, which contain the places above $\ell$. So no place of the modulus lies above $\ell$, and its norm is prime to $\ell$ (`coprime_prod_q_of_isAuxiliary`).

For condition 3, fix $j$. The theorem on the space of lifts, with the summands $R_{j,q}$, gives `DenominatorLe` with the constant $\beta_\ell \log \ell$. The lemma of Section 3 from the general form to the special form, with $\beta_\ell \log \ell \leq \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$, gives the first clause. For the second clause, let $p$ be a main pair for $j$ and $\Xi$, $\Xi'$ test forms. The theorem on the line of a main pair, with $R'_p$, gives `DenominatorLe` on the line. The stabilizers of $U(1)$ at the chosen level are trivial (`New.Data.classAut_eq_bot_of_le_chosenLevel`). The theorem from the line to inner products gives the bound $\exp(\beta_\ell \log \ell) \cdot \ell^{v_\ell(h_{\mathrm{std}})} = \exp(\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell)$. $\square$

Section 3 gives the proof of the theorem on regular families from this result and the sums of Section 5. The whole chain is put together in [the proof of the existence of regular families](/chapter/proof-of-regular-families/).

### Where the deep steps are proved

The steps above use four deep inputs. Each one is the subject of later chapters.

1. Ribet's method to first order, which gives the operator for one lift generator: [Ribet elements](/chapter/ribet-elements/), [first order deformations](/chapter/first-order-deformations/), [tied traces and even classes](/chapter/tied-traces/), and [the bound for denominators](/chapter/denominator-bound/).
2. The main summands: [main summands](/chapter/main-summands/).
3. The twisting theorem: [tied Selmer groups](/chapter/tied-selmer-groups/) and [the twisting theorem](/chapter/twisting-theorem/).
4. The local loss above $\ell$ and the bounds for cup products that it needs: [exponent lattices and Kummer charts](/chapter/exponent-lattices/), [cup products](/chapter/cup-products/) and [the local loss](/chapter/local-loss/).
