---
title: The dimension of the target
lean:
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
decls:
  - New.Data.decreasingPosition_paramW
  - New.Data.finrank_principalForms_spaceW
  - New.Data.targetDim_le_card_mul_besselDegree_mul_mass
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The dimension of the target

The second moment bound of [the chapter on moments](/chapter/moments/) has the main second moment $D_X^2/(\deg \cdot \mathrm{mass}_r)$ on its right side. The hypothesis of the spread theorem has $d_T$ times the second moment on its left side and $\#\bar G \cdot D_X^2$ on its right side. So the proof needs an upper bound for $d_T$ that cancels the denominator $\deg \cdot \mathrm{mass}_r$. This section proves it. The bound is an upper bound only. The proof of Theorem B does not need the exact value of $d_T$.

### The objects

The space $Y_0$ is indefinite, and there is no direct count of forms on it. [Equal multiplicities by the trace formula](/chapter/equal-multiplicities/) moves the count to a definite space. The definite space is $W_m = D.\mathtt{spaceW}\ D.m$, the last of the spaces $W_j$, $1 \leq j \leq m$. The forms of principal level on $W_m$ of the parameter $D.\mathtt{paramW}$ form the space $D.\mathtt{principalForms}\ W_m$. The level is $D.\mathtt{chosenLevel}$, the level that is trivial modulo the chosen places. Three numbers enter.

1. $\#\bar G$, the order of the finite group, as `Nat.card D.chosenGL`.
2. $\mathrm{mass}_r = \mathtt{mass}\ E\ r$, the class sum of the constant function $1$ at the standard level in rank $r$. It is positive.
3. $\deg = D.\mathtt{filling}.\mathtt{besselDegree}$, the product over the infinite places $v$ of the degree constants of the chosen Bessel systems. It is positive.

**Remark (Formalization).** The Bessel systems of the filling are chosen. The definition `New.Data.filling` sets the system at $v$ to `(D.exists_besselSystem v).choose`. So $\deg$ is the product of the degrees of chosen systems. The proof below uses only the field `deg_eq` of the type of these systems, which fixes the degree as the Weyl dimension polynomial of the parameter. So the value of $\deg$ does not depend on the choice.

### The parameter on the definite space

**Lemma (The parameter decreases along the numbering).** For each infinite place $v$ and each row index $i$, exactly $D.\mathtt{basisNumber}\ i$ entries of the parameter $D.\mathtt{paramW}\ v$ are larger than its entry at $i$.

Lean: `New.Data.decreasingPosition_paramW` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* The function `decreasingPosition` counts the larger entries. The entry of $D.\mathtt{paramW}\ v$ at $j$ is larger than the entry at $i$ if and only if the number of $j$ is smaller than the number of $i$ (`paramW_lt_iff`). The count of the numbers below $D.\mathtt{basisNumber}\ i$ is $D.\mathtt{basisNumber}\ i$ (`card_filter_basisNumber`). $\square$

The parameter $D.\mathtt{paramW}\ v$ has a gap for the definite signs. This is the instance `hasGap_signsY_paramW` of New/UpperBound/Objects/Rows.lean. A parameter with a gap is twice the Harish-Chandra parameter of a weight $(\kappa, e)$ (`exists_isHCParam_of_hasGap`). The two proofs below begin by taking this weight. The weight is obtained by `obtain`, so it is a witness of an existence statement. The results do not mention it.

### The forms of principal level

**Lemma (Forms of principal level on the definite space).** The forms of principal level on $W_m$ have dimension

$$\dim D.\mathtt{principalForms}(W_m) = \#\bar G \cdot \mathrm{mass}_r \cdot \prod_{v} d\bigl(\mathtt{toHCParam}\ 1\ (D.\mathtt{paramW}\ v)\bigr),$$

where $d$ is the formal degree of the compact parameter with all signs $1$.

Lean: `New.Data.finrank_principalForms_spaceW` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Let $(\kappa, e)$ be the weight with $D.\mathtt{paramW} = 2(\kappa, e)$, as above.

Step 1: the level is free. For every $g$ in the finite adelic group, the stabiliser $\Gamma \cap g K g^{-1}$ of the class of $g$ is trivial, where $\Gamma$ is the group of rational points and $K = D.\mathtt{chosenLevel}$. This is [Lemma](/decl/New.Data.classAut_eq_bot_of_le_chosenLevel/), with $K \leq D.\mathtt{chosenLevel}$ by reflexivity. Its hypothesis on the rank, $r \leq 2n_m$, is a size bound of $D$ (`nat_le_of_hasLogBound`).

Step 2: the class sum. The level $K$ is the preimage of the trivial subgroup under the reduction at the chosen places. By [Theorem](/decl/New.classSum_one_of_le/) the class sum of $1$ at $K$ is the relative index $[K_0 : K]$ times the class sum at the standard level $K_0$. The relative index is the index of the trivial subgroup in $\bar G$ (`relIndex_levelOf`), which is $\#\bar G$. The class sum at $K_0$ is the mass in rank $\#\mathtt{RowIndex} = r$ ([Theorem](/decl/New.classSum_stdRatPoints_eq_mass/) and `card_rowIndex`). So the class sum of $1$ at $K$ is $\#\bar G \cdot \mathrm{mass}_r$.

Step 3: the count. The forms of principal level on $W_m$ are the algebraic forms of weight $(\kappa, e)$ and level $K$ ([Definition](/decl/New.Space.algFormEquiv/), a linear equivalence, so it keeps the dimension). Since the level is free, their dimension is the number of classes times the dimension of the weight ([Theorem](/decl/New.finrank_levelSpace_smoothFormRep/)). The number of classes is the class sum of $1$ ([Theorem](/decl/New.card_classes_eq_classSum/)). The weight is a product over the infinite places, so its dimension is a product (`Module.finrank_pi`). The dimension of the weight is the product of the formal degrees of the compact parameters (`IsHCParam.prod_formalDegree`, a case of Schur orthogonality for a compact group). Step 2 gives the class sum. $\square$

The proof uses the free level in the form of [the section on algebraic forms](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups) of Volume 4. At a free level each class contributes a full copy of the weight, so no class has a smaller space of invariants.

### The bound

**Theorem (Dimension of the target).** The dimension of the target satisfies

$$d_T \leq \#\bar G \cdot \deg \cdot \mathrm{mass}_r.$$

Lean: `New.Data.targetDim_le_card_mul_besselDegree_mul_mass` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Let $(\kappa, e)$ be the weight as above.

Step 1: the degrees agree. The claim is

$$\prod_v d\bigl(\mathtt{toHCParam}\ 1\ (D.\mathtt{paramW}\ v)\bigr) = \deg.$$

The right side is the product of the degree constants of the chosen Bessel systems. The filling fits the space $Y_0$ ([Theorem](/decl/New.Data.filling_fits/)), and so each chosen system is of discrete series type for its parameter (`isDiscreteSeriesBessel`). The field `deg_eq` of that type says that the degree constant is the Weyl dimension polynomial of the parameter. On the left side, Harish-Chandra's formula says that the formal degree of a parameter with a large gap is the same Weyl dimension polynomial ([Theorem](/decl/New.Orbital.harish_chandra_degree_and_orbital/)). The gap comes from the weight (`h_wt.hasGap`). The source closes this step by `simp` with these four facts.

Step 2: the chain. By [Theorem](/decl/New.Data.targetDim_eq_finrank_goodForms_spaceW/) at the lift index $j = m$, which lies in $[1, m]$ because $1 \leq m$ is a size bound of $D$, the target has the dimension of the good forms on $W_m$:

$$d_T = \dim D.\mathtt{goodForms}(W_m).$$

The good forms are a subspace of the forms of principal level, so their dimension is at most $\dim D.\mathtt{principalForms}(W_m)$ (`Submodule.finrank_le`). The lemma on forms of principal level and Step 1 give

$$d_T \leq \#\bar G \cdot \mathrm{mass}_r \cdot \deg.$$

This is the claim, after a change of the order of the factors. $\square$

**Remark (Formalization).** The result is an inequality of real numbers. The left side is the cast of the natural number `D.targetDim`, and the right side has the real number $\deg$. The order is `Nat.card`, which is $0$ for an infinite type. Lean knows that $\bar G$ is finite, as a product of general linear groups over finite residue fields over a finite set of places. So `Nat.card D.chosenGL` is the true order, and it is positive (`Nat.card_pos`).

### Where the bound is used

The bound is used once, in the proof of the second moment with the dimension (the section on [the scaled Poincaré map](/chapter/proof-of-theorem-b/#the-scaled-poincar-map)). There it multiplies the bound

$$\sum_{s \in \bar G}\|L^*sL\|^2 \leq (1 + 9b^{-4})\,\frac{D_X^2}{\deg \cdot \mathrm{mass}_r}.$$

The product of the two right sides is $\#\bar G\,(1 + 9b^{-4})\,D_X^2$, because $\deg$ and $\mathrm{mass}_r$ cancel. Both are positive: $\deg > 0$ since each degree constant of a Bessel system is positive (`besselDegree_pos`), and $\mathrm{mass}_r > 0$ ([Theorem](/decl/New.mass_pos/)). The cancellation needs these two signs. A bound $d_T \leq \#\bar G \deg\,\mathrm{mass}_r$ with $\deg = 0$ would give no information, and the right side of the moment bound would be the junk value of a division by $0$.

The bound is not sharp in general. The good forms are only a part of the forms of principal level. The proof of Theorem B accepts this loss. The moment hypothesis of the spread theorem needs an upper bound for $d_T$ times the second moment, so an upper bound for $d_T$ is the direction that the proof needs.
