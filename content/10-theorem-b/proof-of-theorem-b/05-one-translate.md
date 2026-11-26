---
title: One translate
lean:
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
decls:
  - New.Data.goodPoincare
  - New.Data.comap_scaledPoincare_eq_comap_goodPoincare
  - New.Data.isSpread_goodPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One translate

This section proves that the translates of the Poincaré map spread. It is the theorem that [the plan](/chapter/theorem-b-plan/#theorem-b-and-its-input) calls the analytic input of Theorem B. The proof joins the two inputs of [the scaled Poincaré map](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) with the spread theorem of [the chapter on few translates](/chapter/few-translates/#one-translate). The only work is to pass from the scaled map $L$ in coordinates to the unscaled map on the source forms.

### The maps

**Definition (Good Poincaré maps).** For $s \in \bar G$, the map $\mathfrak{g}_s : X \to \mathrm{target}$ is

$$\mathfrak{g}_s = \#\bar G\cdot\rho(e_0)\,\rho(s)\,\mathcal{P},$$

the Poincaré map, then the translation by $s$, then the projection onto the good forms, times the order of $\bar G$.

Lean: `New.Data.goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

In the source the composite of the translation and the projection is `D.goodProjTranslate s`. Its codomain is the range of $\rho(e_0)$, by `rangeRestrict`, so the map lands in the target and not in the larger space of forms of principal level.

The factor $\#\bar G$ comes from Theorem A, where it clears a denominator of $e_0$. For Theorem B it is a nonzero scalar and does not matter.

The definition of spread is from [the chapter on few translates](/chapter/few-translates/#one-translate). A family $B_s : V \to W$ spreads with error $\eta$ (`IsSpread B η`) if for every subspace $F$ of $W$ there is an $s$ with

$$\dim B_s^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \eta\Bigr)\dim V,\qquad \alpha = \frac{\dim F}{\dim W}.$$

**Remark (Formalization).** The share $\alpha$ is a quotient of two values of `finrank`, as real numbers. If $\dim W = 0$ the quotient is the junk value $0$. In this chapter $W$ is the target, and $d_T > 0$ by [the lemma that the target is not zero](/decl/New.Data.finrank_targetForms_ne_zero/). So $\alpha$ is the true share. The spread statement itself does not need this.

### From coordinates to source forms

**Lemma (Preimages under the two maps).** Let $s \in \bar G$ and let $F$ be a subspace of the target. Then

$$\bigl(e_0\,\rho(s)\,L\bigr)^{-1}(F) = \kappa\Bigl(\mathfrak{g}_s^{-1}(F)\Bigr),$$

where the left side is the preimage under `rangeRestrict` of $\rho(e_0)$ after $\rho(s)L$, and the right side is the preimage of $\mathfrak{g}_s^{-1}(F)$ under $\kappa^{-1}$.

Lean: `New.Data.comap_scaledPoincare_eq_comap_goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Let $\varphi$ be a vector of the Euclidean space and let $y = \rho(e_0)\rho(s)\mathcal{P}(\kappa^{-1}\varphi)$, a target form. By the definition of $L$, the left map sends $\varphi$ to $c_P\,y$. By the definition of $\mathfrak{g}_s$, the right map sends $\varphi$ to $\#\bar G\cdot y$. The numbers $c_P$ and $\#\bar G$ are not zero ([Lemma](/decl/New.Data.poincareScale_pos/) and `Nat.card_pos`). A subspace contains $c\,y$ for $c \neq 0$ if and only if it contains $y$ (`smul_mem_iff`). So $\varphi$ lies in the left side if and only if $y \in F$, if and only if $\varphi$ lies in the right side. $\square$

### The theorem

**Theorem (One translate).** The maps $\mathfrak{g}_s$, $s \in \bar G$, spread with error $\tfrac32(8b^2)^{-1}$. That is, for every subspace $F$ of the target, with share $\alpha = \dim F/d_T$, there is an $s \in \bar G$ with

$$\dim\mathfrak{g}_s^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \frac{3}{16b^2}\Bigr)\dim X.$$

Lean: `New.Data.isSpread_goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Fix a `Fintype` instance on $\bar G$ from its finiteness (`Fintype.ofFinite`). Let $\rho = D.\mathtt{principalRep}\ Y_0$ and $\varepsilon = (8b^2)^{-1}$. The proof applies [Theorem](/decl/New.isSpread_of_second_moment/) to $\Gamma = \bar G$, the representation $\rho$, the projection $\mathrm{pr}_0 = \rho(e_0)$, the map $B = L$ and this $\varepsilon$. It checks the six hypotheses of that theorem.

1. $\rho$ is unitary. An element acts by right translation, and the Petersson inner product is invariant (`Space.inner_formRep`).
2. $\rho(e_0)$ is a symmetric projection. The element $e_0$ is a central idempotent ([Theorem](/decl/New.Data.isCentralProj_e₀/)), and a central idempotent acts by a symmetric projection in a unitary representation ([Lemma](/decl/New.IsCentralProj.isSymmetricProjection/)).
3. $\rho(e_0)$ commutes with each $\rho(s)$. The coefficients of $e_0$ are a class function, so $e_0$ commutes with each group element in the group algebra. Apply the algebra map $\rho$.
4. $0 \leq \varepsilon$. This is clear.
5. The near isometry. $e_0L$ has error $5b^{-4}$ ([Theorem](/decl/New.Data.isNearIsometry_e₀_comp_scaledPoincare/)). The size bound $5b^{-4} \leq (8b^2)^{-1}$ (`le_of_hasLogBound`) and [Lemma](/decl/New.IsNearIsometry.mono/) give error $\varepsilon$.
6. The moment. The hypothesis is

$$\dim\operatorname{range}\rho(e_0)\cdot\sum_{s}\|L^*\rho(s)L\|^2 \leq \#\bar G\,(1 + \varepsilon)\,(\dim\mathbb{C}^{\mathrm{Classes}\times\mathrm{BesselCoord}})^2.$$

The dimension of the range is $d_T$. The dimension of the Euclidean space is $D_X$ ([Lemma](/decl/New.Filling.finrank_source_eq_sourceDim/)). The size bound $9b^{-4} \leq (8b^2)^{-1}$ (`le_of_hasLogBound`) lowers the right side of [the lemma with the dimension](/decl/New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le/) to the right side here.

The theorem gives, for $F$ a subspace of the target, an $s$ with

$$\dim\bigl(e_0\rho(s)L\bigr)^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \frac32\varepsilon\Bigr)\dim\mathbb{C}^{\mathrm{Classes}\times\mathrm{BesselCoord}}.$$

Here $\alpha = \dim F/d_T$ is the same share as in the claim, because the codomain is the target in both. By the lemma on preimages, the left side is $\dim\kappa(\mathfrak{g}_s^{-1}(F))$. A linear equivalence keeps dimensions, both for the subspace and for the whole space ($\dim\mathbb{C}^{\mathrm{Classes}\times\mathrm{BesselCoord}} = \dim X$). This is the claim, since $\tfrac32(8b^2)^{-1} = 3/(16b^2)$. $\square$

### The two size bounds

The proof uses two size bounds, each proved by `le_of_hasLogBound`.

| Bound | Equivalent form | Used for |
|---|---|---|
| $5b^{-4} \leq (8b^2)^{-1}$ | $b^2 \geq 40$ | the near isometry with error $\varepsilon$ |
| $9b^{-4} \leq (8b^2)^{-1}$ | $b^2 \geq 72$ | the moment with error $\varepsilon$ |

Both hold with a large margin, since $b \geq 1000$. The proof could take a smaller $\varepsilon$, of size $9b^{-4}$. The source takes $\varepsilon = (8b^2)^{-1}$ so that $16\varepsilon = 2/b^2$, which is half of the loss $4/b^2$ allowed in Theorem B. The other half is for the ramified forms, in the next section.

**Remark (Formalization).** The theorem chooses an instance `Fintype D.chosenGL` inside its proof. The statement `IsSpread D.goodPoincare _` does not mention any instance. So the choice does not leak into the statement. The sums of the moment lemma are over a `Fintype` instance taken as a hypothesis, and any two such instances give the same sum.

**Remark (Formalization).** The two scalars of the source differ from the scalars of the textbook form of the argument. The textbook form uses one map $e_0 s P$ with $P$ an isometry up to small error. The source spreads the unscaled $\mathfrak{g}_s$ on $X$, and it proves the two inputs for the scaled map $L$ on the Euclidean space. The lemma on preimages shows that these two families have the same preimages up to the equivalence $\kappa$. So the spread statement is the same for both.
