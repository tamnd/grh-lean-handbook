---
title: The scaled Poincaré map
lean:
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/Unfolding/Moments.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/Derivatives/Field/WeilData.lean
  - New/Derivatives/Field/PrimeDecomposition.lean
decls:
  - New.Data.poincareScale
  - New.Data.poincareScale_pos
  - New.Data.scaledPoincare
  - New.Data.hasAmplitudeBlocks_scaledPoincare
  - New.Data.isNearIsometry_e₀_comp_scaledPoincare
  - New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le
  - New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le
  - New.Data.finrank_targetForms_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scaled Poincaré map

The theorems of [the chapter on moments](/chapter/moments/) are about a map $P$ from the Euclidean space $\mathbb{C}^{\mathrm{Classes} \times \mathrm{BesselCoord}}$ to a unitary representation, with the property `HasAmplitudeBlocks`. This section builds such a map from the Poincaré map $\mathcal{P}$ of $D$ and draws the two inputs (NI) and (SM) of the spread theorem for $D$.

### The Poincaré map and its coordinates

The Poincaré map of $D$ is $\mathcal{P} = D.\mathtt{poincare}$, a linear map from the source forms $X$ to the forms of principal level on $Y_0$. It is $D.\mathtt{poincareAt}$ at a point $D.\mathtt{besselPoint}$ and a linear form $D.\mathtt{besselForm}$. [The section on the series and the period](/chapter/poincare-series/#the-series-represents-the-period) proves that a point and a form exist with $\mathcal{P} = \mathcal{P}^{\mathrm{ser}} \circ \kappa$, where $\mathcal{P}^{\mathrm{ser}}$ is the Poincaré series map of the filling and $\kappa = D.\mathtt{sourceFormCoords}$ is the coordinate map of the source forms ([Corollary](/decl/New.Data.poincare_eq_poincareMap_comp/)).

**Remark (Formalization).** The point and the form are chosen. `D.besselPoint` is `D.exists_poincareAt_eq_poincareMap_comp.choose`, and `D.besselForm` is the next `choose`. So $\mathcal{P}$ is a chosen map. Every result of this chapter holds for the chosen pair, because each one uses only the identity $\mathcal{P} = \mathcal{P}^{\mathrm{ser}} \circ \kappa$, which is the `choose_spec` of the choice. Theorem B is a statement about this one map.

The coordinate map $\kappa : X \to \mathbb{C}^{\mathrm{Classes} \times \mathrm{BesselCoord}}$ is a linear equivalence. It applies the central translation by $D.\mathtt{latticeScale}\ 0$ and then takes the values at the class representatives in the coordinates of the Bessel systems. The standard inner product of the Euclidean space is the inner product of the source. The source forms carry no other inner product in this proof.

### The scale

**Definition (The scale of the Poincaré map).** The scale is the real number

$$c_P = \bigl(\mathrm{vol}(J)\cdot\nu\bigr)^{-1/2},$$

where $J = D.\mathtt{filling}.\mathtt{stdPrincipalLevel}$ is the principal level and $\nu = D.\mathtt{filling}.\mathtt{unipotentCovolume}$ is the covolume of the rational unipotent points.

Lean: `New.Data.poincareScale` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Lemma (The scale is positive).** $c_P > 0$.

Lean: `New.Data.poincareScale_pos` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* The principal level is a level, so its volume is positive (`measureReal_pos_of_isLevel`). The covolume $\nu$ is positive (`unipotentCovolume_pos`). The square root of a positive number is positive. $\square$

**Remark (Formalization).** The square root is `Real.sqrt`, which is $0$ on negative numbers, and the inverse is the inverse of a real number, which is $0$ at $0$. The lemma shows that neither junk value occurs: the product under the root is positive.

**Definition (The scaled Poincaré map).** $L = c_P\,\mathcal{P} \circ \kappa^{-1}$, a linear map from the Euclidean space to the forms of principal level on $Y_0$.

Lean: `New.Data.scaledPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

### Unfolding

**Theorem (Unfolding).** The scaled Poincaré map has amplitude blocks for the level representation: for every $s \in D.\mathtt{filling}.\mathtt{ResidueGL}$ and all coordinates $x, y$,

$$\langle s\,L e_y,\ L e_x\rangle = \frac{\mathcal{A}(x_1, s, y_1)(x_2, y_2)}{\nu},$$

where $\mathcal{A} = \mathtt{amplitudeSum}\ .\mathtt{full}\ .\mathtt{univ}$ is the sum of the amplitudes of the full Bessel function over all terms.

Lean: `New.Data.hasAmplitudeBlocks_scaledPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Step 1. $\mathcal{P}\circ\kappa^{-1} = \mathcal{P}^{\mathrm{ser}}$. By the corollary, $\mathcal{P}\circ\kappa^{-1} = \mathcal{P}^{\mathrm{ser}}\circ\kappa\circ\kappa^{-1}$, and $\kappa\circ\kappa^{-1}$ is the identity (`apply_symm_apply`). So $L = c_P\,\mathcal{P}^{\mathrm{ser}}$.

Step 2. The Petersson formula. Let $s \in \mathtt{ResidueGL}$. Choose an integral element $k$ of the standard level with reduction $\mathtt{Sigma.uncurry}\ s$ at the chosen places (`reduceFamily_liftResidue`). [Theorem](/decl/New.Filling.Fits.petersson_poincare/) says

$$\langle k\,\mathcal{P}^{\mathrm{ser}} e_y,\ \mathcal{P}^{\mathrm{ser}} e_x\rangle = \mathrm{vol}(J)\cdot\mathcal{A}(x_1, s, y_1)(x_2, y_2).$$

The operator of $s$ in the level representation is the action of $k$. So the hypothesis of [Lemma](/decl/New.Filling.hasAmplitudeBlocks_smul_of_inner_eq/) holds with $c = \mathrm{vol}(J) > 0$.

Step 3. The lemma says that $(c\nu)^{-1/2}\mathcal{P}^{\mathrm{ser}}$ has amplitude blocks. This map is $c_P\,\mathcal{P}^{\mathrm{ser}} = L$. $\square$

**Remark (Formalization).** The inner product of Mathlib is conjugate linear in its first argument. So the identity says that the entry $(x, y)$ of $L^*sL$ is $\langle L e_x, s L e_y\rangle$, the complex conjugate of $\mathcal{A}/\nu$. [The section on amplitude blocks](/chapter/moments/#amplitude-blocks-and-the-bessel-translates) states this convention. The norms below are Hilbert-Schmidt norms, which do not see the conjugation.

### The two inputs

**Theorem (Good forms).** The map $e_0 L$ is a near isometry with error $5b^{-4}$: for every subspace $U$ of the source,

$$\dim U - 5b^{-4}D_X \leq \|e_0 L\,\mathrm{pr}_U\|^2.$$

Lean: `New.Data.isNearIsometry_e₀_comp_scaledPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* By [the theorem on bad types](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes), $\rho(e_0) = \rho_{\mathrm{level}}(e_{p_0}\otimes e_{p_1})$. So it suffices to prove the claim for $\rho_{\mathrm{level}}(e_{p_0}\otimes e_{p_1})L$. Apply [Theorem](/decl/New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp/) with $g_i = e_{p_i}$. Its hypotheses are the unfolding theorem, the unitarity of the level representation, the centrality of $e_{p_i}$, and the bound $\operatorname{Re}((1 - e_{p_i})(1)) \leq b^{-8}/2$. The last two are parts 1 and 3 of the theorem on bad types. The $b$ of the filling is $D.b$ by the definition of `New.Data.filling`. $\square$

The constant $5b^{-4}$ has two parts, as [the section on good forms](/chapter/moments/#good-forms) proves. $L$ itself is a near isometry with error $b^{-4}$, because $\|L^*L - 1\|^2 \leq b^{-12}D_X$ and $b^{-12} \leq b^{-8}$. The rest $(1 - e_0)L$ has $\|(1 - e_0)L\|^2 \leq 4b^{-4}D_X$, and projecting a near isometry adds the error (`IsNearIsometry.proj_comp`). So the error is $b^{-4} + 4b^{-4}$.

**Theorem (Second moment).** For any instance `Fintype D.chosenGL`,

$$\sum_{s \in \bar G}\|L^*\rho(s)L\|^2 \leq \Bigl(1 + \frac{9}{b^4}\Bigr)\,\frac{D_X^2}{\deg\cdot\mathrm{mass}_r}.$$

Lean: `New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* [Theorem](/decl/New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le/), applied to the unfolding theorem and the unitarity of the level representation, gives the bound for the sum over $s \in \mathtt{ResidueGL}$ of $\|L^*\rho_{\mathrm{level}}(s)L\|^2$. The right side $D.\mathtt{filling}.\mathtt{mainSecondMoment}$ is $D_X^2/(\deg\cdot\mathrm{mass}_r)$ by definition. The two sums are equal: reindex by the bijection `Equiv.piCurry` and use the lemma on the level representation at an element. $\square$

**Lemma (Second moment with the dimension).** For any instance `Fintype D.chosenGL`,

$$d_T\sum_{s \in \bar G}\|L^*\rho(s)L\|^2 \leq \#\bar G\,\Bigl(1 + \frac{9}{b^4}\Bigr)D_X^2.$$

Lean: `New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Multiply the bound $d_T \leq \#\bar G\,\deg\,\mathrm{mass}_r$ of [the dimension of the target](/chapter/proof-of-theorem-b/#the-dimension-of-the-target) by the second moment theorem. Both factors are nonnegative. The product of the right sides is $\#\bar G\,\deg\,\mathrm{mass}_r\,(1 + 9b^{-4})\,D_X^2/(\deg\,\mathrm{mass}_r)$. Since $\deg > 0$ and $\mathrm{mass}_r > 0$, this is $\#\bar G\,(1 + 9b^{-4})\,D_X^2$. The source uses $D.\mathtt{filling}.\mathtt{sourceDim} = D_X$, the rank $r = \#\mathtt{RowIndex}$, and `Nat.card_eq_fintype_card`, so the result holds for any `Fintype` instance. $\square$

### The target is not zero

**Lemma (The target is not zero).** $\dim D.\mathtt{targetForms} \neq 0$.

Lean: `New.Data.finrank_targetForms_ne_zero` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Apply [Lemma](/decl/New.IsNearIsometry.finrank_range_pos/) to the good forms theorem. Its hypotheses are that the source is nontrivial, which Lean finds by instance search, and $5b^{-4} < 1$, a size bound of $D$ (`lt_of_hasLogBound`). The lemma gives $\dim\operatorname{range}\rho(e_0) > 0$, and the range of $\rho(e_0)$ is the target by definition. $\square$

The idea is short. If the target were $0$, then $e_0L = 0$, and the near isometry for $U$ the whole source would read $(1 - 5b^{-4})D_X \leq 0$. This lemma answers row F-072 of [the register of findings](/chapter/register-of-findings/): the source proves that the target is nonzero, and `targetDim_pos` in ShortAndEnough.lean is this lemma read as $0 < d_T$.

### The instances

The theorems of chapter 13 take the class `WeilData E`, and many lemmas below them take `HasPrimitiveRoot5040 E`. Row F-079 and question Q-27 of the register ask whether the instance reaches the field $E = D.E$ of Theorem B. This chapter traced the instance in the source.

**Remark (Formalization).** The field of the data is `D.E`, defined as `P.E D.towerExp` with the attribute `@[reducible]` (lean:New/Reduction/Data/AdmissibleData.lean#L181). So instance search sees `D.E` as `P.E s` with $s = D.\mathtt{towerExp}$. The class `WeilData E` extends `HasPrimitiveRoot5040 E` and `SplittingChar E`. The source has one global instance of `WeilData (P.E s)`, namely `New.Parameters.instWeilDataE` (lean:New/Derivatives/Field/WeilData.lean#L420). Its parent `HasPrimitiveRoot5040 (P.E s)` is filled by the instance at lean:New/Derivatives/Field/PrimeDecomposition.lean#L138, which takes the power $q_1/5040$ of a primitive root of order $q_1$. A search of the source found no local `letI` or `haveI` of `WeilData`. So the instance that the moment theorems use for $D.E$ is `instWeilDataE` at $s = D.\mathtt{towerExp}$, and its root of unity comes from PrimeDecomposition.lean. The class `HasPrimitiveRoot5040` is a proposition, so any two of its instances are equal. The splitting character inside `instWeilDataE` is chosen with `.some`. Whether a statement depends on that choice is row F-043, which stays open. The scalar $c_{ss}$ of Theorem A comes from the seesaw identity and may depend on it. By [the range lemma](/decl/New.Data.range_normalizedPoincare/) a nonzero scalar does not change the spaces in Theorem B.

### The constants of the two inputs

| Quantity | Bound | Where |
|---|---|---|
| $\|L^*L - 1\|^2$ | $\leq b^{-12}D_X$ | [Theorem](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le/) |
| error of $L$ | $b^{-4}$ | weakened from $b^{-6}$ |
| $\|(1 - e_0)L\|^2$ | $\leq 4b^{-4}D_X$ | two primes, $2b^{-4}D_X$ each |
| error of $e_0L$ | $5b^{-4}$ | the good forms theorem |
| second moment | $\leq (1 + 9b^{-4})D_X^2/(\deg\,\mathrm{mass}_r)$ | the second moment theorem |
| $d_T$ times the second moment | $\leq \#\bar G(1 + 9b^{-4})D_X^2$ | the lemma with the dimension |
