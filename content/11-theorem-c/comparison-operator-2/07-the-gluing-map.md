---
title: The gluing map
lean:
  - New/OneLift/ComparisonOperator/GluingMaps.lean
decls:
  - New.Rows.hookNumberMinus
  - New.Rows.SecondFactorFormValues
  - New.Data.FormTuples
  - New.Rows.IsIntegralFormTuple
  - New.Rows.formTupleNormSq
  - New.Rows.card_firstFactorIndex_le_two_mul_n
  - New.Rows.card_rowIndex_sum_fin_le_two_mul_n
  - New.Rows.nonempty_carrierIndex_embedding_firstFactorIndex
  - New.Rows.hasColumnsBelow_of_eq_zero
  - New.Rows.card_padIndex_sum_flatIndex_sum_secondFactorIndex
  - New.Rows.hasColumnsBelow_colsPlus
  - New.Rows.hasColumnsBelow_colsMinus
  - New.Rows.splittingV
  - New.Rows.gluingLevel
  - New.Rows.classAut_gluingLevel_eq_bot
  - New.Rows.glueLattice
  - New.Rows.isGlued_splittingV_of_isGlued
  - New.Rows.isGlued_glueLattice
  - New.Rows.weilScalar_glueLattice
  - New.Rows.firstFactorScale
  - New.Rows.firstFactorScale_ne_zero
  - New.Rows.firstFactor
  - New.Rows.firstFactorPairing
  - New.Rows.firstFactorPairing_eq_mul_thirdExchangeLeftSide
  - New.Rows.mul_firstFactorPairing_mem_rapidFunctions
  - New.Rows.exists_mul_firstFactorPairing_eq
  - New.Rows.twistFactor
  - New.Rows.exists_norm_twistFactor_sq_eq
  - New.Rows.twistFactor_mul_firstFactorPairing
  - New.Rows.isIntegralAndSmall_firstFactor
  - New.Rows.weylGauge_firstFactor_le_one
  - New.Rows.weylNormSq_firstFactor_le
  - New.Rows.glue
  - New.Rows.inner_adjoint_glue
  - New.Rows.firstFactorChar_mul_upsilonU1_zpow
  - New.Rows.goodForm_mul_liftMod_congruenceGroup
  - New.Rows.conj_normalizedDescent_glue
  - New.Rows.inner_adjoint_glue_goodLift_eq_integral
  - New.Rows.mul_mul_thetaKernelPairing_mem_rapidFunctions
  - New.Rows.inner_adjoint_glue_goodLift_eq_sum_integral
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The gluing map

This section defines the gluing map $\mathrm{glue}_\vartheta$ from tuples of forms on $V^\circ$ to forms on $V_j = V'' \oplus V^\circ$, and computes its adjoint on a good lift. The twist enters only through one number $c'_\vartheta$.

Background in one line each. A *divided splitting* and a *glued lattice* $L_\Lambda$ with matrix $\mathsf{g}$, scalar $c_{\mathsf{g}}$, congruence group $\bar J^1$ and product forms are in [glued lattices](/chapter/comparison-operator-1/#glued-lattices). The descent of a product form is in [the descent of product forms](/chapter/comparison-operator-1/#descent-of-product-forms). The series $\Upsilon_{\vartheta,i}$ and the first factor theorem are in [definite kernels and first factors](/chapter/comparison-operator-1/#definite-kernels-and-first-factors). The good lift $\Theta_{j,\vartheta}$ and the descent are in [the lift and its adjoint](/chapter/single-theta-lifts/#the-lift-and-its-adjoint).

### Form tuples

**Definition (Form tuples).** $hk^-$ is the hook number of the diagram $\mu^-$. The value space of a form on $V^\circ$ is the Weyl module of $\mu^-$, with its invariant inner product. A *form tuple* $\zeta$ is a family of values $\zeta(i, c)$, one for each choice $i$ and each class $c$ of $U(V^\circ)$ at level $\varpi^2$, with the $\ell^2$ inner product. The tuple is *integral* at a $p$-adic embedding $\phi$ if every value has gauge at most $1$. Its squared norm at $\sigma \in \mathrm{Aut}(\mathbb{C})$ is $\|\zeta\|_\sigma^2 = \sum_{i,c}\|\sigma\circ\zeta(i,c)\|^2$.

Lean: `New.Rows.hookNumberMinus`, `New.Rows.SecondFactorFormValues`, `New.Data.FormTuples`, `New.Rows.IsIntegralFormTuple`, `New.Rows.formTupleNormSq` (New/OneLift/ComparisonOperator/GluingMaps.lean).

The level $J(\varpi^2)$ is small enough that every class has trivial stabilizer. So a form on $V^\circ$ is the table of its values at representatives, and the inner product is a plain sum.

### The splitting

**Lemma (Sizes).** $\mathrm{rank}\,V'' = r + 9m + 1 \leq 2n_m$ and $\mathrm{rank}\,V_j = 6r \leq 2n_m$. The $3m$ indices of $S$ embed in those of $V''$. The indices of $V'' \oplus V^\circ$ other than those of $W_j$ in $V''$ are $t$ in number. If $\#N \leq \#n$ and $\kappa$ has no column of height at least $\#N$, then $\kappa$ has no column of height in $[\#N, \#n)$. The diagrams $\mu^+$ on $V''$ and $\mu^-$ on $V^\circ$ have no column of height in $[\mathrm{rank}\,V'', \mathrm{rank}\,V_j)$, respectively $[\mathrm{rank}\,V^\circ, \mathrm{rank}\,V_j)$.

Lean: `New.Rows.card_firstFactorIndex_le_two_mul_n`, `New.Rows.card_rowIndex_sum_fin_le_two_mul_n`, `New.Rows.nonempty_carrierIndex_embedding_firstFactorIndex`, `New.Rows.card_padIndex_sum_flatIndex_sum_secondFactorIndex`, `New.Rows.hasColumnsBelow_of_eq_zero`, `New.Rows.hasColumnsBelow_colsPlus`, `New.Rows.hasColumnsBelow_colsMinus` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The data give $6r \leq n_m$ and $100m + 9 < k \leq r$, so $r + 9m + 1 \leq 2r \leq 2n_m$, and $3m \leq r + 9m + 1$. The count is $j + (3m - j) + (6m + 1) + (t - 9m - 1 - r) + r = t$. The fourth claim is immediate. For $\mu^+$: its columns come from the lift data and have height at most $r_+ < r + 9m + 1$. For $\mu^-$: its columns have height at most $\#$ of the negative signs of $W_j$, which is below $\mathrm{rank}\,V^\circ$. Apply the fourth claim. $\square$

**Definition (The splitting and the level).** The splitting $V_j = V'' \oplus V^\circ$ puts the indices of $W_j$ first in $V''$. The fixed embedding is $W_j \to V''$, and the divided embedding is some embedding of the indices of $S$ in $V''$. Neither depends on the twist. For a matrix $\Lambda$ modulo $\varpi^2$, the level $J_\Lambda$ = `gluingLevel` is the row fixing level of the rows of $\Lambda$ stacked over those of $\varpi\cdot 1$.

Lean: `New.Rows.splittingV`, `New.Rows.gluingLevel` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Lemma (Trivial stabilizers).** At every point, the stabilizer of the class at level $J_\Lambda$ is trivial.

Lean: `New.Rows.classAut_gluingLevel_eq_bot` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* $J_\Lambda$ is contained in the principal level $\varpi$, which is neat at the chosen places by the data, so a rational point in a conjugate of it has finite order and is $1$. $\square$

**Definition (The glued lattice).** For a choice $i$ with matrix $\Lambda$, $L_\Lambda$ is the lattice that [the existence of glued lattices](/chapter/comparison-operator-1/#glued-lattices) gives for $\Lambda$ at the trivial twist, read as a lattice for $\vartheta$.

Lean: `New.Rows.glueLattice` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Lemma (Gluing does not see the twist).** A lattice that is glued for one twist is glued for every twist. So $L_\Lambda$ is glued for $\Lambda$ at every $\vartheta$, and its scalar $c_{\mathsf{g}}$ does not depend on $\vartheta$.

Lean: `New.Rows.isGlued_splittingV_of_isGlued`, `New.Rows.isGlued_glueLattice`, `New.Rows.weilScalar_glueLattice` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The conditions of a glued lattice are congruences modulo $\varpi$ and $\varpi^2$ and integrality on blocks. They involve the splitting and the chosen places, not the twist. The scalar is a function of $\mathsf{g}$ alone. $\square$

**Remark (Formalization).** $L_\Lambda$ comes from `choose` on an existence statement, at the trivial twist. Lean picks one lattice. Every later statement holds for that lattice, and the proofs use only the properties of a glued lattice. The definition is under `seal Finset.univ in`, which stops definitional unfolding and changes nothing else.

### The first factors and the twist factor

**Definition (First factors).** Let $c''$ = `firstFactorScale` be the nonzero constant of [the first factor theorem](/chapter/comparison-operator-1/#definite-kernels-and-first-factors). The first factor is $\varphi''_{\vartheta,i}(h) = \overline{c''\,\Upsilon_{\vartheta,i}(h)}$. Its theta series is
$$\Xi_{\vartheta,i}(g) = \sum_{h \in [J_\Lambda]}\theta''_{\vartheta,\Lambda}\bigl(g, h; \overline{\varphi''_{\vartheta,i}(h)}\bigr),$$
the class sum of the kernel of $(W_j, V'')$ with character $\nu''$ = `firstFactorChar` and datum the stacked rows.

Lean: `New.Rows.firstFactorScale`, `New.Rows.firstFactorScale_ne_zero`, `New.Rows.firstFactor`, `New.Rows.firstFactorPairing` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Lemma (Properties of the first factors).**

1. $\Xi_{\vartheta,i} = c''\cdot L_{\vartheta,i}$, where $L_{\vartheta,i}$ is the left side of the third exchange.
2. For a good form $y$, $y\,\Xi_{\vartheta,i}$ is rapidly decreasing.
3. The values of $\varphi''_{\vartheta,i}$ are integral at every place over a prime $l$ prime to the norm of the level of $\vartheta$. For $\vartheta = 1$ their conjugates have squared norm at most $\exp(fmb\log^2 b)$.

Lean: `New.Rows.firstFactorPairing_eq_mul_thirdExchangeLeftSide`, `New.Rows.mul_firstFactorPairing_mem_rapidFunctions`, `New.Rows.isIntegralAndSmall_firstFactor`, `New.Rows.weylGauge_firstFactor_le_one`, `New.Rows.weylNormSq_firstFactor_le` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* (1) The rows of $\Lambda$ are the first block of the stacked rows, so [the third exchange](/chapter/comparison-operator-2/#the-third-exchange) (`New.Data.thirdExchangeLeftSide_eq_kernelClassSum`) writes its left side as the same class sum with $\Upsilon$ in place of $\overline{\varphi''}$. As $\overline{\varphi''} = c''\Upsilon$, linearity gives the claim. (2) $\Xi$ is a finite sum of multiples of kernels, and the product of a good form with a kernel is rapidly decreasing (`New.Rows.mul_modKernel_mem_rapidFunctions`), as the tame part is trivial off the level. (3) This is the first factor theorem. $\square$

**Theorem (The twist factor).** There are a number $C$ and numbers $c'_\vartheta$ = `twistFactor` such that $|c'_\vartheta|^2 = C/\Gamma_j(\vartheta)$ and
$$c'_\vartheta\,\Xi_{\vartheta,i} = c''\,\mathsf{F}_i$$
for every twist $\vartheta$ and choice $i$.

Lean: `New.Rows.exists_mul_firstFactorPairing_eq`, `New.Rows.twistFactor`, `New.Rows.exists_norm_twistFactor_sq_eq`, `New.Rows.twistFactor_mul_firstFactorPairing` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* Take $C$ and $c'_\vartheta$ from [the three exchanges](/chapter/comparison-operator-2/#the-third-exchange). Then $c'_\vartheta\Xi_{\vartheta,i} = c''(c'_\vartheta L_{\vartheta,i}) = c''\mathsf{F}_i$ by part 1 of the last lemma. $\square$

**Remark (Formalization).** $c'_\vartheta$ is defined by `choose`. The number $C$ may be $0$ in Lean. That $c'_\vartheta \neq 0$ is proved in [the next section](/chapter/comparison-operator-2/#integrality-false-lifts-and-the-seesaw).

### The gluing map and its adjoint

**Definition (The gluing map).** For a form tuple $\zeta$,
$$\mathrm{glue}_\vartheta\,\zeta = M^{l_1}\sum_{(i, c)}\sum_{h \in [J_\Lambda]}\mathrm{productForm}_{L_\Lambda}(h, c^{\mathrm{out}})\bigl(\varphi''_{\vartheta,i}(h)\cdot\zeta(i, c)\bigr),$$
the form supported on the class of $(h, c^{\mathrm{out}})\mathsf{g}$ with value the Cartan product. Here $l_1$ is the denominator exponent of the splitting. The map is linear.

Lean: `New.Rows.glue` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Lemma (The adjoint is a sum of slices).** For a form $\varphi$ on $V_j$,
$$\langle\zeta, \mathrm{glue}_\vartheta^*\varphi\rangle = M^{l_1}\sum_{i, c}\sum_{h}\bigl\langle\varphi''_{\vartheta,i}(h)\cdot\zeta(i,c),\ \varphi\bigl((h, c^{\mathrm{out}})\mathsf{g}\bigr)\bigr\rangle.$$

Lean: `New.Rows.inner_adjoint_glue` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The inner product with a form supported on one class with trivial stabilizer is the pairing of the value with the value of $\varphi$ there. Sum. $\square$

**Lemma (Characters and invariance).** $\nu''\cdot\upsilon^{m/2 - j}$ is the character of $V_j$. A good form is invariant under the lifts of the elements of $\bar J^1$.

Lean: `New.Rows.firstFactorChar_mul_upsilonU1_zpow`, `New.Rows.goodForm_mul_liftMod_congruenceGroup` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The exponents add to $j + \lfloor(5r + k - 1)/2\rfloor + m/2 - j = 3r$, since $m$ is even and $k - 1 = r - m$. This is the exponent in the character of the descent pair. The lifts of $\bar J^1$ are $1$ modulo $\varpi$, so they lie in the level of a good form. $\square$

**Theorem (Descent of a glued form).** For twists $\vartheta$, $\vartheta'$,
$$\overline{\theta^*(\mathrm{glue}_\vartheta\zeta)(g)} = \sum_i\sum_{u \in \bar J^1}M^{l_1}c_{\mathsf{g}}\,\Xi_{\vartheta,i}(gu)\,\Theta(\zeta_i)(gu),$$
with $gu = g(1, \mathrm{liftMod}\,u)$ and $\zeta_i = \zeta(i, \cdot)$.

Lean: `New.Rows.conj_normalizedDescent_glue` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The descent is linear. By [the sum over classes](/chapter/comparison-operator-1/#descent-of-product-forms) (`New.Rows.DividedSplitting.normalizedDescent_stdClassSum_productForm`), with the character identity above, the descent of the term $(i, c)$ is the conjugate of $c_{\mathsf{g}}\sum_u\Xi_{\vartheta,i}(gu)\,\theta^\circ_{(i,c)}(gu)$. The sum over $c$ of the kernels $\theta^\circ_{(i,c)}$ is $\Theta(\zeta_i)$ by definition. The scalars $M^{l_1}$ and $c_{\mathsf{g}}$ are real or do not depend on the twist, and conjugation twice is the identity. $\square$

**Theorem (The adjoint on a good lift).** For a good form $y$,
$$\langle\zeta, \mathrm{glue}_\vartheta^*\Theta_{j,\vartheta}y\rangle = \sum_i M^{l_1}c_{\mathsf{g}}\,\#\bar J^1\int_{[U(W_j)]}y\,\Xi_{\vartheta,i}\,\Theta(\zeta_i),$$
with all lattice data taken at the trivial twist.

Lean: `New.Rows.inner_adjoint_glue_goodLift_eq_integral`, `New.Rows.mul_mul_thetaKernelPairing_mem_rapidFunctions`, `New.Rows.inner_adjoint_glue_goodLift_eq_sum_integral` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The lift is the Bochner integral $\int y(g)\,\theta(g, \cdot)\,dg$, which is integrable. So $\langle\zeta, \mathrm{glue}^*\Theta y\rangle = \langle\mathrm{glue}\,\zeta, \Theta y\rangle$ is $\int y\,\overline{\theta^*(\mathrm{glue}\,\zeta)}$. Insert the last theorem. Each term $y\,\Xi_{\vartheta,i}\,\Theta(\zeta_i)$ is rapidly decreasing, since $\Theta(\zeta_i)$ is a finite sum of kernels, so the sums and the integral exchange. For each $u$, $y(g) = y(gu)$, and the measure on $[U(W_j)]$ is invariant under right translation by $(1, \mathrm{liftMod}\,u)$. So all $\#\bar J^1$ translates give the same integral. $\square$
