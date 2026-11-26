---
title: Integrality, false lifts and the seesaw
lean:
  - New/OneLift/ComparisonOperator/GluingMaps.lean
decls:
  - New.Rows.glue_mem_integralForms
  - New.Rows.colsMinus_le
  - New.Rows.card_secondFactorIndex_le
  - New.Rows.sum_mul_colsMinus_le
  - New.Rows.hookNumberMinus_le
  - New.Rows.card_columnFilling_colsMinus_le
  - New.Rows.card_stdClasses_le_exp_of_le
  - New.Rows.principalLevel_le_gluingLevel
  - New.Rows.M_pow_denominatorExponent_sq_mul_le_exp
  - New.Rows.weylNormSq_evalForm_productForm_le
  - New.Rows.piM_sq_mem_placeAt_descentPair_one
  - New.Rows.normSqAt_glue_le
  - New.Rows.hyperplaneSum_apply_eq_zero
  - New.Rows.normalizedDescent_eq_zero_of_mem_orthogonal
  - New.Rows.tamePart_twistPlace_ne_one
  - New.Rows.stdClassSum_gramForm_eq_zero_of_mem_falseLiftsAt
  - New.Rows.sum_slice_eq_zero_of_mem_falseLiftsAt
  - New.Rows.thetaKernelPairing_adjoint_glue_eq_zero
  - New.Rows.glueFactor
  - New.Rows.glueFactor_ne_zero
  - New.Rows.twistFactor_mul_inner_adjoint_glue
  - New.Rows.periodLift
  - New.Rows.inner_periodLift
  - New.Rows.twistFactor_smul_adjoint_glue_comp
  - New.Rows.isOrthogonalToFalseLifts_glue_periodLift
  - New.Rows.periodLift_injective
  - New.Rows.twistFactor_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integrality, false lifts and the seesaw

This section proves the four properties of the gluing map that the comparison operator needs. The map keeps integrality, it grows norms by at most $\exp(2fmb\log^2 b)$, its image of $\Theta^\circ$ is orthogonal to the false lifts, and the seesaw identity $c'_\vartheta\,\mathrm{glue}_\vartheta^*\Theta_{j,\vartheta} = \Theta^\circ$ holds with $c'_\vartheta \neq 0$.

### Integrality

**Theorem (Gluing keeps integrality).** Let $l$ be a prime prime to the norm of the set $Q$ of $\vartheta$, and $\phi$ an embedding of $\mathbb{C}$ in $\mathbb{C}_l$. If $\zeta$ is integral at $\phi$, so is $\mathrm{glue}_\vartheta\zeta$.

Lean: `New.Rows.glue_mem_integralForms` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* By trivial stabilizers, $\mathrm{glue}\,\zeta$ is $M^{l_1}$ times a plain sum of forms supported on one class, and integral forms are closed under sums. The gauge of such a form is at most the gauge of its value ([the $p$-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge), `weylGauge_deltaForm_le`). Since $M \in (\varpi)$, the gauge of a Cartan product is at most $\|M\|^{-l_1}$ times the product of the gauges of the factors ([the descent of product forms](/chapter/comparison-operator-1/#descent-of-product-forms), `weylGauge_cartanProduct_le`). The first factor has gauge at most $1$ as $l$ is prime to the norm of $Q$, and $\zeta$ has gauge at most $1$. So the gauge of a term is at most $\|M^{l_1}\|\cdot\|M\|^{-l_1} = 1$. $\square$

### Size

**Lemma (Counts).** For the untwisted pair: each column count $k^-_\tau(i)$ of $\mu^-$ is at most the gap; $\mathrm{rank}\,V^\circ \leq t$; with $L = f\,t^2\,\mathrm{gap}$, $\sum_\tau\sum_{i < \mathrm{rank}\,V^\circ} i\cdot k^-_\tau(i) \leq L$; $hk^- \leq \exp(x^{999})$; and the number of fillings of the columns of $\mu^-$ by the basis of $V^\circ$ is at most $\exp(x^{999})$.

Lean: `New.Rows.colsMinus_le`, `New.Rows.card_secondFactorIndex_le`, `New.Rows.sum_mul_colsMinus_le`, `New.Rows.hookNumberMinus_le`, `New.Rows.card_columnFilling_colsMinus_le` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The column counts are differences of entries of the target parameter, which the data bound by the gap. The rank of $V^\circ$ is $(t - 9m - 1 - r) + r \leq t$ as $k \leq r$ gives $9m + 1 \leq r$. Each term $i\cdot k^-_\tau(i)$ is at most $t\cdot\mathrm{gap}$, there are at most $t$ heights and $f$ places, so the sum is at most $L$. The hook number of a diagram with weighted size at most $L$ is at most $(L^L)^3$, and the fillings number at most $(t+1)^L$. The log bound of the data gives $3L^2 \leq x^{999}$ and $L(t+1) \leq x^{999}$, and $\log y \leq y$ finishes. $\square$

**Lemma (Classes and levels).** For $\#n \leq 2n_m$ and a level $K \supseteq J(\varpi^2)$, the classes of $U(n)$ at level $K$ number at most $\exp b$. At the trivial twist the principal level $J(\varpi^2)$ of $V''$ lies in $J_\Lambda$.

Lean: `New.Rows.card_stdClasses_le_exp_of_le`, `New.Rows.principalLevel_le_gluingLevel` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* As $\varpi\bar\varpi = M$, $J(M^2) \subseteq J(\varpi^2) \subseteq K$. The data bound the classes at a level containing $J(M^2)$ by $\exp(\text{a log bound})$ for every rank up to $2n_m$, and the log bound is at most $b$. For the second claim: at the trivial twist the modulus of $J_\Lambda$ is $\varpi^2$, and an element $1$ modulo $\varpi^2$ fixes every row modulo $\varpi^2$. $\square$

**Lemma (One term).** $(M^{l_1})^2\exp(b)\,(N\exp(b)G)^2 \leq \exp(fmb\log^2 b)$, where $N$ is the number of pairs $(i, c)$ and $G$ bounds the orders of the stabilizers on $V_j$. For each $g$, the value at $g$ of the term $(i, c, h)$ of the glued form, moved by $\sigma$, has squared norm at most $G^2\exp(fmb\log^2 b)\|\zeta\|_\sigma^2$. At the trivial twist every place of the level contains $\varpi^2$.

Lean: `New.Rows.M_pow_denominatorExponent_sq_mul_le_exp`, `New.Rows.weylNormSq_evalForm_productForm_le`, `New.Rows.piM_sq_mem_placeAt_descentPair_one` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* For the first bound: $l_1$ is at most an explicit $e$ built from the column sums of $\mu^+$ and the number $L$ of the last lemma. $N$ is at most the number of matrices modulo $\varpi^2$ times the number of row selections times two class counts $\exp b$. Take logarithms, and the log bound of the data gives the claim. For the second: a form on one class has values of squared norm at most the stabilizer order squared times that of its vector ([the $p$-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). The automorphism $\sigma$ commutes with the Cartan product, and the squared norm of a Cartan product is the product of the squared norms. The first factor at $\vartheta = 1$ gives at most $\exp(fmb\log^2 b)$, and $\|\sigma\circ\zeta(i,c)\|^2 \leq \|\zeta\|^2_\sigma$. The last claim holds as each chosen place contains $\varpi$ and the trivial twist has no places in $Q$. $\square$

**Theorem (Gluing grows norms little).** $\|\mathrm{glue}_1\zeta\|^2_\sigma \leq \exp(2fmb\log^2 b)\,\|\zeta\|^2_\sigma$.

Lean: `New.Rows.normSqAt_glue_le` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The squared norm is a sum over at most $\exp b$ classes of $V_j$. At each, the value is $M^{l_1}$ times a sum over the $N$ pairs and the at most $\exp b$ classes $h$ of $V''$, and each term is bounded by the last lemma. The norm of a sum of $K$ terms is at most $K$ times the largest. So the squared norm is at most $(M^{l_1})^2\exp(b)(N\exp(b)G)^2\cdot\exp(fmb\log^2 b)\|\zeta\|^2_\sigma$, and the first bound of the last lemma finishes. $\square$

### False lifts

A *false lift* $\Xi$ at a split place $w$ off the level is a form on $V_j$ in the image of $e_0$, killed by the Hecke polynomial at $w$ at the value of the lift, and orthogonal to the lifts of good forms. Two results of [false lifts](/chapter/false-lifts/) are used, stated here once. First ([PeriodsOfFalseLifts.lean](lean:New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L324)): if the pair fits the parameters, its tame part is not $1$ at the places of $Q$, and $\Xi$ is killed by the hyperplane sums, by the descent and by the Hecke polynomial, then for a splitting $N \oplus l$ with $r + 2\#N + 3 < t$, the class sum of the pairing of $\Xi((h_1, h)x)$ with a conjugate equivariant image of theta kernels of $(W, V^\circ)$ is $0$. Second ([PeriodsOfFalseLifts.lean](lean:New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L718)): under the same hypotheses on $\Xi$, the class sum over $h$ of $\langle\mathrm{productForm}_L(x, h)(y, \overline{\theta^\circ(g, h)}), \Xi\rangle$ is $0$.

**Lemma (Hypotheses on false lifts).** Let $\Xi$ be in the image of $e_0$.

1. $\Xi$ is killed by the tensor of the hyperplane sums $\sum_h\chi_w(\det h)^{-1}h$ over $h = 1 + uv^T$, for $v$ nonzero at one chosen place.
2. If $\Xi$ is orthogonal to the lifts of good forms, its descent is $0$.
3. The tame part of the pair is not $1$ at the places of $Q$.

Lean: `New.Rows.hyperplaneSum_apply_eq_zero`, `New.Rows.normalizedDescent_eq_zero_of_mem_orthogonal`, `New.Rows.tamePart_twistPlace_ne_one` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* (1) Write $\Xi = e_0x$. The tame part is trivial at the chosen place, since it is not in $Q$. So the product of the hyperplane sums with $e_0$ is $0$ ([LabelsAndIndexTypes.lean](lean:New/UpperBound/Objects/LabelsAndIndexTypes.lean#L409)), and the action is an algebra map. (2) By [the lift and its adjoint](/chapter/single-theta-lifts/#the-lift-and-its-adjoint) (`New.Data.normalizedDescent_eq_zero_iff`), it suffices that $\langle Ly, \Xi\rangle = 0$ for every $y$, with $L$ the single lift. As $e_0$ is a central self adjoint projection and $e_0\Xi = \Xi$, $\langle Ly, \Xi\rangle = \langle e_0Ly, \Xi\rangle$, and $e_0Ly$ is the good lift of the projection of $y$. (3) The tame part at a place of $Q$ is that of $\vartheta$, which is not $1$ there. $\square$

**Theorem (Slices of false lifts vanish).** For a false lift $\Xi$, the periods of the first result vanish for $\Xi$, and for every finite point $h$ of $U(V'')$, every vector $y$ of weight $\mu^+$ and every $g$,
$$\sum_c\bigl\langle\Xi\bigl((h, c^{\mathrm{out}})\mathsf{g}\bigr),\ y\cdot\overline{\theta^\circ(g, c^{\mathrm{out}})}\bigr\rangle = 0.$$

Lean: `New.Rows.stdClassSum_gramForm_eq_zero_of_mem_falseLiftsAt`, `New.Rows.sum_slice_eq_zero_of_mem_falseLiftsAt` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* The last lemma gives the hypotheses of the two results, and $r + 2\,\mathrm{rank}\,V'' + 3 = 3r + 18m + 5 < 5r = t$ since $100m + 9 < r$. The class sum of the second result is over the principal level $\varpi$ of $V^\circ$, where the stabilizers are trivial. So the inner product with a form on one class is the pairing of values, and the class sum is the plain sum shown. $\square$

**Remark (Formalization).** The first statement is under `seal Finset.sum Finset.prod in`, the second under `seal Finset.univ in`, and the next under `set_option backward.isDefEq.respectTransparency false in`. They control definitional unfolding during elaboration. They do not change the statements.

**Theorem (The adjoint kills false lifts).** For a false lift $\Xi$, each choice $i$ and every $g$, $\Theta\bigl((\mathrm{glue}_\vartheta^*\Xi)_i\bigr)(g) = 0$.

Lean: `New.Rows.thetaKernelPairing_adjoint_glue_eq_zero` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* By the lemma on the adjoint, $(\mathrm{glue}^*\Xi)(i,c)$ is $M^{l_1}$ times a sum over $h$ of the slices of $\Xi$ at $(h, c^{\mathrm{out}})\mathsf{g}$ paired with $\varphi''(h)$. The conjugate of $\Theta(\zeta)(g)$ pairs $\zeta(c)$ with the kernel $\theta^\circ(g, c^{\mathrm{out}})$. Exchange the sums over $c$ and $h$. Each inner sum over $c$ is the slice of the last theorem, so it is $0$. $\square$

### The seesaw identity

**Definition (Glue factors and $\Theta^\circ$).** $c^\circ_i = M^{l_1}c_{\mathsf{g}}\,\#\bar J^1\,c''$, which is not $0$ and does not depend on $\vartheta$. The map $\Theta^\circ = c'_1\,\mathrm{glue}_1^*\circ\Theta_{j,1}$ goes from good forms on $W_j$ to form tuples.

Lean: `New.Rows.glueFactor`, `New.Rows.glueFactor_ne_zero`, `New.Rows.periodLift` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Theorem (Seesaw).** For every $y$, $\zeta$ and $\vartheta$,
$$c'_\vartheta\langle\zeta, \mathrm{glue}_\vartheta^*\Theta_{j,\vartheta}y\rangle = \sum_i c^\circ_i\int y\,\mathsf{F}_i\,\Theta(\zeta_i) = \langle\zeta, \Theta^\circ y\rangle.$$
So $c'_\vartheta\,\mathrm{glue}_\vartheta^*\circ\Theta_{j,\vartheta} = \Theta^\circ$.

Lean: `New.Rows.twistFactor_mul_inner_adjoint_glue`, `New.Rows.inner_periodLift`, `New.Rows.twistFactor_smul_adjoint_glue_comp` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* Multiply [the adjoint on a good lift](/chapter/comparison-operator-2/#the-gluing-map) by $c'_\vartheta$ and use $c'_\vartheta\Xi_{\vartheta,i} = c''\mathsf{F}_i$ under the integral. The right side does not involve $\vartheta$, so at $\vartheta = 1$ it is $\langle\zeta, \Theta^\circ y\rangle$. Two vectors with the same inner products with all $\zeta$ are equal. $\square$

**Theorem (Orthogonal to false lifts).** For every good form $y$, $\mathrm{glue}_\vartheta(\Theta^\circ y)$ is orthogonal to the false lifts at every split place off the level.

Lean: `New.Rows.isOrthogonalToFalseLifts_glue_periodLift` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* $\langle\Xi, \mathrm{glue}\,\Theta^\circ y\rangle = \langle\mathrm{glue}^*\Xi, \Theta^\circ y\rangle$, which by the seesaw is a sum of integrals of $y\,\mathsf{F}_i\,\Theta((\mathrm{glue}^*\Xi)_i)$. These integrands are $0$ by the last theorem. $\square$

**Theorem (Injectivity and the twist factor).** $\Theta^\circ$ is injective, and $c'_\vartheta \neq 0$.

Lean: `New.Rows.periodLift_injective`, `New.Rows.twistFactor_ne_zero` (New/OneLift/ComparisonOperator/GluingMaps.lean).

*Proof.* Let $\Theta^\circ y = 0$. For a choice $i$ and a tuple $\zeta$ on $V^\circ$, let $\eta$ be $\zeta$ in copy $i$ and $0$ elsewhere. Then $0 = \langle\eta, \Theta^\circ y\rangle = c^\circ_i\int y\,\mathsf{F}_i\,\Theta(\zeta)$, and $c^\circ_i \neq 0$. So [products span](/chapter/comparison-operator-2/#products-span) gives $y = 0$. If $c'_\vartheta = 0$, the seesaw gives $\Theta^\circ = 0$, so every good form is $0$ by injectivity. But the space of good forms has the dimension of the target forms, which is not $0$ ([single theta lifts](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift)). $\square$

**Example (What the seesaw buys).** For twists $\vartheta \neq \vartheta'$ the lifts $\Theta_{j,\vartheta}$ and $\Theta_{j,\vartheta'}$ act on different spaces of forms on $V_j$. After the adjoint gluing maps and the scalars $c'_\vartheta$, $c'_{\vartheta'}$, they become the same map $\Theta^\circ$. So $|c'_\vartheta|^2 = C/\Gamma_j(\vartheta)$ compares norms across twists, which is what the comparison operator of [the first section](/chapter/comparison-operator-2/#what-the-chapter-proves) needs.
