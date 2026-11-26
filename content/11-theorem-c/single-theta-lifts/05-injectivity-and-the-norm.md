---
title: Injectivity and the norm of one lift
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
  - Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean
decls:
  - New.Data.two_mul_card_rowIndex_lt
  - New.Data.liftSeries
  - New.Data.rallisTerm
  - New.Data.exists_principalForms_eq_liftSeries
  - New.Data.hasSum_cosetTerm_of_eq_liftSeries
  - New.Data.exists_end_eq_liftSeries
  - New.Data.rallisOperator
  - New.Data.coe_rallisOperator_apply
  - New.Data.hasSum_inner_rallisOperator
  - New.Data.singleLift_injective
  - New.Data.exists_hasSum_rallisTerm_inner_singleLift
  - New.Data.exists_hasSum_inner_singleLift
  - New.Data.exists_adjoint_singleLift_comp_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Injectivity and the norm of one lift

This section applies Rallis' inner product formula to the single lift $\Theta_{j,\vartheta}$. It proves three results. The lift is injective on the forms of level $J_M$. Its Gram form $\langle\Theta_{j,\vartheta}x, \Theta_{j,\vartheta}y\rangle$ is a sum over cosets. The constant in front of this sum is $c_j\,c_Q(\vartheta)$, where $c_j \neq 0$ does not depend on $\vartheta$. The last form is the operator identity $\Theta_{j,\vartheta}^*\Theta_{j,\vartheta} = c_j\,c_Q\,R_{j,\vartheta}$. The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) uses the injectivity and the operator identity.

The inputs are three. The first is Rallis' formula for sharp data, from [the Rallis inner product formula](/chapter/rallis-inner-product/). The second is the theorem of Section 4 that the block datum is sharp for $J_M$, with the split of its mass. The third is the lemma of Section 3 that turns the class sum on $V_j$ into a Petersson product.

### The rank condition

Rallis' formula of Volume 6 holds in Weil's convergent range. The rank of the target space must be more than twice the rank of the source space.

**Lemma.** The rank $r + t$ of $V_j$ is more than twice the rank $r$ of $W_j$: $2r < r + t$.

Lean: `New.Data.two_mul_card_rowIndex_lt` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* By [the data and its sizes](/chapter/data-and-sizes/), $t = 5r$ and $r \geq 3$. So $r + t = 6r > 2r$. $\square$

The margin is large. The formula needs only $t > r$, and the data give $t = 5r$.

### The series of the lift

Fix $\vartheta$ and $j$. Let $\pi_M Q$ be the product of the primes of the chosen places $M$ and of the places $Q$ of $\vartheta$. Let $S_0$ be the set of the places of $\pi_M Q$ and of their conjugates. For a hermitian space $V$ of rank $r$, let $K^{S_0}$ be the group of the finite points of $U(V)$ that are integral at every place outside $S_0$. For a coset $\gamma$ of $K^{S_0}$, the representative $r_\gamma$ is supported off $S_0$, as in Volume 6: it is $1$ at every place of $S_0$.

The vacuum coefficient of Volume 6 enters with the rank $M = r + t$ of $V_j$ and the character $b = \nu_V$ of the pair on the side of $V_j$:

$$\mathrm{mc}(g) = \bigl(\nu_V(\det g)\,\mathrm{finMultiplier}(g)^{r+t}\bigr)^{-1}.$$

**Definition (The series of the lift).** For a function $y$ on $U(V)(\mathbb{A})$, the series of the $j$-th lift at $\vartheta$ is the Rallis series

$$\mathcal{R}_{j,\vartheta}\,y(g) = \sum_\gamma \mathrm{mc}(r_\gamma)\,y(g\,r_\gamma),$$

where $\gamma$ runs over the cosets of $K^{S_0}$, for the rank $r + t$, the character $\nu_V$ and the set $S_0$.

Lean: `New.Data.liftSeries` (New/Determinant/Norms/AdjointThetaLift.lean).

**Definition (The Rallis term).** For forms $y'$, $y$ of level $J_M$ on $V$ and a coset $\gamma$, the Rallis term is the coset term of Volume 6 divided by the number of $(r+t) \times r$ matrices modulo $\pi_M Q$:

$$\rho_\gamma(y', y) = \frac{\mathrm{mc}(r_\gamma)\,\langle y', R(r_\gamma)\,y\rangle}{|\mathrm{Mat}_{(r+t) \times r}(\mathcal{O}/\pi_M Q)|}.$$

Here $R$ is right translation and $\langle\cdot,\cdot\rangle$ is the Petersson product on $V$.

Lean: `New.Data.rallisTerm` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma (The series keeps the level).** Let $V$ have rank $r$ and let $y$ be a form of level $J_M$ on $V$. There is a form $z$ of level $J_M$ on $V$ whose function is $\mathcal{R}_{j,\vartheta}\,y$.

Lean: `New.Data.exists_principalForms_eq_liftSeries` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The theorem of Volume 6 on the series of a form (`New.SiegelWeil.exists_form_eq_rallisSeries`) needs three inputs. The rank condition is the lemma above. The character $\nu_V$ must be unramified off $S_0$, and $J_M$ must contain the points that are integral and supported off $S_0$. Both inputs are fields of the sharpness of the block datum, from Section 4. The chosen places are not empty, so that theorem applies. $\square$

**Lemma (The product with the series).** Let $V$ have rank $r$, and let $x$, $y$, $z$ be forms of level $J_M$ on $V$ with $z = \mathcal{R}_{j,\vartheta}\,y$. Then

$$\langle x, z\rangle = \sum_\gamma \mathrm{mc}(r_\gamma)\,\langle x, R(r_\gamma)\,y\rangle,$$

and the sum converges.

Lean: `New.Data.hasSum_cosetTerm_of_eq_liftSeries` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The inner product of two forms of level $J_M$ is the Petersson product of their functions. The Petersson product with the series may be taken term by term (`New.SiegelWeil.hasSum_petersson_rallisSeries`). That lemma needs the rank condition and the integrability of $x$, which holds because a form is square integrable on a space of finite volume. $\square$

### The Rallis operator

The series is linear in $y$, and it keeps the level. So it defines an operator on the forms of level $J_M$.

**Lemma.** For every $j$, $\vartheta$ and every space $V$ of rank $r$, there is a linear endomorphism $R$ of the forms of level $J_M$ on $V$ such that the function of $R\,y$ is $\mathcal{R}_{j,\vartheta}\,y$ for every $y$.

Lean: `New.Data.exists_end_eq_liftSeries` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* For each $y$, choose the form $z$ of the lemma on the level. A form of level $J_M$ is determined by its inner products with all forms of level $J_M$. By the lemma on the product, $\langle x, z\rangle$ is a sum of terms that are linear in $y$. So the choice is additive and homogeneous. $\square$

**Definition (The Rallis operator).** The Rallis operator $R_{j,\vartheta}$ on the forms of level $J_M$ on $V$ is the endomorphism of the lemma.

Lean: `New.Data.rallisOperator`, `New.Data.coe_rallisOperator_apply` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma.** For forms $x$, $y$ of level $J_M$ on $V$,

$$\langle x, R_{j,\vartheta}\,y\rangle = \sum_\gamma \mathrm{mc}(r_\gamma)\,\langle x, R(r_\gamma)\,y\rangle.$$

Lean: `New.Data.hasSum_inner_rallisOperator` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Apply the lemma on the product with $z = R_{j,\vartheta}\,y$. $\square$

The representative of the trivial coset is integral and is $1$ at every place of $S_0$, so it lies in $J_M$ and fixes $y$. Its vacuum coefficient is $1$. So the trivial coset gives the term $\langle x, y\rangle$. The other terms are small in a precise sense: Volume 6 proves that $\mathcal{R}$ is a perturbation of the identity at each place. That is the source of the injectivity below.

### Injectivity

**Theorem (The single lift is injective).** Let $\vartheta$ be a tame character and let $1 \leq j \leq m$. Then the single lift $\Theta_{j,\vartheta}$ is injective on the forms of level $J_M$ on $W_j$.

Lean: `New.Data.singleLift_injective` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Let $O$ be the $j$-th descent pair at $\vartheta$, and let $L$ be the lift of forms by the datum $\phi_{v^+} = v^+ \otimes (\Psi_{\mathrm{bl}} \otimes \mathrm{vac})$.

1. By Section 3, $v^+$ is an edge from the type of $2\varsigma$ on $W_j$ to the type of $\mathrm{paramV}$ on $V_j$.
2. By Section 4, the finite datum is sharp for $J_M$ off $S_0$. The chosen places are not empty.
3. The rank condition holds by the lemma above.
4. So [Rallis' formula and injectivity](/chapter/rallis-inner-product/) applies (`New.SiegelWeil.rallis_inner_product_cosetTerm`). For a form $y$ of level $J_M$, $L y = 0$ implies $y = 0$.
5. By Section 3, $(\Theta_{j,\vartheta}\,y)^\natural = L y$. If $\Theta_{j,\vartheta}\,y = 0$, then $L y = 0$, so $y = 0$. $\square$

**Remark (Formalization).** The theorem holds on all of the forms of level $J_M$. The good forms of Section 1 are a subspace of them, so the good lift `New.Data.goodLift` is injective too. The theorem is not stated only for good forms. The proof uses no $L$-function. In the classical non-vanishing theorem, the lift of a cuspidal representation $\pi$ is not zero when a special value of an $L$-function of $\pi$ is not zero. Here the role of that value is played by the injectivity of the series $\mathcal{R}$ of Volume 6.

### The Gram form

The constant of Rallis' formula depends only on the spaces and on the real datum $v^+$, with its weights. A tame character $\vartheta$ has weight $0$, so the character $\mu_j^0\vartheta$ has the weight $-\kappa_j$ for every $\vartheta$. So the real data of the $j$-th pair are the same for every $\vartheta$, and one constant serves for every $\vartheta$.

**Theorem (The Gram form, first form).** Let $1 \leq j \leq m$. There is a constant $A \neq 0$ with the following property. For every tame character $\vartheta$ and all forms $x$, $y$ of level $J_M$ on $W_j$,

$$\langle\Theta_{j,\vartheta}\,x, \Theta_{j,\vartheta}\,y\rangle = \sum_\gamma A\,g_O\,\rho_\gamma(x, y),$$

where $O$ is the $j$-th descent pair at $\vartheta$, $g_O$ is its Gram factor from Section 4, and the sum converges.

Lean: `New.Data.exists_hasSum_rallisTerm_inner_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Take the constant $C \neq 0$ of Rallis' formula for the pair at the trivial character. Let $d_\kappa$ be the dimension of the weight of the forms on $V_j$. Put $A = C\,d_\kappa$. Fix $\vartheta$, $x$ and $y$, and let $L$ be the lift as in the proof of injectivity.

1. The constant $C$ holds for every pair of characters of the given weights. Apply it with $\nu_W$ and $\nu_V$ of the pair at $\vartheta$. The block datum is sharp with mass $c_\Psi$. So $\langle L x, L y\rangle_{\mathrm{Pet}} = \sum_\gamma C\,c_\Psi\,\mathrm{mc}(r_\gamma)\,\langle x, R(r_\gamma)\,y\rangle$.
2. By the lemma on class sums of Section 3, $\langle\Theta_{j,\vartheta}\,x, \Theta_{j,\vartheta}\,y\rangle = [K_0^V : K]\,d_\kappa\,\langle L x, L y\rangle_{\mathrm{Pet}}$.
3. By the lemma of Section 4, $[K_0^V : K]\,c_\Psi = g_O/|\mathrm{Mat}_{(r+t) \times r}(\mathcal{O}/\pi_M Q)|$.
4. Multiply the sum of step 1 by $[K_0^V : K]\,d_\kappa$ and insert step 3. Each term becomes $C\,d_\kappa\,g_O\,\rho_\gamma(x, y)$. $\square$

The factor $g_O$ still depends on $\vartheta$, through $Q$. The theorem of Section 4 on the split of $g_O$ separates this dependence.

**Theorem (The Gram form).** Let $1 \leq j \leq m$. There is a constant $c_j \neq 0$ with the following property. For every tame character $\vartheta$ and all forms $x$, $y$ of level $J_M$ on $W_j$,

$$\langle\Theta_{j,\vartheta}\,x, \Theta_{j,\vartheta}\,y\rangle = \sum_\gamma c_j\,c_Q\,\mathrm{mc}(r_\gamma)\,\langle x, R(r_\gamma)\,y\rangle,$$

where $c_Q$ is the twist factor of the $j$-th pair at $\vartheta$, $\gamma$ runs over the cosets of $K^{S_0}$ in the finite points of $U(W_j)$, and the sum converges.

Lean: `New.Data.exists_hasSum_inner_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Take $A$ from the first form and put $c_j = A\,c_M$, where $c_M$ is the chosen factor of the pair at the trivial character. It is not $0$, by Section 4. The chosen places and the ranks $r$, $t$ do not depend on $\vartheta$. So $c_M$ is the chosen factor of the pair at every $\vartheta$. By the theorem of Section 4 on the split of the Gram factor, $g_O/|\mathrm{Mat}_{(r+t) \times r}(\mathcal{O}/\pi_M Q)| = c_M\,c_Q$. Insert this in each term of the first form. $\square$

The sum has no $L$-value and no factor of the form $\langle y', y\rangle$ alone. It is a sum over cosets, and each term is a translate of $y$ paired with $x$.

**Example (The trivial coset).** By the remark after the lemma on $R_{j,\vartheta}$, the trivial coset has the term $c_j\,c_Q\,\langle x, y\rangle$. If the other terms were absent, the lift would be a multiple of an isometry, with $\|\Theta_{j,\vartheta}\,y\|^2 = c_j\,c_Q\,\|y\|^2$. The other cosets add the corrections $c_j\,c_Q\,\mathrm{mc}(r_\gamma)\langle x, R(r_\gamma)\,y\rangle$. Their size is controlled by the bound $|\mathrm{mc}(g)| = [gL : L \cap gL]^{-(r+t)/2}$ of Volume 6.

### The operator identity

**Theorem (The norm of one lift).** Let $1 \leq j \leq m$. There is a constant $c_j \neq 0$ such that for every tame character $\vartheta$,

$$\Theta_{j,\vartheta}^*\,\Theta_{j,\vartheta} = c_j\,c_Q\,R_{j,\vartheta}$$

on the forms of level $J_M$ on $W_j$.

Lean: `New.Data.exists_adjoint_singleLift_comp_eq` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Take $c_j$ from the theorem on the Gram form. Two operators agree if they have the same matrix coefficients $\langle x, \cdot\,y\rangle$. On the left, $\langle x, \Theta^*\Theta\,y\rangle = \langle\Theta x, \Theta y\rangle$, and the theorem gives this as a sum over cosets. On the right, the lemma on $R_{j,\vartheta}$ gives $\langle x, R_{j,\vartheta}\,y\rangle$ as the same sum without the factor $c_j\,c_Q$. A convergent sum has one value. $\square$

The adjoint $\Theta_{j,\vartheta}^*$ is the descent $\theta$ by Section 3. So the theorem says that $\theta\,\Theta_{j,\vartheta}$ is $c_j\,c_Q$ times the series $\mathcal{R}_{j,\vartheta}$ on the forms of level $J_M$. The constant $c_j$ is the same for every $\vartheta$, and all dependence on $\vartheta$ is in $c_Q$ and in $R_{j,\vartheta}$. The determinant $Z_j(\vartheta)$ of Section 1 is taken on the good forms, a subspace of the forms of level $J_M$. The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) passes from this identity to the good forms.
