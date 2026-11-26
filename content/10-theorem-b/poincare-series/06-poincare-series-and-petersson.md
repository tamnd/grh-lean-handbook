---
title: Poincaré series and the Petersson formula
lean:
  - New/Spanning/Unfolding/PoincareSeries.lean
decls:
  - New.Filling.Fits.exists_coe_finiteEquiv_eq_conj
  - New.Filling.Fits.reduction_finiteEquiv_iff
  - New.Filling.Fits.cutBessel_ratEquiv_mul
  - New.Filling.Fits.enorm_cutBessel_ratEquiv_mul_le
  - New.Filling.Fits.tsum_cutBessel_classUnipotent
  - New.Filling.Fits.exists_tsum_enorm_cutBessel_le
  - New.Filling.Fits.integrable_cutBessel
  - New.Filling.Fits.integral_mul_tsum_cutBessel
  - New.Filling.Fits.integrable_and_integral_mul_poincareSeries
  - New.Filling.Fits.integral_typeKernel_mul_besselFn
  - New.Filling.Fits.realConv_tsum_cutBessel_classUnipotent
  - New.Filling.Fits.exists_levelSpace_tsum_cutBessel_eq
  - New.Filling.Fits.coe_poincareMap
  - New.Filling.Fits.measurePreserving_realHomeomorph
  - New.Filling.Fits.integral_mul_poincareSeries_eq_sum_classes
  - New.Filling.Fits.hasLevel_mul_right
  - New.Filling.Fits.mem_principalLevel_iff_mem_termsOver
  - New.Filling.Fits.amplitudeSum_apply_eq_integral_tsum
  - New.Filling.Fits.petersson_poincare
  - New.Filling.Fits.finrank_levelSpace_eq_sourceDim
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Poincaré series and the Petersson formula

This section builds the Poincaré map $\mathcal{P}$ of [Theorem B and its plan](/chapter/theorem-b-plan/#the-model-case) and proves the Petersson formula. In this section $S$ is admissible, and $E$ contains a primitive root of unity of order $5040$.

### The fit

The series live on a hermitian space $V$ with its own group $G = \mathrm{U}(V)$, its discrete group $\Gamma$ of rational points and its adelic group $G(\mathbb{A}) = G_\infty \times G_f$. The space $V$ *fits* $S$ if the Bessel system of $S$ at each infinite place has the type of $V$, the grading of $V$ is standard, the type kernel is idempotent, and the finite part of the point of $V$ is a finite idele times the image of a central $\eta$ times the lattice basis of $S$ times an integral matrix that reduces to $1$ at the chosen places ([Definition](/decl/New.Filling.Fits/)).

A fit gives three maps: an isomorphism $\gamma \mapsto \gamma$ of the rational points of $S$ onto $\Gamma$, a homeomorphism $y(\cdot)$ of $G_\infty$ onto $\prod_v G_1$ that turns left translation by $g$ into left translation by the infinite part of $g$ ([Definition](/decl/New.Filling.Fits.realHomeomorph/)), and an isomorphism $\psi$ of the finite adelic group of $V$ onto that of $S$ ([Definition](/decl/New.Filling.Fits.finiteEquiv/)).

**Lemma (The finite isomorphism).** $\psi$ is conjugation by an integral matrix that reduces to $1$ at the chosen places. So $\psi(k)$ lies in $K$ with reduction $s$ if and only if $k$ is integral with reduction $s$. The map $y(\cdot)$ preserves the Haar measures.

Lean: `New.Filling.Fits.exists_coe_finiteEquiv_eq_conj`, `New.Filling.Fits.reduction_finiteEquiv_iff`, `New.Filling.Fits.measurePreserving_realHomeomorph` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* $\psi$ is conjugation by the finite point of $V$, a change to the lattice basis and conjugation by $\iota(\eta)^{-1}$. By the definition of a fit, the composite is conjugation by an integral matrix that reduces to $1$, as $\eta$ is central and the idele is central. Such a conjugation preserves integrality and reductions. At each place $y(\cdot)$ is a left and right translation of a unimodular group. $\square$

### The cut Bessel functions

For $a = (c, i)$, with $c$ a class and $i$ a Bessel coordinate, the *cut Bessel function* is

$$\phi_a(g) = \begin{cases}\beta_c(y(g_\infty))\,W_i(y(g_\infty)) & \text{if } \psi^{-1}(h_c^{-1}\iota(\eta))\,g_f \in J,\\ 0 & \text{otherwise,}\end{cases}$$

where $J$ is the principal level at the chosen places in the orthonormal bases of $V$ ([Definition](/decl/New.Filling.Fits.cutBessel/), [Definition](/decl/New.Filling.stdPrincipalLevel/)). The *Poincaré series* of $\varphi \in \mathbb{C}^{\mathrm{Classes}\times I}$ is $\mathcal{P}\varphi(g) = \sum_a\varphi_a\sum_{\gamma \in \Gamma}\phi_a(\gamma g)$ (the definition `New.Filling.Fits.poincareSeries` in [PoincareSeries.lean](lean:New/Spanning/Unfolding/PoincareSeries.lean#L307)).

**Lemma (Translates of a cut function).** For rational $\gamma$, $\phi_a(\gamma g) = \beta_c(y)W_i(y)$ with $y = \gamma_\infty y(g_\infty)$ if $h_c^{-1}\gamma_f\iota(\eta)\psi(g_f) \in K(M)$, and $0$ otherwise. So $\|\phi_a(\gamma g)\| \leq \beta_c(y)\prod_v\|W_v(y_v)\|$. The sum of $\phi_a(ug)$ over $u \in \mathsf{U}_c(M)$ is $W_i(y(g_\infty))$ or $0$, by the same condition.

Lean: `New.Filling.Fits.cutBessel_ratEquiv_mul`, `New.Filling.Fits.enorm_cutBessel_ratEquiv_mul_le`, `New.Filling.Fits.tsum_cutBessel_classUnipotent` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* Apply $\psi$ and the lemma on the finite isomorphism. The norm bound is $\|W\| \leq \prod_v\|W_v\|$ for a tensor product. For the sum, $W$ and the condition at the finite places are invariant under $\mathsf{U}_c(M)$, and $\sum_u\beta_c(uy) = 1$. $\square$

**Theorem (Convergence).** There is a constant $C$ with $\sum_{\gamma \in \Gamma}\|\phi_a(\gamma g)\| \leq C$ for all $g$. Each $\phi_a$ is integrable on $G(\mathbb{A})$.

Lean: `New.Filling.Fits.exists_tsum_enorm_cutBessel_le`, `New.Filling.Fits.integrable_cutBessel` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* Let $T$ be the terms over $(c, 1, c)$. [The theorem on the majorants](/chapter/poincare-series/#convergence-of-the-amplitude-sums) gives $C$ with $\sum_{\gamma \in T}\beta_c(\gamma^{-1}y)\prod_v\|W_v((\gamma^{-1}y)_v)\| \leq C$ for all $y$. Fix $g$. If no $\delta$ satisfies the condition of the lemma on translates, every term is $0$. Otherwise fix such a $\delta$ and write the terms as $\gamma^{-1}\delta$. If $\gamma^{-1}\delta$ satisfies the condition too, then $\gamma \in T$, since both conditions together give $h_c^{-1}\gamma_fh_c \in K(M)$. So the sum is at most the sum over $T$ at the point $\delta_\infty y(g_\infty)$, which is at most $C$. The integral of $\|\phi_a\|$ is the integral over $\Gamma\backslash G(\mathbb{A})$ of the sum over $\Gamma$. This is at most $C$ times the volume of the quotient, which is finite. $\square$

**Theorem (Unfolding).** Let $y$ be a form on $V$ of any type, a bounded automorphic function ([Definition](/decl/New.Space.IsForm/)). Then $y\cdot\mathcal{P}\varphi$ is integrable on $\Gamma\backslash G(\mathbb{A})$, and

$$\int_{\Gamma\backslash G(\mathbb{A})}y\,\mathcal{P}\varphi = \sum_a\varphi_a\int_{G(\mathbb{A})}y\,\phi_a.$$

Lean: `New.Filling.Fits.integral_mul_tsum_cutBessel`, `New.Filling.Fits.integrable_and_integral_mul_poincareSeries` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* $y$ is bounded and invariant under $\Gamma$, so $y\phi_a$ is integrable and $y(g)\sum_\gamma\phi_a(\gamma g) = \sum_\gamma(y\phi_a)(\gamma g)$. The integral over the quotient of a sum over $\Gamma$ of an integrable function is its integral over $G(\mathbb{A})$ ([reduction theory](/chapter/reduction-theory/)). The sum over $a$ is finite. $\square$

### The series is a form

**Theorem (The Poincaré map).** For each $a$ there is a form of type the discrete series kernel $\kappa_l$ and level $J$ that equals $g \mapsto \sum_\gamma\phi_a(\gamma g)$. So there is a linear map $\mathcal{P}$ from $\mathbb{C}^{\mathrm{Classes}\times I}$ to this space of forms, whose value at $\varphi$ is the Poincaré series $\mathcal{P}\varphi$ as a function.

Lean: `New.Filling.Fits.integral_typeKernel_mul_besselFn`, `New.Filling.Fits.realConv_tsum_cutBessel_classUnipotent`, `New.Filling.Fits.exists_levelSpace_tsum_cutBessel_eq`, `New.Filling.Fits.coe_poincareMap` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* The type kernel at each place fixes the local Bessel function, since $W_v$ lies in the discrete series of type $l_v$ ([Bessel functions at a real place](/chapter/bessel-real-place/#bessel-functions-as-averages)). The integrand is a product over the places, so right convolution with $\kappa_l$ fixes each coordinate of $W$. Group the series by cosets of $\mathsf{U}_c(M)$. On each coset the part of the series is a translate of $W$ times an indicator at the finite places, by the lemma on translates, and convolution fixes it. The sum over cosets converges absolutely with a bound uniform in $g$ by the convergence theorem. So convolution and sum can be exchanged, and the sum is fixed too. It is bounded and invariant under $\Gamma$. The condition at the finite places is invariant under right translation by $J$. $\square$

### Folding and the Petersson formula

For a class $c$, the *class point* is $x_c = \psi^{-1}(\iota(\eta)^{-1}h_c)$ ([Definition](/decl/New.Filling.Fits.classPoint/)).

**Theorem (Folding).** Let $z$ be a form of level $J$. Then

$$\int_{\Gamma\backslash G(\mathbb{A})}z\,\mathcal{P}\varphi = \operatorname{vol}(J)\sum_c\int_{G_\infty}\beta_c(y(x))\Bigl(\sum_i\varphi_{(c,i)}W_i(y(x))\Bigr)z(x, x_c)\,dx.$$

Lean: `New.Filling.Fits.integral_mul_poincareSeries_eq_sum_classes` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* Apply unfolding. The function $\phi_{(c,i)}$ is supported on $G_\infty \times x_cJ$, and there it does not depend on the finite part. As $z$ has level $J$, $z(x, g_f) = z(x, x_c)$ on this set. So the integrand splits as a function of $x$ times the indicator of $x_cJ$. Fubini gives the product of the two integrals, and the second is $\operatorname{vol}(J)$. $\square$

**Lemma (The value at a class point).** Let $x \in G_f$ with $h_c^{-1}x \in K(M)$, and $k \in K$ with reduction $s$. For rational $\gamma$, $h_{c'}^{-1}\gamma_f^{-1}xk \in K(M)$ if and only if $\gamma$ is a term over $(c, s, c')$. The translate of a function of level $J$ by an integral $k$ has level $J$.

Lean: `New.Filling.Fits.mem_principalLevel_iff_mem_termsOver`, `New.Filling.Fits.hasLevel_mul_right` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* Write $m = h_c^{-1}x \in K(M)$. The element is $(h_c^{-1}\gamma_fh_{c'})^{-1}mk$. It lies in $K(M)$ exactly when $h_c^{-1}\gamma_fh_{c'} \in K$ with reduction equal to that of $mk$, which is $s$. The group $J$ is normal in the integral group. $\square$

**Lemma (Exchange in an entry).** For each entry $(i, i')$, the amplitude sum over $T$ is $\int\sum_\gamma\beta_c(y)\beta_{c'}(\gamma^{-1}y)K(\gamma, y)_{i,i'}\,dy$.

Lean: `New.Filling.Fits.amplitudeSum_apply_eq_integral_tsum` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* The sum of the integrals of the norms is finite ([the theorem on the majorants](/chapter/poincare-series/#convergence-of-the-amplitude-sums)). So the sum and the integral can be exchanged. $\square$

**Theorem (Petersson formula).** Let $a = (c, i)$, $a' = (c', i')$, and $k$ integral with reduction $s$ at the chosen places. Then

$$\langle k\cdot\mathcal{P}e_{a'}, \mathcal{P}e_a\rangle = \operatorname{vol}(J)\cdot\mathcal{A}(c, s, c')_{i,i'},$$

where the amplitude sum is over all rational terms, for the full side.

Lean: `New.Filling.Fits.petersson_poincare` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* Put $z = k\cdot\mathcal{P}e_{a'}$. It has level $J$. The inner product is $\int\bar z\,\mathcal{P}e_a$ over the quotient. Folding with $\varphi = e_a$ leaves the class $c$:

$$\operatorname{vol}(J)\int_{G_\infty}\beta_c(y(x))W_i(y(x))\,\overline{z(x, x_c)}\,dx.$$

At $(x, x_c)$ the series $z$ is $\sum_\gamma\phi_{a'}(\gamma^{-1}(x, x_ck))$. By the lemma on translates and the lemma on the value at a class point, the term of $\gamma^{-1}$ survives exactly when $\gamma$ is a term over $(c, s, c')$. Its value is $\beta_{c'}(\gamma^{-1}y)W_{i'}(\gamma^{-1}y)$ with $y = y(x)$. Substitute $y = y(x)$, which preserves the measure. The integrand becomes $\sum_\gamma\beta_c(y)\beta_{c'}(\gamma^{-1}y)W_i(y)\overline{W_{i'}(\gamma^{-1}y)}$. The lemma on the exchange in an entry gives the amplitude sum. $\square$

**Theorem (The dimension of the source).** The space of algebraic forms on $\mathrm{U}(X_0)$ of weight $(k_w, 0)$ and the source level has dimension $\dim_{\mathrm{source}}$. This equals the number of classes times the dimension of the representation of weight $k_w$, and it is positive.

Lean: `New.Filling.Fits.finrank_levelSpace_eq_sourceDim` (New/Spanning/Unfolding/PoincareSeries.lean).

*Proof.* The stabilizers at the source level are trivial, so a form has one free value in the representation at each class. A fit identifies the Bessel coordinates with the weights of this representation. Both factors are positive. $\square$

**Remark (Formalization).** The inner product and the integrals are Bochner integrals. The unfolding theorem proves the integrability that they need, so no junk value $0$ enters. The class representatives $h_c$, the cutoffs $\beta_c$ and the central $\eta$ are chosen. The formula holds for each choice, with the classes, the cutoffs and the terms of that choice.
