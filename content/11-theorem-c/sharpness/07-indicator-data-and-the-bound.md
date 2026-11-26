---
title: Indicator data and the bound
lean:
  - New/Derivatives/Sharpness/BoundAttained.lean
decls:
  - New.copyEmbedding
  - New.copyExponent
  - New.coeff_prod_rename_copyEmbedding
  - New.Data.map_subst_linearSeries_copy
  - New.Data.norm_natCast_prod_eq_rpow_neg_sum
  - New.Data.twelveSpace
  - New.Data.twelveTaylor
  - New.Data.indicatorDatum
  - New.Data.exists_integral_isThetaFunction_twelveTaylor_eq
  - New.Data.exists_norm_le_norm_indicatorDatum
  - New.Data.exists_le_norm_coeff_indicatorDatum
  - New.Data.norm_map_mul_intVacuum_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Indicator data and the bound

Section 6 bounds $\mathrm{val}_{12}(l)$, a statement about products of power series on the curve. This section carries the bound to a Taylor coefficient of an indicator datum and proves the main theorem of Section 1. The tools are the theta functions along a frame and Fourier inversion of [the integral vacuum](/chapter/integral-vacuum/).

### Twelve copies of the variables

**Definition (Copies).** Let $k \in \mathbb{N}$ and $b < k$. The map $x \mapsto (x, b)$ embeds the variables of one copy as the $b$-th of $k$ copies. For exponents $\alpha_b$, $b < k$, on one copy, the exponent $\alpha$ on $k$ copies has the part $\alpha_b$ in copy $b$.

Lean: `New.copyEmbedding`, `New.copyExponent` (New/Derivatives/Sharpness/BoundAttained.lean), with `New.copyExponent_apply`.

**Lemma (Coefficients of a product of copies).** Let $\Psi_b$, $b < k$, be power series in one copy of the variables. Rename $\Psi_b$ into copy $b$. Then the coefficient of $\prod_b\Psi_b$ at the exponent $\alpha$ with parts $\alpha_b$ is $\prod_b\mathrm{coeff}_{\alpha_b}\Psi_b$.

Lean: `New.coeff_prod_rename_copyEmbedding` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* The coefficient of a product at $\alpha$ is the sum over the families $(\beta_b)$ with $\sum_b\beta_b = \alpha$ of $\prod_b\mathrm{coeff}_{\beta_b}(\Psi_b)$. A renamed series has nonzero coefficients only at exponents in copy $b$. So in a nonzero term each $\beta_b$ lies in copy $b$. The part of $\alpha$ in copy $b$ is then $\beta_b$, so $\beta_b = \alpha_b$. Only one term remains. $\square$

**Lemma (One copy of a form).** Let $f$ be an entire function and $\mu$ a linear form in one copy. Substitute in the Taylor series of $f$ the linear form that is $\mu$ on copy $b$ and $0$ on the other copies, and apply $\iota_p$ to the coefficients. The result is the series of $f$ along $\iota_p\circ\mu$, renamed into copy $b$.

Lean: `New.Data.map_subst_linearSeries_copy` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* Both sides are the Taylor series of $f$ substituted into the same linear form in copy $b$. Substitution commutes with $\iota_p$ and with renaming. $\square$

**Lemma (Norms of natural numbers).** If $n_x \neq 0$ for all $x$ in a finite set, then $|\iota_p(\prod_xn_x)| = p^{-\sum_xv(n_x)}$.

Lean: `New.Data.norm_natCast_prod_eq_rpow_neg_sum` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* $|n| = p^{-v(n)}$ for $n \neq 0$, and both sides are multiplicative. $\square$

### The space and the datum

**Definition (The space of twelve columns).** The space `D.twelveSpace` is $\mathrm{Hom}(E, E^{12})$ of $12 \times 1$ matrices over $E$, with the sum of the norms of the coordinates and all signs $+1$. Its Schwartz space $\mathcal{S}$ models the adelic Heisenberg representation.

Lean: `New.Data.twelveSpace` (New/Derivatives/Sharpness/BoundAttained.lean).

**Definition (The rescaled Taylor series).** For $F \in \mathcal{S}$, `D.twelveTaylor F` is the jet series of $F$ at the scale $a = \pi_M\cdot\mathrm{jetScale}$: for $F$ in the finite part it is the Taylor series at $0$ of $z \mapsto \Theta_F(az)$, where $\Theta_F$ is the theta function of $F$. It is a power series in the variables $z_{\tau,b}$, $\tau \in \Phi$, $b < 12$.

Lean: `New.Data.twelveTaylor` (New/Derivatives/Sharpness/BoundAttained.lean).

Here $\mathrm{jetScale} = \mathrm{periodFactor}\cdot\mathrm{areaScale}/\mathrm{cmPeriod}$. The jet series and the scale are in [theta functions along a frame](/chapter/integral-vacuum/#theta-functions-along-a-frame) and [the scale](/chapter/integral-vacuum/#the-scale).

**Definition (Indicator datum).** For a modulus $\mathfrak{m}$ of $E$ and a class $y_0$ of matrices over $\mathcal{O}_E/\mathfrak{m}$, the vector `D.indicatorDatum 𝔪 y₀` has the Gaussian $\exp(-|x|^2/2)$ as its part at infinity, the indicator of $y_0$ as its part at the places that divide $\mathfrak{m}$, and the vacuum at the other finite places.

Lean: `New.Data.indicatorDatum` (New/Derivatives/Sharpness/BoundAttained.lean), with `New.modDatum`.

### From series to vectors

**Lemma (A vector for twelve series).** Let $w$ be a tight frame of length $M$ with multiplicities $c$. Let $e_b : J \to \mathbb{N}$, $b < 12$, with $3e_b(i) \leq c_i$. There is $F \in \mathcal{S}$ with three properties.

1. $\iota_p$ applied to `D.twelveTaylor F` is the product over the copies $b < 12$ of the series $\prod_iy(\mu_iz)^{e_b(i)}\,\Theta$, renamed into copy $b$.
2. $|\iota_p(F(\mathrm{fin}(x)))| \leq 1$ for every finite adelic vector $x$.
3. The theta function of $F$ is a theta function for the lattice $\bar\pi_M\mathfrak{a}_0^{12}$.

Lean: `New.Data.exists_integral_isThetaFunction_twelveTaylor_eq` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* Write $y^{e}\theta^{c} = (y\theta^3)^{e}\theta^{c - 3e}$. This is a monomial section of the curve with the degrees $(c - 3e, 0, e)$, and $c - 3e \geq 0$ by hypothesis. [The resolution product along a frame](/decl/New.Parameters.exists_isResolutionProduct_of_isTightFrame/) gives $F$ with the properties 2 and 3, and with the jet series equal to the product over $(i, b)$ of the Taylor series of the monomial sections along the forms of copy $b$. The area of the curve is computed from the lattice $\mathrm{cmPeriod}\cdot\mathcal{O}_K$. The scale fits: $\mathrm{cmPeriod}/\bar\pi_M/\mathrm{areaScale}\cdot(\pi_M\,\mathrm{jetScale}) = \mathrm{periodFactor}$, so the forms of copy $b$ are $\mathrm{periodFactor}\cdot\overline{\tau(w_i)}$. Apply $\iota_p$ and the lemma on one copy of a form. The product over $i$ of $\theta(\mu_iz)^{c_i}$ is $\Theta$. $\square$

**Lemma (From a vector to an indicator datum).** Let $F \in \mathcal{S}$ satisfy the properties 2 and 3 of the last lemma. Let $\mathfrak{m}$ have the ideal $(\pi_M)$, let $L$ be a linear form on $\mathcal{S}$, and let $y$ be a finite adelic vector. There is a class $y_0$ modulo $\mathfrak{m}$ with
$$\bigl|\iota_p\bigl(M^{12f}\,L(F)\,\mathrm{vac}(\mathrm{fin}(y))\bigr)\bigr| \leq \bigl|\iota_p\bigl(L(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0)\bigr)\bigr|.$$

Lean: `New.Data.exists_norm_le_norm_indicatorDatum` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* The integer $\bar\pi_M$ is integral and $\bar\pi_M\pi_M = M$. [Fourier coefficients](/decl/New.Space.exists_fourier_coefficients/) with $\delta = \bar\pi_M$ and $N = M$ give vectors $u_i$ with $\bar\pi_Mu_i \in \mathfrak{a}_0^{12}$ and numbers $c_i$ with
$$\sum_ic_i\,\varrho(\mathrm{fin}(u_i))\,\mathrm{vac} = M^{12f}F,$$
since $\Phi \times \{0, \dots, 11\}$ has $12f$ elements. Each $c_i\,\mathrm{vac}$ is a signed sum of translates of $F$. So [its values are integral](/decl/New.Space.norm_mul_vacElem_le_one_of_eq_sum/) with those of $F$: $|\iota_p(c_i\,\mathrm{vac}(\mathrm{fin}(y)))| \leq 1$.

Each translate $\varrho(\mathrm{fin}(u_i))\,\mathrm{vac}$ is a sum $\sum_{y_0}\chi(z_i(y_0))\,\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0$, where $\chi$ is the self-dual character of the finite adeles (`New.exists_rho_finVec_vacElem_eq_sum_modDatum`). This needs $\bar\pi_Mu_i$ integral, which holds. Apply $L$ and multiply by $v_0 = \mathrm{vac}(\mathrm{fin}(y))$:
$$M^{12f}L(F)\,v_0 = \sum_{i, y_0}\chi(z_i(y_0))\,(c_iv_0)\,L(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0).$$
The values of $\chi$ are roots of unity, so they have norm $1$. The sets of $i$ and of $y_0$ are finite. Take $y_0$ with the largest $|\iota_p(L(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0))|$. The ultrametric inequality gives the claim. $\square$

**Remark (Formalization).** The class $y_0$ is a maximizer over a finite set, from `Finite.exists_max`. It depends on $p$, on $\iota_p$ and on $L$. The source gives no explicit $y_0$.

### The reduction

Let $\mathrm{intVacuum} = \mathrm{vacuumScale}^{12}\,\mathrm{vac}$ be the integral vacuum of $\mathcal{S}$ (`New.Parameters.intVacuum`, in [the integral vacuum](/chapter/integral-vacuum/#the-integral-vacuum)).

**Theorem (Reduction to the curve).** Let $w$ be a tight frame of length $M$ with multiplicities $c_i \geq 3|l|$. Suppose $\mathrm{val}_{12}(l) \leq r$. Let $\mathfrak{m}$ have the ideal $(\pi_M)$ and let $y$ be a finite adelic vector. Then there are an exponent $\gamma$ on the variables $z_{\tau,b}$ and a class $y_0$ modulo $\mathfrak{m}$ with $\sum_{b<12}\gamma(\tau, b) = l_\tau$ for every $\tau$ and the following property. Put $A = \mathrm{vacuumScale}^{12}\,\mathrm{coeff}_\gamma\,\mathrm{twelveTaylor}(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0)$. Then
$$p^{-r}\bigl|\iota_p\bigl(M^{12f}\,\mathrm{intVacuum}(\mathrm{fin}(y))\bigr)\bigr| \leq |\iota_p(A)|.$$

Lean: `New.Data.exists_le_norm_coeff_indicatorDatum` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* By [monomials suffice](/decl/New.CMLattice.LeastValLE.exists_monomial/) there are exponents $\alpha_b$ with $\sum_b\alpha_b = l$ and $e_b$ with $|e_b| \leq |l|$ such that
$$p^{-r} \leq \prod_b\Bigl|\mathrm{coeff}_{\alpha_b}\Bigl(\prod_iy(\mu_iz)^{e_b(i)}\,\Theta\Bigr)\Bigr|.$$
Then $3e_b(i) \leq 3|e_b| \leq 3|l| \leq c_i$. Take $F$ from the lemma on a vector for twelve series. Let $\gamma$ have the parts $\alpha_b$; then $\sum_b\gamma(\tau, b) = \sum_b\alpha_b(\tau) = l_\tau$. Put $a = \mathrm{coeff}_\gamma\,\mathrm{twelveTaylor}(F)$. By property 1 and the lemma on coefficients of a product of copies, $p^{-r} \leq |\iota_p(a)|$.

Apply the last lemma to the linear form $L = \mathrm{vacuumScale}^{12}\,\mathrm{coeff}_\gamma\circ\mathrm{twelveTaylor}$. It gives $y_0$ with
$$\bigl|\iota_p\bigl(M^{12f}\,\mathrm{vacuumScale}^{12}a\,\mathrm{vac}(\mathrm{fin}(y))\bigr)\bigr| \leq \bigl|\iota_p\bigl(L(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0)\bigr)\bigr|.$$
The left side is $|\iota_p(a)|\cdot|\iota_p(M^{12f}\,\mathrm{intVacuum}(\mathrm{fin}(y)))|$, since the space has rank $12$. With $p^{-r} \leq |\iota_p(a)|$ the claim follows. $\square$

### The size of $t$

**Lemma (Conjugates of $t$).** Let $l_\tau \leq \kappa(\tau) + x^{42}$ for every $\tau$, and let $y$ be a finite adelic vector. Put
$$t = M^{12f}\prod_\tau B(l_\tau)^2\cdot\mathrm{intVacuum}(\mathrm{fin}(y)).$$
Then $|\sigma(t)| \leq \exp(fmb/k)$ for every ring automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Data.norm_map_mul_intVacuum_le` (New/Derivatives/Sharpness/BoundAttained.lean), with `New.Parameters.norm_ringEquiv_intVacuum_le`.

*Proof.* The factor $M^{12f}\prod_\tau B(l_\tau)^2$ is a natural number, so $\sigma$ fixes it. By [the bound on conjugates](/chapter/integral-vacuum/#the-integral-vacuum), $|\sigma(\mathrm{intVacuum}(\mathrm{fin}(y)))| \leq \exp(C_0q_1^2)^{12}$ with $C_0 = $ `P.vacuumBoundConst`, and $C_0 \leq C = $ `P.constantBound`. Each $B(l_\tau)$ is a product of $n^\sharp$ factors, each at most $l_\tau + n^\sharp \leq 2b + n^\sharp$. So
$$M^{12f}\prod_\tau B(l_\tau)^2 \leq \exp\bigl(12f\log M + 2fn^\sharp\log(2b + n^\sharp)\bigr).$$
[The five inequalities of the data](/chapter/data-and-sizes/#the-scales-and-the-five-inequalities) give, through `New.Data.le_of_hasLogBound`,
$$12f\log M + 2fn^\sharp\log(2b + n^\sharp) + 12Cq_1^2 \leq \frac{fm}{k}\,b.$$
Multiply the two bounds. $\square$

**Remark (Formalization).** The constant $C_0$ is defined by `choose` from an existence statement, so it is not explicit. Only the comparison $C_0 \leq C$ and the size inequality of the data are used.

### The proof of the main theorem

We now prove [the sharpness theorem](/decl/New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff/) of Section 1.

Lean: `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` (New/Derivatives/Sharpness/BoundAttained.lean).

*Proof.* Choose a finite adelic vector $y$ with $c_0 = \mathrm{intVacuum}(\mathrm{fin}(y)) \neq 0$ (`New.Parameters.exists_intVacuum_ne_zero`). Choose [a tight frame of length $M$](/decl/New.Data.exists_isTightFrame/) $w$ with multiplicities $c_i \geq 6fb$, such that for every prime $p$ some form $\mu_{i_0}$ has unit coefficients. Put
$$t = M^{12f}\prod_\tau B(l_\tau)^2\,c_0.$$
Then $t \neq 0$, since $M \neq 0$, $c_0 \neq 0$ and every $B(l_\tau) \neq 0$ (`New.Data.lossProduct_ne_zero`). The bound on the conjugates of $t$ is the last lemma.

Fix $\mathfrak{m}$ with the ideal $(\pi_M)$, a prime $p$ and $\iota_p$. Read $l$ as an exponent on $\Phi \times \{()\}$. Take $i_0$ for this $p$. The degree is small: $|l| \leq f\cdot 2b$, as $l_\tau \leq \kappa(\tau) + x^{42} \leq 2b$. So $3|l| \leq 6fb \leq c_i$. The degree $l$ is near the weights. [Twelve copies](/decl/New.Data.leastValLE_twelve/) gives
$$\mathrm{val}_{12}(l) \leq r := S_p + 2V_B - V_l, \qquad V_B = \sum_\tau v(B(l_\tau)),\quad V_l = \sum_\tau v(l_\tau!).$$
The reduction to the curve gives $\gamma$ and $y_0$ with $\sum_b\gamma(\tau, b) = l_\tau$ and, with $s_0 = M^{12f}c_0$ and $A = \mathrm{vacuumScale}^{12}\,\mathrm{coeff}_\gamma\,\mathrm{twelveTaylor}(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0)$,
$$p^{-r}|\iota_p(s_0)| \leq |\iota_p(A)|.$$
Here $|\iota_p(s_0)| > 0$. By the lemma on norms of natural numbers, $|\iota_p(\prod_\tau B(l_\tau))| = p^{-V_B}$ and $|\iota_p(\prod_\tau l_\tau!)| = p^{-V_l}$. As $t = s_0\,(\prod_\tau B(l_\tau))^2$,
$$p^{-S_p} = \bigl(|\iota_p(s_0)|\,p^{-2V_B}\bigr)^{-1}\,p^{-V_l}\,\bigl(p^{-r}|\iota_p(s_0)|\bigr) \leq |\iota_p(t)|^{-1}\,\Bigl|\iota_p\Bigl(\prod_\tau l_\tau!\Bigr)\Bigr|\,|\iota_p(A)|.$$
The right side is $|\iota_p(\mathrm{vacuumScale}^{12}\,t^{-1}\prod_\tau l_\tau!\;\mathrm{coeff}_\gamma\cdots)|$. $\square$

**Remark (Formalization).** The Lean proof is preceded by `seal Finset.univ in`. The source comment says that this keeps definitional checks from unfolding the finite sums. It does not change the statement. The number $t$ depends on $y$ and on $l$, but not on $p$, $\iota_p$ or $\mathfrak{m}$. The frame $w$ also does not depend on $p$; only the index $i_0$ of the unit form does. Lean accepts this proof, if the reported checks hold.
