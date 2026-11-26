---
title: Scaling, integral jets and stable standard data
lean:
  - New/Derivatives/Vacuum/Scale.lean
  - New/Derivatives/Vacuum/JetIntegrality.lean
decls:
  - New.jet_rescale
  - New.Space.jet_jetSeries_of_isHomogeneous
  - New.norm_adeleExtension_le_one_iff
  - New.CMLattice.area_eq_of_a₁_eq
  - New.Parameters.norm_periodFactor_mul_daggerForms_le_one
  - New.Parameters.norm_jetScale_sq
  - New.norm_jet_le_one_of_pderiv_mem
  - New.CMLattice.smul_derivative_derivative_negLogTheta_mem
  - New.CMLattice.jetRing
  - New.CMLattice.norm_constantCoeff_le_of_mem_jetRing
  - New.CMLattice.pderiv_mem_jetRing
  - New.CMLattice.norm_jet_thetaProd_pow_mul_le_one
  - New.Parameters.finHeisenbergOp_mem_standardData
  - New.Parameters.omega_finHeisenbergOp_intVacuum
  - New.Parameters.omega_mem_standardData
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Scaling, integral jets and stable standard data

This section collects three groups of facts that Sections 7 and 8 use. The first group relates jets of the Taylor series $J_a f$ to theta values and computes the modulus of the scale. The second proves that the jets of a power of a theta product, times an integral series, are integral. The third proves that standard data are stable under two kinds of operators.

### Scaling

**Lemma (Jets of a rescaled series).** Let $Q$ be homogeneous of degree $l$, $a$ a constant and $F$ a power series. Then $\mathrm{jet}(Q)(F(az)) = a^l\, \mathrm{jet}(Q)(F)$.

Lean: `New.jet_rescale` (New/Derivatives/Vacuum/Scale.lean).

*Proof.* The jet is $\sum_\alpha Q_\alpha \alpha! F_\alpha$, and only $|\alpha| = l$ occurs. The coefficient of $z^\alpha$ in $F(az)$ is $a^{|\alpha|} F_\alpha$. $\square$

**Lemma (Jets as theta values).** Let $V$ be a hermitian space with signs $\varepsilon$, $f$ a vector of the Weil model $\mathcal{S}(V)$, $a \in \mathbb{C}$ and $Q$ homogeneous of degree $l$. Then

$$\mathrm{jet}(Q)(J_a f) = a^l\, \theta\big(v_Q \otimes f\big),$$

where $v_Q$ is the Fock vector of $Q$ for the signs of the coordinates and $\otimes$ is the integrated action of the real Heisenberg group.

Lean: `New.Space.jet_jetSeries_of_isHomogeneous` (New/Derivatives/Vacuum/Scale.lean).

*Proof.* $J_a f$ is $J_1 f$ with the variables scaled by $a$. Apply the previous lemma and the formula for $a = 1$ of [the Weil representation from a vacuum](/chapter/weil-representation/). $\square$

So the divisibility of jets of $J_a f$ is the divisibility of theta values, which is the form in which the later chapters use it.

**Lemma (Integrality of an adelic image).** Let $\sigma \colon E \to F$ be an embedding into a $p$-adic field. The image of a finite adele $x$ under the extension of $\sigma$ to finite adeles has norm at most $1$ if and only if the component of $x$ at the place of $\sigma$ is integral.

Lean: `New.norm_adeleExtension_le_one_iff` (New/Derivatives/Vacuum/Scale.lean).

**Lemma (Integral dagger forms).** Let $u_j$ be a vector over $E$ such that $\alpha^{-1}u_j$ is integral at the places above $p$, where $\alpha$ is the idele of the parameters. Then the coefficients of the linear form $z \mapsto u_j^\dagger z$, read in $\mathbb{C}_p$ and multiplied by $\iota_p(\mathrm{periodFactor})$, are integral.

Lean: `New.Parameters.norm_periodFactor_mul_daggerForms_le_one` (New/Derivatives/Vacuum/Scale.lean).

*Proof.* The coefficient at the infinite place $v$ and the coordinate $i$ is $\sigma(u_{j,i})$, for the embedding $\sigma$ into $\mathbb{C}_p$ that $\iota_p$ and the CM type give at $v$. The norm of $\iota_p(\mathrm{periodFactor})$ equals the norm of $\sigma$ applied to the component of $\alpha^{-1}$ at the place of $\sigma$ (`New.Parameters.norm_iota_periodFactor`, in [the integral vacuum and tight frames](/chapter/integral-vacuum/)). So the product is the image of the component of $\alpha^{-1}u_{j,i}$, and the previous lemma applies. $\square$

**Lemma (Equal invariants give equal areas).** Two CM lattices for $d$ with the same invariant $a_1$ have the same area.

Lean: `New.CMLattice.area_eq_of_a₁_eq` (New/Derivatives/Vacuum/Scale.lean).

*Proof.* With the same $a_1$, each lattice is an isogeny image of the other with a natural number factor $N$, so each area is a natural multiple of the other. The product of the two multiples is $1$. $\square$

**Theorem (The modulus of the scale).** $|\mathrm{jetScale}|^2 = \Omega_E^{-1}$, where $\Omega_E = e^{c_d} \cdot 2\pi/\mathrm{rd}_E$ with the constant $c_d$ of the formula of Chowla and Selberg and the root discriminant $\mathrm{rd}_E$.

Lean: `New.Parameters.norm_jetScale_sq` (New/Derivatives/Vacuum/Scale.lean).

*Proof.* This is the formula of Chowla and Selberg ([CM elliptic curves](/chapter/cm-elliptic-curves/)) for the lattice conjugate by $\sigma = 1$. That lattice has the invariant $a_1$ of $\Omega_0\mathcal{O}_K$, so by the previous lemma it has the area $|\Omega_0|^2\sqrt d/2$, and the identity follows from the relation between $\mathrm{periodFactor}$, $\mathrm{areaScale}$ and the area proved in [the integral vacuum and tight frames](/chapter/integral-vacuum/). $\square$

### Integral jets of theta products

Let $C$ be a CM lattice for $d$, $\theta$ its normalized theta function with $\theta(0) = 1$, $g = -\log\theta$, and $y$ the parameter of [CM elliptic curves](/chapter/cm-elliptic-curves/), all as power series over $\mathbb{C}_p$. For linear forms $\mu_i$, the ring $\mathcal{M}(\mu)$ consists of the integral power series in the $y(\mu_i z)$. A *theta product* is $\Theta_\mu^m = \prod_i \theta(\mu_i z)^{m_i}$.

**Lemma (Jets on a ring closed under derivatives).** Let $S$ be a ring of power series over $\mathbb{C}_p$ whose elements have integral constant terms and which is closed under all partial derivatives. Let $\varphi \colon R \to \mathbb{C}_p$ be a ring homomorphism with integral values. Then $\mathrm{jet}(\varphi(Q))(F)$ is integral for all $F \in S$ and all polynomials $Q$ over $R$.

Lean: `New.norm_jet_le_one_of_pderiv_mem` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* Induction on $Q$. For a constant $a$, the jet is $\varphi(a)$ times the constant term of $F$. The jet is additive in $Q$, and the norm is ultrametric. For $Q X_x$ the jet of $F$ is the jet of $\partial_x F$ along $Q$, and $\partial_x F \in S$. $\square$

**Lemma (The second derivative of $-\log\theta$).** $d \cdot g''$ is an integral series in $y$.

Lean: `New.CMLattice.smul_derivative_derivative_negLogTheta_mem` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* The second derivative $g''$ is a constant $2g_2$ plus the translated function $x$, a series in $y$. Multiplication by $\sqrt{-d}$ maps the lattice into itself, so $\iota_p(\sqrt{-d})$ is integral, and $d = -(\sqrt{-d})^2$. The constant $\sqrt{-d}\cdot 2g_2$ is integral by `New.CMLattice.norm_sqrt_mul_coeff_two_negLogTheta_le_one` ([CM elliptic curves](/chapter/cm-elliptic-curves/)), so $d \cdot 2g_2$ is integral, and $d\,x$ is integral since $x$ is. $\square$

**Definition (The jet ring).** $\mathcal{J}(\mu)$ is the ring generated by $\mathcal{M}(\mu)$, the series $\theta(\mu_i z)$ and the series $g'(\mu_i z)$.

Lean: `New.CMLattice.jetRing` (New/Derivatives/Vacuum/JetIntegrality.lean).

Its elements have integral constant terms, because $y(0) = 0$, $\theta(0) = 1$ and $g'(0) = 0$.

Lean: `New.CMLattice.norm_constantCoeff_le_of_mem_jetRing` (New/Derivatives/Vacuum/JetIntegrality.lean).

**Lemma (The jet ring is closed under derivatives).** Let $\mu_i = d\,\nu_i$ with $\nu_i$ integral. Then $\mathcal{J}(\mu)$ is closed under all partial derivatives.

Lean: `New.CMLattice.pderiv_mem_jetRing` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* By the Leibniz rule it suffices to check the generators. The series of $\mathcal{M}(\mu)$ have derivatives in $\mathcal{M}(\mu)$, since $\mu$ is integral. From $\theta' = -\theta g'$, the derivative of $\theta(\mu_i z)$ in $z_x$ is $-\mu_{i,x}\,\theta(\mu_i z) g'(\mu_i z)$. The derivative of $g'(\mu_i z)$ is $\mu_{i,x}\, g''(\mu_i z) = \nu_{i,x}\, (d g'')(\mu_i z)$, which lies in $\mathcal{M}(\mu)$ by the previous lemma. $\square$

The factor $d$ in $\mu$ is needed only for the last generator: it clears the denominator of $g''$.

**Theorem (Integral jets of theta products).** Let $\mu_i = d\,\nu_i$ with $\nu_i$ integral, $m_i, N \ge 0$, and $H \in \mathcal{M}(\mu)$. For every ring homomorphism $\varphi$ with integral values and every polynomial $Q$,

$$\big\|\mathrm{jet}(\varphi(Q))\big((\Theta_\mu^m)^N H\big)\big\| \le 1.$$

Lean: `New.CMLattice.norm_jet_thetaProd_pow_mul_le_one` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* The series lies in $\mathcal{J}(\mu)$. Apply the lemma on rings closed under derivatives. $\square$

The theorem gives integrality and nothing more. The divisibility comes from the normal form in Section 4, which uses the finer structure of the theta products.

### Stability of standard data

Recall from [the integral vacuum and tight frames](/chapter/integral-vacuum/) that the standard data $\mathrm{Std}_\delta(V)$ of level $\delta$ are the span, over the complex numbers $c$ with $\iota_p(c)$ integral, of the translates $\rho(x)\,\phi^\circ$ of the integral vacuum by the finite adelic points $x$ such that $\delta x$ is integral above $p$.

**Lemma (Heisenberg operators).** If $\delta x$ is integral above $p$, the Heisenberg operator $\rho(x)$ maps $\mathrm{Std}_\delta(V)$ into itself.

Lean: `New.Parameters.finHeisenbergOp_mem_standardData` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* On a generator, $\rho(x)\rho(x')\phi^\circ$ is a root of unity times $\rho(x + x')\phi^\circ$, and $\delta(x + x')$ is integral above $p$. A root of unity has norm $1$. $\square$

**Lemma (A Weil operator on a translate of the vacuum).** For a finite unitary point $g$ and a finite adelic $x$, with $L$ the standard lattice,

$$\omega(1, g)\,\rho(x)\,\phi^\circ = \lambda(g^{-1})^{-1}\; \rho(gx) \sum_{y \in L/(L \cap g^{-1}L)} \rho(gy)\,\phi^\circ,$$

where $\lambda$ is the finite part of the multiplier of the Weil operators.

Lean: `New.Parameters.omega_finHeisenbergOp_intVacuum` (New/Derivatives/Vacuum/JetIntegrality.lean).

**Theorem (Weil operators).** If $g$ is integral above $p$, then $\omega(1, g)$ maps $\mathrm{Std}_\delta(V)$ into itself.

Lean: `New.Parameters.omega_mem_standardData` (New/Derivatives/Vacuum/JetIntegrality.lean).

*Proof.* On a generator, apply the previous lemma. The factor $\lambda(g^{-1})^{-1}$ has norm $1$ under $\iota_p$, because $g^{-1}$ is also integral above $p$ (`New.Parameters.norm_finMultiplier_eq_one`, in [the seesaw identity, part 1](/chapter/seesaw-identity-1/)). If $\delta x$ is integral above $p$, so is $\delta g x$, since $g$ is an integral matrix there (`New.Parameters.mulVec_mem_integralAfter`). The same holds for $\delta g y$ with $y \in L$. So each term is standard data, and the Heisenberg lemma applies. $\square$

**Remark (Formalization).** The sum over $L/(L \cap g^{-1}L)$ is the Lean sum `finsum`, which is $0$ when the support is infinite. The proof of stability uses only that every term is standard data (`finsum_induction`), so it holds whatever the value of the sum.
