---
title: The adelic representation and the theta functional
lean:
  - Lib/Weil/Construction/WeilData.lean
  - Lib/Weil/Construction/AdelicRepresentation.lean
  - Lib/Weil/Construction/CanonicalTheta.lean
decls:
  - New.adelicHeisenberg
  - New.vacuumFn
  - New.isVacuum_vacuumFn
  - New.weilMultiplier
  - New.adelicAction
  - New.Space.ω
  - New.Space.IsThetaFunctional
  - New.Space.IsRatInvariant.hasSum_modelInner
  - New.Space.exists_isThetaFunctional
  - New.Space.IsThetaFunctional.eq_smul
  - New.Space.θ
  - New.Space.hasSum_dataInner
  - New.Space.theta_eq_theta_omega
  - New.Space.theta_boxProd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The adelic representation and the theta functional

This section puts the real and the finite constructions together. The result is a unitary representation $\omega$ of the adelic unitary group $G$ on a Banach space $\mathcal{S}(V)$. For a hermitian space $V$ with a point, the section then constructs the theta functional $\theta_V$: a bounded functional on $\mathcal{S}(V)$ that is invariant under the rational Heisenberg operators. It is unique up to a scalar.

Throughout, $E$ is a CM field with [Weil data](/decl/New.WeilData/), $\mathbb{A} = \mathbb{A}_E$ is its ring of adeles, $\psi$ is the standard additive character of $\mathbb{A}$, trivial on $E$, and $s \colon \{1, \dots, n\} \to \{\pm 1\}$ is a sign vector. The group $G = G(E, s)$ is the [adelic unitary group](/decl/New.G/) of the form $h$ with matrix $\mathrm{diag}(s)$, the [standard form](/decl/New.stdForm/).

### The adelic Heisenberg datum and its vacuum

**Definition (The adelic Heisenberg datum).** The adelic Heisenberg datum on $\mathbb{A}^n$ has the bicharacter
$$\beta(x, y) = \psi\big(\tfrac{\jmath}{2}\, h(y, x)\big), \qquad h(y, x) = y^* \operatorname{diag}(s)\, x.$$

Lean: `New.adelicHeisenberg` (Lib/Weil/Construction/WeilData.lean).

Since $\bar{\jmath} = -\jmath$ and $h$ is hermitian, the argument $\tfrac{\jmath}{2} h(x, x)$ is skew, and $\psi$ is trivial on skew adeles of this form. So $\beta(x, x) = 1$.

**Definition (The adelic vacuum).** For $x \in \mathbb{A}^n$ with infinite components $x_{i, \tau}$ and finite part $x_f$,
$$e(x) = \exp\Big(-\pi \sum_{i} \sum_{\tau} \operatorname{Im}(\Phi_\tau \jmath)\, |x_{i, \tau}|^2\Big) \cdot \begin{cases} \psi_f\big(\tfrac{c_0 \jmath}{2}\, x_f^* x_f\big) & \text{if } \alpha^{-1} x_f \in \hat{\mathcal{O}}^n, \\ 0 & \text{otherwise.} \end{cases}$$
Here $\tau$ runs over the infinite places, $\Phi_\tau$ is the embedding of the CM type at $\tau$, and $c_0 = (1 - \jmath^{-1})/2$.

Lean: `New.vacuumFn`, `New.vacuumFn_eq_exp_mul_ite` (Lib/Weil/Construction/WeilData.lean).

Since $c_0 \jmath / 2 = (\jmath - 1)/4$ and $\psi_f$ does not see the skew part $\jmath x_f^* x_f/4$, the phase is $\psi_f(-\tfrac14 x_f^* x_f)$. The vacuum does not depend on the signs $s$.

The idele $\kappa$ with component $(2\pi \operatorname{Im} \Phi_\tau \jmath)^{-1/2}$ at each infinite place $\tau$ and finite part $\alpha$ identifies the two halves of the construction with $\mathbb{A}^n$. Along this isomorphism, $\beta$ is the product of the bicharacter of the real Heisenberg datum of [Section 4](/decl/New.Fock.realHeisenberg/) with the signs $s_i$ at each pair $(\tau, i)$, and of the finite bicharacter of [Section 5](/decl/New.stdLattice.finVac/). The vacuum $e$ is the product of the Gaussian [real vacuum](/decl/New.Fock.realVac/) and the lattice vacuum. This is an orthogonal sum in the sense of [Section 3](/chapter/weil-representation/#weil-operators-and-their-cocycle).

**Theorem (The adelic vacuum).** The function $e$ is a vacuum for the adelic Heisenberg datum and the measure $\mu$ on $\mathbb{A}^n$ that is the image of the product of the real and the finite measures under the isomorphism above.

Lean: `New.isVacuum_vacuumFn`, `New.vacuumMeasure`, `New.adelicSum`, `New.WeilData.scaleIdele`, `New.WeilData.conj_scaleIdele_mul` (Lib/Weil/Construction/AdelicRepresentation.lean; Lib/Weil/Construction/WeilData.lean).

*Proof.* The vacuum of an orthogonal sum is the product of the vacua, and the two factors are vacua by [the real vacuum](/decl/New.Fock.isVacuum_realVac/) and [the lattice vacuum](/decl/New.stdLattice.isVacuum_finVac/). $\square$

### The adelic Weil representation

An element $g \in G$ has components $g_\tau$ at the infinite places and a finite part $g_f \in G_f$. At an infinite place, $g_\tau$ is a unitary matrix for $\mathrm{diag}(s)$, and the real multiplier of [Section 4](/decl/New.Fock.realMultiplier/) is the conjugate of the determinant of the block of $g_\tau$ on the coordinates of sign $-1$.

**Definition (The adelic multiplier).** For $g \in G$,
$$\Delta(g) = \Big(\prod_{\tau} \Delta_\tau(g_\tau)\Big)\, \Delta_f(g_f),$$
where $\Delta_\tau$ is the real multiplier and $\Delta_f$ is [the finite multiplier](/decl/New.finMultiplier/).

Lean: `New.weilMultiplier`, `New.weilMultiplier_inv`, `New.weilMultiplier_ne_zero` (Lib/Weil/Construction/AdelicRepresentation.lean).

**Theorem (The adelic Weil action).** The group $G$ acts on $\mathbb{A}^n$ by matrices. The action preserves $\beta$ and $\mu$. With the multiplier $\Delta$, it is a multiplier action on the adelic vacuum with cocycle $1$.

Lean: `New.adelicAction` (Lib/Weil/Construction/AdelicRepresentation.lean).

*Proof.* The action preserves $\beta$ since $g^* \operatorname{diag}(s) g = \operatorname{diag}(s)$. Along the isomorphism with real and finite coordinates, the action is the product of the real action of [Section 4](/decl/New.Fock.realAction/) and the finite action of [Section 5](/decl/New.finAction/). So it preserves the product measure, and the double integral in the cocycle identity is the product of the real and the finite double integrals. Multiply the two cocycle identities, each with value $1$. $\square$

**Definition (The Weil representation on $\mathcal{S}(V)$).** Let $V$ be a [hermitian space with a point](/decl/New.Space/) of signs $s$. The space $\mathcal{S}(V)$ is the model of the adelic vacuum, with its norm, its inner product $\langle \cdot, \cdot \rangle$ and its vacuum vector $\mathrm{vac}$. The Heisenberg operators are $\varrho(x)$ for $x \in \mathbb{A}^n$, and the Weil representation $\omega \colon G \to \mathrm{End}(\mathcal{S}(V))$ is [the Weil representation](/decl/New.Heisenberg.IsVacuum.weilRep/) of the adelic action.

Lean: `New.Space.ω`, `New.𝒮`, `New.Space.ϱ`, `New.Space.dataInner`, `New.Space.vacElem`, `New.Space.omega_rho`, `New.Space.dataInner_omega`, `New.Space.dataInner_vacElem_omega_vacElem`, `New.Space.continuous_omega` (Lib/Weil/Construction/AdelicRepresentation.lean).

By Section 3, these operators satisfy the following.

1. $\omega(g)\varrho(x) = \varrho(g x)\omega(g)$ for $g \in G$ and $x \in \mathbb{A}^n$.
2. $\langle \omega(g) f, \omega(g) f' \rangle = \langle f, f' \rangle$.
3. $\langle \mathrm{vac}, \omega(g)\mathrm{vac} \rangle = \overline{\Delta(g)}^{\,-1}$.
4. The map $(g, f) \mapsto \omega(g) f$ is continuous.

The space $\mathcal{S}(V)$ and the operators depend only on the signs $s$. The point of $V$ enters through the rational vectors: the subgroup $V(E) = \{x_V^{-1} y : y \in E^n\} \subset \mathbb{A}^n$, where $x_V \in \mathrm{GL}_n(\mathbb{A})$ is the point of $V$. On rational vectors $\beta$ is $1$, since $\psi$ is trivial on $E$. The quotient $\mathbb{A}^n / V(E)$ is compact.

### Theta functionals

**Definition (Theta functional).** A bounded functional $\ell$ on $\mathcal{S}(V)$ is rationally invariant if $\ell(\varrho(\gamma) f) = \ell(f)$ for every $\gamma \in V(E)$ and every $f$. A theta functional of $V$ is a rationally invariant functional $\theta$ with
$$\int_{\mathbb{A}^n / V(E)} \big|\theta(\varrho(x)\,\mathrm{vac})\big|^2\, dx = 1,$$
for the Haar probability measure on the quotient.

Lean: `New.Space.IsThetaFunctional`, `New.Space.IsRatInvariant`, `New.Space.ratVectors` (Lib/Weil/Construction/AdelicRepresentation.lean).

The tool for theta functionals is a summation formula. For rationally invariant $\ell$ and $\ell'$, the function $x \mapsto \ell(\varrho(x) f)\,\overline{\ell'(\varrho(x) f')}$ is continuous and periodic under $V(E)$. The characters of the compact group $\mathbb{A}^n/V(E)$ are the functions $x \mapsto \beta(x, x_V^{-1}\gamma)^2$ for $\gamma \in E^n$: this is the self-duality of $V(E)$.

**Theorem (The summation formula).** Let $\ell$ and $\ell'$ be rationally invariant functionals, and let $c$ be the mean of $\ell(\varrho(x)\mathrm{vac})\,\overline{\ell'(\varrho(x)\mathrm{vac})}$ over $x \in \mathbb{A}^n/V(E)$. Then for all $f, f' \in \mathcal{S}(V)$,
$$\sum_{\gamma \in E^n} c\, \big\langle f', \varrho(x_V^{-1}\gamma) f \big\rangle = \ell(f)\, \overline{\ell'(f')},$$
and the series converges.

Lean: `New.Space.IsRatInvariant.hasSum_modelInner`, `New.Space.IsRatInvariant.quotMean_eq_mul_modelInner`, `New.Space.summable_modelInner`, `New.Space.isDualFamily_beta_sq` (Lib/Weil/Construction/AdelicRepresentation.lean).

*Proof.* The series converges absolutely by [the Wiener bound](/chapter/weil-representation/#weil-operators-and-their-cocycle) of Section 3: superpose $f$ from translates of the vacuum, and count the rational vectors in a compact set. The mean of $\ell(\varrho(x) f)\overline{\ell'(\varrho(x) f')}$ over the quotient is an invariant sesquilinear form in $(f', f)$. By [the uniqueness of the invariant form](/decl/New.Heisenberg.IsVacuum.form_eq_mul_modelInner/), it is $c \langle f', f \rangle$. Replace $f$ by $\varrho(\gamma) f$. Since $\ell$ absorbs $\varrho(\gamma)$ and the commutator of $\varrho(\gamma)$ and $\varrho(x)$ is $\beta(x, \gamma)^2$, this gives the Fourier coefficients of the periodic function. Fourier inversion at $0$ gives the formula. $\square$

**Theorem (Existence of a theta functional).** Every hermitian space $V$ with a point has a theta functional.

Lean: `New.Space.exists_isThetaFunctional` (Lib/Weil/Construction/AdelicRepresentation.lean).

*Proof.* Suppose not. Let $\ell$ be rationally invariant, and let $c \ge 0$ be its mean as in the summation formula. If $c > 0$, then $c^{-1/2}\ell$ is a theta functional. So $c = 0$, and the summation formula with $f = f'$ gives $|\ell(f)|^2 = 0$. Hence every rationally invariant functional is $0$. For each $u$ the series $f \mapsto \sum_\gamma \langle u, \varrho(x_V^{-1}\gamma) f\rangle$ is rationally invariant, so it vanishes. Take $u = \varrho(-a)\mathrm{vac}$ and $f = u$. As a function of $a$, the result is a Fourier series on $\mathbb{A}^n/V(E)$ with constant term $\langle \mathrm{vac}, \mathrm{vac}\rangle = 1$. Its mean is $1$, but it vanishes. This is a contradiction. $\square$

**Theorem (Uniqueness of the theta functional).** Let $\theta$ be a theta functional of $V$. Then every rationally invariant functional $\ell$ is $c\,\theta$ for some $c \in \mathbb{C}$.

Lean: `New.Space.IsThetaFunctional.eq_smul`, `New.Space.IsThetaFunctional.exists_eq_apply_smul`, `New.Space.IsThetaFunctional.injective_apply_heisenbergOp` (Lib/Weil/Construction/AdelicRepresentation.lean).

*Proof.* The functional $\theta$ is not $0$, since its mean is $1$. Take $u$ with $\theta(u) = 1$, and let $c$ be the mean of $\ell(\varrho(x)\mathrm{vac})\overline{\theta(\varrho(x)\mathrm{vac})}$. The summation formula for the pairs $(\ell, \theta)$ and $(\theta, \theta)$ has the same series up to the factor $c$. So $\ell(f)\overline{\theta(u)} = c\,\theta(f)\overline{\theta(u)}$, that is, $\ell = c\,\theta$. $\square$

The same argument shows that a vector $f$ is determined by its theta function $x \mapsto \theta(\varrho(x) f)$.

### The theta functional of a space

The uniqueness leaves a scalar of modulus one. The source does not fix it: it picks the functionals of the standard lines by `choose`.

For each sign $c \in \{\pm 1\}$, let $\theta_c$ be a theta functional of the standard line of sign $c$. The [standard space](/decl/New.signedSpace/) of signs $s$ is the orthogonal sum of these lines. It has a theta functional $\theta_s$ with
$$\theta_s(\varrho(x)\mathrm{vac}) = \prod_{i} \theta_{s_i}(\varrho(x_i)\mathrm{vac})$$
for every $x \in \mathbb{A}^n$. To get it, take any theta functional: the summation formula factors over the coordinates, so its values on translates of the vacuum are a constant multiple of the product, and one rescales by a factor of modulus one.

By [Landherr's theorem](/decl/New.Space.landherr/) in the form of [Volume 4](/decl/New.Space.exists_x_eq_and_ratEmbed_conj_eq/), two hermitian spaces with a point and the same signs $s$ are related by an element of $G$: there is $g \in G$ with $g\, V(E) \subset W(E)$.

**Definition (The theta functional of $V$).** Take $g \in G$ that carries the rational vectors of $V$ into those of the standard space. The theta functional of $V$ is $\theta_V = \theta_s \circ \omega(g)$.

Lean: `New.Space.θ`, `New.Space.rawTheta`, `New.Space.theta_eq_rawTheta`, `New.Space.isThetaFunctional_rawTheta`, `New.lineTheta`, `New.exists_isThetaFunctional_signedSpace`, `New.Space.exists_mapsTo_ratVectors` (Lib/Weil/Construction/AdelicRepresentation.lean; Lib/Weil/Construction/CanonicalTheta.lean).

The functional $\theta_V$ is a theta functional of $V$, since $\omega(g)$ preserves the inner product and carries the vacuum to a vector with the same mean. For $f \in \mathcal{S}(V)$ and $x \in \mathbb{A}^n$, we write $f(x) = \theta_V(\varrho(x) f)$. This is the theta function of $f$. So $\theta_V(f) = f(0)$, $\theta_V(\varrho(y) f) = f(y)$, and $|f(x)| \le \|\theta_V\|\,\|f\|$.

**Remark (Formalization).** The definition contains three choices. The rank one functionals $\theta_{\pm 1}$ come from `choose` applied to the existence theorem. The functional $\theta_s$ is a second `choose`. The element $g$ is a third `choose`, inside a case split whose other branch takes any theta functional of $V$. By Landherr's theorem the other branch does not occur, and the next theorem shows that $\theta_V$ does not depend on $g$. It does depend on the choices of $\theta_{\pm 1}$ and $\theta_s$, each up to a scalar of modulus one. The findings list this as F-050. The source also composes $\theta_V$ with $\varrho(0)$, which is the identity, so that $\theta_V(f) = f(0)$ holds by definition.

**Theorem (Transport of the theta functional).** Let $W$ and $V$ be hermitian spaces with a point and the same signs, and let $g \in G$ carry $W(E)$ into $V(E)$. Then $\theta_W(f) = \theta_V(\omega(g) f)$ for every $f \in \mathcal{S}(V)$. In particular, if $V \cdot \gamma$ is the space with the point of $V$ moved by $\gamma \in G$, then $\theta_{V \cdot \gamma} = \theta_V \circ \omega(\gamma)$.

Lean: `New.Space.theta_eq_theta_omega`, `New.Space.theta_move`, `New.Space.theta_omega_eq_of_mapsTo_ratVectors` (Lib/Weil/Construction/CanonicalTheta.lean).

*Proof.* First let $W$ be the standard space. Let $g_0$ be the element chosen in the definition of $\theta_V$. Then $g g_0$ carries $V(E)$ into itself, so its matrix entries in the coordinates of $V$ are rational, and $g g_0$ is a rational point $\gamma$ of the unitary group of $V$. By [Weil's invariance](/decl/New.Space.theta_omega_ratEmbed/) of Section 7, $\theta_V \circ \omega(\gamma^{-1}) = \theta_V$. With $g_0 \gamma^{-1} g = 1$ this gives $\theta_V \circ \omega(g) = \theta_s$. For general $W$, take $p$ that carries the standard space to $W$, apply the first case to $p$ and to $g p$, and cancel $\omega(p)$. $\square$

**Theorem (The theta functional of an orthogonal sum).** Let the point of $V$ be the block sum of the points of $V_1$ and $V_2$ along a splitting of the coordinates, with the signs split in the same way. Then for $f_1 \in \mathcal{S}(V_1)$ and $f_2 \in \mathcal{S}(V_2)$,
$$\theta_V(f_1 \boxtimes f_2) = \theta_{V_1}(f_1)\, \theta_{V_2}(f_2).$$

Lean: `New.Space.theta_boxProd`, `New.Space.boxProd` (Lib/Weil/Construction/CanonicalTheta.lean).

*Proof.* Take $g_1$ and $g_2$ that carry the standard spaces to $V_1$ and $V_2$. The block matrix of $(g_1, g_2)$ carries the standard space of signs $s$ to $V$. Both sides are bounded bilinear forms in $(f_1, f_2)$, and the vectors $\omega(g_i)\varrho(y_i)\mathrm{vac}$ span dense subspaces. So it is enough to compare the two sides on these vectors. There, by the transport theorem and the product formula for $\theta_s$, each side is the product over the coordinates of the rank one values $\theta_{s_i}(\varrho(y_i)\mathrm{vac})$. $\square$

**Theorem (Theta values and inner products).** For $f, f' \in \mathcal{S}(V)$,
$$\sum_{\gamma \in E^n} \big\langle f', \varrho(x_V^{-1}\gamma) f \big\rangle = \theta_V(f)\, \overline{\theta_V(f')}, \qquad \langle f, f' \rangle = \int_{\mathbb{A}^n/V(E)} f'(x)\, \overline{f(x)}\, dx.$$

Lean: `New.Space.hasSum_dataInner`, `New.Space.dataInner_eq_quotMean` (Lib/Weil/Construction/AdelicRepresentation.lean).

*Proof.* This is [the summation formula](/decl/New.Space.IsRatInvariant.hasSum_modelInner/) and its proof for $\ell = \ell' = \theta_V$, where the constant $c$ is $1$. $\square$

The second identity is the form in which the inner product enters the Rallis inner product formula of [a later chapter](/chapter/rallis-inner-product/).
