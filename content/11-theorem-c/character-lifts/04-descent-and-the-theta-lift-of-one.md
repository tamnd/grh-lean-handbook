---
title: The descent and the theta lift of one
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
decls:
  - New.LValueData.toPoly_eq_rename_fockPoly
  - New.LValueData.fockPoly_eq_schurCoeffPoly
  - New.LValueData.theta_pairThetaKernel_omega_fockDatum
  - New.LValueData.kernelForm_eq_vectorKernelForm
  - New.LValueData.normalizedDescent_eq_inner_kernelForm
  - New.LValueData.inner_trivialLift
  - New.LValueData.isHCParam_zero
  - New.LValueData.fitsParams_descentPair
  - New.LValueData.isForm_const_one
  - New.LValueData.constForm
  - New.LValueData.trivialLift_eq_smul_thetaLift
  - New.LValueData.lift_fockDatum_const_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The descent and the theta lift of one

The lift $\varphi_X$ of Section 3 is a class sum of kernels. The previous chapter defines a different object for the same descent pair: the theta lift $\Theta_W(\xi)$ of a form $\xi$ on $U(1)$, an integral over $U(1)(E)\backslash U(1)(\mathbb{A})$, and its adjoint, the normalized descent $\theta^*$. This section connects the two. The kernel form at $g$ is the vector kernel of the pair at $(x, g)$. So the descent of a form $y$ is its inner product with the kernel, and $\varphi_X$ is the index of the chosen level times $\Theta_W(1)$.

### The Fock polynomial of a one row weight

Let $\kappa$ be the weight of the descent pair, with one row of length $\ell_\tau$ at $\tau$. A coordinate vector $\eta$ of the Weyl module of $\kappa$ gives a polynomial in two ways. The polynomial `toPoly η` is $\sum_i (G\eta)_i\, b_i$ for the Gram matrix $G$ of the weight and the basis $b$ of products of minors, in variables $z_{\tau, a, k}$ with $a \in n$. The Fock polynomial `fockPoly η` of the descent pair is a polynomial in the variables $z_{\tau, a, u}$ of $\mathrm{Hom}(W, V)$, with $u$ in the one point index set of the line.

**Lemma (Two polynomials).** `toPoly η` is the image of `fockPoly η` under the renaming $z_{\tau, a, u} \mapsto z_{(\tau, a), 0}$.

Lean: `New.LValueData.toPoly_eq_rename_fockPoly` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Both sides are linear in $\eta$. A linear map on the Weyl module is fixed by its values on the translates of the evaluation vector by the points of $\prod_\tau \mathrm{GL}_n(\mathbb{C})$ (`ext_schur_weylEval`). On these vectors the laws `top` and `intertwines` of the matrix `mixedCartan` compute the Fock polynomial: it is the highest polynomial with the rows substituted. The two sides agree on them. $\square$

**Lemma (Fock polynomial as a matrix coefficient).** `fockPoly η` is the polynomial $z \mapsto (\eta^{\mathsf T} G)\, S_\kappa(z)\, \mathbf{1}$, the matrix coefficient `schurCoeffPoly (η ᵥ* weylGramOver) 1` of the Schur matrix.

Lean: `New.LValueData.fockPoly_eq_schurCoeffPoly` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Compare the values at a point $z$. By the previous lemma, the value of `fockPoly η` at $z$ is the value of `toPoly η` at an array $y$. The evaluation vector of $y$ is the translate by $z$ of the evaluation vector of rank one (`schur_mulVec_weylEval`). In rank one every minor of size $1$ is the variable itself, so the evaluation vector of rank one is $\mathbf{1}$. The value is the pairing of $S_\kappa(z)\mathbf{1}$ with $G\eta$. $\square$

### The kernel is the vector kernel

Let $\eta$ be a coordinate vector of the weight. The Fock datum `fockDatum η` of the descent pair is the Fock vector of `fockPoly η` at the infinite places, tensored with the block datum $f_0$ at the finite places. Let $\omega$ be the Weil action of $U(1)(\mathbb{A}) \times U(V)(\mathbb{A})$ and $\theta$ the theta functional of $\mathrm{Hom}(W, V)$.

**Lemma (Theta values of Fock data).** For $x$ in the archimedean group of the line, $y$ in the archimedean group of $V$, $g \in U(1)(\mathbb{A}_f)$ and $h \in G_f$,

$$\theta\big(\omega((x, g), (y, h))\, \mathrm{fockDatum}(\eta)\big) = \big\langle \bar\eta,\ \rho_\kappa(y^{-1})\, \theta_X(g)(h)\big\rangle_{\mathrm{Gram}}.$$

The value does not depend on $x$.

Lean: `New.LValueData.theta_pairThetaKernel_omega_fockDatum` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Both sides are $\theta$ of a Fock vector tensored with $\omega((1, g), (1, h)) f_0$. On the left the real points act on the Fock vector alone (`pairWeil_integrated_all`). The real point $x$ of $U(1)$ acts on the Fock vector of `fockPoly η` by the character of its weight, which is trivial by `conjWeylRep_eq_one`. The point $y^{-1}$ then moves the covector of the pairing. On the right the Gram pairing with a vector of jets is the jet along the polynomial `schurCoeffPoly` (`dotProduct_schurJet_mulVec`), which is `fockPoly η` by the previous lemma. The jet of the theta series along a polynomial is the theta value of the Fock vector of that polynomial (`jet_jetSeries_eq_theta`). $\square$

The descent pair has a vector kernel `vectorKernelForm (x, g)`: the form on $V$ whose Gram pairing with $\zeta$ is the theta value of the Fock datum of $\bar\zeta$ (`gramForm_vectorKernel`). This is the kernel of the theta lift of the previous chapter.

**Lemma (Kernel form and vector kernel).** For every real point $x$ of $U(1)$ and every $g$, $\theta_X(g) = $ `vectorKernelForm (x, g)`.

Lean: `New.LValueData.kernelForm_eq_vectorKernelForm` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Two vectors with the same Gram pairings with all $\zeta$ are equal (`ext_gramForm_left`). Fix $h$ and $\zeta$. The pairing of $\zeta$ with the vector kernel is the theta value of the Fock datum of $\bar\zeta$ at $((x, g), (1, h))$. By the previous lemma at $y = 1$ and $\eta = \bar\zeta$, this is $\langle\zeta, \theta_X(g)(h)\rangle_{\mathrm{Gram}}$. $\square$

**Lemma (Descent as an inner product).** For a form $y$ in `X.descentPair.FormV`, a real point $x$ and a finite point $g$ of $U(1)$,

$$\theta^*(y)(x, g) = \langle\theta_X(g), y\rangle.$$

Lean: `New.LValueData.normalizedDescent_eq_inner_kernelForm` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The previous chapter proves that the normalized descent is the inner product with the vector kernel (`normalizedDescent_eq_inner_vectorKernelForm`). Replace the vector kernel by $\theta_X(g)$. $\square$

**Theorem (Inner products with the lift).** For a form $y$ in `X.descentPair.FormV` and every $z \in U(1)(\mathbb{A}_f)$,

$$\langle\varphi_X, y\rangle = \sum_{[g] \in U(1)(E)\backslash U(1)(\mathbb{A}_f)/K_M} \frac{1}{\#\mathrm{Aut}(g)}\, \theta^*(y)(1, gz).$$

Lean: `New.LValueData.inner_trivialLift` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* By the translation lemma of Section 3, $\varphi_X$ is the class sum of $g \mapsto \theta_X(gz)$. The inner product with $y$ is additive in the first variable, so it commutes with finite class sums (`map_classSum`). Then apply the descent lemma at $x = 1$ to each term. $\square$

This is the adjointness of lift and descent for $\varphi_X$. It is the identity that later chapters use most: the inner product of a form $y$ with the lift of a character is a finite sum of values of the descent of $y$.

### The lift is a multiple of the theta lift of one

The theta lift of the previous chapter needs a parameter of the source that fits the descent pair.

**Lemma (Parameter of the line).** The weight of the line, with exponent $0$, has the Harish-Chandra parameter $0$.

Lean: `New.LValueData.isHCParam_zero` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* On a line the parameter is a single number at each place, so it is injective. The parameter of the weight of the line is computed from the columns of height strictly between $0$ and $1$. There are none, so the parameter is $0$. $\square$

**Lemma (The parameter fits).** The parameter $0$ fits `X.descentPair` (`FitsParams 0`).

Lean: `New.LValueData.fitsParams_descentPair` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* There are four conditions. First, the parameter $0$ on $W$ and the parameter `paramV` of $V$ correspond under the block rule. This follows from the criterion `paramsCorrespond_iff` for a lift weight, since `paramV` is twice the Harish-Chandra parameter of the weight on $V$. The number of negative signs of $W$ is $0$, so the determinant exponent of the rule is `detExp`. Second, the numbering of the one basis vector is $0$. Third, `colsPlus` has no column higher than $1$, by the lemma on the columns. Fourth, `colsMinus` is $0$. $\square$

**Lemma (The constant is a form).** The constant function $1$ on $U(1)(\mathbb{A})$ is a form of parameter $0$ for the type kernel `typeKernel 0` of the line.

Lean: `New.LValueData.isForm_const_one` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Let $\psi$ be the constant algebraic form whose value is the highest unit vector $v^+$ of the weight of the line. It is smooth and invariant under the rational points, because the weight is trivial on the line. The function attached to it is $\psi^\natural(x, g) = \langle v^+, v^+\rangle_{\mathrm{Gram}} = 1$ (`gramForm_highestVector_self`). The function attached to an algebraic form with a Harish-Chandra parameter is a form (`isForm_ofAlgForm`). $\square$

**Definition (Constant form).** `X.constForm` is the constant $1$ as an element of the space of forms of parameter $0$ on the line.

Lean: `New.LValueData.constForm` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

**Theorem (Lift of one).** The lift of the character is a multiple of the theta lift of the constant $1$:

$$\varphi_X = [K_0(U(1)) : K_M]\cdot \Theta_W(1),$$

with $[K_0(U(1)) : K_M] = $ `stdLevelIndex X.chosenLevel` the index of the chosen level in the integral points of $U(1)$.

Lean: `New.LValueData.trivialLift_eq_smul_thetaLift` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Two vectors with the same inner product with every $y$ are equal (`ext_inner_right`). Fix $y$ and put $f(g) = \langle\theta_X(g), y\rangle$.

Step 1. By the theorem on inner products with the lift at $z = 1$ and the descent lemma, $\langle\varphi_X, y\rangle$ is the class sum of $f$ at $K_M$.

Step 2. The previous chapter writes $\Theta_W(1)$ as the integral $\int_{U(1)(E)\backslash U(1)(\mathbb{A})} \mathrm{vectorKernelForm}(g)\, dg$ (`thetaLift_eq_integral`). The integrand is integrable (`integrable_smul_vectorKernelForm`), so the inner product with $y$ moves inside the integral. With the conjugate symmetry of the inner product, $\langle\Theta_W(1), y\rangle = \int \theta^*(y)(g)\, dg$.

Step 3. The descent $\theta^*(y)$ is a form on the line (`isForm_normalizedDescent`), so it is continuous and left invariant. Its average over the real points at $g$ is $f(g)$, since it does not depend on the real point. The function $f$ is right invariant under $K_M$, by the invariance of the kernel. So the integral over $U(1)(E)\backslash U(1)(\mathbb{A})$ is $[K_0(U(1)) : K_M]^{-1}$ times the class sum of $f$ at $K_M$ (`integral_quotMeasure_eq_classSum`, in [reduction theory for definite unitary groups](/chapter/reduction-theory/)).

Step 4. So $\langle[K_0(U(1)):K_M]\,\Theta_W(1), y\rangle = [K_0(U(1)):K_M]\cdot[K_0(U(1)):K_M]^{-1}$ times the class sum of $f$, which is $\langle\varphi_X, y\rangle$. The index is a positive integer, hence real, so it passes through the conjugate linear first variable unchanged. $\square$

**Corollary (Lift of one at the Fock datum).** The theta lift of the constant $1$ by the kernel `pairThetaKernel` at the Fock datum of the highest vector $v^+$ of the weight on $V$ is

$$\mathrm{lift}\big(\mathrm{fockDatum}(v^+), 1\big) = [K_0(U(1)) : K_M]^{-1}\cdot \varphi_X^\natural,$$

with $\varphi_X^\natural = $ `ofAlgForm paramV 1 φ_X` the function on $U(V)(\mathbb{A})$.

Lean: `New.LValueData.lift_fockDatum_const_one` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* By the theorem, $\varphi_X^\natural$ is the index times $\Theta_W(1)^\natural$. The function attached to the theta lift is the scalar lift at the Fock datum of the highest vector (`ofAlgForm_thetaLift` and `isArrow_fockDatum.coe_formLift`, in the previous chapter). Divide by the index. $\square$

The corollary puts $\varphi_X$ in the form to which the Rallis inner product formula applies. Section 6 uses it in this form.
