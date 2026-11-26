---
title: The Fock model at a real place
lean:
  - Lib/Weil/Fock/Basic.lean
  - Lib/Weil/Fock/PolynomialVectors.lean
  - Lib/Weil/Fock/OscillatorPair.lean
  - Lib/Weil/Fock/WeightedNorms.lean
decls:
  - New.Fock.realHeisenberg
  - New.Fock.realVac
  - New.Fock.beta_mul_realVac
  - New.Fock.isVacuum_realVac
  - New.Fock.realMultiplier
  - New.Fock.realMultiplier_mul_integral_eq_one
  - New.Fock.realAction
  - New.Fock.realWeil_vacVector_apply_zero
  - New.Fock.polyVector
  - New.Fock.fockInner_polyVector
  - New.Fock.denseRange_polyVector
  - New.Fock.hasDerivAt_realWeil
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Fock model at a real place

This section applies the abstract theory of Sections 2 and 3 at one real place of $F$. The group is the unitary group $U(\varepsilon)$ of a diagonal hermitian form of signature $(p, q)$ on $\mathbb{C}^n$. The vacuum is the Gaussian, the model is the Fock model, and the multiplier is the conjugate of the determinant of the negative block. The main result is that the cocycle of this action is $1$. The section then describes the polynomial vectors and the derivative of the representation. The next chapter, [local theta in the Fock model](/chapter/local-theta/), uses these objects for the local theta correspondence.

### Notation

Let $\iota$ be a finite set, and let $\varepsilon \colon \iota \to \{\pm 1\}$ be a family of signs. Write $\varepsilon$ also for the diagonal matrix $\mathrm{diag}(\varepsilon)$. For $x, y \in \mathbb{C}^\iota$ write $y^* x = \sum_i \overline{y_i} x_i$. The unitary group is
$$U(\varepsilon) = \{ u \in \mathrm{GL}_\iota(\mathbb{C}) : u^* \varepsilon u = \varepsilon \}.$$
It acts on $\mathbb{C}^\iota$ by matrix multiplication. The measure $\mu$ on $\mathbb{C}^\iota$ is Lebesgue measure divided by $\pi^{|\iota|}$.

Lean: `New.USign`, `New.Fock.normalizedVolume` (Lib/General/Groups/CongruenceSubgroups.lean, Lib/General/Analysis/GaussianIntegral.lean).

### The Gaussian vacuum

**Definition (The real datum).** The real Heisenberg datum of $\varepsilon$ on $\mathbb{C}^\iota$ is
$$\beta(x, y) = \exp\bigl(\tfrac12 (y^* \varepsilon x - x^* \varepsilon y)\bigr) = \exp(i \operatorname{Im}(y^*\varepsilon x)).$$
The real vacuum is the Gaussian $e(x) = \exp(-\tfrac12 x^* x)$.

Lean: `New.Fock.realHeisenberg`, `New.Fock.realVac` (Lib/Weil/Fock/Basic.lean).

The bicharacter is the character $\exp(i\,\cdot)$ of the symplectic form $\operatorname{Im}(y^* \varepsilon x)$ on the real space $\mathbb{C}^\iota$, so it is the classical $\beta$ of Section 2. The Gaussian does not depend on $\varepsilon$. Let $\zeta(x) \in \mathbb{C}^\iota$ be the vector with $\zeta(x)_i = \overline{x_i}$ if $\varepsilon_i = 1$ and $\zeta(x)_i = x_i$ if $\varepsilon_i = -1$. This is a real linear isometry of $\mathbb{C}^\iota$.

Lean: `New.Fock.holomorphicCoord`, `New.Fock.holomorphicCoord_eq` (Lib/Weil/Fock/Basic.lean).

**Lemma (The kernel).** For all $x, y \in \mathbb{C}^\iota$,
$$\beta(y, x)\, e(x - y) = e(x)\, e(y)\, \exp\bigl(\zeta(y)^* \zeta(x)\bigr).$$

Lean: `New.Fock.beta_mul_realVac` (Lib/Weil/Fock/Basic.lean).

*Proof.* Both sides are exponentials. Expand $-\tfrac12 (x - y)^*(x - y)$ and compare the exponents coordinate by coordinate, in the two cases $\varepsilon_i = 1$ and $\varepsilon_i = -1$. $\square$

So the reproducing identity of the model, for $v = e F$, says $F(x) = \int F(y)\exp(\zeta(y)^*\zeta(x))\,e(y)^2\,d\mu(y)$. This is Bargmann's reproducing formula for functions of $\zeta(x)$, in which the positive coordinates appear conjugated.

**Theorem (The Gaussian is a vacuum).** The Gaussian $e$ is a vacuum for the real datum of $\varepsilon$ and the measure $\mu$.

Lean: `New.Fock.isVacuum_realVac`, `New.Fock.integral_exp_holomorphicCoord` (Lib/Weil/Fock/Basic.lean).

*Proof.* The Gaussian is continuous, integrable, even, real, and $e(0) = 1$. For the identity of the vacuum, use [the kernel lemma](/decl/New.Fock.beta_mul_realVac/) twice. The integrand becomes $e(z)^2$ times exponentials that are linear in $\zeta(z)$ and $\overline{\zeta(z)}$. The reproducing formula for exponentials, $\int \exp(\zeta(z)^* c)\,e(z)^2\,d\mu(z) = 1$ and its translates, is a Gaussian integral. It gives $e(x)e(y)$. $\square$

The model of this vacuum is the Fock space $\mathcal{F}_\varepsilon$, with the Heisenberg operators $\rho(y)$, the vacuum vector $e$ and the inner product $\int \bar v w\,d\mu$.

Lean: `New.Fock.fockSpace`, `New.Fock.realHeisenbergOp`, `New.Fock.vacVector`, `New.Fock.fockInner` (Lib/Weil/Fock/Basic.lean).

### The multiplier and the cocycle

For a square matrix $u$ and a set $S$ of indices, the principal minor $\det(u_S)$ is the determinant of the block of $u$ on the indices of $S$. The source writes it as $\det(P_+ + P_- u)$, where $P_+$ is the projection on the coordinates of sign $+1$ and $P_- = 1 - P_+$.

Lean: `New.principalMinor`, `New.Fock.posProj`, `New.Fock.principalMinor_sign_eq_det` (Lib/Weil/Fock/Basic.lean).

**Definition (The real multiplier).** For $u \in U(\varepsilon)$, the real multiplier is
$$\Delta_\infty(u) = \overline{\det(u_{-})},$$
the conjugate of the principal minor of $u$ on the indices $i$ with $\varepsilon_i = -1$.

Lean: `New.Fock.realMultiplier`, `New.Fock.norm_realMultiplier_le`, `New.Fock.realMultiplier_ne_zero` (Lib/Weil/Fock/Basic.lean, Lib/Weil/Fock/OscillatorPair.lean).

If all signs are $+1$, then the minor is the empty determinant, and $\Delta_\infty = 1$. The source proves $|\Delta_\infty(u)| \le \|u\|^{|\iota|}$ and $\Delta_\infty(u) \ne 0$. The second fact comes from the cocycle identity below at the pair $(u, u)$: it writes $1$ as a product with the factor $\Delta_\infty(u)$.

**Theorem (The real cocycle is 1).** For $g, h \in U(\varepsilon)$,
$$\Delta_\infty(g)\,\Delta_\infty(h)\,\Delta_\infty((gh)^{-1}) \int\!\!\int e(h x)\, e(g h y)\, \beta(x, y)\, e(x + y)\, d\mu(y)\, d\mu(x) = 1.$$

Lean: `New.Fock.realMultiplier_mul_integral_eq_one`, `New.Fock.det_fromBlocks_mul_fromBlocks_eq_realMultiplier_mul` (Lib/Weil/Fock/Basic.lean).

*Proof.* Put $k = gh$ and $z = (x, y) \in \mathbb{C}^\iota \oplus \mathbb{C}^\iota$. The integrand is $\exp(-z^* A z)$ with
$$A = \tfrac12 \left( J^* J + \begin{pmatrix} 1 & 1 + \varepsilon \\ 1 - \varepsilon & 1 \end{pmatrix} \right), \qquad J = \begin{pmatrix} h & 0 \\ 0 & k \end{pmatrix}.$$
The hermitian part $A + A^*$ is $J^*J + \left(\begin{smallmatrix} 1 & 1 \\ 1 & 1 \end{smallmatrix}\right)$. This is positive definite, because $J$ is invertible and the second matrix is positive semidefinite. So $A$ is accretive. The complex Gaussian integral gives
$$\int \exp(-z^* A z)\, d\mu(z) = (\det A)^{-1},$$
and Fubini's theorem writes this as the iterated integral of the theorem. It remains to prove that $\det A = \Delta_\infty(g)\Delta_\infty(h)\Delta_\infty(k^{-1})$. Put $T(m) = P_+ + P_- m$, so that $\det T(m) = \det(m_-)$. The source factors $A$ into three block matrices:
$$A = \begin{pmatrix} T(h) & 1 - P_+ \\ 0 & T(k^{-1}) k \end{pmatrix}^{\!*} \begin{pmatrix} P_+ & P_+ - 1 \\ 1 & 1 \end{pmatrix} \begin{pmatrix} 1 & 1 \\ -T(h) & -T(h) + T(g^{-1}) k \end{pmatrix}.$$
The identity holds because $h^*\varepsilon h = \varepsilon$ and $k^*\varepsilon k = \varepsilon$: the difference of the two sides is one half of $\mathrm{diag}(h^*\varepsilon h - \varepsilon, \varepsilon - k^*\varepsilon k)$. The determinant of the first factor is $\overline{\det T(h)\,\det T(k^{-1})\,\det k}$. The second factor has determinant $1$, and the third has determinant $\det(T(g^{-1})k)$. Now $\overline{\det T(m)} = \Delta_\infty(m)$, and $\det T(m^{-1}) = \Delta_\infty(m)$ for a unitary $m$, and $|\det k| = 1$. The product is $\Delta_\infty(h)\Delta_\infty(k^{-1})\Delta_\infty(g)$. $\square$

**Definition (The real Weil representation).** The action of $U(\varepsilon)$ on $\mathbb{C}^\iota$ preserves $\beta$ and $\mu$. With the multiplier $\Delta_\infty$ it is a multiplier action with cocycle $1$, by the theorem above. Its Weil representation $\omega_\infty$ on the Fock space is the real Weil representation.

Lean: `New.Fock.realAction`, `New.Fock.realWeil` (Lib/Weil/Fock/Basic.lean).

**Proposition (The vacuum coefficient).** For $u \in U(\varepsilon)$, $(\omega_\infty(u)e)(0) = \det(u_-)^{-1}$.

Lean: `New.Fock.realWeil_vacVector_apply_zero` (Lib/Weil/Fock/PolynomialVectors.lean).

*Proof.* This is [the overlap with the vacuum](/decl/New.Heisenberg.IsVacuum.conj_delta_mul_weilRep_vacElem/) for this action, with $\overline{\Delta_\infty(u)} = \det(u_-)$. $\square$

**Remark (Formalization).** The classical Weil representation of $U(p, q)$ depends on a choice of a splitting of the metaplectic cover over $U(p,q)$, and the usual choices differ by a power of $\det$. The source makes one choice, the conjugate of $\det(u_-)$, and proves that it gives a true representation. Other normalizations appear later as twists by powers of the determinant: the twisted representations of the oscillator pairs at the end of this section are of this kind.

### Polynomial vectors

**Definition (Polynomial vectors).** For a complex polynomial $P$ in the variables $X_i$, $i \in \iota$, the polynomial vector is
$$v_P(x) = P(\zeta(x))\, e(x).$$

Lean: `New.Fock.polyVector`, `New.Fock.polyVector_apply`, `New.Fock.polyVector_one`, `New.Fock.polyVector_injective` (Lib/Weil/Fock/Basic.lean).

The vector $v_P$ lies in the Fock space. The source proves this by induction on $P$. The derivative of $t \mapsto \rho(t y) v_P$ at $t = 0$ is the vector of the polynomial $\sum_i (y_i A_i - \overline{y_i \varepsilon_i} B_i) P$. Here $A_i$ is multiplication by $X_i$ and $B_i$ is $\partial/\partial X_i$ if $\varepsilon_i = 1$, and $A_i = -\partial/\partial X_i$ and $B_i$ is multiplication by $X_i$ if $\varepsilon_i = -1$. A closed subspace contains this derivative, and two choices of $y$ isolate $X_i P$. The map $P \mapsto v_P$ is injective, and $v_1 = e$.

Lean: `New.Fock.raiseOp`, `New.Fock.lowerOp`, `New.Fock.heisenbergDeriv`, `New.Fock.hasDerivAt_realHeisenbergOp` (Lib/Weil/Fock/Basic.lean).

**Example (One coordinate).** Let $\iota$ have one element. If $\varepsilon = 1$, then $U(\varepsilon)$ is the circle group, $\Delta_\infty = 1$, and $u$ preserves $e$. By [the elements that fix the vacuum](/decl/New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul/), $(\omega_\infty(u) v)(x) = v(\bar u x)$. So $\omega_\infty(u) v_{X^k} = u^k v_{X^k}$, since $v_{X^k}(x) = \bar x^k e(x)$. If $\varepsilon = -1$, then $\Delta_\infty(u) = \bar u$ and $v_{X^k}(x) = x^k e(x)$. So $\omega_\infty(u) v_{X^k} = \bar u^{k+1} v_{X^k}$. The circle acts with the weights $0, 1, 2, \dots$ in the first case and $-1, -2, -3, \dots$ in the second.

**Theorem (The Fischer inner product).** For polynomials $P$ and $Q$,
$$\langle v_P, v_Q \rangle = \bigl(\overline{P}(\partial) Q\bigr)(0),$$
where $\overline{P}$ has the conjugate coefficients. For monomials, $\langle v_{X^\mu}, v_{X^{\mu'}}\rangle = \prod_i \mu_i!$ if $\mu = \mu'$, and $0$ otherwise.

Lean: `New.Fock.fockInner_polyVector`, `New.Fock.fockInner_polyVector_monomial`, `New.Fock.fockInner_X_mul`, `New.fockPairing` (Lib/Weil/Fock/PolynomialVectors.lean, Lib/GLn/SchurModule/Basic.lean).

*Proof.* Induction on $P$. For a constant, $\langle e, v_Q\rangle = v_Q(0) = Q(0)$ by the reproducing property. The step from $P$ to $P X_i$ uses $\langle v_{P X_i}, v_Q\rangle = \langle v_P, v_{\partial_i Q}\rangle$: multiplication by $X_i$ is adjoint to $\partial_i$. The source gets this from the commutation of $A_i$ and $B_i$ with $\omega_\infty(u)$ in matrix coefficients, at $u = 1$. The formula for monomials reads off the coefficient of $X^\mu$. $\square$

**Theorem (Density).** The polynomial vectors are dense in the Fock space for the $L^1$ norm.

Lean: `New.Fock.denseRange_polyVector`, `New.Fock.exists_tendsto_fockMoment`, `New.Fock.fockMoment` (Lib/Weil/Fock/PolynomialVectors.lean, Lib/Weil/Fock/WeightedNorms.lean).

*Proof.* Let $V$ be the closure of the polynomial vectors. Each translate $\rho(y) e$ has finite moments $\int (1 + |x|)^N |\rho(y)e(x)|\,d\mu$ for all $N$. The source proves that a vector with finite moments is a limit of polynomial vectors in all these weighted norms at once. The moment with $N = 0$ is the norm. So $V$ contains all the translates $\rho(y) e$. A bounded functional that is $0$ on $V$ is $0$ on these translates, so it is $0$ by [superposition](/decl/New.Heisenberg.IsVacuum.map_eq_integral/). $\square$

**Theorem (The derivative of the representation).** Let $\gamma$ be a curve in $U(\varepsilon)$ with $\gamma(0) = 1$, and let the matrix $\gamma(t)$ have the derivative $Y$ at $t = 0$. Then for every polynomial $P$, the derivative of $t \mapsto \omega_\infty(\gamma(t)) v_P$ at $t = 0$ is $v_Q$ with
$$Q = \sum_{a, b \in \iota} Y_{ab}\, A_a B_b\, P.$$

Lean: `New.Fock.hasDerivAt_realWeil`, `New.Fock.weilDeriv`, `New.Fock.glOp` (Lib/Weil/Fock/PolynomialVectors.lean, Lib/Weil/Fock/Basic.lean).

*Proof.* The matrix $Y$ satisfies $Y^*\varepsilon + \varepsilon Y = 0$. Let $D(P)$ be the derivative, and consider the form $B(Q, P) = \langle v_Q, D(P) - v_{Q'}\rangle$ with $Q' = \sum Y_{ab}A_aB_bP$. The form vanishes at $(1, 1)$: by the [vacuum coefficient](/decl/New.Fock.realWeil_vacVector_apply_zero/), both terms are minus the trace of the negative block of $Y$, the derivative of $\det(P_+ + P_-\gamma(t))^{-1}$. The commutation of $A_a$ and $B_b$ with $\omega_\infty(\gamma(t))$ in matrix coefficients moves the multiplication by $X_j$ from one side of $B$ to the derivative $\partial_j$ on the other side. A sesquilinear form on polynomials with these two properties is $0$. So $D(P) - v_{Q'}$ is orthogonal to all $v_Q$, and it is $0$ by density and the definiteness of the inner product. $\square$

### Products and further material

The Fock space of $T \times \iota$, for a finite set $T$ of real places, contains the product $\prod_{\tau} v_\tau(x_\tau)$ of vectors on $\mathbb{C}^\iota$. The product of polynomial vectors is the polynomial vector of the product, inner products multiply, and a block diagonal element $(u_\tau)_\tau$ acts factor by factor with the multiplier $\prod_\tau \Delta_\infty(u_\tau)$. This is how the source treats all the infinite places of $E$ at once.

Lean: `New.Fock.piTensor`, `New.Fock.piTensor_polyVector`, `New.Fock.fockInner_piTensor`, `New.Fock.blockU`, `New.Fock.realMultiplier_blockU`, `New.Fock.realWeil_piTensor` (Lib/Weil/Fock/Basic.lean).

The file of oscillator pairs computes the matrix coefficients $\langle v_Q, \omega_\infty(u) v_P\rangle$ for harmonic $P$ and $Q$ and block diagonal $u$. It forms the commuting actions of a dual pair on the Fock space of matrices. [Local theta in the Fock model](/chapter/local-theta/) and [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) use this material.

Lean: `New.Fock.fockMatrixCoeff_eq_fockInner`, `New.Fock.detTwist`, `New.OscillatorRep`, `New.OscillatorPair`, `New.Fock.oscillatorPair_detTwist` (Lib/Weil/Fock/OscillatorPair.lean).
