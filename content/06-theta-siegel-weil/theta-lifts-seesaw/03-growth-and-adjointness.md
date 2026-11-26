---
title: Growth, convergence and adjointness
lean:
  - Lib/Weil/DualPair/ThetaLiftConvergence.lean
  - Lib/Weil/DualPair/KernelDecay.lean
  - Lib/Weil/DualPair/ShortIsotropicVectors.lean
decls:
  - New.Space.exists_reduction_norm_le_height
  - New.ThetaKernel.eventually_exists_norm_omega_le_mul_height_pow
  - New.ThetaKernel.moderate_growth
  - New.Space.lift
  - New.ThetaKernel.lift_equivariant
  - New.ThetaKernel.integrable_theta_mul
  - New.ThetaKernel.exists_clm_lift
  - New.ThetaKernel.isModerate_lift
  - New.Space.ModerateWeight
  - New.ThetaKernel.integrable_prod_weightFn
  - New.ThetaKernel.integral_mul_lift_eq_integral_mul_lift_swap
  - New.ThetaKernel.petersson_lift_eq_petersson_descent
  - New.Space.exists_short_isotropic
  - New.pairTheta_modDatum_decay
  - New.pairTheta_modDatum_decay_of_rightInv
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Growth, convergence and adjointness

In this section $(\omega, \theta)$ is an abstract theta kernel for $S$ and $T$ on a Banach space $X$, as in the [definition](/decl/New.ThetaKernel/) of Section 1. The first part proves that the kernel grows at most polynomially in the heights. The second part defines the lift of a function of rapid decay and proves that the lift converges, has moderate growth, and is adjoint to a descent. The last part returns to the pair $\operatorname{Hom}(S, T)$ of Section 2 and states a rapid decay of the kernel in one variable.

### Reduction with a height bound

Reduction theory says that $\Gamma_S \backslash G_S$ is covered by a Siegel set. The proof of moderate growth needs a more quantitative form: a point $g$ is a rational translate of a compact set times a real point whose size is controlled by the height of $g$.

**Lemma (Reduction with a height bound).** Let $V$ be a space with $n'$ coordinates. There is a compact set $\Omega \subset G_V$ with the following property. For every $g \in G_V$ there are $\gamma \in \Gamma_V$ and a finite list $y_1, \dots, y_k$ of real points such that, with $x = y_1 \cdots y_k$:

1. $\gamma g (x, 1)^{-1} \in \Omega$;
2. $\|x_\tau\| \leq \operatorname{ht}_V(g)$ for every infinite place $\tau$;
3. $2^k \leq \operatorname{ht}_V(g)$;
4. $\|(y_i)_\tau\| \leq 2$ for every $i$ and every $\tau$.

Here $\|\cdot\|$ is the operator norm of a complex $n' \times n'$ matrix.

Lean: `New.Space.exists_reduction_norm_le_height` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* By Mahler's criterion of [reduction theory](/chapter/reduction-theory/) there is a compact $\Omega$ such that every $g$ with $\operatorname{ht}_V(g) \leq 2$ has a rational translate in $\Omega$. A halving step (`New.Space.exists_height_mul_inv_le_max`) gives, for every $g$, a real point $y$ with $\|y_\tau\| \leq 2$ for all $\tau$ and
$$\operatorname{ht}_V(g (y, 1)^{-1}) \leq \max(\operatorname{ht}_V(g)/2, 2).$$
We prove by induction on $k$: if $\operatorname{ht}_V(g) \leq 2^{k+1}$, then $g$ is reduced by a list of $k$ points of norm at most $2$ whose product has norm at most $2^k$. For $k = 0$ this is Mahler's criterion. For the step, apply the halving step to $g$, and the induction hypothesis to $g (y, 1)^{-1}$, which has height at most $2^{k+1}$. Append $y$ to the list. Finally choose $k$ with $2^k \leq \operatorname{ht}_V(g) < 2^{k+1}$. This is possible since $\operatorname{ht}_V(g) \geq 1$. $\square$

**Lemma.** Fix $g_0 \in G_S$. For all large integers $A$ and all $h \in G_T$ there is $\delta \in \Gamma_T$ with
$$\|\omega(g_0, \delta h)\| \leq 2^A \operatorname{ht}_T(h)^A.$$

Lean: `New.ThetaKernel.eventually_exists_norm_omega_le_mul_height_pow` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* Let $\Omega$ be the compact set of the previous lemma for $T$, and let $B$ be the compact set of real points with all components of norm at most $2$. By joint continuity, $\omega$ is bounded on the compact set $\{g_0, 1\} \times (\Omega \cup B)$ by a constant $C$. Take $A$ with $2^A \geq C$. Write $\delta h = z\, (y_1 \cdots y_k, 1)$ with $z \in \Omega$. Then $\omega(g_0, \delta h) = \omega(g_0, z) \prod_i \omega(1, (y_i, 1))$, and each of the $k + 1$ factors has norm at most $2^A$. So the norm is at most $2^A (2^A)^k \leq 2^A \operatorname{ht}_T(h)^A$. $\square$

### Moderate growth

**Theorem (Moderate growth of theta kernels).** There are a constant $C$ and an integer $A$ such that for all $g \in G_S$, $h \in G_T$ and $\varphi \in X$,
$$|\theta(\omega(g, h)\varphi)| \leq C \|\varphi\| \big(\operatorname{ht}_S(g) \operatorname{ht}_T(h)\big)^A.$$

Lean: `New.ThetaKernel.moderate_growth` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* Apply the previous lemma with $g_0 = 1$ to the kernel and to its swap, the kernel for $T$ and $S$ with the same $\theta$ (`New.ThetaKernel.swap`). Both statements hold for all large exponents, so there is one $A$ for both. For given $g, h$ this gives $\gamma \in \Gamma_S$ and $\delta \in \Gamma_T$ with $\|\omega(\gamma g, 1)\| \leq 2^A \operatorname{ht}_S(g)^A$ and $\|\omega(1, \delta h)\| \leq 2^A \operatorname{ht}_T(h)^A$. By the invariance of $\theta$,
$$\theta(\omega(g, h)\varphi) = \theta(\omega(\gamma g, \delta h)\varphi) = \theta\big(\omega(\gamma g, 1)\, \omega(1, \delta h)\, \varphi\big).$$
So $|\theta(\omega(g, h)\varphi)| \leq \|\theta\|\, 4^A \operatorname{ht}_S(g)^A \operatorname{ht}_T(h)^A \|\varphi\|$. $\square$

In particular, for fixed $h$ and $\varphi$, the function $g \mapsto \theta(\omega(g, h)\varphi)$ has moderate growth on $G_S$ (`New.ThetaKernel.isModerate`). If $\varphi$ is fixed by an open subgroup of $G_{S,f}$, this function is automorphic (`New.ThetaKernel.isAutomorphic`).

**Remark (Formalization).** For the Weil representation the usual proofs bound the theta series on a Siegel set by a direct estimate. The source does not use the form of $\omega$ at all. It uses only that $\omega$ is a continuous homomorphism, so that its norm is bounded on compact sets and submultiplicative, and that reduction theory writes every point as a rational translate of a compact set times about $\log_2 \operatorname{ht}$ real points of bounded size. The exponent $A$ that comes out depends on the bound of $\omega$ on the compact set, and the proof gives no explicit value.

### The lift

**Definition (Theta lift).** For $\varphi \in X$ and a function $y$ on $G_S$, the theta lift of $y$ with datum $\varphi$ is the function on $G_T$
$$\mathcal{L}_\varphi y(h) = \int_{[S]} \theta(\omega(g, h)\varphi)\, y(g)\, dg.$$

Lean: `New.Space.lift` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

The integral is a Bochner integral for the quotient measure of [automorphic forms](/chapter/automorphic-forms/). It is defined for every $y$, and it is $0$ when the integrand is not integrable. All results below assume that $y$ is automorphic of rapid decay, and then the integrand is integrable.

**Lemma (Equivariance).** Let $y$ be automorphic on $G_S$. For $k \in G_S$ and $h, l \in G_T$,
$$\mathcal{L}_\varphi y(h l) = \mathcal{L}_{\omega(k, l)\varphi}\, y_k(h), \qquad y_k(g) = y(g k).$$

Lean: `New.ThetaKernel.lift_equivariant` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* The integrand $g \mapsto \theta(\omega(g, h l)\varphi)\, y(g)$ is left invariant under $\Gamma_S$, and the quotient measure is invariant under right translation by $k$. Substitute $g k$ for $g$ and use $\omega(g k, h l) = \omega(g, h)\, \omega(k, l)$. $\square$

The case $k = 1$ is the right translation law $\mathcal{L}_\varphi y(h l) = \mathcal{L}_{\omega(1, l)\varphi} y(h)$ (`New.lift_mul_right`). The lift is left invariant under $\Gamma_T$ (`New.ThetaKernel.fixesLeft_lift`).

**Theorem (Convergence).** Let $y$ be automorphic of rapid decay on $G_S$.

1. For all $\varphi$ and $h$, the function $g \mapsto \theta(\omega(g, h)\varphi)\, y(g)$ is integrable on $[S]$.
2. There are continuous linear functionals $L_h$ on $X$ with $\mathcal{L}_\varphi y(h) = L_h(\varphi)$ for all $\varphi$ and $h$.
3. $\mathcal{L}_\varphi y$ is continuous and has moderate growth on $G_T$.

Lean: `New.ThetaKernel.integrable_theta_mul`, `New.ThetaKernel.exists_clm_lift`, `New.ThetaKernel.continuous_lift`, `New.ThetaKernel.isModerate_lift` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* Moderate growth gives $|\theta(\omega(g, h)\varphi)\, y(g)| \leq |C| \|\varphi\| \operatorname{ht}_T(h)^A \cdot |y(g)| \operatorname{ht}_S(g)^A$. Since $y$ is rapid, the last factor is bounded. The integrand is continuous, and $[S]$ has finite measure. This proves 1, and integration of the bound gives the moderate growth in 3. For 2, take $L_h$ to be the integral over $[S]$ of the operator valued function $g \mapsto y(g)\, \theta \circ \omega(g, h)$. For continuity, write $\mathcal{L}_\varphi y(h) = L_1(\omega(1, h)\varphi)$ by the right translation law, and use the continuity of $h \mapsto \omega(1, h)\varphi$. $\square$

By 1, the lift is bilinear in $\varphi$ and $y$ (`New.ThetaKernel.liftBilin`).

**Remark (Formalization).** The lift is not asserted to be automorphic in general. Its level depends on $\varphi$: by the equivariance lemma, it is right invariant under $l$ when $\omega(1, l)\varphi = \varphi$. The lift of a form of a type is treated in Section 4, where the edge hypotheses supply the type.

### Weights and adjointness

The seesaw of Section 5 integrates kernels against forms on a third group $G_U$, read through a map to $G_T$. The following structure records the data of such a map.

**Definition (Moderate weight).** A moderate weight from $U$ to $T$ is a pair of a continuous function $M$ on $G_U$ of moderate growth and a continuous map $j : G_U \to G_T$, such that $\operatorname{ht}_T(j(v)) \leq C \operatorname{ht}_U(v)$ for some constant $C$ and all $v$.

Lean: `New.Space.ModerateWeight` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

**Lemma.** Let $y$ be rapid on $S$, $F$ rapid on $U$, and $(M, j)$ a moderate weight from $U$ to $T$. Then the function $(v, g) \mapsto M(v) F(v)\, \theta(\omega(g, j(v))\varphi)\, y(g)$ is integrable on $[U] \times [S]$.

Lean: `New.ThetaKernel.integrable_prod_weightFn` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* The kernel is at most $|C| \|\varphi\| \operatorname{ht}_T(j(v))^A$ times a bounded function of $g$, and $\operatorname{ht}_T(j(v))^A \leq C^A \operatorname{ht}_U(v)^A$. Since $M$ is moderate and $F$ is rapid, $M F \operatorname{ht}_U^A$ is bounded. A bounded continuous function is integrable on a space of finite measure. $\square$

**Theorem (Transposition and adjointness).** Let $y$ be automorphic of rapid decay on $G_S$ and $y'$ automorphic of rapid decay on $G_T$. Write $\mathcal{L}'$ for the lift of the swapped kernel, from $T$ to $S$. Then
$$\int_{[T]} y'(h)\, \mathcal{L}_\varphi y(h)\, dh = \int_{[S]} y(g)\, \mathcal{L}'_\varphi y'(g)\, dg,$$
and for the Petersson product $\langle F, F' \rangle = \int \overline{F}\, F'$,
$$\langle y', \mathcal{L}_\varphi y \rangle_T = \big\langle \overline{\mathcal{L}'_\varphi \bar y'}, y \big\rangle_S.$$

Lean: `New.ThetaKernel.integral_mul_lift_eq_integral_mul_lift_swap`, `New.ThetaKernel.petersson_lift_eq_petersson_descent` (Lib/Weil/DualPair/ThetaLiftConvergence.lean).

*Proof.* The previous lemma with $U = T$, $M = 1$ and $j$ the identity shows that $(h, g) \mapsto y'(h)\, \theta(\omega(g, h)\varphi)\, y(g)$ is integrable on $[T] \times [S]$. Fubini's theorem exchanges the two integrals, and the inner integral over $[T]$ is $\mathcal{L}'_\varphi y'(g)$. For the second identity apply the first to $\bar y'$, which is again rapid. $\square$

The map $y' \mapsto \overline{\mathcal{L}'_\varphi \bar y'}$ is the descent. The theorem says that the descent is the adjoint of the lift on functions of rapid decay. Cusp forms are of rapid decay, so the theorem covers the usual case of lifts of cusp forms. The source states the identity with the same datum and the conjugation outside the lift, so it needs no conjugation on $X$.

### Rapid decay of the kernel of the pair

For the Weil representation of $\operatorname{Hom}(S, T)$ the kernel decays in one variable when the finite datum is supported on maps of full rank at some prime. The proof needs short isotropic vectors.

**Lemma (Short isotropic vectors).** If $\operatorname{ht}_S(g) > 2$, the lattice of $S$ moved by $g$ contains a nonzero isotropic rational vector $x$, $x^* J_S x = 0$, of length at most $2 / \operatorname{ht}_S(g)$.

Lean: `New.Space.exists_short_isotropic` (Lib/Weil/DualPair/ShortIsotropicVectors.lean).

**Theorem (Rapid decay in the first variable).** Let $\mathfrak{m}$ be a modulus with at least one prime divisor, and let $\Psi$ be a function on $n' \times n$ matrices modulo $\mathfrak{m}$ supported on matrices with a left inverse. For each integer $M$ there are integers $B, N$ and a constant $C$ such that for every Fock vector $v$ with finite moment $\mu_N(v) = \int (1 + \|y\|)^N |v(y)|\, dy$, and for all $g, h$,
$$\big|\theta^{S,T}_{a,b}(v \otimes \Psi \otimes \mathrm{vac})(g, h)\big|\, \operatorname{ht}_S(g)^M \leq C\, \mu_N(v)\, \operatorname{ht}_T(h)^B.$$
With $\Psi$ supported on matrices with a right inverse, the same holds with the roles of $g$ and $h$ exchanged.

Lean: `New.pairTheta_modDatum_decay`, `New.pairTheta_modDatum_decay_of_rightInv` (Lib/Weil/DualPair/KernelDecay.lean).

*Proof sketch.* Let $w$ be a prime of $\mathfrak{m}$. If the lift of $\Psi$ is nonzero at a finite adelic matrix $x$, then the component $x_w$ has a left inverse over the residue ring at $w$. So the datum is supported on maps that are injective at $w$ (`New.pairTheta_decay_of_injective`). Let $\operatorname{ht}_S(g) > 2$. Take a short isotropic vector $c$ of $S$ at $g$ and a short basis $d$ of $T$ at $h$, of length at most a constant times $\operatorname{ht}_T(h)$. The rational maps $z \mapsto d_i \langle c, z \rangle$ of rank one are isotropic for the form of $\operatorname{Hom}(S, T)$, and they act on data by translations that do not change $\theta$. Since the support of the finite datum consists of maps injective at $w$, the pairing of each point of the support with these rank one maps is nonzero (the conditions of `New.IsShortPair`). Small shifts along these maps then let the proof trade a power of $\operatorname{ht}_S(g)$ for a moment of the Fock vector $v$. The moderate growth theorem bounds the rest. $\square$

**Remark (Formalization).** The docstring of the file names the method: small shifts along a short isotropic vector, instead of Siegel sets. For decay the file cites Kudla and Rallis (1994), where estimates of this kind are made on Siegel sets. The source needs at least one prime in $\mathfrak{m}$. With $\mathfrak{m} = \mathcal{O}_E$ the hypothesis `h_ne` fails, and the theorem says nothing. The constants $B$, $N$ and $C$ are not given explicitly.
