---
title: Bessel functions as averages
lean:
  - New/Spanning/Bessel/Average.lean
  - New/Spanning/Bessel/LargeFunction.lean
decls:
  - New.DiscreteSeries.UnitarySignFrame
  - New.DiscreteSeries.besselIntegrand
  - New.DiscreteSeries.besselAverage
  - New.DiscreteSeries.lintegral_unfold_besselGraphMeasure
  - New.DiscreteSeries.measurePreserving_unfold_besselGraphMeasure
  - New.DiscreteSeries.besselBallVolume
  - New.DiscreteSeries.besselBallVolume_ne_top
  - New.DiscreteSeries.besselBallVolume_ne_zero
  - New.DiscreteSeries.lintegral_decay_le_besselBallVolume
  - New.DiscreteSeries.norm_dsCoeffInFrame_le
  - New.DiscreteSeries.continuous_besselIntegrand
  - New.DiscreteSeries.enorm_besselIntegrand
  - New.DiscreteSeries.lintegral_enorm_besselIntegrand_le
  - New.DiscreteSeries.integrable_besselIntegrand
  - New.DiscreteSeries.besselAverage_mul
  - New.DiscreteSeries.isBesselFunction_besselAverage
  - New.DiscreteSeries.convolve_besselAverage
  - New.DiscreteSeries.enorm_besselAverage_le
  - New.DiscreteSeries.integrable_besselAverage
  - New.DiscreteSeries.formalDegree_mul_integral_norm_sq_besselAverage
  - New.Filling.IsDiscreteSeriesBessel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bessel functions as averages

The full function $W$ of the Bessel system is not given by a formula. It is an average of a matrix coefficient of the discrete series over the group $R$ of [the previous section](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length). This section defines the average, proves that it converges, and proves the three properties that the rest of the chapter uses: it is a Bessel function, the kernel of the discrete series reproduces it, and its squared norm in $L^2(\mathsf U\backslash G_1)$ is a period.

### The data of the average

The coefficient $c_\lambda$ is defined on the group $U(\operatorname{diag}\varepsilon)$ of a diagonal form of signs, not on $G_1$. A fixed frame carries it over.

**Definition.** A *unitary sign frame* for the signs $\varepsilon$ is an invertible matrix $p$ with $p^* J_1 p = \operatorname{diag}(\varepsilon)$ that is also unitary.

Lean: `New.DiscreteSeries.UnitarySignFrame` (New/Spanning/Bessel/LargeFunction.lean).

The frame gives the isomorphism $g \mapsto p^{-1}gp$ from $G_1$ onto $U(\operatorname{diag}\varepsilon)$, and the coefficient in the frame is $c_\lambda(g) = c_\lambda(p^{-1}gp)$ (`New.DiscreteSeries.frameEquiv`, `New.HCParam.dsCoeffInFrame`, Lib/Weil/Periods/Grading.lean). For the coefficient $c_\lambda$ of a doubled Harish-Chandra parameter $l = 2\lambda$, see [the section on parameters](/chapter/discrete-series/) in Volume 5. Because $p$ is unitary, the operator norm of $p^{-1}gp$ is the operator norm of $g$, and the decay of $c_\lambda$ in the norm on $U(\operatorname{diag}\varepsilon)$ is a decay in the norm on $G_1$.

**Remark (Formalization).** The frame is a type class argument. In the source it is the instance `New.Data.unitarySignFrameY`, which is `Nonempty.some` of an existence statement, so the frame is a choice. No statement of the chapter depends on which frame is chosen, but the function $W$ does. See [the last section](/chapter/bessel-real-place/#the-bessel-system-of-the-data).

### The integrand and the average

Fix a continuous unitary representation $\rho$ of $H = U(k)$ on $\mathbb{C}^I$, a point $x \in G_1$, and a vector $v \in \mathbb{C}^I$. For $s = (g, h) \in R$ put
$$\pi(s) = \operatorname{wave}(\sigma(g))\,\rho(h),$$
where $\sigma(g)$ is the sum of the entries of $g$ just above the diagonal on the frame, [`New.simpleRootSum`](/decl/New.simpleRootSum/), and $\operatorname{wave}(c) = \exp(c - \bar c)$ as in [the chapter on Bessel subgroups](/chapter/bessel-bruhat/#bessel-functions-and-the-schur-bound). Since $\sigma$ is additive on $S$ and vanishes on $H$, $\pi$ is a unitary representation of $R$.

**Definition (Bessel average).** For $y \in G_1$ and $s \in R$,
$$\Phi_y(s) = c_\lambda(x^{-1}gy)\,\operatorname{wave}(-\sigma(g))\,\rho(h)^{-1}v, \qquad W_x(y) = \int_R \Phi_y(s)\,ds,$$
with $s = (g, h)$ and the measure $ds = du\,dh$.

Lean: `New.DiscreteSeries.besselIntegrand`, `New.DiscreteSeries.besselAverage` (New/Spanning/Bessel/Average.lean).

So $W_x(y) = \int_R c_\lambda(x^{-1}sy)\,\pi(s)^{-1}v\,ds$. The integral is a Bochner integral. If $\Phi_y$ is not integrable, the source value of $W_x(y)$ is $0$, a junk value. The lemmas below exclude this case under the gap condition.

**Example.** Take $\varrho = 0$. Then $\mathsf U$ is trivial, $R \cong U(k)$ with the Haar probability measure, and $W_x(y) = \int_{U(k)} c_\lambda(x^{-1}\iota(h)y)\,\rho(h)^{-1}v\,dh$. This is the projection of the function $h \mapsto c_\lambda(x^{-1}\iota(h)y)$ onto the $\rho$-isotypic part, paired with $v$. In rank one, with $G_1 = U(1,1)$ and $H = U(1)$, it picks out one Fourier coefficient in the angle of $h$. This is the weight $k$ component of a matrix coefficient, which is the classical starting point of Petersson's construction.

### Unfolding

The integrals over $R$ and over $\mathsf U\backslash G_1$ combine to an integral over $G_1$.

**Lemma (Unfolding).** For a measurable $f : G_1 \to [0, \infty]$ and $x \in G_1$,
$$\int_{G_1} f(g)\,dg = \int_{\mathsf U\backslash G_1} \int_R f(xsy)\,ds\,dy.$$
Equivalently, the map $(y, s) \mapsto sy$ carries the product of the quotient measure and $ds$ to the Haar measure of $G_1$.

Lean: `New.DiscreteSeries.lintegral_unfold_besselGraphMeasure`, `New.DiscreteSeries.measurePreserving_unfold_besselGraphMeasure` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Write $s = \iota(k)u$ with $u \in \mathsf U$ and $k \in H$. The integrals over $u$ and over $y \in \mathsf U\backslash G_1$ together give the integral over $G_1$, by [`New.lintegral_orbitMeasure_lintegral`](/decl/New.lintegral_orbitMeasure_lintegral/) of [the chapter on reduction theory](/chapter/reduction-theory/). Left invariance of the Haar measure removes $x\iota(k)$, and $H$ has total mass $1$. $\square$

### The ball and the covering bound

The convergence of $W_x$ comes from the decay of $c_\lambda$ and a count of the points of $R$ near a point.

**Definition.** $\operatorname{vol}_x$ is the measure in $R$ of the set of $s$ with $\|x^{-1}sx - 1\| \leq 1$, the matrix $x^{-1}sx$ being read in the sign frame.

Lean: `New.DiscreteSeries.besselBallVolume` (New/Spanning/Bessel/LargeFunction.lean).

**Lemma.** $0 < \operatorname{vol}_x < \infty$.

Lean: `New.DiscreteSeries.besselBallVolume_ne_top`, `New.DiscreteSeries.besselBallVolume_ne_zero` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* The map $s \mapsto x^{-1}sx$ from $R$ to $G_1$ is proper: $R$ is closed in $G_1 \times H$ and $H$ is compact. So the preimage of the closed unit ball around $1$ is compact, and the measure is finite. The set contains a neighbourhood of $1$ in $R$, and $ds$ is positive on open sets. $\square$

**Lemma (Covering bound).** Let $N = 9r^2$. For all $x, y \in G_1$,
$$\int_R \Bigl(\frac{2}{\|x^{-1}sy\|}\Bigr)^N ds \leq 16^N \operatorname{vol}_x.$$

Lean: `New.DiscreteSeries.lintegral_decay_le_besselBallVolume` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Let $j(s) = x^{-1}sx$, a proper homomorphism from $R$ to $G_1$. Then $j(s)\,x^{-1}y = x^{-1}sy$. The source applies a general bound (`New.lintegral_decay_le`, Lib/DiscreteSeries/Haar/TotalMass.lean): for a proper homomorphism $j$ into a unitary group of size $r$, a right invariant measure that is finite on compact sets, and an integer $c > 8r^2$,
$$\int \Bigl(\frac{2}{\|j(s)g\|}\Bigr)^c ds \leq 16^c \cdot \operatorname{meas}\{s : \|j(s) - 1\| \leq 1\}$$
for every $g$. Its proof bounds the measure of each set where $\|j(s)g\|$ lies in a range by a covering with translates of the small ball, and sums over the ranges. The condition $c > 8r^2$ makes the sum converge. Here $c = 9r^2$ and $g = x^{-1}y$. $\square$

**Lemma (Decay of the coefficient).** If $l$ has the gap $500r^3 + A$ ([`New.HCParam.HasLargeGap`](/chapter/discrete-series/)), then for $j \leq A$ and $g \in G_1$,
$$|c_\lambda(g)| \leq \Bigl(\frac{2}{\|g\|}\Bigr)^{j + 9r^2}.$$

Lean: `New.DiscreteSeries.norm_dsCoeffInFrame_le` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Since $r^2 \leq r^3$, the exponent $j + 9r^2$ is at most the gap $500r^3 + A$. The decay bound `New.DiscreteSeries.norm_dsCoeff_le_pow` of [the chapter on the discrete series](/chapter/discrete-series/) in Volume 5 gives $|c_\lambda(g)| \leq (2/\|g\|)^m$ for every exponent $m$ up to the gap. $\square$

The exponent has two parts. The part $9r^2$ pays for the covering bound. The part $j$ is free and gives the decay of $W$ in the next sections. For the data $D$ the excess $A$ is $r^7$, so there is a large free part.

### Convergence and the Bessel law

**Lemma.** Let $\rho$ be continuous, $\|v\| = 1$, and let $l$ have the gap $500r^3 + A$. Then:

1. $(y, s) \mapsto \Phi_y(s)$ is continuous;
2. $\|\Phi_y(s)\| = |c_\lambda(x^{-1}sy)|$;
3. $\int_R \|\Phi_y(s)\|\,ds \leq 16^{9r^2}\operatorname{vol}_x$ for every $y$;
4. $\Phi_y$ is integrable on $R$.

Lean: `New.DiscreteSeries.continuous_besselIntegrand`, `New.DiscreteSeries.enorm_besselIntegrand`, `New.DiscreteSeries.lintegral_enorm_besselIntegrand_le`, `New.DiscreteSeries.integrable_besselIntegrand` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* (1) $c_\lambda$, $\sigma$, $\operatorname{wave}$ and $\rho$ are continuous. (2) $\operatorname{wave}$ has modulus $1$ and $\rho(h)$ is unitary. (3) Use (2), the decay lemma with $j = 0$, and the covering bound. (4) follows from (1), (3) and $\operatorname{vol}_x < \infty$. $\square$

The bound (3) is uniform in $y$. This makes $W_x$ bounded, which is part of the definition of a Bessel function.

**Theorem (The average is a Bessel function).** Under the hypotheses of the lemma:

1. $W_x(sy) = \pi(s)W_x(y)$ for $s \in R$ and $y \in G_1$;
2. $W_x$ is a Bessel function for $\rho$: it is bounded and measurable, $W_x(uy) = \operatorname{wave}(\sigma(u))W_x(y)$ for $u \in \mathsf U$, and $W_x(\iota(h)y) = \rho(h)W_x(y)$ for $h \in H$.

Lean: `New.DiscreteSeries.besselAverage_mul`, `New.DiscreteSeries.isBesselFunction_besselAverage` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* (1) Substitute $ts^{-1}$ for $t$ in the integral. The measure $ds$ is right invariant, and $\operatorname{wave}(-\sigma(ts^{-1})) = \operatorname{wave}(\sigma(s))\operatorname{wave}(-\sigma(t))$ by additivity of $\sigma$. So $\Phi_{sy}(t s^{-1}) = \pi(s)\Phi_y(t)$, and $\pi(s)$ is a continuous linear map that commutes with the integral. (2) Boundedness is item 3 of the lemma. Measurability follows from the joint continuity of the integrand. For $u \in \mathsf U$, apply (1) to $(u, 1) \in R$. For $h \in H$, apply (1) to $(\iota(h), h)$. $\square$

For the definition of a Bessel function, see [Definition](/decl/New.IsBesselFunction/) in [the chapter on Bessel subgroups](/chapter/bessel-bruhat/#bessel-functions-and-the-schur-bound).

### Reproduction by the kernel

Let $\deg = d_\lambda$ be the formal degree of $l$ ([`New.HCParam.formalDegree`](/decl/New.HCParam.formalDegree/)). Under the gap condition, $e_\lambda = d_\lambda c_\lambda$ is an idempotent kernel on $G_1$: continuous, integrable, self adjoint, and $e_\lambda * e_\lambda = e_\lambda$ (`New.isIdempotentKernel_dsCoeffInFrame`, Lib/Weil/Periods/Grading.lean, with [Definition](/decl/New.IsIdempotentKernel/) from Volume 5). Convolution on the right is $(F * \psi)(y) = \int_{G_1}\psi(a^{-1})F(ya)\,da$, [`New.convolve`](/decl/New.convolve/).

**Theorem (Reproduction).** Under the hypotheses of the lemma, $W_x * e_\lambda = W_x$.

Lean: `New.DiscreteSeries.convolve_besselAverage` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* The product formula of the kernel gives $\int_{G_1} d_\lambda c_\lambda(a^{-1})c_\lambda(ga)\,da = c_\lambda(g)$ for every $g$. Apply it with $g = x^{-1}sy$, multiply by $\pi(s)^{-1}v$, and integrate over $s$. Then exchange the integrals over $a$ and $s$. The exchange needs the double integral to converge absolutely. The inner integral over $s$ is bounded by $16^{9r^2}\operatorname{vol}_x$ uniformly in $ya$, and $c_\lambda$ is integrable on $G_1$. $\square$

This is the property that makes $W_x$ belong to the discrete series. The Schur bound of [a later section](/chapter/bessel-real-place/#schur-bounds-and-orthonormality) uses it through [Lemma](/decl/New.IsIdempotentKernel.enorm_integral_convolve_sq_le/).

### The norm is a period

**Lemma.** For $\|v\| = 1$ and every $y$, $\|W_x(y)\| \leq \int_R |c_\lambda(x^{-1}sy)|\,ds$. Under the hypotheses of the lemma, $W_x$ is integrable on $\mathsf U\backslash G_1$.

Lean: `New.DiscreteSeries.enorm_besselAverage_le`, `New.DiscreteSeries.integrable_besselAverage` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* The first claim is the triangle inequality for the integral with item 2 of the lemma. For the second, integrate the first bound over $\mathsf U\backslash G_1$ and unfold: the result is $\int_{G_1}|c_\lambda|$, which is finite since $e_\lambda$ is integrable and $d_\lambda > 0$. $\square$

**Theorem (Norm as a period).** Under the hypotheses of the lemma,
$$d_\lambda \int_{\mathsf U\backslash G_1}\|W_x(y)\|^2\,dy = \langle v, W_x(x)\rangle.$$

Lean: `New.DiscreteSeries.formalDegree_mul_integral_norm_sq_besselAverage` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Write $\|W_x(y)\|^2 = \langle W_x(y), W_x(y)\rangle$ and insert the integral over $R$ for the second factor. The term at $s$ is $c_\lambda(x^{-1}sy)$ times $\langle W_x(y), \pi(s)^{-1}v\rangle$. Since $\pi(s)^{-1} = \pi(s)^*$, this is $\langle \pi(s)W_x(y), v\rangle = \langle W_x(sy), v\rangle$ by the Bessel law. So the integrand depends on $sy$ only, and unfolding turns the double integral into $\int_{G_1} c_\lambda(x^{-1}g)\langle W_x(g), v\rangle\,dg$, up to complex conjugation. Substitute $g = xa$. Since $c_\lambda(a^{-1}) = \overline{c_\lambda(a)}$, the result is $d_\lambda^{-1}$ times $\langle v, (W_x * e_\lambda)(x)\rangle$. Reproduction gives $\langle v, W_x(x)\rangle$. $\square$

The value $\langle v, W_x(x)\rangle = \int_R c_\lambda(x^{-1}sx)\langle v, \pi(s)^{-1}v\rangle\,ds$ is a period of $c_\lambda$ over the conjugate $x^{-1}Rx$, twisted by the matrix coefficient of $\pi$. So $W_x \neq 0$ if and only if this period is not zero. The next section finds a point $x$ at which the period is large.

### Bessel systems of discrete series type

The last section of the chapter produces a Bessel system whose full function is a multiple of such an average. The structure that records this is the following.

**Definition.** A Bessel system $B$ *has type* $(l, \kappa_w)$ for a parameter $l$ and a weight $\kappa_w$ if:

1. $\deg B$ is the value of Weyl's dimension polynomial at $l$;
2. after an invertible change of coordinates, $\rho$ is the transposed Schur representation of weight $\kappa_w$ at $g^T$;
3. $\int_{U(\operatorname{diag}\varepsilon)} e_l(a)\,W(y\,p a p^{-1})\,da = W(y)$ for each coordinate of $W$;
4. there are $c \in \mathbb{R}$, $x \in G_1$ and $v$ such that for every $y$ the integrand $\Phi_y$ is integrable and $W(y) = c\,W_x(y)$.

Lean: `New.Filling.IsDiscreteSeriesBessel` (New/Spanning/Bessel/LargeFunction.lean).

Item 1 identifies $\deg B$ with $d_\lambda$: under a large gap the formal degree equals Weyl's dimension polynomial [`New.weylDimensionPoly`](/decl/New.weylDimensionPoly/) at $l$ (`New.Orbital.formalDegree_eq_weylDimensionPoly`, Lib/DiscreteSeries/Character/FormalDegree.lean). Item 3 is reproduction, written with the kernel $e_l$ = [`New.HCParam.dsKernel`](/decl/New.HCParam.dsKernel/) on $U(\operatorname{diag}\varepsilon)$ instead of $e_\lambda$ on $G_1$. Item 4 keeps the integrability inside the structure, so a user of the structure does not meet the junk value of the Bochner integral.

**Remark (Formalization).** The structure is in the namespace `New.Filling`, but it is declared in LargeFunction.lean, before `New.DiscreteSeries`. It is the conclusion of `New.Data.exists_besselSystem`, and the file Unfolding/PoincareSeries.lean of [the chapter on Poincaré series](/chapter/poincare-series/) uses it.
