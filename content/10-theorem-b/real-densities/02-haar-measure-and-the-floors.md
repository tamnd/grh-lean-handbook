---
title: Haar measure and the floors
lean:
  - New/Spanning/Frames/RealPlaceGauge.lean
decls:
  - New.Floors.lintegral_heisenbergMeasure_complex
  - New.Floors.dualColumnGaussian
  - New.Floors.lintegral_dualColumnGaussian_ascConv
  - New.Floors.dualColumnGaussian_inv
  - New.Floors.lintegral_dualColumnGaussian_inv_besselHaar
  - New.Floors.ascConv_heisenbergMeasure_eq_besselHaar
  - New.Floors.RealPlaceSizes.complexData
  - New.Floors.RealPlaceSizes.haarRatio
  - New.Floors.RealPlaceSizes.groupMeasure_eq_haarRatio_smul
  - New.Floors.RealPlaceSizes.leGramFibre_mconv_floorMeasure
  - New.Floors.RealPlaceSizes.leGramFibre_partialGroupMeasure
  - New.Floors.RealPlaceSizes.inv_groupMeasure_le
  - New.Floors.RealPlaceSizes.haarRatio_le
  - New.Floors.RealPlaceSizes.lintegral_quotientMeasureFrom_eq_haarRatio_mul
  - New.Floors.RealPlaceSizes.haarRatio_ne_zero_and_groupMeasure_eq_smul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Haar measure and the floors

The general machine of [the chapter on frames](/chapter/local-frames/) integrates over $G_1$ with a measure $\mathsf M$ that is built floor by floor. This section builds the place datum at $\mathbb C$ and compares $\mathsf M$ with Haar measure. The result is that $\mathsf M = \lambda\, dg$ for a number $\lambda$ with $0 < \lambda < \infty$ and $\lambda \leq \operatorname{vol} U(r)/\operatorname{vol} U(k)$. All later bounds carry the factor $\lambda$, and the normalising constant of the forms removes it.

### The measures of the floors

Recall the measures of a place datum from [the chapter on frames](/chapter/local-frames/). The Heisenberg group of floor $a < \varrho$ carries a measure $\eta_a$, and $\eta_a$ is the point mass at $1$ for $a \geq \varrho$. The floor $l$ carries a measure $\theta_l$: for $l < \varrho$ it is the law of the inverse Weyl elements of floor $l$ convolved with $\eta_l$; for $l = \varrho$ it is the field `topFloorMeasure` of the datum; for $l = n$ it is the field `measureH`; above $n$ it is the point mass at $1$. Then

$$\mathsf M = (\eta_{\varrho+1} * \theta_{\varrho+1}) * \cdots * (\eta_0 * \theta_0), \qquad \mathsf m_j = (\eta_{j-1} * \theta_{j-1}) * \cdots * (\eta_0 * \theta_0),$$

and $\theta_{\varrho + 1} * \cdots * \theta_0$ is the measure `quotientMeasureFrom 0`, which stands for integration over $\mathsf U \backslash G_1$. Lean: `New.Floors.PlaceData.floorMeasure`, `New.Floors.PlaceData.groupMeasure`, `New.Floors.PlaceData.partialGroupMeasure` (New/Spanning/Frames/Levels.lean).

At the place $\mathbb C$ the Heisenberg measure has an explicit form. The Heisenberg element of floor $a$ with vector $v$ and skew parameter $\beta$ sends $e^*_a$ to $e^*_a + v + (\beta - \tfrac12 h(v, v)) e_a$, where $v$ lies in the span of the basis vectors of floor above $a$.

**Lemma.** Let $a < \varrho$ and let $f \geq 0$ be measurable on $G_1$. Then $\int f\, d\eta_a$ is the Lebesgue integral of $f(n(v, ti))$ over the vectors $v$ of the floors above $a$ and $t \in \mathbb R$, where $n(v, \beta)$ is the Heisenberg element of floor $a$.

Lean: `New.Floors.lintegral_heisenbergMeasure_complex` (New/Spanning/Frames/RealPlaceGauge.lean).

### The place datum at the complex place

**Definition (The place datum at $\mathbb C$).** Assume the sizes at a real place for $\rho$, $s$, $b$. The place datum at $\mathbb C$ has the index set $\iota = \{i \in \kappa : i \neq k_0\}$, the form `middleGram 1`, the block parameter $m = 0$, and these fields:

1. the hyperbolic basis is the basis `complexBasis` of the complex place;
2. `levelUnit` $= 1$;
3. `closePairs` is the set of pairs $(\omega_1, \omega_2)$ of vectors with $|\omega_1|^2 + |\omega_2|^2 < 1$, for the Euclidean length;
4. `boxSet` is the set of $x \in G_1$ with operator norm $\|x\| \leq \rho$;
5. `positions` is all of $G_1$;
6. `measureH` is the Haar probability measure of $U(\kappa)$, carried into $G_1$;
7. `topFloorMeasure` is the law of floor $\varrho$ of [the complex place](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place), convolved with `measureH`.

Lean: `New.Floors.RealPlaceSizes.complexData` (New/Spanning/Frames/RealPlaceGauge.lean).

The law of floor $\varrho$ is the image of $S_k((|c|^2 - 1)^+)\, dc$ under $c \mapsto w_\varrho(c)^{-1}$, where $w_\varrho(c)$ is the boost at $c/\min(1, |c|)$ for $c \neq 0$. The other fields of the structure are proofs: the box is compact, the close pairs form an open set with compact closure that contains $(0, 0)$, `measureH` is invariant under $U(\kappa)$ and has mass at most $1$, and the top floor measure is carried by the floor group and has the measure of the quadric through $z$ as its image. The last proof uses the law of floor $\varrho$ on the hyperboloid of [the complex place](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place), which needs $k > 1$. The sizes give $k \geq n^7 > 1$.

The index set $\iota$ has $k - 1$ elements. With $m = 0$ the block rank is $2$, so the free index set has $k - 1 - 4 = k - 5$ elements. The span $X'$ of these free orthonormal vectors carries the analysis of the next two sections.

### Lebesgue measure on the unipotent group

The first comparison is on the unipotent group $\mathsf U$ of the frame. [Volume 5](/chapter/bessel-bruhat/#haar-measures-on-the-unipotent-groups) gives $\mathsf U$ the Haar measure `besselHaar`: Lebesgue measure in the free entries of the rows $e_a$, which are complex, and in the imaginary parts of the entries at $(e_a, e^*_a)$, which are real.

**Definition.** For $l \in \mathbb N$ and $g \in G_1$, let $w_b = g\, e^*_b$ be the column $e^*_b$ of $g$, and let

$$\gamma_l(g) = \exp\Bigl(-\pi \sum_{b < \min(l, \varrho)} \Bigl(\sum_{i :\, \mathrm{floor}(i) > b} |w_b(i)|^2 + (\operatorname{Im} w_b(e_b))^2\Bigr)\Bigr).$$

Lean: `New.Floors.dualColumnGaussian` (New/Spanning/Frames/RealPlaceGauge.lean).

**Lemma.** Let $l \leq \varrho$. Then $\int \gamma_l\, d(\eta_0 * \cdots * \eta_{l-1}) = 1$.

Lean: `New.Floors.lintegral_dualColumnGaussian_ascConv` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Induction on $l$. For $l = 0$ the measure is the point mass at $1$ and $\gamma_0 = 1$. For the step from $a$ to $a + 1$, write an element of $\eta_0 * \cdots * \eta_a$ as $\nu\, n(v, \beta)$ with $\nu$ in the product of the lower Heisenberg groups. The element $n(v, \beta)$ puts $v$ and $\operatorname{Im} \beta$ into the free entries of the column $e^*_a$ and fixes the columns $e^*_b$ with $b < a$. The element $\nu$ keeps the free entries of the column $e^*_a$. So $\gamma_{a+1}(\nu\, n(v, \beta)) = \exp(-\pi(|v|^2 + (\operatorname{Im} \beta)^2))\, \gamma_a(\nu)$. By the lemma on $\eta_a$ and Fubini, the integral is $\int e^{-\pi(|v|^2 + t^2)}\, dv\, dt$ times the integral for $a$. The Gaussian integral is $1$, and the induction hypothesis gives $1$. $\square$

**Lemma.** For $y \in G_1$, $\gamma_\varrho(y^{-1})$ is the standard Gaussian $\exp(-\pi(\sum |y_{e_a, j}|^2 + \sum_a (\operatorname{Im} y_{e_a, e^*_a})^2))$, where the first sum runs over the free entries of the rows $e_a$. Hence $\int_{\mathsf U} \gamma_\varrho(y^{-1})\, d\mathrm{besselHaar}(y) = 1$.

Lean: `New.Floors.dualColumnGaussian_inv`, `New.Floors.lintegral_dualColumnGaussian_inv_besselHaar` (New/Spanning/Frames/RealPlaceGauge.lean).

The first statement holds because $y^{-1} = J_1 y^* J_1$: the column $e^*_a$ of $y^{-1}$ is the row $e_a$ of $y$ up to conjugation, signs and the exchange of $e_b$ with $e^*_b$. The second follows because the free entries carry `besselHaar` to Lebesgue measure.

**Theorem.** The convolution $\eta_0 * \cdots * \eta_{\varrho - 1}$ of the Heisenberg measures of the floors is the Haar measure `besselHaar` of $\mathsf U$, carried into $G_1$ by the inclusion.

Lean: `New.Floors.ascConv_heisenbergMeasure_eq_besselHaar` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Write $\eta = \eta_0 * \cdots * \eta_{\varrho - 1}$ and $du$ for `besselHaar`. By [Volume 5](/chapter/bessel-bruhat/#haar-measures-on-the-unipotent-groups), $\eta$ is invariant under left and right translation by $\mathsf U$, and it is carried by $\mathsf U$ (Lean: `New.Floors.ascConv_heisenbergMeasure_invariant`). Let $f \geq 0$ be measurable. Since $\int \gamma_\varrho(y^{-1})\, du(y) = 1$ and $\eta$ is right invariant,

$$\int f\, d\eta = \int_{\mathsf U} \int_{G_1} \gamma_\varrho(y^{-1})\, f(xy)\, d\eta(x)\, du(y).$$

Exchange the integrals. For almost every $x$, $x \in \mathsf U$, and left invariance of $du$ replaces $y$ by $x^{-1} y$. This gives $\int_{G_1} \int_{\mathsf U} \gamma_\varrho(y^{-1} x)\, f(y)\, du(y)\, d\eta(x)$. Exchange again. By left invariance of $\eta$ and the first lemma, $\int \gamma_\varrho(y^{-1} x)\, d\eta(x) = 1$ for each $y \in \mathsf U$. What remains is $\int f(y)\, du(y)$. $\square$

The argument is the classical proof of the uniqueness of Haar measure by a test function with integral $1$, as in Folland, *A Course in Abstract Harmonic Analysis*, Section 2.2. Here the Gaussian fixes the constant, so the two measures are equal and not only proportional.

### The ratio of the two measures

The measure $\mathsf M$ is invariant under right translation by $G_1$ (by [the chapter on frames](/chapter/local-frames/)), and $G_1$ is unimodular. So $\mathsf M$ is a multiple of Haar measure by a number in $[0, \infty]$. The source picks that number with `choose`.

**Definition.** The ratio $\lambda \in [0, \infty]$ (Lean: `haarRatio`) is a number with $\mathsf M = \lambda\, dg$, chosen from the existence statement `New.exists_eq_smul_haar`. Here $dg$ is the Haar measure `volume` of $G_1$.

Lean: `New.Floors.RealPlaceSizes.haarRatio`, `New.Floors.RealPlaceSizes.groupMeasure_eq_haarRatio_smul` (New/Spanning/Frames/RealPlaceGauge.lean).

**Remark (Formalization).** The existence statement says: every s-finite right invariant measure is $d \cdot \mu$ for some $d$ in $[0, \infty]$. A priori the chosen number could be $0$ or $\infty$. Every later use of $\lambda$ goes through the theorem at the end of this section, which excludes both values. Since Haar measure is not zero, the number $d$ is unique, so the choice does not matter.

### Choosing the vectors in turn

The upper bound for $\lambda$ compares two descriptions of the measure of tuples with a given Gram matrix. The first is Haar measure of $G_1$. The second chooses the vectors $e_0, e^*_0, \dots, e_{\varrho-1}, e^*_{\varrho-1}, z$ one by one, as the floor measures do. The tool is the relation `LeGramFibre` of [Volume 5](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place): $\operatorname{LeGramFibre}(E, m)$ says that the law of $g \mapsto gE$ under $m$ is at most the fibre measure of the Gram map $Y \mapsto Y^* J_1 Y$ over the Gram matrix of $E$.

**Lemma.** Let $l \leq \varrho$, let $E$ be the tuple of basis vectors of the floors below $l$, and let $E'$ be $E$ with the frame vector $f_l$ of floor $l$ added. If $\operatorname{LeGramFibre}(E, m)$, then $\operatorname{LeGramFibre}(E', m * \tfrac12 \check\theta_l)$, where $\check\theta_l$ is the image of $\theta_l$ under $g \mapsto g^{-1}$.

Lean: `New.Floors.RealPlaceSizes.leGramFibre_mconv_floorMeasure` (New/Spanning/Frames/RealPlaceGauge.lean).

The proof uses that the image of $\check\theta_l$ under $g \mapsto g f_l$ is the measure on the quadric through $f_l$, and that half of this measure is at most the fibre measure of Lebesgue measure ([Volume 5](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place), the proposition on frame vectors). The factor $\tfrac12$ comes from the coordinate $h(y, y)/2$ of the fibres.

**Lemma.** Let $l \leq \varrho$. Then $\operatorname{LeGramFibre}(E_l, 4^{-l}\, \check{\mathsf m}_l)$, where $E_l$ is the tuple $(e_0, e^*_0, \dots, e_{l-1}, e^*_{l-1})$ and $\check{\mathsf m}_l$ is the image of $\mathsf m_l$ under inversion.

Lean: `New.Floors.RealPlaceSizes.leGramFibre_partialGroupMeasure` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Induction on $l$. The case $l = 0$ is the empty tuple. For the step, $4^{-(a+1)} \check{\mathsf m}_{a+1}$ is the convolution of $4^{-a}\check{\mathsf m}_a$, of $\tfrac12 \check\theta_a$ and of $\tfrac12 \eta_a$. The previous lemma adds $e_a$. The proposition on dual vectors of [Volume 5](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place) adds $e^*_a$: half the image of $\eta_a$ under $u \mapsto u e^*_a$ is at most the fibre measure. $\square$

**Proposition.** The image of $\mathsf M$ under inversion satisfies $\check{\mathsf M} \leq (\operatorname{vol} U(r)/\operatorname{vol} U(k))\, dg$.

Lean: `New.Floors.RealPlaceSizes.inv_groupMeasure_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Floors above $n$ carry point masses, and floor $n$ carries the Haar probability measure of $U(\kappa)$. So $\check{\mathsf M} = \check{\mathsf m}_\varrho * \check\theta_\varrho * dh$, with $dh$ the Haar probability measure of $U(\kappa)$ in $G_1$. Write it as $2^{2\varrho + 1}(m * dh)$ with $m = 4^{-\varrho}\check{\mathsf m}_\varrho * \tfrac12\check\theta_\varrho$. The two lemmas give $\operatorname{LeGramFibre}(E, m)$ for the tuple $E$ of the $2\varrho + 1$ basis vectors outside $X_0$. The comparison of [Volume 5](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place) for such tuples gives $m * dh \leq \operatorname{vol} U(r)/(\operatorname{vol} U(k)\, 2^{2\varrho+1})\, dg$ (Lean: `New.LeGramFibre.mconv_embedH_le`). The powers of $2$ cancel. $\square$

**Corollary.** $\lambda \leq \operatorname{vol} U(r)/\operatorname{vol} U(k)$.

Lean: `New.Floors.RealPlaceSizes.haarRatio_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Haar measure of the unimodular group $G_1$ is invariant under inversion, so $\check{\mathsf M} = \lambda\, dg$. Evaluate both sides of the proposition on the ball $B$ of operator norm at most $2$. It has finite positive Haar measure, so $\lambda\, \operatorname{vol}(B) \leq (\operatorname{vol} U(r)/\operatorname{vol} U(k)) \operatorname{vol}(B)$ can be divided by $\operatorname{vol}(B)$. $\square$

### The ratio is finite and positive

**Lemma.** Let $f \geq 0$ be measurable on $G_1$ and invariant on the left under $\mathsf U$. Then

$$\int f\, d(\theta_{\varrho+1} * \cdots * \theta_0) = \lambda \int_{\mathsf U \backslash G_1} f.$$

Lean: `New.Floors.RealPlaceSizes.lintegral_quotientMeasureFrom_eq_haarRatio_mul` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Write $\theta = \theta_{\varrho+1} * \cdots * \theta_0$. By the theorem on $\mathsf U$, $\mathsf M = du * \theta$, so $(g, u) \mapsto ug$ carries $\theta \times du$ to $\lambda\, dg$. Then $\theta$ represents the quotient of $\lambda\, dg$ by $\mathsf U$: a left $\mathsf U$-invariant function has the same law under $\theta$ and under the orbit measure of $\lambda\, dg$. The orbit measure is $\lambda$ times `besselQuotMeasure`. $\square$

**Theorem (The ratio of the measures).** Assume the sizes at a real place. Then:

1. $\lambda \neq 0$ and $\lambda \neq \infty$;
2. $\mathsf M = \lambda\, dg$;
3. for every measurable $f \geq 0$ that is invariant on the left under $\mathsf U$, $\int f\, d(\theta_{\varrho+1} * \cdots * \theta_0) = \lambda \int_{\mathsf U \backslash G_1} f$;
4. $(\operatorname{vol} U(k)/\operatorname{vol} U(r)) \cdot \lambda \leq 1$.

Lean: `New.Floors.RealPlaceSizes.haarRatio_ne_zero_and_groupMeasure_eq_smul` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Parts 2 and 3 are the definition and the lemma. Part 4 and $\lambda \neq \infty$ follow from the corollary, since $\operatorname{vol} U(r)/\operatorname{vol} U(k)$ is finite and positive. If $\lambda = 0$, then $\mathsf M = 0$. But $\mathsf M$ is not the zero measure (Lean: `New.Floors.PlaceData.partialGroupMeasure_ne_zero`). So $\lambda \neq 0$. $\square$

A last instance records that $\mathsf M$ is a Haar measure of $G_1$. The general machine asks for this in its local gains.

**Remark (Formalization).** The constant $\lambda$ is never computed. The source needs only that it is finite and positive and the upper bound of part 4. The normalising constant $c_F$ of [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells) divides by $\lambda^2$. Part 4 is the step where $\lambda$ leaves the estimates. The Haar measure $dg$ is the measure `volume` of $G_1$ of [the chapter on the discrete series](/chapter/discrete-series/#parameters-and-the-coefficient).
