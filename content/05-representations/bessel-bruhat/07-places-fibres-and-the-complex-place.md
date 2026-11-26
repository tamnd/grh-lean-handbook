---
title: Places, fibres and the complex place
lean:
  - Lib/General/Measure/QuadricDisintegration.lean
  - Lib/General/Measure/FibreMeasure.lean
  - Lib/DiscreteSeries/Bruhat/FloorMeasures.lean
  - Lib/DiscreteSeries/Bruhat/FourierKernels.lean
  - Lib/DiscreteSeries/Bruhat/FloorFibre.lean
  - Lib/DiscreteSeries/Bruhat/ComplexPlace.lean
  - Lib/DiscreteSeries/Bruhat/SphereFibres.lean
  - Lib/DiscreteSeries/Bessel/FrameFibre.lean
decls:
  - New.Floors.Place
  - New.Floors.Place.plancherel_inequality
  - New.Floors.HyperbolicBasis.isDisintegration_floorVolume
  - New.LeFibreMeasure
  - New.Floors.leFibreMeasure_frameVector
  - New.Floors.leFibreMeasure_dualVector
  - New.Floors.lintegral_eq_polar
  - New.Floors.cellDensity
  - New.Floors.cartan_decomposition
  - New.Floors.map_orbitPoint_cellLaw_top
  - New.Floors.exists_isDisintegration_le_sphereDensity
  - New.LeGramFibre.mconv_fixerHaar_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Places, fibres and the complex place

This section gives the measure theory for orbits of frames, over a general place and over $\mathbb C$.

### Places

**Definition (Place).** A *place* is a locally compact Polish topological ring $A$ with a continuous involution, an additive Haar measure $dx$ and an element $\tau$ with $\tau + \bar\tau = 1$, together with the following data:

1. a unit $\delta$ with $\bar\delta = -\delta$, and a Haar measure $\nu$ on the skew elements $\{b : \bar b = -b\}$, such that $(a, b) \mapsto \tau \delta^{-1} a + b$ carries $\nu \times \nu$ to $dx$;
2. a measurable multiplicative modulus $|\cdot|_A : A \to [0, \infty]$, invariant under $x \mapsto \bar x$ and $x \mapsto -x$, such that the image of $dx$ on $A^n$ under $x \mapsto Mx$ is $|\det M|_A^{-1} dx$ for an invertible matrix $M$;
3. a continuous additive character $\psi$ with $|\psi| = 1$;
4. a constant $c \in [0, \infty]$ and a continuous integrable $G \ge 0$ with $G(0) = 1$ whose Fourier transform $z \mapsto \int G(v) \psi(\bar v z)\, dv$ has $L^1$ norm at most $c$.

Almost every element is a unit, and $|u|_A^{-1} \le |g(u)|^2$ on units for a locally integrable $g$.

Lean: `New.Floors.Place` (Lib/General/Measure/QuadricDisintegration.lean).

**Theorem (Plancherel inequality).** Let $A$ be a place, $\eta$ a unit and $f$ measurable and integrable on $A^\iota$ for a finite set $\iota$. Then
$$\int_{A^\iota} \Bigl| \int_{A^\iota} \psi(\eta\, v^* w) f(w)\, dw \Bigr|^2 dv \le \Bigl(\frac{c}{|\eta|_A}\Bigr)^{|\iota|} \int_{A^\iota} |f|^2.$$

Lean: `New.Floors.Place.plancherel_inequality` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* Multiply the integrand by the damping factor $\prod_i G(\bar x v_i)$ for a unit $x$. For the damped integral the bound on the Fourier transform of $G$ gives the constant. As $x \to 0$ through units the factor tends to $1$, and Fatou's lemma passes the bound to the limit. $\square$

**Remark (Formalization).** The constant $c$ is a datum of the place, and the definition allows $c = \infty$. Then the inequality is empty. At $\mathbb C$ the source takes $c = \pi^2$. With $\psi(x) = \exp(x - \bar x)$ and $|\eta|_{\mathbb C} = |\eta|^2$, the Plancherel theorem on $\mathbb R^{2n}$ (Folland, *Real Analysis*, 2nd ed., Thm. 8.29) gives the constant $(\pi^2/|\eta|^2)^n$ for this pairing, so the inequality is then an equality for $f \in L^1 \cap L^2$.

The source uses this inequality to bound oscillatory kernels $\psi(\xi\, v^* J y)$ between measures that are Lebesgue measure in some coordinates and have bounded mass on boxes in the others (Lean: `New.Floors.Place.FourierSqNormLe`).

### Measures on the floors

Over a place, the Heisenberg group $\mathcal N_l$ of Section 3 carries the image measure
$$\eta_l = (dv \times \nu)\circ \nu_l^{-1}, \qquad (v, \beta) \mapsto \nu_l(v, \beta),$$
for $l < \varrho$, where $dv$ is Haar measure on the coordinates of $V_{l+1}$. For $l \ge \varrho$ the measure $\eta_l$ is the point mass at $1$ (Lean: `New.Floors.Place.heisenbergMeasure`). The source proves that $\eta_l$ is invariant under left and right translation by $\mathcal N_l$, and that it commutes with point masses of $H_{l+1}$. The convolution $\eta_0 * \cdots * \eta_{j-1}$, in ascending order, is a measure on $\mathcal N_{<j}$ (Lean: `New.Floors.ascConv`). It is carried by the product $\mathcal N_0 \cdots \mathcal N_{j-1}$.

The measure on a quadric is the second ingredient. A hyperbolic basis of $V_\varrho$ identifies each $V_b$ with a sum of hyperbolic planes and an orthonormal part. For a skew $\beta$, the measure on the quadric of index $\beta$ is carried into $V_b$ by this basis.

**Proposition.** Let $\mu$ be the Haar measure on $V_b$, extended by zero to the whole space. The measures on the quadrics of $V_b$ disintegrate $\mu$ along $x \mapsto h(x, x)$: for measurable $f \ge 0$, $\int f(h(x, x), x)\, d\mu(x) = \iint f(\delta^{-1} b, x)\, dl_b(x)\, d\nu(b)$. For continuous $f \ge 0$ of compact support, $b \mapsto \int f\, dl_b$ is finite and continuous.

Lean: `New.Floors.HyperbolicBasis.isDisintegration_floorVolume` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

### Fibre measures

A measure $l$ on $X$ is *at most the fibre measure* $d\mu/d\nu$ of $\pi : X \to B$ over $b$ if the following holds. For every lower semicontinuous $K \ge 0$ and every $C$, if $\int_{\pi^{-1}(S)} K\, d\mu \le C \nu(S)$ for all small open neighbourhoods $S$ of $b$, then $\int K\, dl \le C$.

Lean: `New.LeFibreMeasure` (Lib/General/Measure/FibreMeasure.lean).

The next two results are at the place $\mathbb C$, on $\mathbb C^n$ with the form $J_1$ of $G_1$.

**Proposition.** Let $b \le \varrho$ and let $f_b$ be the frame vector of floor $b$. Consider the map that sends $y$ to its products $h(e_i, y)$ with the basis vectors of floor below $b$, and to $\operatorname{Re} h(y, y)$. Over the value of this map at $f_b$, half the measure of the quadric $h(y, y) = h(f_b, f_b)$ in $V_b$ is at most the fibre measure of Lebesgue measure.

Lean: `New.Floors.leFibreMeasure_frameVector` (Lib/DiscreteSeries/Bruhat/FloorFibre.lean).

**Proposition.** Let $a < \varrho$. Consider the map that sends $y$ to its products with $e_a$ and with the basis vectors of floor below $a$, and to $\operatorname{Re} h(y, y)$. Over the value of this map at $e^*_a$, half the image of $\eta_a$ under $u \mapsto u e^*_a$ is at most the fibre measure of Lebesgue measure.

Lean: `New.Floors.leFibreMeasure_dualVector` (Lib/DiscreteSeries/Bruhat/FloorFibre.lean).

The fibre is the set of isotropic $y$ with $h(e_a, y) = 1$ that are orthogonal to the lower floors, and by Section 3 the map $u \mapsto u e^*_a$ is a bijection from $\mathcal N_a$ onto it. The factor $\tfrac12$ comes from the coordinate: the fibres are quotients by $d(h(y,y)/2)$. The proof first bounds the image of $d\mu\, dv$ under $(\mu, v) \mapsto e^*_a + v + \mu e_a$, with $v \in V_{a+1}$ (Lean: `New.Floors.leFibreMeasure_dualPoint`). In the coordinates $\mu = t/2 + \beta - q(v)$, with $t$ real and $\beta$ skew, this measure is $dv \times \tfrac12 dt \times \nu$.

**Remark (Formalization).** The lemma that gives this change of coordinates takes a shift $q$ with a hypothesis that $q$ is continuous. The hypothesis is named `_hq` in [FloorFibre.lean](lean:Lib/DiscreteSeries/Bruhat/FloorFibre.lean#L336) and is not used: the change of coordinates is a translation in $\mu$ for each fixed $v$, and Lebesgue measure is invariant under it for any $q$.

Let $\mathcal F$ be the frame $(e_0, \dots, e_{\varrho - 1}, z)$, and let $r = 2\varrho + k + 1$ be the dimension of the whole space. Its fixer in $G_1$ is $\mathsf U^0 H$, with the measure $ds$ that is the convolution of the measure of $\mathsf U^0$ from Section 5 with the Haar probability measure of $H$.

**Theorem.** Let $m$ be an s-finite measure on $G_1$ whose image under $g \mapsto g \mathcal F$ is at most the fibre measure of the Gram map $E \mapsto E^* J_1 E$ over the Gram matrix of $\mathcal F$. Then
$$m * ds \le \frac{\operatorname{vol} U(r)}{\operatorname{vol} U(k)\, 2^{\varrho + 1}}\, dg,$$
where $dg$ is Haar measure on $G_1$, normalised through the compact dual.

Lean: `New.LeGramFibre.mconv_fixerHaar_le` (Lib/DiscreteSeries/Bessel/FrameFibre.lean).

Here $\operatorname{vol} U(j) = \prod_{i=1}^{j} S_i(1)$, with $S_i(r) = 2\pi^i r^{i-1}/(i-1)!$. The comparison of Haar measure of $U(J_1)$ with the fibre measure of the Gram map is the local form of the Siegel mass computation (Siegel, Ann. of Math. 36 (1935)).

### The complex place

The place $\mathbb C$ has $\tau = \tfrac12$, $\delta = i/2$, $\nu$ the image of Lebesgue measure under $t \mapsto it$, modulus $|x|^2$, character $\psi = \operatorname{wave}$ and $c = \pi^2$ (Lean: `New.Floors.complexPlace`). This is the same $\operatorname{wave}$ as in the law of Bessel functions.

**Proposition (Polar coordinates).** Let $|\kappa| = k$, let $x$ be a basis vector of $\mathbb C^\kappa$, and let $g \ge 0$ be measurable. Then
$$\int_{\mathbb C^\kappa} g(\omega)\, d\omega = \int_0^\infty \frac{S_k(r)}{2} \int_{U(k)} g(h \sqrt r\, x)\, dh\, dr,$$
where $dh$ is the Haar probability measure.

Lean: `New.Floors.lintegral_eq_polar` (Lib/DiscreteSeries/Bruhat/ComplexPlace.lean).

Here $r$ is the squared radius, and $S_k(r)/2 = \pi^k r^{k-1}/(k-1)!$ is the derivative in $r$ of the volume $\pi^k r^k/k!$ of the ball.

For $|a| \ge 1$ let $w(a)$ be the boost that acts on the plane of a fixed basis vector $x$ of $X_0$ and $z$ by the matrix with rows $(\bar a, s)$ and $(-s, -a)$, where $s = \sqrt{|a|^2 - 1}$, and fixes the other basis vectors. On floor $l$, the chart $w_l(c)$ is the boost at $c/\min(1, |c|)$ for $l = \varrho$ and $c \ne 0$, and the Weyl element $w_l(c)$ of Section 4 otherwise.

**Definition.** The density of floor $l$ is
$$D_l(c) = \begin{cases} |c|^{2(k-1) + 4(\varrho - l)}, & l < \varrho, \\ S_k\bigl((|c|^2 - 1)^+\bigr), & l \ge \varrho. \end{cases}$$
The law of floor $l$ is the image of $D_l(c)\, dc$ under $c \mapsto w_l(c)^{-1}$.

Lean: `New.Floors.cellDensity` (Lib/DiscreteSeries/Bruhat/ComplexPlace.lean).

**Remark (Formalization).** For $k \ge 2$ and $|c| \le 1$ the top density is $S_k(0) = 0$, so the values of the chart on the closed unit disc do not matter. For $k = 1$ the exponent $k - 1$ is $0$, and $0^0 = 1$ gives $D_\varrho(c) = 2\pi$ on $|c| \le 1$. There the chart is the boost at $c/|c|$, or the Weyl element at $c = 0$. These values are conventions. The results on the hyperboloid below assume $k > 1$.

**Theorem (Cartan decomposition).** Let $\sigma \in H_\varrho$ be an isometry of $V_\varrho = X_0 \oplus \mathbb C z$ that fixes the lower floors, and let $c = h(z, \sigma z)$ with $|c| > 1$. Then $\sigma = \iota(k_1)\, w_\varrho(c)\, \iota(k_2)$ for some $k_1, k_2 \in U(k)$.

Lean: `New.Floors.cartan_decomposition` (Lib/DiscreteSeries/Bruhat/ComplexPlace.lean).

*Proof.* The column $\sigma z$ has $h(\sigma z, \sigma z) = -1$ and the entry $-c$ at $z$. So its part $v$ in $X_0$ has $\|v\|^2 = |c|^2 - 1$. Choose $k_1 \in U(k)$ with $k_1^{-1} v = \sqrt{|c|^2 - 1}\, x$. Then $w_\varrho(c)^{-1} \iota(k_1)^{-1} \sigma$ fixes $z$, so it lies in $\iota(U(k))$. $\square$

This is the decomposition $K A K$ of the group $U(k, 1)$ for elements outside the compact part, as in Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Thm. 7.39.

**Theorem (The hyperboloid).** Let $k > 1$. Let $\sigma$ have the law of $w_\varrho(c)^{-1} \iota(h)$, where $c$ has the law $D_\varrho(c)\, dc$ and $h$ has the Haar probability law on $U(k)$. Then the law of $\sigma^{-1} z$ is the measure on the quadric $h(v, v) = -1$ of $V_\varrho$ that disintegrates Lebesgue measure along $h$.

Lean: `New.Floors.map_orbitPoint_cellLaw_top` (Lib/DiscreteSeries/Bruhat/ComplexPlace.lean).

*Proof.* Write a point of the hyperboloid as $\sqrt{|c|^2 - 1}\, h x + c z$. Polar coordinates on $X_0$ in the variable $h$, and Lebesgue measure in $c$, give a family of measures on the quadrics $h(v, v) = \Gamma$ with density $S_k((\Gamma + |c|^2)^+)$. This family disintegrates Lebesgue measure on $V_\varrho$, and disintegrations are unique. So at $\Gamma = -1$ it is the quadric measure. The law of $\sigma^{-1} z = \iota(h)^{-1} w_\varrho(c) z$ is the same measure after $c \mapsto -c$ and $h \mapsto h^{-1}$. $\square$

This is the invariant measure of the hyperboloid $U(k,1)/U(k)$ in polar coordinates (Helgason, *Groups and Geometric Analysis*, Ch. I §5). The case $k = 1$ is excluded for the reason of the last remark. For $k = 1$ the density $S_1((\Gamma + |c|^2)^+)$ is $2\pi$ also where $\Gamma + |c|^2 < 0$, and there the point $\sqrt{0}\, h x + c z$ is not on the quadric.

**Theorem (Sphere fibres).** Let $k \ge 2$. There is an s-finite kernel $l$ from the skew numbers to $\mathbb C^k$ that disintegrates Lebesgue measure along $y \mapsto y^* y$, such that for every skew $\beta$ and every $R$
$$l_\beta\{y : |y_i| \le R \text{ for all } i\} \le S_k(k R^2).$$

Lean: `New.Floors.exists_isDisintegration_le_sphereDensity` (Lib/DiscreteSeries/Bruhat/SphereFibres.lean).

*Proof.* For $\beta = it$ the sphere of squared radius $r = 2t \ge 0$ is the orbit of $\sqrt r x$ under $U(k)$. Give it the invariant measure of mass $S_k(r)$, and the zero measure for $r < 0$. Polar coordinates show that these measures integrate to Lebesgue measure. A vector with $|y_i| \le R$ has $y^* y \le k R^2$, and $S_k$ is increasing on $[0, \infty)$ for $k \ge 1$. $\square$
