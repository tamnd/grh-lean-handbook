---
title: Depth
lean:
  - New/Spanning/Frames/Levels.lean
  - New/Spanning/Frames/Depth.lean
decls:
  - New.Floors.PlaceData.IsStable
  - New.Floors.PlaceData.stableProducts
  - New.Floors.PlaceData.depth
  - New.Floors.PlaceData.volumeExponent
  - New.Floors.PlaceData.depthWeight
  - New.Floors.PlaceData.commonVectors
  - New.Floors.PlaceData.IsCommonBound
  - New.Floors.PlaceData.depth_mul_left
  - New.Floors.PlaceData.IsCommonBound.depth_le
  - New.Floors.Gauge.floorMassLe_depth_pow
  - New.Floors.Gauge.floorsConst
  - New.Floors.Gauge.lintegral_depth_pow_section_le
  - New.Floors.Gauge.lintegral_invDepthWeight_le
  - New.Floors.Gauge.floorConst
  - New.Floors.Gauge.lintegral_heisenbergMeasure_inv_depth_le
  - New.Floors.Gauge.lintegral_depthWeight_le
  - New.Floors.Gauge.exists_unit_mem_stableProducts_of_isHead
  - New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Depth

A pair of points $x$ and $xy$ sees the vector $e_a$ in two ways. The *depth* of $e_a$ measures how far the two views disagree: it is large when few vectors of $Y^{(a)}$ look short from both points. This section proves the three facts about depth that the gains need. For a fixed position, deep vectors are rare. For a fixed vector, few translates of the position keep it shallow. A position far from $1$ has a deep vector, while a head keeps the first vectors shallow.

### Stable vectors and depth

A vector $\omega$ is *short from* $g$ and $g'$ if $(g^{-1}\omega, g'^{-1}\omega)$ is a close pair (`IsShortFrom`).

**Definition (Stable).** The class of $\omega$ in $Y^{(l)}$ is *stable* at $g$ and $g'$ if $\omega \perp e_b$ for $b < l$ and $(g^{-1}\omega, g'^{-1}\omega')$ is a close pair for some $\omega'$ that agrees with $\omega$ at all indices of level at least $l$.

Lean: `New.Floors.PlaceData.IsStable` (New/Spanning/Frames/Levels.lean).

**Definition (Stable products).** For $a < \varrho$ and $x, y \in \mathsf{G}$, the set $\mathfrak{d}_a(x, y) \subseteq A$ is the set of the coordinates $\omega(e^*_a)$, that is the products $h(e_a, \omega)$, of the vectors $\omega$ whose class in $Y^{(a)}$ is stable at $x$ and $xy$.

Lean: `New.Floors.PlaceData.stableProducts` (New/Spanning/Frames/Levels.lean).

**Definition (Depth).** The *depth* of $e_a$ at $x$ and $xy$ is $\delta_a(x, y) = \mathrm{vol}(\mathfrak{d}_a(x, y))^{-1} \in [0, \infty]$.

Lean: `New.Floors.PlaceData.depth` (New/Spanning/Frames/Levels.lean).

**Example.** For a large lattice datum at a finite place, let $x$ be near at $a + 1$. Then $\mathfrak{d}_a(x, y)$ is an ideal of the ring of integers, and the depth is the index of this ideal (`New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq`, in [the chapter on the finite places](/chapter/finite-densities/)). At the complex place, $\mathfrak{d}_a$ is a disc, and the depth is $1/\pi$ times the infimum of $|\zeta|^2$ at $x$ plus $|\zeta|^2$ at $xy$ over the duals $\zeta$ of $e_a$ (`New.Floors.RealPlaceSizes.depth_eq`, in [the chapter on the real places](/chapter/real-densities/)). So at the complex place a vector is deep when every dual of $e_a$ is long at one of the two points.

**Definition (Exponent and weight).** The exponent of the depths is $s = \#\mathrm{FreeIndex} - (3n + 1 + m)$, truncated at $0$ (`volumeExponent`). The *weight* of length $j$ is

$$\wp_j(x, y) = \prod_{a < \min(j, \varrho)}\delta_a(x, y)^{-s}.$$

Lean: `New.Floors.PlaceData.volumeExponent`, `New.Floors.PlaceData.depthWeight` (New/Spanning/Frames/Levels.lean).

A weight is small when some vector is deep. The weight will be put in front of one frame and its inverse in front of the other, so the weights must be integrable in both directions. That is the content of the integrals below.

**Lemma (Depth is invariant).** If $\xi \in R^{(a+1)}$, then $\delta_a(\xi x, y) = \delta_a(x, y)$.

Lean: `New.Floors.PlaceData.depth_mul_left` (New/Spanning/Frames/Depth.lean).

*Proof.* The element $\xi$ changes the first $a + 1$ frame vectors by combinations of earlier ones. It maps the stable vectors at $x, xy$ to the stable vectors at $\xi x, \xi xy$, and it does not change the product with $e_a$ of a vector orthogonal to the $e_b$, $b < a$. So $\mathfrak{d}_a$ does not change (`New.Floors.PlaceData.stableProducts_mul_left`). $\square$

### Common vectors

**Definition (Common vectors).** For $g, z \in \mathsf{G}$ and a matrix $v$ of $\varrho$ linear forms on $X'$, the set of *common vectors* is the set of the $\omega \in A^{\mathrm{FreeIndex}}$ with $v\omega = 0$ whose image in $V$ (by the matrix of the basis of $X'$) is short from $g$ and $gz$.

Lean: `New.Floors.PlaceData.commonVectors` (New/Spanning/Frames/Levels.lean).

**Definition (Common bound).** Let $\Lambda \in [0, \infty]$, a size $S$, and a set $W$ of vectors of $X'$. A function $\varphi \geq 0$ on $X'$ is a *common bound* for $W$ if it is measurable and, for every $u$:

1. $\mathrm{vol}\{h(u, \omega) : \omega \in W\}^{-1} \leq \varphi(u)$;
2. the set of the $c \in A$ for which every $h(cu, \omega)$, $\omega \in W$, lies in the set of the differences $M^{-1}(h(\omega_1, \omega'_1) - h(\omega_2, \omega'_2))$ of products of close pairs has volume at most $\varphi(u)$;
3. for every $j$, $\int_{\text{size}\ j}\varphi^s \leq \Lambda^{99n(j+1)}$.

Lean: `New.Floors.PlaceData.IsCommonBound` (New/Spanning/Frames/Levels.lean).

Field 8 of a gauge asks for a common bound for the common vectors of every $g \in K$, position $z$ and $v$. The common vectors are a subspace of large rank that looks the same from both points, which is step 8 of the guide.

**Lemma (Depth from a common bound).** Let $\varphi$ be a common bound for the common vectors of $g, x, v$, and let $\sigma$ map each common vector to a vector orthogonal to the $e_b$, $b < a$. Then

$$\delta_a(\sigma g, x) \leq \varphi\bigl((\sigma^{-1}e_a)_X\bigr).$$

Lean: `New.Floors.PlaceData.IsCommonBound.depth_le` (New/Spanning/Frames/Depth.lean).

*Proof.* Each common vector $\omega$, moved by $\sigma$, is stable at $\sigma g$ and $\sigma gx$, so its product with $e_a$ lies in $\mathfrak{d}_a(\sigma g, x)$. This product is $h(\sigma^{-1}e_a, \omega)$, a product with the vector $u = (\sigma^{-1}e_a)_X$. So $\mathfrak{d}_a$ contains the set of field 1, and the inverse volume of $\mathfrak{d}_a$ is at most $\varphi(u)$. $\square$

### Deep vectors are rare

**Lemma (Deep vectors are rare).** Let $x$ be a position and $a < \varrho$. Then `FloorMassLe a C` holds for the function $g \mapsto \delta_a(g, x)^s$, with $C = \Lambda^{10^4n}$. That is, for every $g$,

$$\int_{\{\sigma :\ \sigma g\ \text{near at}\ a + 1\}}\delta_a(\sigma g, x)^s\,d\theta_a(\sigma) \leq \Lambda^{10^4n}.$$

Lean: `New.Floors.Gauge.floorMassLe_depth_pow` (New/Spanning/Frames/Depth.lean).

*Proof.* Move $g$ into the box by an element of $R^{(a+1)}$, which does not change the depth. Field 8 of the gauge gives a common bound $\varphi$, and the lemma above bounds the depth by $\varphi$ of the vector $(\sigma^{-1}e_a)_X$. Push $\theta_a$ to the quadric. The near points are short, and the integral of $\varphi^s$ over the short points of the quadric is bounded by solving in one block and by field 3 of the common bound. $\square$

The source sets $\mathcal{F}_\Lambda = \Lambda^{10^6n^3}$ (`floorsConst`), the bound for all the floors of a head together: at most $n$ floors at $\Lambda^{10^6n^2}$ each.

Lean: `New.Floors.Gauge.floorsConst` (New/Spanning/Frames/Depth.lean).

**Lemma (On a section).** Let $p$ be a head of length $a + 1$, $x$ a position, $y \in K$ and $\nu \in U_{<a}$. Let $w_p$ be the Weyl element of length $a + 1$. Then

$$\int\mathbf{1}_{\text{near at}\ a+1}(z)\,\delta_a(z, x)^s\,d\eta_a(n) \leq |p_a^{-1}|^{r_a + 1/2}\cdot\Lambda^{10^6n^2},\qquad z = w_pn\nu y,$$

where $r_a = k + 1 + 2(\varrho - a - 1)$.

Lean: `New.Floors.Gauge.lintegral_depth_pow_section_le` (New/Spanning/Frames/Depth.lean).

*Proof.* The vector $z^{-1}e_a$ runs over the section $h(e_a, \cdot) = \bar p_a$ of the cone as $n$ runs over the Heisenberg group, by the definition of $w_p$. The integral over the section of the common bound is bounded by the lemma on integration over a section, and the factor $|p_a^{-1}|^{r_a+1/2}$ is the modulus of the rescaling that turns $\eta_a$ into the section measure. $\square$

**Lemma (The inverse weight).** Let $j \leq \varrho$, $p$ a head of length $j$, $x$ a position and $g$ near at $j$. Then

$$\int\wp_j(w_p\nu g, x)^{-1}\mathbf{1}_{\text{near at}\ j}(w_p\nu g)\,d\eta_{<j}(\nu) \leq \Bigl(\prod_{a < j}|p_a^{-1}|^{r_a + 1/2}\Bigr)\cdot\Lambda^{10^6n^3},$$

where $\eta_{<j}$ is the convolution of the Heisenberg measures of the floors below $j$ (`ascConv heisenbergMeasure j`).

Lean: `New.Floors.Gauge.lintegral_invDepthWeight_le` (New/Spanning/Frames/Depth.lean).

*Proof.* The inverse weight is the product of the $\delta_a^s$, $a < j$. Integrate one floor at a time, from the top of the head down, with the lemma on a section on each floor. The depth of $e_a$ does not depend on the Heisenberg elements of the floors below $a$, by the invariance lemma. The $j \leq n$ factors $\Lambda^{10^6n^2}$ give at most $\Lambda^{10^6n^3}$. $\square$

### Long coordinates force depth

The cost of floor $l$ on the position ball is

$$\mathcal{C}_l = |M|^{r_l + 1/2}\cdot c_P^{\#\mathrm{FreeIndex}}\cdot\Lambda^{4900n}\qquad(\texttt{floorConst}\ l).$$

Lean: `New.Floors.Gauge.floorConst` (New/Spanning/Frames/Depth.lean).

The set $\mathrm{cb}_l(g)$ (`closeBelow l g`) is the set of the $z$ for which $g^{-1}\nu z$ lies in the position ball for some $\nu \in U_{<l}$.

**Lemma (Long coordinates force depth).** Let $g \in K$, $a < \varrho$, and let $g^{-1}y$ lie in the position ball. Then

$$\int\mathbf{1}_{\mathrm{cb}_a(g)}(ny)\,\delta_a(g, g^{-1}ny)^{-s}\,d\eta_a(n) \leq |M|^{r_a + 1/2}\cdot\Lambda^{4600n}.$$

Lean: `New.Floors.Gauge.lintegral_heisenbergMeasure_inv_depth_le` (New/Spanning/Frames/Depth.lean).

*Proof.* The inverse depth is the volume of $\mathfrak{d}_a$. A point $ny$ in $\mathrm{cb}_a(g)$ has a lift with coordinates of size $17$ (`New.Floors.Gauge.exists_lift_of_mem_closeBelow`), and the products of the stable vectors with $e_a$ then lie in a set whose volume is bounded by field 2 of a common bound, evaluated at the vector part of $n$ divided by $M$. Integrate this bound over the vector part. The rescaling by $M$ costs $|M|^{r_a+1/2}$, and the integral of $\varphi^s$ costs a power of $\Lambda$. $\square$

**Lemma (The weight over the position ball).** Let $j \leq \varrho$, $g, y \in \mathsf{G}$, with $g$ near at $j$. Then

$$\int\mathbf{1}_{\text{position ball}}(g^{-1}\nu y)\,\wp_j(g, g^{-1}\nu y)\,d\eta_{<j}(\nu) \leq \prod_{l < j}\mathcal{C}_l.$$

Lean: `New.Floors.Gauge.lintegral_depthWeight_le` (New/Spanning/Frames/Depth.lean).

*Proof.* Integrate one floor at a time with the lemma above. The factor $c_P^{\#\mathrm{FreeIndex}}\Lambda^{300n}$ that separates $\Lambda^{4600n}$ from $\mathcal{C}_l$ covers the change from $\mathrm{cb}$ to the position ball. $\square$

### Far positions and heads

**Lemma (Heads keep the first vectors shallow).** Let $j \leq \varrho$, $p, q$ heads of length $j$, let $M^{-1}$ have size $1$, and let $x$, $xy$, $w_p^{-1}x$ and $w_q^{-1}xy$ be near at $j$. Then for every $a < j$ the set $\mathfrak{d}_a(x, y)$ contains a unit $c$ with $c^{-1}$ of size $10n$.

Lean: `New.Floors.Gauge.exists_unit_mem_stableProducts_of_isHead` (New/Spanning/Frames/Depth.lean).

*Proof.* The four nearness conditions and the heads give sizes for the frame vectors at both points (the lemma on heads). A dual of $e_a$ of bounded size at both points, multiplied by the unit of field 4 of the gauge, becomes a stable vector whose product with $e_a$ is a unit. The sizes add up to $10n$. $\square$

**Lemma (Bounded depths bound the position).** Let $\Gamma, S$ be gauges, $j \leq \varrho$, $p, q$ heads of length $j$ for $S$. If $j \neq 0$, let $M^{-1}$ have size $1$ for $S$, and let the numbers of size $10n$ for $S$ have size $1$ for $\Gamma$. Let $ux, v(xy) \in K$ for some $u, v \in \mathsf{U}$ with $M^{-1}(vxy - ux)$ of size $2$, and let $w_p^{-1}x$ and $w_q^{-1}xy$ be near at $j$. If for every $a$ with $j \leq a < \varrho$ the set $\mathfrak{d}_a(x, y)$ contains a unit with inverse of size $1$, then $M^{-1}(y - 1)$ has size $99n$. Sizes refer to $\Gamma$ unless $S$ is named.

Lean: `New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts` (New/Spanning/Frames/Depth.lean).

*Proof.* For $a < j$ the lemma on heads gives the unit in $\mathfrak{d}_a$, for $S$, and the hypothesis on $10n$ turns it into a unit of size $1$ for $\Gamma$. So every $e_a$ has a short dual for the two points modulo $M$ (`New.Floors.Gauge.hasShortDual_of_mem_stableProducts`). The lemmas on gauges that differ little, applied on all quotients, show that the lengths at $x$ and $xy$ differ little modulo $M$ on the whole space. So $M^{-1}(x^{-1}(xy) - 1) = M^{-1}(y - 1)$ is bounded (`New.Floors.Gauge.hasMatrixSize_sub_one_of_forall_stableProducts`). $\square$

The contrapositive is step 10 of the guide: a position $y$ with $M^{-1}(y - 1)$ large has a deep vector after the head. [The last section](/chapter/local-frames/#gains-and-shells) uses it in this form, through the field on deep vectors of a shell.

**Remark (Formalization).** The depth is defined as an inverse volume in $[0, \infty]$. If $\mathfrak{d}_a$ has volume $0$, the depth is $\infty$ and the weight is $0$; if $\mathfrak{d}_a$ has infinite volume, the depth is $0$. The source proves that neither case occurs, for all $x$ and $y$ (`New.Floors.PlaceData.volume_stableProducts_ne_zero_ne_top`): the set is open, contains $0$, and lies in a compact set. So the weight and its inverse are always finite and nonzero. The exponent $s$ is a natural number with truncated subtraction: if $\#\mathrm{FreeIndex} < 3n + 1 + m$, then $s = 0$ and every weight is $1$. The shells of the last section need $s \geq 9\cdot 10^7n^4$, so a reader should check that the rank of $X'$ is large enough in the place data that are used.
