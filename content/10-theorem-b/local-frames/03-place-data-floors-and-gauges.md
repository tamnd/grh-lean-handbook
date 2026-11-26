---
title: Place data, floors and gauges
lean:
  - New/Spanning/Frames/Levels.lean
  - New/Spanning/Frames/Correlations.lean
decls:
  - New.Floors.PlaceData
  - New.Floors.PlaceData.floorMeasure
  - New.Floors.PlaceData.groupMeasure
  - New.Floors.PlaceData.IsNear
  - New.Floors.PlaceData.descConv_floorMeasure_succ
  - New.Floors.PlaceData.lintegral_weylRatio_mul
  - New.Floors.PlaceData.partialGroupMeasure_mconv_dirac
  - New.Floors.PlaceData.lintegral_partialGroupMeasure_weylElem_inv_mul
  - New.Floors.PlaceData.partialCorrelation
  - New.Floors.PlaceData.IsPairingKernel
  - New.Floors.PlaceData.IsPairingKernel.partialCorrelation_eq_integral_succ
  - New.Floors.PlaceData.FloorMassLe
  - New.Floors.PlaceData.quotientMeasureFrom_isNear_le
  - New.Floors.Gauge
  - New.Floors.Gauge.leadingMinor_mem_ofSize_of_isNear
  - New.Floors.Gauge.isBalanced_of_isNear
  - New.Floors.Gauge.positionsOfSize
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Place data, floors and gauges

This section fixes the data of one place and the measures built from them. The group measure is built floor by floor. On floor $l \leq \varrho$ one chooses the frame vector $f_l$ on its quadric and an element of the Heisenberg group along it. Floor $\varrho + 1$ carries the measure of $H$. A *correlation* is then an integral over the floors from some $l$ on, and a *gauge* is a size together with a constant $\Lambda$ whose powers bound volumes.

### The data of a place

**Definition (Place data).** A *place datum* $F$ for the form $T$ consists of a basis of hyperbolic pairs and orthonormal vectors adapted to the frame, and of

1. a measure on $G^{(\varrho)}$ (`topFloorMeasure`), carried by $G^{(\varrho)}$, that $\sigma \mapsto \sigma^{-1}f_\varrho$ maps to the measure of the top quadric;
2. a measure on $H$ (`measureH`), not zero, carried by $H$ and invariant under right translation by $H$, which for every $g$ gives mass at most $1$ to the $h$ with $h g \in \mathsf{U}K$;
3. a unit $M$ (`levelUnit`) with $\bar M = M$, the *level*;
4. a set of *close pairs* of vectors, open, with $0$ in it and with compact closure;
5. a compact set $K \subseteq \mathsf{G}$ (`boxSet`), the *box*;
6. a measurable set of *positions* in $\mathsf{G}$.

The two measures are s-finite.

Lean: `New.Floors.PlaceData` (New/Spanning/Frames/Levels.lean).

In the place data that are used, the close pairs are the pairs with $|\omega_1|^2 + |\omega_2|^2 < 1$ at a real place, and the pairs with $\omega_1$ in the lattice and $\omega_2 \equiv \omega_1$ modulo $M$ at the finite places.

**Definition (Floor measures).** The measure $\theta_l$ of floor $l$ (`floorMeasure l`) is the convolution $\lambda_l \ast \eta_l$ for $l < \varrho$, where $\eta_l$ is the Haar measure of the Heisenberg group of floor $l$ and $\lambda_l$ (`weylLaw l`) is carried by the inverses of the elements that swap the lines of $e_l$ and $e^*_l$. It is the top floor measure for $l = \varrho$, the measure of $H$ for $l = \varrho + 1$, and the unit mass at $1$ for $l > \varrho + 1$.

Lean: `New.Floors.PlaceData.floorMeasure` (New/Spanning/Frames/Levels.lean).

The source writes $\mathrm{desc}(\theta, l, i) = \theta_{l+i-1}\ast\cdots\ast\theta_l$ (`descConv`). The measure $\mu_{\geq l} = \mathrm{desc}(\theta, l, \varrho + 2 - l)$ (`quotientMeasureFrom l`) stands for the invariant measure on $(\mathsf{U} \cap G^{(l)})\backslash G^{(l)}$. The measure $\mathfrak{m}_j$ (`partialGroupMeasure 0 j`) is the convolution of the $\eta_a\ast\theta_a$ for $a < j$.

**Definition (Group measure).** The *group measure* is $\mathsf{M} = (\eta_{\varrho+1}\ast\theta_{\varrho+1})\ast\cdots\ast(\eta_0\ast\theta_0)$, the convolution over all $\varrho + 2$ floors.

Lean: `New.Floors.PlaceData.groupMeasure` (New/Spanning/Frames/Levels.lean).

**Lemma (One floor down).** Let $l < \varrho$ and $i \in \mathbb{N}$. Then

$$\theta_{l+i}\ast\cdots\ast\theta_l = \bigl(\lambda_l \ast (\theta_{l+i}\ast\cdots\ast\theta_{l+1})\bigr)\ast\eta_l.$$

Lean: `New.Floors.PlaceData.descConv_floorMeasure_succ` (New/Spanning/Frames/Levels.lean).

*Proof.* By definition $\theta_l = \lambda_l\ast\eta_l$, and convolution is associative. The higher floors are carried by $G^{(l+1)}$, and each Weyl element of floor $l$ commutes with $G^{(l+1)}$. So $\lambda_l$ commutes with the convolution of the higher floors, and the identity follows by associativity. $\square$

**Lemma (Right invariance).** Let $l + i = \varrho + 2$ and $s \in G^{(l)}$. Then $\mathfrak{m}_{l, i}\ast\delta_s = \mathfrak{m}_{l, i}$, where $\mathfrak{m}_{l, i}$ is the convolution of the $\eta_a\ast\theta_a$ for $l \leq a < l + i$. In particular $\mathsf{M}$ is right invariant.

Lean: `New.Floors.PlaceData.partialGroupMeasure_mconv_dirac` (New/Spanning/Frames/Levels.lean).

*Proof.* By induction on the number $i$ of floors. For $i = 0$ the group $G^{(l)}$ is trivial. On floor $l$, write the measure as $\rho\ast\theta_l$ with $\rho = \mathfrak{m}_{l+1,\,i-1}\ast\eta_l$. An element of $R^{(l+1)}\cap G^{(l)}$ is $un$ with $u \in G^{(l+1)}$, absorbed by the induction, and $n$ in the Heisenberg group of floor $l$, absorbed by $\eta_l$. So the $\rho$-average of a test function is invariant under $R^{(l+1)}\cap G^{(l)}$ on the left, and the lemma `New.Floors.PlaceData.lintegral_floorMeasure_mul_right` moves $s$ through $\theta_l$. $\square$

**Lemma (Weyl ratio on the measure).** Let $j \leq \varrho$, let $p, q$ be sequences of units and let $\Phi \geq 0$ be measurable. Then

$$\int\Phi(w_q^{-1}w_px)\,d\mu_{\geq 0}(x) = \prod_{a < j}|p_a/q_a|^{k + 2(\varrho - a)}\int\Phi(x)\,d\mu_{\geq 0}(x).$$

Lean: `New.Floors.PlaceData.lintegral_weylRatio_mul` (New/Spanning/Frames/Levels.lean).

*Proof.* The element $w_q^{-1}w_p$ is diagonal (the lemma on the Weyl ratio), and it fixes the basis vectors of floor at least $j$. The source moves it through the floors one at a time. On floor $a < j$ it changes the measure $\theta_a$ by the factor $|p_a/q_a|^{k + 2(\varrho - a)}$, which comes from the density of $\lambda_a$ and from the conjugation of the Heisenberg group of floor $a$. $\square$

**Lemma (Weyl elements on the lower floors).** Let $\mathsf{M}$ be a Haar measure, let $j \leq \varrho + 2$, $p$ a sequence of units and $\Phi \geq 0$ measurable and left invariant under $G^{(j)}$. Then

$$\int\Phi(w_p^{-1}g)\,d\mathfrak{m}_j(g) = \int\Phi(g)\,d\mathfrak{m}_j(g).$$

Lean: `New.Floors.PlaceData.lintegral_partialGroupMeasure_weylElem_inv_mul` (New/Spanning/Frames/Levels.lean).

*Proof.* The group measure factors as $\mathsf{M} = \mathfrak{m}_{j,\,\varrho+2-j}\ast\mathfrak{m}_j$, where the first factor is carried by $G^{(j)}$ and is right invariant under $G^{(j)}$. A Haar measure is left invariant, so $\Phi(w_p^{-1}\cdot)$ and $\Phi$ have the same integral against $\mathsf{M}$. The source transfers this equality to $\mathfrak{m}_j$ with `New.Floors.PlaceData.lintegral_mul_left_eq_of_factor`, which uses the invariance of $\Phi$ under $G^{(j)}$. $\square$

### Near points and correlations

**Definition (Near).** A point $g$ is *near at $j$* if $R^{(j)}g$ meets the box $K$.

Lean: `New.Floors.PlaceData.IsNear` (New/Spanning/Frames/Levels.lean).

**Definition (Correlation from floor $j$ on).** For a kernel $k$ on $\mathsf{G}\times\mathsf{G}$, the *correlation from floor $j$ on* is

$$k_j(g, y) = \int k(xg, xy)\,d\mu_{\geq j}(x).$$

Lean: `New.Floors.PlaceData.partialCorrelation` (New/Spanning/Frames/Correlations.lean).

**Definition (Pairing kernel).** Let $j \in \mathbb{N}$ and $w \in \mathsf{G}$. A kernel $k$ is a *pairing kernel* at floor $j$ for $w$ if

1. $k$ is jointly measurable;
2. for $n, n' \in U_{<l}$, $k_{l+1}(ng, n'y) = \psi\bigl(M^{-1}(\sigma_0(wn'w^{-1}) - \sigma_0(n))\bigr)k_{l+1}(g, y)$, where $\sigma_0$ (`simpleRootSum`) is the sum of the superdiagonal entries of the frame block;
3. $wsw^{-1} = s$ for $s \in G^{(j)}$;
4. for every $l$, the integral $\int|k(xg, xy)|\,d\mu_{\geq l}(x)$ has a finite bound that does not depend on $g, y$;
5. if $k_l(g, y) \neq 0$, then $g$ is near at $l$.

Lean: `New.Floors.PlaceData.IsPairingKernel` (New/Spanning/Frames/Correlations.lean).

The rules hold for $k(g, y) = \langle W(g), W(wy)\rangle$ when $W$ is a cut Bessel function ([the section on densities](/chapter/local-frames/#densities-as-integrals-over-two-frames)).

**Lemma (Correlation, one floor up).** Let $k$ be a pairing kernel at floor $j$ for $w$ and let $l \in \mathbb{N}$. Then $\sigma \mapsto k_{l+1}(\sigma g, \sigma y)$ is $\theta_l$-integrable, and

$$k_l(g, y) = \int k_{l+1}(\sigma g, \sigma y)\,d\theta_l(\sigma).$$

Lean: `New.Floors.PlaceData.IsPairingKernel.partialCorrelation_eq_integral_succ` (New/Spanning/Frames/Correlations.lean).

*Proof.* This is Fubini's theorem for $\mu_{\geq l} = \mu_{\geq l+1}\ast\theta_l$. Rule 4 gives the integrability. $\square$

**Definition (Mass of a floor).** For $c : \mathsf{G} \to [0, \infty]$ and $K' \in [0, \infty]$, the statement `FloorMassLe j K' c` says that for every $g$,

$$\int_{\{\sigma :\ \sigma g\ \text{near at}\ j + 1\}} c(\sigma g)\,d\theta_j(\sigma) \leq K'.$$

Lean: `New.Floors.PlaceData.FloorMassLe` (New/Spanning/Frames/Correlations.lean).

**Lemma (Mass of the near points).** Let $V \in [0, \infty]$ and suppose that `FloorMassLe a V 1` holds for every $a < n$. Then for every $l$ and $c$, the $g$ with $gc$ near at $\varrho + 2$ have $\mu_{\geq l}$-mass at most $V^{n - l}$.

Lean: `New.Floors.PlaceData.quotientMeasureFrom_isNear_le` (New/Spanning/Frames/Correlations.lean).

*Proof.* By descending induction on $l$, with Tonelli's theorem on each floor: the mass of floor $a$ on the near points is at most $V$, and the floors above $a$ give the factor $V^{n - a - 1}$. The source uses the monotony of nearness in $j$ (`New.Floors.PlaceData.IsNear.anti`) to pass from one condition to the next. $\square$

### Gauges

**Definition (Gauge).** A *gauge* $\Gamma$ for the place datum $F$ is a size $A_{(\cdot)}$ together with a number $\Lambda \in [0, \infty]$ (`loss`) such that

1. each $A_{(j)}$ is compact, $2 \leq \Lambda < \infty$, $m \leq 9n$ and the constant $c_P$ of Plancherel's formula (`P.kernelBound`) is at least $1$;
2. $M$, the basis matrix, the element of trace one divided by the skew unit, and the elements of $K$ have size $1$;
3. for a close pair $(\omega_1, \omega_2)$, the vectors $\omega_1$ and $M^{-1}(\omega_1 - \omega_2)$ have size $1$;
4. if $M^{-1}$ has size $1$, then for each $i$ some unit $c$ with $c^{-1}$ of size $i + 2$ makes $(c\omega_1, c\omega_2)$ a close pair for all $\omega_1, \omega_2$ of size $i$;
5. a unit of size $j$ has modulus at most $\Lambda^j$, and $A_{(j)}$ has volume at most $\Lambda^{j+1}$;
6. there is room for two blocks of rank $2m + 2$ among the orthonormal basis vectors;
7. the volume of $A^{2m+2}$ disintegrates along the standard form into an s-finite kernel whose measures give mass at most $\Lambda^{(2m+2)(j+1)}$ to the vectors of size $j$;
8. for each $g \in K$, each position $z$ and each matrix $v$ of $\varrho$ linear forms on $X'$, the common vectors have a common bound (see [the section on depth](/chapter/local-frames/#depth)).

Lean: `New.Floors.Gauge` (New/Spanning/Frames/Correlations.lean).

The last two fields are the facts that the two later chapters prove separately at a real place and at the finite places. The others are checks of sizes.

**Lemma (Minors of near points).** Let $\Gamma$ be a gauge, $l \in \mathbb{N}$, and let $y$ and $\gamma^{-1}y$ be near at $l$. Then for $j \leq l$ the leading minor of order $j$ of the matrix $(h(f_a, \gamma f_b))_{a,b}$ has size $9n$.

Lean: `New.Floors.Gauge.leadingMinor_mem_ofSize_of_isNear` (New/Spanning/Frames/Correlations.lean).

*Proof.* Let $\xi y, \xi'\gamma^{-1}y \in K$ with $\xi, \xi' \in R^{(l)}$. The leading minors do not change under unitriangular changes of the first $l$ frame vectors, so the minor is a minor of a product of two matrices of size $1$. The lemma `New.Floors.Size.leadingMinor_mem_ofSize` gives the size $9n$. $\square$

**Lemma (Near points are balanced).** Let $g$ be near at $j$ and $a < j$. Then $e_a$ is balanced at $g$ with bound $L^5$.

Lean: `New.Floors.Gauge.isBalanced_of_isNear` (New/Spanning/Frames/Correlations.lean).

*Proof.* Let $\xi g \in K$ with $\xi \in R^{(j)}$. The vector $\xi^{-1}e_a$ is congruent to $e_a$ modulo the $e_b$, $b < a$, so it is a lift of $e_a$ in $Y^{(a)}$. Its image $g^{-1}\xi^{-1}e_a = (\xi g)^{-1}e_a$ is a column of the inverse of an element of $K$, so it has size $1 + 4 = 5$ by the lemma on inverses. The source builds the dual from $\xi^{-1}e^*_a$ and bounds it in the same way. $\square$

**Definition (Position ball).** The *position ball* of $\Gamma$ is the set of the positions $z$ for which $M^{-1}(z - 1)$ has size $1$.

Lean: `New.Floors.Gauge.positionsOfSize` (New/Spanning/Frames/Correlations.lean).

**Remark (Formalization).** The source does not form the quotient $(\mathsf{U}\cap G^{(l)})\backslash G^{(l)}$. It integrates against the measure $\mu_{\geq l}$ on the group, which is a convolution of measures on subgroups. A function that is invariant under $\mathsf{U}$ on the left then has the integral that the quotient would give. The same device appears in [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/). The rule 4 of a pairing kernel asks for a uniform bound, which holds for kernels of compact support modulo $\mathsf{U}$, and it makes every correlation an absolutely convergent integral.
