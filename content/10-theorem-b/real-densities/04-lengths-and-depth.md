---
title: Lengths and depth
lean:
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Frames/RealShells.lean
decls:
  - New.Floors.lengthAt
  - New.Floors.inducedLength
  - New.Floors.realDepth
  - New.Floors.lengthAt_smul
  - New.Floors.inducedLength_sq_lt_iff
  - New.Floors.realDepth_lt_iff
  - New.Floors.RealPlaceSizes.mem_stableProducts_iff
  - New.Floors.RealPlaceSizes.stableProducts_eq
  - New.Floors.RealPlaceSizes.depth_eq
  - New.Floors.RealPlaceSizes.lengthLeAt_of_lengthAt_le
  - New.Floors.RealPlaceSizes.lengthAt_le_of_lengthLeAt
  - New.Floors.IsCutBessel
  - New.Floors.IsCutBessel.isCut_complexData
  - New.Floors.IsCutBessel.mem_ofSize_gauge
  - New.Floors.IsCutBessel.isHead_gauge_iff
  - New.Floors.IsCutBessel.norm_leadingMinor_le_of_besselOrbitalIntegral_ne_zero
  - New.Floors.positionBall
  - New.Floors.IsCutBessel.exists_sq_le_realDepth
  - New.Floors.IsCutBessel.hasDeepVector_of_notMem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lengths and depth

The general machine measures how far a position $x$ is from $1$ by the depth of the frame vectors $e_a$ at two points $y$ and $yx$. The depth is the inverse volume of a set $\mathfrak d_a$ of products. At a finite place $\mathfrak d_a$ is a fractional ideal. At $\mathbb C$ it is a disc, and its radius is given by a minimum of Euclidean lengths. This section computes the disc, defines the cut Bessel functions of the chapter, and proves that a remote position makes some frame vector deep.

### Lengths at a point

**Definition.** For $g \in G_1$ and a vector $y$, the length of $y$ at $g$ is $|y|_g = |g^{-1} y|$, the Euclidean length of $g^{-1} y$. For $l \in \mathbb N$, the induced length $|y|_{g,l}$ is the infimum of $|y'|_g$ over the vectors $y'$ congruent to $y$ modulo the span of the $e_b$ with $b < l$.

Lean: `New.Floors.lengthAt`, `New.Floors.inducedLength` (New/Spanning/Frames/RealPlaceGauge.lean).

Two vectors are congruent below $l$ (Lean: `New.Floors.CongrBelow`, New/Spanning/Frames/Lengths.lean) if they agree at every index of level at least $l$. The indices of level below $l$ are the $e_b$ with $b < l$. A vector is orthogonal below $l$ (Lean: `New.Floors.IsOrthogonalBelow`) if its coordinates at the $e^*_b$, $b < l$, vanish. The coordinate at $e^*_b$ is the product $\langle e_b, \omega \rangle$.

**Lemma.** For every $c \in \mathbb C$, $|c y|_g = |c|\, |y|_g$. The inequality $|y|_{g,l}^2 < t$ holds if and only if some $y'$ congruent to $y$ below $l$ has $|y'|_g^2 < t$.

Lean: `New.Floors.lengthAt_smul`, `New.Floors.inducedLength_sq_lt_iff` (New/Spanning/Frames/RealPlaceGauge.lean).

The second statement holds because the infimum of a set of nonnegative numbers is below $\sqrt t$ exactly when one of the numbers is.

### The depth of a frame vector

**Definition (Depth at $\mathbb C$).** For $a < \varrho$ and $g, g' \in G_1$, the depth of $e_a$ at $g$ and $g'$ is

$$d_a(g, g') = \inf_\zeta \bigl(|\zeta|_{g,a}^2 + |\zeta|_{g',a}^2\bigr),$$

where $\zeta$ runs over the vectors orthogonal below $a$ with $\langle e_a, \zeta \rangle = 1$.

Lean: `New.Floors.realDepth` (New/Spanning/Frames/RealPlaceGauge.lean).

The vector $e^*_a$ is admissible, so the infimum runs over a nonempty set. All terms are nonnegative, so $d_a(g, g') \geq 0$.

**Lemma.** $d_a(g, g') < t$ if and only if there are vectors $\zeta$, $\zeta'$ with $\zeta$ orthogonal below $a$, $\zeta(e^*_a) = 1$, $\zeta'$ congruent to $\zeta$ below $a$, and $|\zeta|_g^2 + |\zeta'|_{g'}^2 < t$.

Lean: `New.Floors.realDepth_lt_iff` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Suppose $d_a(g, g') < t$. Pick an admissible $\zeta$ with $|\zeta|_{g,a}^2 + |\zeta|_{g',a}^2 < t$. The last lemma gives a lift $\zeta_1$ at $g$ with $|\zeta_1|_g^2 < t - |\zeta|_{g',a}^2$, and then a lift $\zeta_2$ at $g'$ with $|\zeta_2|_{g'}^2 < t - |\zeta_1|_g^2$. The vector $\zeta_1$ is again orthogonal below $a$ with coordinate $1$ at $e^*_a$, since a congruence below $a$ does not change the coordinates at the $e^*_b$. Take $\zeta = \zeta_1$ and $\zeta' = \zeta_2$. The converse uses the last lemma twice in the other direction. $\square$

Recall from [the chapter on frames](/chapter/local-frames/) the general definitions. A vector $\omega$ is stable at $g$ and $g'$ below $l$ if it is orthogonal below $l$ and $(g^{-1}\omega, g'^{-1}\omega')$ is a close pair for some $\omega'$ congruent to $\omega$ below $l$. The set $\mathfrak d_a(x, y)$ is the set of products $\omega(e^*_a)$ of the vectors stable at $x$ and $xy$ below $a$. The depth is $\operatorname{vol}(\mathfrak d_a(x, y))^{-1}$, in $[0, \infty]$.

Lean: `New.Floors.PlaceData.IsStable`, `New.Floors.PlaceData.stableProducts`, `New.Floors.PlaceData.depth` (New/Spanning/Frames/Levels.lean).

**Lemma.** Assume the sizes at a real place. At $\mathbb C$, $c \in \mathfrak d_a(x, y)$ if and only if $c = \omega(e^*_a)$ for a vector $\omega$ orthogonal below $a$ that has a lift $\omega'$ congruent below $a$ with $|\omega|_x^2 + |\omega'|_{xy}^2 < 1$.

Lean: `New.Floors.RealPlaceSizes.mem_stableProducts_iff` (New/Spanning/Frames/RealPlaceGauge.lean).

This is the definition with the close pairs of $\mathbb C$.

**Theorem (The disc of products).** Assume the sizes at a real place. For $a < \varrho$ and $x, y \in G_1$,

$$\mathfrak d_a(x, y) = \{c \in \mathbb C : |c|^2\, d_a(x, xy) < 1\}.$$

Lean: `New.Floors.RealPlaceSizes.stableProducts_eq` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* For $c = 0$ both sides contain $c$: take $\omega = \omega' = 0$. For $c \neq 0$, write $\omega = c\zeta$ and $\omega' = c\zeta'$. Then $\omega(e^*_a) = c$ exactly when $\zeta(e^*_a) = 1$, and the condition $|\omega|_x^2 + |\omega'|_{xy}^2 < 1$ is $|\zeta|_x^2 + |\zeta'|_{xy}^2 < 1/|c|^2$. By the lemma on $d_a$, such $\zeta$, $\zeta'$ exist exactly when $d_a(x, xy) < 1/|c|^2$. $\square$

**Corollary.** Assume the sizes at a real place. Then $\operatorname{depth}_a(x, y) = d_a(x, xy)/\pi$.

Lean: `New.Floors.RealPlaceSizes.depth_eq` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Let $d = d_a(x, xy)$. If $d > 0$, the set is the open disc of radius $d^{-1/2}$, of area $\pi/d$, and its inverse area is $d/\pi$. If $d = 0$, the set is all of $\mathbb C$, of infinite area. Its inverse area is $0$, and $\mathrm{ofReal}(0/\pi) = 0$. $\square$

**Remark (Formalization).** The general depth lies in $[0, \infty]$ and is the inverse of a volume. The case $d = 0$ gives an infinite volume, whose inverse is $0$ in $[0, \infty]$. This agrees with the value $d/\pi$, so the corollary holds without a case split in its statement. The source states $d_a$ in $\mathbb R$ as an infimum; `Real.iInf` of a set bounded below by $0$ is the true infimum here.

### Sizes and lengths

The gauge of [Section 3](/chapter/real-densities/#the-gauge-at-the-complex-place) has sizes, not lengths. The general notion `LengthLeAt g i y` says that $g^{-1} y$ has size $i$, that is, every entry of $g^{-1} y$ has modulus at most $L^i$ (Lean: `New.Floors.Size.LengthLeAt`, New/Spanning/Frames/Lengths.lean).

**Lemma.** Assume the sizes at a real place and $\rho \leq L$.

1. If $|y|_g \leq L^i$, then $y$ has size $i$ at $g$ in the gauge of scale $L$.
2. If $y$ has size $i$ at $g$, then $|y|_g \leq \sqrt r\, L^i$.

Lean: `New.Floors.RealPlaceSizes.lengthLeAt_of_lengthAt_le`, `New.Floors.RealPlaceSizes.lengthAt_le_of_lengthLeAt` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* An entry is at most the Euclidean length, and a vector of $r$ entries of modulus at most $L^i$ has length at most $\sqrt r L^i$. $\square$

### Cut Bessel functions

The rest of the chapter works with one kind of Bessel function: the cut of a normalised Bessel function of irreducible type. [The chapter on the Bessel functions at the real place](/chapter/bessel-real-place/#decay-and-the-cut) builds such pairs.

**Definition (Cut Bessel function).** Let $\mathrm{rep}$ be a representation of $U(\kappa)$ on $\mathbb C^I$, and let $F$, $F_0 : G_1 \to \mathbb C^I$ be continuous. Then $F$ is a cut Bessel function for $(\mathrm{rep}, \rho, s, b, F_0, f)$ if:

1. $(F_0, F)$ is a cut pair with base $b$ and decay rate $f$, in the sense of [the chapter on the Bessel functions at the real place](/chapter/bessel-real-place/#decay-and-the-cut);
2. $\rho$, $s$ and $b$ satisfy the sizes at a real place;
3. $\mathrm{rep}$ is irreducible in the sense that every matrix that commutes with all $\mathrm{rep}(h)$ is scalar.

Lean: `New.Floors.IsCutBessel` (New/Spanning/Frames/RealShells.lean).

By the cut pair, $F$ is a Bessel function of type $\mathrm{rep}$, $F$ vanishes where the Bessel length exceeds $b^{6n+2} = \rho$, and the $L^2$ distance of $F$ and $F_0$ is at most $b^{-r^3 f} \sqrt{\operatorname{card} I}$.

**Lemma.** A cut Bessel function $F$ is cut for the place datum at $\mathbb C$: it is a Bessel function of frequency $1$, and $F(x) \neq 0$ implies $ux$ lies in the box $\|ux\| \leq \rho$ for some $u \in \mathsf U$.

Lean: `New.Floors.IsCutBessel.isCut_complexData` (New/Spanning/Frames/RealShells.lean).

*Proof.* If $F(x) \neq 0$, the Bessel length of $x$ is at most $\rho$. The result of [the chapter on the Bessel functions at the real place](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length) on the length gives $u \in \mathsf U$ with $\|ux\| \leq \rho$ (Lean: `New.RealPlace.exists_norm_le_of_besselLength_le`). $\square$

**Lemma.** For the gauge of scale $L \geq \rho$, a number $z$ has size $i$ if and only if $|z| \leq L^i$. A list $p$ is a head of length $j$ if and only if $|p_0 \cdots p_{l-1}|^{-1} \leq L$ for every $l \leq j$.

Lean: `New.Floors.IsCutBessel.mem_ofSize_gauge`, `New.Floors.IsCutBessel.isHead_gauge_iff` (New/Spanning/Frames/RealShells.lean).

The general head condition asks that the inverses of the products have size $1$ (Lean: `New.Floors.Size.IsHead`, New/Spanning/Frames/Lengths.lean).

**Theorem.** Let $F$ be a cut Bessel function, and suppose the orbital integral $\int F(y) \otimes F(\gamma^{-1} y)^*\, dy$ is not zero. Then every leading minor of the matrix $(h(f_a, \gamma f_b))_{a,b}$ of the frame vectors has modulus at most $\rho^{9n}$.

Lean: `New.Floors.IsCutBessel.norm_leadingMinor_le_of_besselOrbitalIntegral_ne_zero` (New/Spanning/Frames/RealShells.lean).

The general form of this theorem is in [the chapter on frames](/chapter/local-frames/) (Lean: `New.Floors.Gauge.leadingMinor_mem_ofSize_of_besselOrbitalIntegral_ne_zero`, New/Spanning/Frames/Densities.lean). The cut gives the required near points.

### Remote positions are deep

**Definition.** The position ball at scale $T$ is the set of $x \in G_1$ such that every entry of $x - 1$ has modulus at most $T^{99n}$.

Lean: `New.Floors.positionBall` (New/Spanning/Frames/RealShells.lean).

Fix $j \leq \varrho$ and lists $p$, $q$. A point $y$ is active at the position $x$ if $\langle F(y), F(yx) \rangle \neq 0$ and the points $w_p^{-1} y$ and $w_q^{-1} yx$ are near at $j$. Here $w_p$ is the Weyl element of $p$. The general definition is `New.Floors.PlaceData.IsActive` (New/Spanning/Frames/Densities.lean).

**Theorem.** Let $F$ be a cut Bessel function, $j \leq \varrho$, and $p$, $q$ heads of length $j$ for the gauge of scale $L \geq \rho$. Let $T \geq L^{11n}$ and let $x$ be outside the position ball at scale $T$. If $y$ is active at $x$, then some $a$ with $j \leq a < \varrho$ has $d_a(y, yx) \geq T^2$.

Lean: `New.Floors.IsCutBessel.exists_sq_le_realDepth` (New/Spanning/Frames/RealShells.lean).

*Proof.* Suppose $d_a(y, yx) < T^2$ for every $a \geq j$. Let $\Gamma$ be the gauge of scale $T$. The cut gives $u, v \in \mathsf U$ with $uy$ and $vyx$ in the box. Their entries have modulus at most $\rho \leq T$, so the difference $vyx - uy$ has size $2$ for $\Gamma$. Since $|T^{-1}|^2 d_a(y, yx) < 1$, the disc theorem puts $T^{-1}$ into $\mathfrak d_a(y, x)$ for every $a \geq j$, and $T$ has size $1$ for $\Gamma$. The numbers of size $10n$ for the gauge of scale $L$ have modulus at most $L^{10n} \leq T$, so they have size $1$ for $\Gamma$. The general theorem of [the chapter on frames](/chapter/local-frames/) (Lean: `New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts`, New/Spanning/Frames/Depth.lean) now says that $x - 1$ has size $99n$ for $\Gamma$. So $x$ lies in the position ball at scale $T$. This is a contradiction. $\square$

The general theorem builds the units below $j$ from the heads $p$ and $q$, and it uses the units of $\mathfrak d_a$ for $a \geq j$. Each unit gives one column of $x - 1$ of bounded size.

**Corollary (Far means deep).** Under the same hypotheses, let $T^{-1} \leq \tau/2$. Then every point active at $x$ has a frame vector $e_a$, $a \geq j$, with $\operatorname{depth}_a(y, x) \geq \tau^{-2}$.

Lean: `New.Floors.IsCutBessel.hasDeepVector_of_notMem` (New/Spanning/Frames/RealShells.lean).

*Proof.* Take $a$ from the theorem. Then $\tau^{-2} \leq (2T^{-1})^{-2} = T^2/4 \leq d_a(y, yx)/\pi$, since $\pi \leq 4$. The corollary on the depth gives $\operatorname{depth}_a(y, x) = d_a(y, yx)/\pi$. $\square$

In Lean the conclusion is `HasDeepVector j p q F x (ofReal τ ^ 2)⁻¹` (Lean: `New.Floors.PlaceData.HasDeepVector`, New/Spanning/Frames/Densities.lean). This is the input for the shells of [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells).

**Example.** This example lies outside the sizes, which ask for $\varrho \geq 10^8$. Take $\varrho = 1$, so there is one hyperbolic pair $e_0$, $e^*_0$, and take $g = g' = 1$. The admissible $\zeta$ are the vectors with $\zeta(e^*_0) = 1$. There is no congruence below $0$, so $d_0(1, 1) = \inf 2|\zeta|^2 = 2$, attained at $\zeta = e^*_0$. The disc $\mathfrak d_0(1, 1)$ is $\{|c|^2 < 1/2\}$, of area $\pi/2$, and the depth is $2/\pi$. If $g = g' = \operatorname{diag}(t, 1, \dots, 1, t^{-1})$ is the diagonal element with $t$ at $e_0$ and $t^{-1}$ at $e^*_0$, then $|e^*_0|_g = t$. The depth is $2t^2/\pi$, which grows as $t \to \infty$. Large depth means that every dual vector of $e_0$ is long at both points.
