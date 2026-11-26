---
title: Gains and shells
lean:
  - New/Spanning/Frames/Gains.lean
  - New/Spanning/Frames/Shells.lean
decls:
  - New.Floors.Gauge.sq_lintegral_le_mul_lintegral
  - New.Floors.Gauge.sq_lintegral_le_weightedSquareProduct
  - New.Floors.Gauge.formMajorant_sq_le_of_floorMassLe
  - New.Floors.PlaceData.deepModulus
  - New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_le_sum_deepModulus
  - New.Floors.Gauge.pivotL1Norm_sq_le_of_deep
  - New.Floors.Gauge.formMajorant_sq_le_of_hasDeepVector
  - New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char
  - New.Floors.Gauge.partialCorrelation_mul_eq_integral_sectionPoint
  - New.Floors.Gauge.lintegral_section_le
  - New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads
  - New.Floors.PlaceData.shellNormalization
  - New.Floors.Gauge.IsShell
  - New.Floors.Gauge.IsShell.setLIntegral_le
  - New.Floors.Gauge.IsShell.setLIntegral_formMajorant_le
  - New.Floors.Gauge.IsShell.setLIntegral_le_inv_height
  - New.Floors.Gauge.lintegral_le_of_shells
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Gains and shells

At one position $x$, the majorant $\mathsf{F}^*_j(x)$ is an integral of a product of two pivot norms, one for each frame. This section first separates the two frames by a weight made of depths, so that each frame is paired with itself and [the bound for one frame](/chapter/local-frames/#one-frame) applies. Then it finds three sources of a gain: a frequency, two different heads, and a deep vector. Last, it cuts the positions into shells by their height and sums the shells.

### Separating the frames

**Theorem (Separating the frames).** Let $\mathsf{M}$ be a Haar measure, $p$ a head of length $j \leq \varrho$, and $x$ a position. Let $B, B' \geq 0$ be measurable, left invariant under $R^{(j)}$, and zero off the points near at $j$. Suppose that where $f(g) \neq 0$,

$$f(g)^2 \leq K\,\frac{B(g)}{\wp_j(g, x)}\cdot\frac{B'(w_p^{-1}g)}{\wp_j(w_p^{-1}g, x)}.$$

Then

$$\Bigl(\int f\,d\mathsf{m}_j\Bigr)^2 \leq K\,D^2\int B\,d\mu_{<j}\int B'\,d\mu_{<j},\qquad D = \Bigl(\prod_{a<j}|p_a^{-1}|^{r_a+1/2}\Bigr)\mathcal{F}_\Lambda.$$

Lean: `New.Floors.Gauge.sq_lintegral_le_mul_lintegral` (New/Spanning/Frames/Gains.lean).

*Proof.* Apply Cauchy-Schwarz with the weights crossed: $B$ at $g$ is paired with the inverse weight at $w_p^{-1}g$, and $B'$ at $w_p^{-1}g$ with the inverse weight at $g$. Then integrate each inverse weight over the unipotent group by the lemma on the inverse weight. In the first integral put $w_pg$ for $g$. In the second, $w_p^{-1}$ is the Weyl element of the head $p^*$, which is a head too. $\square$

This is step 11 of the guide. The weight $\wp_j$ is the price of separation, and the second moments $\mathsf{S}$ contain it. For the two correlations of a cut $W$ the theorem takes the form: if $f(g)^2$ is at most $K\mathcal{F}_\Lambda$ times $b_j(k_1)(g)/\wp_j(g, x)$ times $b_j(k_w)(w_p^{-1}g)/\wp_j(w_p^{-1}g, x)$, then $(\int f\,d\mathsf{m}_j)^2 \leq K\,\mathsf{Q}_j(x)$ (`sq_lintegral_le_weightedSquareProduct`).

Lean: `New.Floors.Gauge.sq_lintegral_le_weightedSquareProduct` (New/Spanning/Frames/Gains.lean).

**Theorem (No gain).** Let $W$ be cut, $p$ a head of length $j \leq \varrho$, $x$ a position, $\mathsf{M}$ a Haar measure, and `FloorMassLe j V 1`. Then $\mathsf{F}^*_j(x)^2 \leq V^2\,\mathsf{Q}_j(x)$.

Lean: `New.Floors.Gauge.formMajorant_sq_le_of_floorMassLe` (New/Spanning/Frames/Gains.lean).

*Proof.* Cauchy-Schwarz on floor $j$ for each of the two pivot norms, then the separation. $\square$

### A deep vector

**Definition (Deep modulus).** For a kernel $k$, a depth $D$ and $a < \varrho$, the *deep modulus* at $y$ is $|c_{a+1}(k)(y, yx)|$ if $\delta_a(y, x) \geq D$, and $0$ otherwise.

Lean: `New.Floors.PlaceData.deepModulus` (New/Spanning/Frames/Gains.lean).

**Lemma (The cut at the first deep vector).** Let $k$ be a pairing kernel, and suppose that for each $\sigma \in G^{(l)}$ with $k(\sigma g, \sigma gx) \neq 0$ some $a \geq l$ has $\delta_a(\sigma g, x) \geq D$. Then

$$P_l(k)(g, gx) \leq \sum_{l \leq a < \varrho}\int\mathrm{dm}_a(\sigma g)\,d(\theta_a * \cdots * \theta_l)(\sigma).$$

Lean: `New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_le_sum_deepModulus` (New/Spanning/Frames/Gains.lean).

*Proof.* By downward induction on $l$: on floor $l$ the frame is deep at $e_l$, or its first deep vector comes later. If no floor $a \geq l$ is left, the kernel vanishes along the orbit. Each piece is an integral over floor $l$ of an integral over the floors from $l + 1$ to $a$. $\square$

**Theorem (Gain from a deep vector, one pivot).** Let $x$ be a position, $k$ a pairing kernel, and suppose that for each $\sigma \in G^{(l)}$ with $k(\sigma g, \sigma gx) \neq 0$ some $a \geq l$ has $\delta_a(\sigma g, x) \geq \varepsilon^{-1}$. Then

$$P_l(k)(g, gx)^2 \leq \varepsilon^s\,\mathcal{F}_\Lambda\,\frac{b_l(g)}{\wp_l(g, x)}.$$

Lean: `New.Floors.Gauge.pivotL1Norm_sq_le_of_deep` (New/Spanning/Frames/Gains.lean).

*Proof.* Cut the pivot norm into at most $\varrho$ pieces by the lemma above. For one piece, apply Cauchy-Schwarz against the inverse weight of length $a + 1$, whose integral over the floors is at most a power of $\Lambda$ times $\wp_l(g, x)^{-1}$ by the lemma on several floors. The gain $\varepsilon^s$ comes from $1 \leq \varepsilon\,\delta_a$, which holds where the deep modulus is not zero (`lintegral_deepModulus_sq_le`). The pieces and the powers of $\Lambda$ fit into $\mathcal{F}_\Lambda$. $\square$

**Theorem (Gain from a deep vector).** Let $W$ be cut, $p$ a head of length $j \leq \varrho$, $x$ a position, $\mathsf{M}$ a Haar measure, $V \geq 1$ with `FloorMassLe j V 1`, and let $x$ have a deep vector of depth $\sigma^{-1}$. Then

$$\mathsf{F}^*_j(x)^2 \leq \sigma^s\,V^2\,\mathsf{Q}_j(x).$$

Lean: `New.Floors.Gauge.formMajorant_sq_le_of_hasDeepVector` (New/Spanning/Frames/Gains.lean).

*Proof.* Bound the second pivot norm by Cauchy-Schwarz with the mass $V$, and the first by the gain from a deep vector on one pivot. The hypothesis of that gain holds along the whole orbit: where the second modulus is not zero, $W$ vanishes at neither translate of the two points, so both points are near at $j$ and the point is active. Then separate the frames. $\square$

### A frequency and two heads

**Theorem (Gain from a frequency).** Let $W$ be cut, $p$ a head of length $j \leq \varrho$, $x$ a position, $\mathsf{M}$ a Haar measure, and let $\psi(\eta z) = \psi(\xi z)$ for a unit $\xi$ and all $z$ of size $200n^2$. Then

$$\mathsf{F}_j\bigl(x; \psi(\eta Z_{j,j})\bigr)^2 \leq (c_P/|\xi|)^{\#\mathrm{FreeIndex}}\,\mathsf{Q}_j(x).$$

Lean: `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char` (New/Spanning/Frames/Gains.lean).

*Proof.* If the double integral is not zero, then $g$ and $w_p^{-1}g$ are near at $j$, and one element of $R^{(j)}$ moves both to bounded size. On the supports the Gram entry has size $200n^2$, so the weight is the character of frequency $\xi$. The inner integral is then a correlation times the conjugate of a Fourier transform, and Cauchy-Schwarz in $\sigma$ with the Plancherel bound on the quadric gives the factor $(c_P/|\xi|)^{\#\mathrm{FreeIndex}}$. $\square$

When the heads differ in their last entry, the gain comes from the phase of the lifts.

**Lemma (The phase of the lifts).** Let $W$ be cut, $\xi = (1/p_i - 1/q_i)/M$, and $n$ in the Heisenberg group of floor $i$. Let $y'$ be the point over $n$ of the section $h(e_i, y') = \bar p_i$. Then

$$c_{i+1}(k_w)(ng, ng') = \int\psi\bigl(-\xi\,h(y', y_\sigma)\bigr)\,c_{i+2}(k_w)(\sigma g, \sigma g')\,d\theta_{i+1}(\sigma),$$

where $y_\sigma$ is the orbit point of $\sigma$ on floor $i + 1$ and $w = w_q^{-1}w_p$ for the heads of length $i + 1$.

Lean: `New.Floors.Gauge.partialCorrelation_mul_eq_integral_sectionPoint` (New/Spanning/Frames/Gains.lean).

*Proof.* Unfold the correlation by one floor. The source moves $n$ past the floor element $\sigma$; the Bessel rules at the two points, which carry the Weyl elements of $p$ and $q$, give the character of frequency $\xi$. The next vector $y_\sigma$ is orthogonal to $e_i$ and $e^*_i$, which reduces the phase to $h(y', y_\sigma)$. $\square$

**Lemma (Plancherel on a section).** Under the same notation, with $p$ a head of length $i + 1$,

$$\int_{\{w_png\ \text{near at}\ i+1\}}\Bigl|\int\psi(-\xi\,h(y', y_\sigma))\,\varphi(\sigma)\,d\theta_{i+1}\Bigr|^2d\eta_i(n) \leq \Bigl(\frac{c_P}{|\xi|}\Bigr)^{\#\mathrm{FreeIndex}}|p_i^{-1}|^{r_i+1/2}\mathcal{F}_\Lambda\int|\varphi|^2\,d\theta_{i+1},$$

for $\varphi(\sigma) = c_{i+2}(k_w)(\sigma g, \sigma g')$.

Lean: `New.Floors.Gauge.lintegral_section_le` (New/Spanning/Frames/Gains.lean).

*Proof.* The point $y'$ runs over the section as $n$ runs over the near set, which is the setting of the lemma on integration over a section. The inner integral is a Fourier transform of $\varphi$ pushed to the quadric, at the frequency $\xi y'$, and the Plancherel bound on the quadric applies. $\square$

**Theorem (Gain from two heads).** Let $W$ be cut, $p$ a head of length $j = i + 1 \leq \varrho$, $x$ a position, $\mathsf{M}$ a Haar measure, and $\xi = (1/p_i - 1/q_i)/M$ a unit. Then

$$\mathsf{F}_j(x; 1)^2 \leq (c_P/|\xi|)^{\#\mathrm{FreeIndex}}\,\mathsf{Q}_j(x).$$

Lean: `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads` (New/Spanning/Frames/Gains.lean).

*Proof.* Separate the frames, with the first pivot on the section (`sq_lintegral_mul_comp_weylElem_inv_le_of_section`). The second correlation carries the phase of the lifts, and Plancherel on a section gives the gain. $\square$

These are steps 12 and 13 of the guide. All three gains have the same form, a factor times $\mathsf{Q}_j(x)$, and so the shells can treat them together.

### Shells

**Definition (Shell normalization).** The unit in which integrals over positions are measured is

$$\mathcal{N}(W) = \Bigl(\prod_{l < \varrho}|M|^{r_l+1/2}\Bigr)\,c_P^{\#\mathrm{FreeIndex}\cdot\varrho}\,\|W\|^2.$$

Lean: `New.Floors.PlaceData.shellNormalization` (New/Spanning/Frames/Shells.lean).

**Definition (Shell).** A set $S \subseteq \mathsf{G}$ is a *shell* of height $h$ for $\Gamma$, $j$, $p$, $q$, $W$ if

1. $1 \leq h < \infty$;
2. $S$ is covered by the position balls of at most $2h^{9n}$ gauges $\Gamma'$, each with loss $\Lambda' \leq \Lambda h^2$;
3. for $x \in S$ and $\sigma < 1$ with $\Lambda^{1200n^2} \leq \sigma^{400n^2}h$, the position $x$ has a deep vector of depth $\sigma^{-2}$.

Lean: `New.Floors.Gauge.IsShell` (New/Spanning/Frames/Shells.lean).

Field 3 is "far means deep". In the source it is a hypothesis, to be proved at each kind of place from the lemma that bounded depths bound the position.

**Theorem (One shell).** Let $S$ be a shell of height $h$, $j \leq \varrho$, $W$ cut, and $q$ a head of length $j$ ($p$ need not be one). If $f(x)^2 \leq e^2\mathsf{Q}_j(x)$ on $S$, then

$$\kappa_j(p, q)\int_Sf\,d\mathsf{M} \leq e\,\Lambda^{2\cdot 10^6n^3}\,h^{10^5n^2}\,\mathcal{N}(W).$$

Lean: `New.Floors.Gauge.IsShell.setLIntegral_le` (New/Spanning/Frames/Shells.lean).

*Proof.* Apply the theorem that the gain survives on each ball of the cover and add; Cauchy-Schwarz and the bound for one frame cost the powers of $\Lambda$ and $\Lambda'$. The number of balls is at most $2h^{9n}$, and $\Lambda'^{25000n^2} \leq (\Lambda h^2)^{25000n^2}$. $\square$

**Theorem (A remote shell).** Let $S$ be a shell of height $h$, $p, q$ heads of length $j \leq \varrho$, $W$ cut, $V \geq 1$ with `FloorMassLe j V 1`, $h > \Lambda^{2400n^2}$ and $\tau^{800n^2} = h^{-1}$. Then

$$\kappa_j(p, q)\int_S\mathsf{F}^*_j\,d\mathsf{M} \leq V\tau^s\,\Lambda^{2\cdot 10^6n^3}\,h^{10^5n^2}\,\mathcal{N}(W).$$

Lean: `New.Floors.Gauge.IsShell.setLIntegral_formMajorant_le` (New/Spanning/Frames/Shells.lean).

*Proof.* The condition $h > \Lambda^{2400n^2}$ gives $\Lambda^{1200n^2} \leq \tau^{400n^2}h$, so field 3 gives every active point a vector of depth at least $\tau^{-2}$. The gain from a deep vector gives $\mathsf{F}^*_j(x)^2 \leq \tau^{2s}V^2\mathsf{Q}_j(x)$, and the theorem on one shell concludes. $\square$

**Theorem (Height against gain).** Let $S$ be a shell of height $h$, $p, q$ heads of length $j \leq \varrho$, $W$ cut, $V \geq 1$ with `FloorMassLe j V 1`, $e \leq 1$, $f \leq \mathsf{F}^*_j$, $f(x)^2 \leq (Ve^s)^2\mathsf{Q}_j(x)$ on $S$, and $9\cdot 10^7n^4 + r \leq s$. Then

$$\kappa_j(p, q)\int_Sf\,d\mathsf{M} \leq h^{-1}\bigl(V e^r\,\Lambda^{3\cdot 10^8n^4}\,\mathcal{N}(W)\bigr).$$

Lean: `New.Floors.Gauge.IsShell.setLIntegral_le_inv_height` (New/Spanning/Frames/Shells.lean).

*Proof.* It suffices to find $g \leq e$ with gain $Vg^s$ and $g^{9\cdot 10^7n^4}h^{1+10^5n^2} \leq \Lambda^{29\cdot 10^7n^4}$. Below the threshold $h \leq \Lambda^{2400n^2}$ take $g = e$; the height is then bounded by a power of $\Lambda$. Beyond it, take the smaller of $e$ and $\tau = h^{-1/(800n^2)}$, and use the remote shell. The $9\cdot 10^7n^4$ spare powers of $\tau$ pay for $h^{1+10^5n^2}$, and the other $r$ powers stay as $e^r$. $\square$

**Theorem (The sum over the shells).** Let each $S_i$ be a shell of height $2^i$, with $\bigcup_iS_i$ covering the support of $f$. Let $p, q$ be heads of length $j \leq \varrho$, $W$ cut, $V \geq 1$ with `FloorMassLe j V 1`, and $f \leq \mathsf{F}^*_j$. Suppose that if $e < 1$, then $f(x)^2 \leq (Ve^s)^2\mathsf{Q}_j(x)$ for all positions $x$. Let $9\cdot 10^7n^4 + r \leq s$. Then

$$\kappa_j(p, q)\int f\,d\mathsf{M} \leq V\,\min(1, e)^r\,\Lambda^{4\cdot 10^8n^4}\,\mathcal{N}(W).$$

Lean: `New.Floors.Gauge.lintegral_le_of_shells` (New/Spanning/Frames/Shells.lean).

*Proof.* If $e \geq 1$, use the bound $\mathsf{F}^*_j(x)^2 \leq V^2\mathsf{Q}_j(x)$ without gain, that is the case $e = 1$. Apply the theorem on height against gain on each shell, and add: $\sum_i2^{-i} = 2$, and the factor $2$ goes into the extra power of $\Lambda$. $\square$

The constants are large but fixed: $s$ must exceed $9\cdot 10^7n^4$, so the rank of $X'$ must be large compared with $n^4$. With $e$ the gain from a frequency or from two heads, $e^r$ is a power of $c_P/|\xi|$, and this is what the chapters on the real and the finite places use to bound the local densities.

**Remark (Formalization).** All the bounds of this section are in $[0, \infty]$, and none needs integrability: the theorem on the sum over the shells holds even when the right side is $\infty$. The gain hypothesis is stated for every position, not only on $S$, and for a function $f$ that need not be measurable; the one-shell bound handles this by a square-root majorant. The shells themselves are not constructed here. The cover by few balls and the field "far means deep" are proved separately at the real and at the finite places (`New/Spanning/Frames/RealShells.lean` and `New/Spanning/Frames/FiniteShells.lean`), which is why the source states them as fields of a structure.
