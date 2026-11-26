---
title: One frame
lean:
  - New/Spanning/Frames/OneFrame.lean
decls:
  - New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_sq_le
  - New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_sq_le_of_floorMassLe_one
  - New.Floors.PlaceData.IsPairingKernel.weightedSquareIntegral_eq_add_succ
  - New.Floors.Gauge.lintegral_invDepthWeight_descConv_le
  - New.Floors.lintegral_weightedSquareIntegral_le_of_lintegral_le
  - New.Floors.Gauge.closeMass
  - New.Floors.Gauge.cutSquare
  - New.Floors.Gauge.climbConst
  - New.Floors.Gauge.lintegral_cutSquare_le
  - New.Floors.Gauge.exists_factor_cutSquare_le
  - New.Floors.Gauge.lintegral_weightedSquare_le
  - New.Floors.Gauge.lintegral_weightedSquareIntegral_le
  - New.Floors.PlaceData.headDensity_sq_mul_eq_modulus
  - New.Floors.Gauge.headDensity_mul_lintegral_le_mul_pairingNormSq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One frame

After Cauchy-Schwarz, each of the two frames of the majorant is paired with itself. This section bounds the second moment $\mathsf{S}_j(k, x)$ of one frame, integrated over the position ball, by the squared $L^2$ norm of the kernel. The integration climbs the floors one at a time. A step below the pivot floor uses up a weight; a step above it adds a vector by Parseval's formula. At the end, a gain on the position ball survives the integration.

### Cauchy-Schwarz on a floor

**Lemma (Cauchy-Schwarz on a floor).** Let $k$ be a pairing kernel at floor $j$, and let $u, v \geq 0$ be measurable. Suppose `FloorMassLe l K u`, and $|c_{l+1}(k)(\sigma g, \sigma y)|^2 \leq u(\sigma g)\,v(\sigma)$ for $\sigma \in G^{(l)}$. Then

$$P_l(k)(g, y)^2 \leq K\int v\,d\theta_l.$$

Lean: `New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_sq_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* The floor measure lives on $G^{(l)}$, and the correlation vanishes unless $\sigma g$ is near at $l + 1$. On that set, write $|c_{l+1}| \leq \sqrt{u}\sqrt{v}$ and apply the Cauchy-Schwarz inequality; the integral of $u$ over the near set is at most $K$. $\square$

With $u = 1$ this is the plain form: if `FloorMassLe l K 1`, then $P_l(k)(g, y)^2 \leq K\int|c_{l+1}(k)(\sigma g, \sigma y)|^2\,d\theta_l(\sigma)$.

Lean: `New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_sq_le_of_floorMassLe_one` (New/Spanning/Frames/OneFrame.lean).

The second moment unfolds into one term per floor.

**Lemma (Unfolding the second moment).** For a pairing kernel $k$ and $l \leq \varrho$,

$$\mathsf{S}_l(k, x) = \int a_l\,d\mu_{<l+1} + \mathsf{S}_{l+1}(k, x).$$

Lean: `New.Floors.PlaceData.IsPairingKernel.weightedSquareIntegral_eq_add_succ` (New/Spanning/Frames/OneFrame.lean).

*Proof.* Unfold $b_l$ once; the integral against $\mu_{<l}$ of an integral against $\theta_l$ is the integral against $\mu_{<l+1} = \theta_l * \mu_{<l}$. $\square$

So $\mathsf{S}_l \leq \mathsf{S}_0$ for $l \leq n$ (`weightedSquareIntegral_le_weightedSquareIntegral_zero`), and a bound on each term gives a bound on the sum.

**Lemma (Term by term).** Let $\mu$ be a measure, $j \leq \varrho$, and $k$ a pairing kernel at floor $j$. If for every $l$ with $j \leq l \leq \varrho$,

$$\int\!\!\int a_l(g)\,d\mu_{<l+1}(g)\,d\mu(x) \leq c,$$

then $\int\mathsf{S}_j(k, x)\,d\mu(x) \leq n\,c$.

Lean: `New.Floors.lintegral_weightedSquareIntegral_le_of_lintegral_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* Unfold $\mathsf{S}_j$ into the terms $l = j, \ldots, \varrho$ by the lemma above. There are at most $n$ terms. $\square$

The inverse weights are integrable over the floors, by the lemma that deep vectors are rare applied on each floor.

**Lemma (Deep vectors are rare on several floors).** Let $x$ be a position and $l + i \leq \varrho$. Then

$$\int\wp^{-1}_{l+i}(\sigma g)\,d(\theta_{l+i-1} * \cdots * \theta_l)(\sigma) \leq (\Lambda^{10^4n})^i\,\wp^{-1}_l(g).$$

Lean: `New.Floors.Gauge.lintegral_invDepthWeight_descConv_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* By induction on $i$. One floor is the lemma that deep vectors are rare: the new factor $\delta_a^s$ has floor mass at most $\Lambda^{10^4n}$, and the old factors do not change under the floor $a$, by the invariance of depth. $\square$

### Climbing above the pivot

The steps above the pivot cannot use a weight. They use the Heisenberg groups instead.

**Definition (Close mass and cut square).** For $l$ and $g, y \in \mathsf{G}$, the *close mass* is the $\eta_{<l}$-measure of the $\nu$ with $g^{-1}\nu y$ in the position ball. The *cut square* is

$$\mathrm{cs}_l(k)(g, y) = \min\bigl(\infty\cdot\mathrm{cm}_l(g, y),\ |c_{l+1}(k)(g, y)|^2\bigr),$$

which is $0$ where the close mass is $0$ and the square elsewhere. The *cost of a step* is $\mathcal{C}_l$ for $l < \varrho$ and $1$ for $l = \varrho$ (`climbConst`).

Lean: `New.Floors.Gauge.closeMass`, `New.Floors.Gauge.cutSquare`, `New.Floors.Gauge.climbConst` (New/Spanning/Frames/OneFrame.lean).

The cut by $\infty\cdot\mathrm{cm}_l$ stands for the indicator of $\mathrm{cb}_l(g)$. The source chooses it because it is measurable in the pair $(g, y)$, while the indicator of the set $\mathrm{cb}_l(g)$ is not obviously so.

**Lemma (One floor up).** Let $k$ be a pairing kernel at floor $j$ and $j \leq l \leq \varrho$. Then

$$\int\mathrm{cs}_l(k)(g, ny)\,d\eta_l(n) \leq \mathrm{cc}_l\int\mathrm{cs}_{l+1}(k)(\sigma g, \sigma y)\,d\theta_{l+1}(\sigma),$$

where $\mathrm{cc}_l$ is the cost of the step.

Lean: `New.Floors.Gauge.lintegral_cutSquare_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* If the close mass at level $l + 1$ is $0$, then the close mass at level $l$ of $(g, ny)$ is $0$ for almost every $n$, because $\eta_{<l+1} = \eta_{<l} * \eta_l$, and both sides are $0$. Otherwise the cut on the right does nothing, since the close mass is the same at $(\sigma g, \sigma y)$ (`closeMass_mul_mul`). Below the top floor, the left side is Parseval's inequality on the Heisenberg group of floor $l$ at the frequency $M^{-1}$, applied to the function $n \mapsto c_{l+1}(k)(g, ny)$, which vanishes off a set of the right size; the constant is $\mathcal{C}_l$. On the top floor $\eta_\varrho$ is a point mass, and Cauchy-Schwarz on $H$ costs $1$. $\square$

**Lemma (All floors above l).** Let $\mathsf{M}$ be a Haar measure, $k$ a pairing kernel at floor $j$, and $j \leq l \leq \varrho + 1$. There is an s-finite measure $\rho$ with $\mathsf{M} = \eta_{<l} * \rho$ and

$$\Bigl(\prod_{a < l}\mathrm{cc}_a\Bigr)\int\!\!\int\mathrm{cs}_l(k)(g, y)\,d\rho(y)\,d\mu_{<l+1}(g) \leq \Bigl(\prod_{a < \varrho}\mathcal{C}_a\Bigr)\iint|k(g, y)|^2\,d\mu_{\geq 0}\,d\mu_{\geq 0}.$$

Lean: `New.Floors.Gauge.exists_factor_cutSquare_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* By downward induction on $l$. At $l = \varrho + 1$ the kernel is not averaged and there is no cost. For the step from $l + 1$ to $l$, take the measure $\rho$ of $l + 1$ and convolve it with $\eta_l$. The cut square of floor $l + 1$ is left invariant under $U_{<l+1}$, so the factor lemma lets $y$ move by $\sigma$. Apply the lemma on one floor up for each $y$, swap the integrals, and undo the shift. $\square$

The source says that the factorization $\mathsf{M} = \eta_{<l} * \rho$ is a form of Weil's quotient integral formula for $U_{<l}$, with an s-finite measure on the group in place of the invariant measure on the cosets.

### The bound for one frame

**Theorem (One frame, one pivot).** Let $\mathsf{M}$ be a Haar measure, $k$ a pairing kernel at floor $j$, and $j \leq l \leq \varrho$. Then

$$\int_{\text{position ball}}\int a_l(g)\,d\mu_{<l+1}(g)\,d\mathsf{M}(x) \leq \Bigl(\prod_{a < \varrho}\mathcal{C}_a\Bigr)\iint|k(g, y)|^2\,d\mu_{\geq 0}\,d\mu_{\geq 0}.$$

Lean: `New.Floors.Gauge.lintegral_weightedSquare_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* Write $x = g^{-1}\nu y$ with $\nu \in U_{<l}$. The modulus of the correlation does not depend on $\nu$ (`enorm_partialCorrelation_mul_of_mem_unipotentBelow`), and the weight $\wp_l(g, g^{-1}\nu y)$ has integral over $\nu$ at most $\prod_{a<l}\mathcal{C}_a$, by the lemma on the weight over the position ball. What is left is the cut square, bounded by the lemma on all floors above $l$. $\square$

**Theorem (One frame).** Let $\mathsf{M}$ be a Haar measure and $k$ a pairing kernel at floor $j \leq \varrho$. Then

$$\int_{\text{position ball}}\mathsf{S}_j(k, x)\,d\mathsf{M}(x) \leq n\Bigl(\prod_{l < \varrho}\mathcal{C}_l\Bigr)\iint|k(g, y)|^2\,d\mu_{\geq 0}\,d\mu_{\geq 0}.$$

Lean: `New.Floors.Gauge.lintegral_weightedSquareIntegral_le` (New/Spanning/Frames/OneFrame.lean).

*Proof.* Apply the lemma on term by term with $\mu$ the restriction of $\mathsf{M}$ to the position ball and $c$ the bound of one frame, one pivot. $\square$

### The gain survives

**Lemma (Powers of the head).** For $j \leq \varrho$ and $r_a = k + 1 + 2(\varrho - a - 1)$,

$$\kappa_j(p, q)^2\Bigl(\prod_{a<j}|p_a^{-1}|^{r_a+1/2}\Bigr)^2\prod_{a<j}|p_a/q_a|^{r_a+1} = |q_0\cdots q_{j-1}|^{-1}.$$

Lean: `New.Floors.PlaceData.headDensity_sq_mul_eq_modulus` (New/Spanning/Frames/OneFrame.lean).

*Proof.* Compare the exponents of $|p_a|$ and $|q_a|$. The exponent of $|p_a|$ is $r_a - (2r_a + 1) + (r_a + 1) = 0$, and the exponent of $|q_a|$ is $r_a - (r_a + 1) = -1$. $\square$

The factor $|p_a/q_a|^{r_a+1}$ is the modulus of left translation by $w = w_q^{-1}w_p$ on the second frame.

**Theorem (The gain survives).** Let $\mathsf{M}$ be a Haar measure, $W$ cut, $j \leq \varrho$, $p$ any sequence of units, $q$ a head of length $j$ for $\Gamma$, and $S$ a subset of the position ball of a second gauge $\Gamma'$. Let $f \geq 0$ have the gain $e$ on $S$: $f(x)^2 \leq e^2\mathsf{Q}_j(x)$ for $x \in S$. Then

$$\kappa_j(p, q)\int_Sf\,d\mathsf{M} \leq e\Bigl(\prod_{l < \varrho}|M|^{r_l + 1/2}\Bigr)c_P^{\#\mathrm{FreeIndex}\cdot\varrho}\,\Lambda^{1500000n^3 + 1}\,\Lambda'^{25000n^2}\,\|W\|^2,$$

where $\Lambda'$ is the loss of $\Gamma'$.

Lean: `New.Floors.Gauge.headDensity_mul_lintegral_le_mul_pairingNormSq` (New/Spanning/Frames/OneFrame.lean).

*Proof.* The function $f$ need not be measurable, so bound it by the square root of the gain, and apply the Cauchy-Schwarz inequality on $S$. This gives two integrals of second moments. The first is the plain frame, bounded by the theorem on one frame for $\Gamma'$. The second is the twisted frame; it is bounded the same way after a left translation by $w$, whose modulus is the factor $\prod|p_a/q_a|^{r_a+1}$. The lemma on powers of the head turns $\kappa_j^2$ and the factors $|p_a^{-1}|^{r_a+1/2}$ of $\mathsf{Q}_j$ into $|q_0 \cdots q_{j-1}|^{-1}$, whose inverse has size $1$ because $q$ is a head, so the modulus lemma of the gauge bounds it by $\Lambda$. The rest is the collection of constants, with $\mathcal{F}_\Lambda^3$ and the costs $\mathcal{C}_l$ of $\Gamma'$. $\square$

The point of the theorem is that $p$ need not be a head: the powers of $|p_a|$ cancel. This is why the shells of the last section need only $q$ to be a head for the bound of one shell.

**Remark (Formalization).** The quotient $\mathsf{U}\backslash\mathsf{G}$ never appears. The norm $\|W\|^2$ is an integral against the measure $\mu_{\geq 0}$ on the group, and the climbing lemma builds, for each $l$, an s-finite measure $\rho$ with $\mathsf{M} = \eta_{<l} * \rho$. The cut square replaces an indicator by $\min(\infty\cdot m, \cdot)$ in $[0, \infty]$ so that joint measurability is automatic. The constants are not optimized: $\Lambda^{1500000n^3}$ comes from $\mathcal{F}_\Lambda^3 \cdot \prod\mathcal{C}_l$ and is only used through its form, a fixed power of $\Lambda$.
