---
title: Band limits and the local bounds
lean:
  - New/Spanning/Frames/RealBandLimits.lean
decls:
  - New.Floors.normalizedCellIntegral
  - New.Floors.IsCutBessel.continuous_normalizedCellIntegral
  - New.Floors.IsCutBessel.inner_embedH_mul
  - New.Floors.IsCutBessel.inner_normalizedCellIntegral_eq_of_last_entry
  - New.Floors.IsCutBessel.partialCorrelationProduct_top_eq
  - New.Floors.IsCutBessel.descent_last_entry_of_norm_le_one
  - New.Floors.IsCutBessel.integrable_and_integral_wave_mul_inner_normalizedCellIntegral
  - New.Floors.IsCutBessel.integrable_and_integral_wave_mul_floorForm_succ
  - New.Floors.quotientPairing
  - New.Floors.sq_lintegral_enorm_inner_le
  - New.Floors.isBesselFunction_sub
  - New.Floors.IsCutBessel.enorm_quotientPairing_sub_le
  - New.Floors.IsCutBessel.formIntegrandL1Norm_zero_eq
  - New.Floors.lintegral_add_sq_le
  - New.Floors.IsCutBessel.rho_le_pow
  - New.Floors.IsCutBessel.r_eq_add
  - New.Floors.IsCutBessel.norm_le_of_mem_positionBall
  - New.Floors.sq_error_mul_ballBound_le
  - New.Floors.IsCutBessel.setLIntegral_quotientPairing_sq_le
  - New.Floors.IsCutBessel.scaledVolumeRatio_mul_pow_div_pow_le
  - New.Floors.one_add_inv_pow_twelve_sq_add_le
  - New.Floors.IsCutBessel.enorm_formConst_mul_le_one
  - New.Floors.IsCutBessel.norm_floorForm_zero_le
  - New.Floors.IsCutBessel.norm_floorForm_wave_le
  - New.Floors.IsCutBessel.norm_floorForm_heads_le
  - New.Floors.exists_hasLocalBounds_of_isCutBessel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Band limits and the local bounds

This section proves the theorem on [the local bounds at a real place](/chapter/real-densities/#the-chapter-and-its-place). It needs three more pieces: a top form, the descent from each floor to the one below, and a bound for the bottom form. In this section $F$ is the cut of the Bessel function $W$ with base $b$ and degree $f$.

### The top form

**Definition.** For a list $p$, let $\sigma_p$ be the chart of the big cell of floor $\varrho$ at $p_\varrho$ (Lean: `New.Floors.cellChart`, Lib/DiscreteSeries/Bruhat/ComplexPlace.lean). The normalized cell integral is $\Xi(p) = N_{\sigma_p}(p)$, the vector of [Section 1](/chapter/real-densities/#the-chapter-and-its-place) built from $F$.

Lean: `New.Floors.normalizedCellIntegral` (New/Spanning/Frames/RealBandLimits.lean).

**Remark (Formalization).** For $c \neq 0$ the chart is the boost at $c/\min(1, |c|)$, so it is defined also for $|c| < 1$. For $|p_\varrho| \leq 1$ the real factor $\sqrt{|p_\varrho|^2 - 1}^{\,k-1}$ is $0$, as `Real.sqrt` is $0$ on negative numbers. The density of the top floor is $0$ on the closed unit disc. So the value $\Xi(p) = 0$ there does not change any integral below.

**Lemma.** The map $p \mapsto \Xi(p)$ is continuous.

Lean: `New.Floors.IsCutBessel.continuous_normalizedCellIntegral` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Fix $p$. Near $p$ all lists are heads for one gauge, by [the gauge for two heads](/chapter/real-densities/#cut-bessel-functions-over-shells). So the integrand of the orbital integral is supported in one compact set, and it is jointly continuous. The integral is then continuous at $p$. The real factor is continuous. $\square$

**Lemma.** For $k \in U(\kappa)$ and $x, y \in G_1$, $\langle F(kx), F(ky) \rangle = \langle F(x), F(y) \rangle$.

Lean: `New.Floors.IsCutBessel.inner_embedH_mul` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Left translation by $k$ acts on the values of $F$ by the unitary matrix $\operatorname{rep}(k)$. $\square$

**Theorem (The top form at a chart).** Let $q_\varrho = p_\varrho$. Let $\sigma$ fix the hyperbolic basis vectors of floors below $\varrho$, with $h(z, \sigma z) = p_\varrho$. Then $\langle \Xi(p), \Xi(q) \rangle = \langle N_\sigma(p), N_\sigma(q) \rangle$.

Lean: `New.Floors.IsCutBessel.inner_normalizedCellIntegral_eq_of_last_entry` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* If $|p_\varrho| \leq 1$, both sides have the factor $0$. Otherwise $\sigma = k\, \sigma_p\, k'$ with $k, k' \in U(\kappa)$, by the Cartan decomposition of [the chapter on the Bruhat cell](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place). The orbital integral of $F$ at $w_p k \sigma_p k'$ differs from that at $w_p \sigma_p$ by unitary maps on the two tensor factors. The same maps occur for $q$, since $q_\varrho = p_\varrho$. The inner product does not change. $\square$

**Lemma.** Above the top floor, for $\sigma$ that fixes the hyperbolic basis vectors, the integrand of the forms is

$$\langle F(y), F(yx) \rangle\, \langle F(\sigma^{-1} w_q^{-1} yx), F(\sigma^{-1} w_p^{-1} y) \rangle.$$

Lean: `New.Floors.IsCutBessel.partialCorrelationProduct_top_eq` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* The partial correlations above floor $\varrho$ are averages over $U(\kappa)$ of inner products. The previous lemma removes the average. $\square$

### Descent

**Theorem (Descent on the top floor).** Let $\varphi$ be measurable on $\mathbb C$ with $|\varphi| \leq 1$. Let $p_c$ and $q_c$ be $p$ and $q$ with the entry $\varrho$ replaced by $\operatorname{unitOrOne}(c)$. Put $\Phi(c) = \varphi(c) \langle \Xi(p_c), \Xi(q_c) \rangle$. Then $\Phi$ is integrable on $\mathbb C$, and

$$\int_{\mathbb C} \Phi(c)\, dc = c_F\, \mathcal I_\varrho\bigl(p, q; x \mapsto \varphi(h(z, xz))\bigr).$$

For $\varphi(c) = \operatorname{wave}(\xi c)$ this is the descent with a character.

Lean: `New.Floors.IsCutBessel.descent_last_entry_of_norm_le_one`, `New.Floors.IsCutBessel.integrable_and_integral_wave_mul_inner_normalizedCellIntegral` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* The general descent of [the chapter on frames](/chapter/local-frames/) (Lean: `New.Floors.PlaceData.integrable_and_integral_succ_eq_mul_floorForm`, New/Spanning/Frames/Densities.lean) applies. Its inputs are the chart, the density of the top floor and the finite integral of the majorant from Section 5. It remains to identify the integrand at each unit $z$. If $|z| \leq 1$, the factor of $\Xi$ and the density are both $0$. Otherwise the measure on the right is $\mathsf M = \lambda\, dg$. The substitution $(y, yx)$ turns the Gram form into a double integral of the integrand of the previous lemma. The constants agree: the product of the two normalising factors is $c_F\, \kappa_\varrho\, \delta(z)\, \lambda^2$, where $\delta$ is the density $2\pi^k (|z|^2 - 1)^{k-1}/(k-1)!$ of the top floor. $\square$

**Theorem (Descent below the top).** Let $i < \varrho$ and $\xi \in \mathbb C$. With $p_c$, $q_c$ now changed at the entry $i$, the function $c \mapsto \operatorname{wave}(\xi c)\, c_F\, \mathcal I_{i+1}(p_c, q_c; 1)$ is integrable, and its integral is $c_F\, \mathcal I_i(p, q; x \mapsto \operatorname{wave}(\xi Z(x)_{ii}))$.

Lean: `New.Floors.IsCutBessel.integrable_and_integral_wave_mul_floorForm_succ` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* This is the general descent for a character (Lean: `New.Floors.Gauge.integral_psi_mul_floorForm_succ`, New/Spanning/Frames/Densities.lean). Its only input is the finite integral of the majorant from Section 5. $\square$

### The bottom form

**Definition.** For $A, B : G_1 \to \mathbb C^I$, the matrix coefficient is $\langle A, R(x) B \rangle = \int_{\mathsf U \backslash G_1} \langle A(y), B(yx) \rangle\, dy$.

Lean: `New.Floors.quotientPairing` (New/Spanning/Frames/RealBandLimits.lean).

**Lemma.** The following hold.

1. For $A$ strongly measurable and $B$ a Bessel function of type `rep`, $\bigl(\int |\langle A(y), B(yx) \rangle|\, dy\bigr)^2 \leq \int |A|^2 \int |B|^2$ over $\mathsf U \backslash G_1$.
2. The difference of two Bessel functions of type `rep` is a Bessel function of type `rep`.
3. $|\langle F, R(x) F \rangle - \langle W, R(x) W \rangle| \leq 2 b^{-r^3 f} |I|$ for every $x$.
4. At floor $0$ with weight $1$, $\mathsf F_0(x; 1) = \lambda^2 |\langle F, R(x) F \rangle|^2$ for all lists.
5. If $\int g^2 \leq \alpha^2$ and $\int h^2 \leq \beta^2$, then $\int (g + h)^2 \leq (\alpha + \beta)^2$.

Lean: `New.Floors.sq_lintegral_enorm_inner_le`, `New.Floors.isBesselFunction_sub`, `New.Floors.IsCutBessel.enorm_quotientPairing_sub_le`, `New.Floors.IsCutBessel.formIntegrandL1Norm_zero_eq`, `New.Floors.lintegral_add_sq_le` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Item 1 is the Cauchy-Schwarz inequality, and right translation keeps the norm of a Bessel function. Item 2 is direct. For item 3, write the difference as $\langle F - W, R(x) F \rangle + \langle W, R(x)(F - W) \rangle$. The cut pair gives $\int |F - W|^2 \leq b^{-2r^3 f} |I|$ and $\int |F|^2, \int |W|^2 \leq |I|$. Item 1 bounds each term by $b^{-r^3 f} |I|$. Item 4 unfolds the form at floor $0$, where $\mathsf M = \lambda\, dg$. Item 5 is the Minkowski inequality in $L^2$. $\square$

**Lemma.** Assume the sizes of a cut Bessel function. Then:

1. $\rho \leq b^{7n}$ and $r = s + 5n + 5$;
2. if $x$ is in the position ball at scale $T_0 = b^{6r} \rho^{11n}$, then $\|x\| \leq b^{700nr}$ for the operator norm;
3. if $b \geq 2$, $n, r \geq 1$ and $f \geq 4000n$, then $(2 b^{-r^3 f})^2 (b^{700nr})^{9r^2} b^{99r^2} \leq (b^{-12})^2$.

Lean: `New.Floors.IsCutBessel.rho_le_pow`, `New.Floors.IsCutBessel.r_eq_add`, `New.Floors.IsCutBessel.norm_le_of_mem_positionBall`, `New.Floors.sq_error_mul_ballBound_le` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Item 1 uses $\rho = b^{6n+2}$ with $n \geq 2$, and $k = s + 3n + 6$ with $r = 2\varrho + k + 1$. For item 2, let $R = T_0^{99n}$. The entries of $x - 1$ have modulus at most $R$, so $\|x\| \leq \|x - 1\| + 1 \leq (r^2 + 1) R \leq \rho^2 R$, as $8r \leq \rho$. With $\rho \leq b^{7n}$ this is a power of $b$ with exponent $14n + 99n(6r + 77n^2)$. This is at most $700nr$, since $10^9 n^3 \leq r$. For item 3, the exponent of $b$ on the left is at most $2 + 6300 n r^3 + 99 r^2 - 2r^3 f$, and $f \geq 4000n$ makes it at most $-24$. $\square$

**Lemma (Near positions).** Let $f \geq 4000n$ and $\deg > 0$. Let $\int_{G_1} |\langle W, R(x) W \rangle|^2\, dx \leq |I|^2/\deg$, and let $\deg \cdot \operatorname{vol}\{\|g\| \leq T\} \leq T^{9r^2} b^{99r^2}$ for every $T \geq 1$. Then

$$\int_{B(T_0)} |\langle F, R(x) F \rangle|^2\, dx \leq \frac{(1 + b^{-12})^2 |I|^2}{\deg},$$

where $B(T_0)$ is the position ball at scale $T_0 = b^{6r} \rho^{11n}$.

Lean: `New.Floors.IsCutBessel.setLIntegral_quotientPairing_sq_le` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* On $B(T_0)$, $|\langle F, R(x) F \rangle| \leq |\langle W, R(x) W \rangle| + 2b^{-r^3 f} |I|$. The first term has $L^2$ norm at most $|I|/\sqrt{\deg}$. The ball $B(T_0)$ lies in $\{\|g\| \leq b^{700nr}\}$, so the constant second term has squared $L^2$ norm at most $(b^{-12})^2 |I|^2/\deg$ by item 3 above. Minkowski adds the two norms. $\square$

**Lemma.** The following hold.

1. If $\deg \cdot \Theta \leq b^{4r^2}$ and $t_0 = b^{6r}$, then $\Theta \rho^{10^9 n^4} \rho^{24k} t_0^{10^8 n^4}/t_0^s \leq b^{-12}/\deg$.
2. If $b \geq 2$, then $(1 + b^{-12})^2 + b^{-12} \leq 1 + b^{-10}$.
3. $c_F\, \lambda\, (\lambda |I|)^2 \leq 1$.

Lean: `New.Floors.IsCutBessel.scaledVolumeRatio_mul_pow_div_pow_le`, `New.Floors.one_add_inv_pow_twelve_sq_add_le`, `New.Floors.IsCutBessel.enorm_formConst_mul_le_one` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Item 1 compares exponents of $b$ with $\rho \leq b^{7n}$ and $s \geq 10^{10} n^4$. Item 2 is $(1 + b^{-12})^2 + b^{-12} = 1 + (3 + b^{-12}) b^{-2} b^{-10}$ with $(3 + 1)/4 = 1$. Item 3 is $c_F (\lambda |I|)^2 = \operatorname{vol} U(k)/\operatorname{vol} U(r)$ and the bound on $\lambda$ of [Section 2](/chapter/real-densities/#haar-measure-and-the-floors). $\square$

**Theorem (The mass at a real place).** Under the hypotheses of the near positions lemma and $\deg \cdot \Theta \leq b^{4r^2}$, for all lists $p$, $q$,

$$|c_F\, \mathcal I_0(p, q; 1)| \leq \frac{1 + b^{-10}}{\deg}.$$

Lean: `New.Floors.IsCutBessel.norm_floorForm_zero_le` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* At floor $0$ the head density is $1$, so $|\mathcal I_0| \leq \int \mathsf F_0(x; 1)\, d\mathsf M$. Split $G_1$ into $C = B(T_0)$ and its complement. On $C$, item 4 and $\mathsf M = \lambda\, dg$ give $c_F \lambda \cdot \lambda^2 \int_C |\langle F, R(x) F \rangle|^2$. The near positions lemma and item 3 bound this by $(1 + b^{-12})^2/\deg$. Off $C$, every list is a head of length $0$ for the gauge of scale $\rho$, and $\mathsf F_0 \leq \mathsf F^+_0$. The theorem on remote positions of [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells) with $L = \rho$ and $t = b^{6r}$ and item 1 give $b^{-12}/\deg$. Item 2 adds the two parts. $\square$

### Decay

**Theorem (Decay in the frequency).** Let $i \leq \varrho$ and $\nu \in \mathbb C^\times$. Then

$$|I|\, \bigl|c_F\, \mathcal I_i\bigl(p, q; x \mapsto \operatorname{wave}(\nu Z(x)_{ii})\bigr)\bigr| \leq \Theta\, b^{2000n^9}\, \ell_{k - n^7}(|\nu|^{-1})\, \Lambda(i, p)\, \Lambda(i, q),$$

with $\Lambda = \Lambda_{b^{60n^2}, n^6}$.

Lean: `New.Floors.IsCutBessel.norm_floorForm_wave_le` (New/Spanning/Frames/RealBandLimits.lean).

**Theorem (Decay for unequal entries).** Let $i + 1 \leq \varrho$ and $\nu = p_i^{-1} - q_i^{-1} \neq 0$. Then $|I|\, |c_F\, \mathcal I_{i+1}(p, q; 1)|$ is at most $\Theta\, b^{2000n^9}\, \ell_{k - n^7}(|\nu|^{-1})\, \Lambda(i+1, p)\, \Lambda(i+1, q)$.

Lean: `New.Floors.IsCutBessel.norm_floorForm_heads_le` (New/Spanning/Frames/RealBandLimits.lean).

*Proof of both.* Apply the bound of the forms of Section 5 with $y = \nu$. Its hypothesis is the gain of the general machine for a character (Lean: `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char`, New/Spanning/Frames/Gains.lean) or for unequal heads (Lean: `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads`). At $\mathbb C$ the level is $1$. $\square$

### The local bounds

**Theorem (Local bounds at a real place).** Under hypotheses 1 to 4 of [Section 1](/chapter/real-densities/#the-chapter-and-its-place), there are forms $J$ with the local bounds for $F$, with $b$ and $\deg$.

Lean: `New.Floors.exists_hasLocalBounds_of_isCutBessel` (New/Spanning/Frames/RealBandLimits.lean).

*Proof.* Put $J_i(p, q) = c_F\, \mathcal I_i(p, q; 1)$ for $i \leq \varrho$ and $J_i(p, q) = \langle \Xi(p), \Xi(q) \rangle$ for $i > \varrho$. Check the six conditions of a sieve system with $N = \varrho$.

1. $\operatorname{wave}(0) = \exp(0) = 1$.
2. For $i < \varrho$ use the descent below the top, and for $i = \varrho$ the descent on the top floor. The integral is $c_F\, \mathcal I_i(p, q; \omega)$ with $\omega(x) = \operatorname{wave}(\xi Z(x)_{ii})$. If $\xi = 0$, then $\omega = 1$ and the integral is $J_i(p, q)$. If $\xi \neq 0$, the decay in the frequency bounds $|I|$ times its modulus, and $|I| \geq 1$.
3. The top form is a Gram matrix of the vectors $\Xi(a_j)$, so it is positive semidefinite.
4. The top form is continuous, since $\Xi$ is continuous.
5. The mass at a real place gives $|J_0| \leq (1 + b^{-10})/\deg$.
6. The decay for unequal entries, with $|I| \geq 1$.

Condition 2 of the local bounds is the top form at a chart. $\square$

**Remark (Formalization).** The decay bounds carry the factor $|I|$, and the local bounds do not. The proof drops it with $|I| \geq 1$. The file imports `Lib.Cohomology.Etale.Basic`, but no declaration of that file is used in the statements or proofs above. The import adds no hypothesis.

**Example.** Let $b = 2$. The bottom bound is $(1 + 2^{-10})/\deg$. Its two parts are $(1 + 2^{-12})^2/\deg$ from the near positions and $2^{-12}/\deg$ from the remote ones. Their sum is $(1 + 2^{-11} + 2^{-24} + 2^{-12})/\deg$, which is less than $(1 + 2^{-10})/\deg$.
