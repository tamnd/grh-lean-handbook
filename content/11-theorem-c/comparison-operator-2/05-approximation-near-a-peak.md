---
title: Approximation near a peak
lean:
  - New/OneLift/ComparisonOperator/ProductsSpan.lean
decls:
  - New.Data.negIndex_posRowIndex_injective_and_padSigns
  - New.Data.exists_datum_norm_modKernel_sub_polyMatrixCoeff_le
  - New.Data.paddedMinorProd_mem_supported
  - New.Data.maxOpNorm_sum_one_le
  - New.Data.polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded
  - New.Data.exists_eval_smul_paddedMinorProd
  - New.Data.flatKernelWeight
  - New.Data.holomorphicWeight
  - New.Data.antiholomorphicWeight
  - New.Data.polyMatrixCoeff_paddedMinorProd
  - New.Data.flatKernelWeight_antiholomorphicWeight_bounds
  - New.Data.carrierChar_hasWeight_sub_card
  - New.Data.exists_isPeak_carrierForm
  - New.Data.paddedSpace
  - New.Data.firstMinimum_le_paddedSpace
  - New.Data.exists_sum_choiceFn_eq_integral
  - New.Data.inv_pow_twenty_mul_pow_nStar
  - New.Data.inv_pow_le_firstMinimum_mul
  - New.Data.card_carrierIndex_le_and_card_sum_padIndex_le
  - New.Data.integral_mul_polyMatrixCoeff_paddedMinorProd
  - New.Data.exists_choiceFn_approx
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Approximation near a peak

This section proves the two steps of the proof that products span that do not involve the good form. Step 1 writes an integral of the carrier against a kernel on $(S, \widetilde W)$ as a combination of the functions $\mathsf{F}_i$. Step 3 shows that, away from the cusps, some combination of the $\mathsf{F}_i$ is close to one fixed function $\mathsf{F}^0$ with $\mathsf{F}^0(1) \neq 0$.

### Notation

Fix $1 \leq j \leq m$. The space $S$ has signature $(2m, m)$, with index set $\mathrm{CarrierIndex}$ of $3m$ elements. The space $W^\flat$ is $E^{6m+1}$. We write:

- $\lambda_1(g)$ for the first minimum of the lattice moved by $g$, cut off at $1$;
- $|h|$ for the largest operator norm `New.Rows.maxOpNorm` of a real point $h$;
- $m_u$ for the quotient of minors `New.holMinorsPi` of a weight $u$, from [the model function](/chapter/discrete-series/#the-holomorphic-case-the-cusp-kernel-and-the-character-wave);
- $c_Q(h, h')$ for the matrix coefficient `New.Rows.polyMatrixCoeff` of the real Weil representation at the Fock vector of $Q$;
- $n_* = 2ft^3$ for `New.Data.nStar`.

A weight $(a; c)$ has the entry $a$ at the signs $+1$ of $S$ and $c$ at the signs $-1$. The number $\Delta'$ = `New.Data.reducedHalfGap` is $\Delta/2 - (t+1)/2$, where $\Delta$ is the gap between the weights of consecutive lifts. The number $\mu_1^+(w)$ is $\#\mathrm{DetIndex}(j, w)$, the number of columns of the diagram $\mu^+$ of the $j$-th lift at $w$. The number $n''$ = $\#\mathrm{FirstFactorIndex}(j)$ is $r + 9m + 1$ (`New.Data.card_firstFactorIndex`).

The fixed polynomial $P$ = `New.Data.paddedMinorProd` is defined in [the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data):
$$P = \prod_\tau \det(y^-_\tau)^{\mu_1^+(\tau) + n'' + m}\prod_{h < r_+}\det(y_{\tau,h})^{k^+(\tau, h)},$$
where $y^-_\tau$ is the $m \times m$ block in the rows $\mathrm{negIndex}$ and the negative columns, $y_{\tau, h}$ is the $2m \times 2m$ block in the rows $\mathrm{posRowIndex}(h)$ and the positive columns, $r_+ = k + j - 1$, and $k^+$ are the column counts of the untwisted descent pair.

### The padded space and the polynomial

**Definition (The padded space).** $\widetilde W = W_j \oplus (E^j)^- \oplus E^{3m-j}$, with signs $\mathrm{padSigns}(j)$.

Lean: `New.Data.paddedSpace` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

**Lemma (Rows of the minors).** The map $\mathrm{negIndex}$ and each map $\mathrm{posRowIndex}(h)$ are injective. The rows $\mathrm{negIndex}(a)$ have sign $-1$ in $\widetilde W$, and the rows $\mathrm{posRowIndex}(h, a)$ have sign $1$.

Lean: `New.Data.negIndex_posRowIndex_injective_and_padSigns` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* For $a < j$, $\mathrm{negIndex}(a)$ is the $a$-th index of the negative padding block, and for $a \geq j$ it is the basis vector of number $k + a - 1$ of $W_j$. The vectors of number at least $r_+ = k + j - 1$ of $W_j$ are negative, so all these rows have sign $-1$, and distinct $a$ give distinct rows. For $h + a < r_+$, $\mathrm{posRowIndex}(h, a)$ is the basis vector of number $h + a$, which is positive. Otherwise it is the $a$-th index of the positive padding block. Two values are equal only if both lie in the same branch with the same $a$. $\square$

**Lemma (The variables of $P$ are positive).** Give the variable in row $x$ and column $y$ the sign of $x$ times the sign of $y$. Then $P$ is a polynomial in the variables of sign $1$.

Lean: `New.Data.paddedMinorProd_mem_supported` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* The minor $\det y^-_\tau$ has negative rows and negative columns, and $\det y_{\tau,h}$ has positive rows and positive columns, by the previous lemma. Products and powers of polynomials in a set of variables stay in that set. $\square$

**Lemma (Degree).** $P$ is homogeneous of a degree $d \leq b\sqrt b$.

Lean: `New.Data.exists_eval_smul_paddedMinorProd` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* A $p \times p$ minor is homogeneous of degree $p$. So the degree at the place $w$ is
$$\deg_w = \sum_{h < r_+} 2m\,k^+(w, h) + m\bigl(\mu_1^+(w) + n'' + m\bigr).$$
The sum of the $k^+(w, h)$ is at most $\mu_1^+(w)$, so $\deg_w \leq 2m(\mu_1^+(w) + n'' + m)$, and $2(\mu_1^+(w) + n'' + m) \leq 5b$ by `New.Data.two_mul_card_detIndex_add_le`. So $\deg_w \leq 2m\cdot 5b$, and the total degree $d$ is at most $f\cdot 10mb$. The data give $10fmb \leq b\sqrt b$. $\square$

**Lemma (The coefficient of $P$).** For any weights $\gamma$, $e$ of the two characters, $c_P(1, 1) \neq 0$, and $c_P$ is bounded on the product of the real groups of $S$ and $\widetilde W$.

Lean: `New.Data.polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Let $v$ be the Fock vector of $P$. The Fock representation is unitary (`New.Fock.isUnitaryRep_detTwist`): there are a Hilbert space and a linear map $l$ that carries the Fock form to the inner product and the action to isometries. Then $c_P(1, 1) = \langle l v, l v\rangle$, which is nonzero as $P \neq 0$: each minor has distinct rows by the lemma on rows, and distinct columns, so it is a nonzero polynomial. Up to factors of modulus $1$, $c_P(h, h') = \langle l v, l(\omega(h, h')v)\rangle$. By Cauchy and Schwarz, $|c_P(h, h')| \leq \|lv\|^2$. $\square$

**Lemma (Extension by $1$).** For a real point $y$ of $U(W_j)$, the point $(y, 1, 1)$ of $U(\widetilde W)$ has $|(y, 1, 1)| \leq |y|$.

Lean: `New.Data.maxOpNorm_sum_one_le` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* The operator norm of a block diagonal matrix is the largest norm of a block, the identity block has norm $1$, and $|y| \geq 1$ as $y$ is unitary for an indefinite form. $\square$

### The weights

**Definition (The three weights).** At every infinite place $w$:

- $u_1 = (-\Delta'; 6m+1)$, the weight of the kernels on $(S, W^\flat)$;
- $u_2(w) = (\Delta'; \mu_1^+(w) + r + 2m)$, the holomorphic weight;
- $u_3(w) = (0; \mu_1^+(w) + n'' + 2m)$, the antiholomorphic weight.

Lean: `New.Data.flatKernelWeight`, `New.Data.holomorphicWeight`, `New.Data.antiholomorphicWeight` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

We have $u_3 = (0; 3m) + u_1 + u_2$. Indeed, at the signs $+1$, $0 - \Delta' + \Delta' = 0$. At the signs $-1$, $3m + 6m + 1 + \mu_1^+ + r + 2m = \mu_1^+ + (r + 9m + 1) + 2m$.

**Lemma (The character of the kernel).** The character $\beta_j$ = `New.Data.carrierChar` has weight $m - \mu_1^+(w)$ at $w$ and trivial tame part.

Lean: `New.Data.carrierChar_hasWeight_sub_card` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* By [the third exchange](/chapter/comparison-operator-2/#the-third-exchange), $\beta_j$ has weight $(m + e_j) - w_j(w)$, with $e_j$ the exponent of $\upsilon$ in the first factor character. The identity $\mu_1^+(w) + e_j = w_j(w)$ (`New.Data.card_detIndex_add_firstFactorCharExp`) turns this into $m - \mu_1^+(w)$. $\square$

**Lemma (Factoring $c_P$).** Let the second character have weight $m - \mu_1^+$, and the first any weight $\gamma$. For every real point $h$ of $U(S)$,
$$c_P(h, 1) = c_P(1, 1)\,m_{u_2}(h)\,\overline{m_{u_3}(h)}.$$

Lean: `New.Data.polyMatrixCoeff_paddedMinorProd` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* The general factorization `New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj` of [neighbours and reproduction](/chapter/siegel-weil/) applies to a polynomial in the variables of sign $1$ that is scaled by principal minors under substitution. Each minor of $P$ uses all columns of one sign. So the substitution by $(u^{-1}, 1)$ multiplies $\det y_{\tau,h}$ by the principal minor of $u_\tau$ on the positive indices, and $\det y^-_\tau$ by the principal minor on the negative indices. The exponents are $\nu(w) = \sum_h k^+(w, h)$ for the positive minor and $\kappa(w) = \mu_1^+(w) + n'' + m$ for the negative one. The general result gives the holomorphic weight $(-\nu; \mathrm{rank}\,\widetilde W - m)$ plus the shift $m - (m - \mu_1^+) = \mu_1^+$, and the antiholomorphic weight $(0; \kappa + m)$, with $m$ negative indices in $\widetilde W$. Now $-\nu + \mu_1^+ = \Delta'$, as $\mu_1^+ = \nu + \Delta'$, and $\mathrm{rank}\,\widetilde W - m + \mu_1^+ = r + 2m + \mu_1^+$. So the weights are $u_2$ and $u_3$. $\square$

**Lemma (Bounds on the weights).** For every order $o$, the weights $u_1$ and $u_3$ are $K$-dominant and have holomorphic gap $300n_*$ at every place. Every entry of $u_3$ has modulus at most $5b$.

Lean: `New.Data.flatKernelWeight_antiholomorphicWeight_bounds` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Both weights are constant on each sign, so they are $K$-dominant. The gap is the difference of the entry at the signs $-1$ and the entry at the signs $+1$. For $u_1$ it is $6m + 1 + \Delta'$. For $u_3$ it is at least $\Delta'$ up to a nonnegative term, as $\mu_1^+ \geq \Delta'$. The data give $300n_* + t \leq \Delta/2$ (`New.Data.mul_nStar_add_t_le_halfGap`), so $\Delta' \geq 300n_*$. For the size, $0 \leq \mu_1^+ + n'' + 2m \leq 2(\mu_1^+ + n'' + m) \leq 5b$, using $m \leq n''$. $\square$

### Peaks and first minima

**Lemma (A peak of the carrier).** Let $o$ put the signs $+1$ first. Assume that $\varphi^\circ$ is rapidly decreasing of every level and holomorphic of weight $(0; 3m)$ for $o$. Then $\varphi^\circ$ has a peak $g_1$, and $\lambda_1(g_1) \geq (5b\sqrt b)^{-1/2}$.

Lean: `New.Data.exists_isPeak_carrierForm` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* A nonzero bounded function has a point where its modulus exceeds half the supremum. The carrier is bounded as it is rapidly decreasing, and nonzero by [the carrier](/chapter/comparison-operator-2/#the-carrier) (`New.Rows.exists_isPeak_of_mem_rapidOfLevel` packages this). Then apply [peaks away from the cusp](/chapter/discrete-series/#the-holomorphic-case-the-cusp-kernel-and-the-character-wave) (`New.Rows.IsPeak.le_firstMinimum`) with $A = 5b$ and $A' = \sqrt b$. Its hypotheses hold: the weight $(0; 3m)$ has gap $3m \geq 1$ and entries at most $3m \leq 5b$. The level element is $\sqrt{-d}$, with $\overline{\sqrt{-d}} = -\sqrt{-d}$ and imaginary part $\sqrt d \leq \sqrt b$. The carrier is invariant under the rational points and right invariant at the level $\sqrt{-d}$, since it is of every level. $\square$

**Lemma (Padding keeps the first minimum).** For $g$ in $U(W_j)$, $\lambda_1^{W_j}(g) \leq \lambda_1^{\widetilde W}(g, 1)$.

Lean: `New.Data.firstMinimum_le_paddedSpace` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* The first minimum of an orthogonal sum is at least the smaller of the two first minima. The padding is a sum of two definite standard spaces, each of first minimum at least $1$, so its first minimum is $1$ after the cut off. As $\lambda_1^{W_j}(g) \leq 1$, the minimum of the two is $\lambda_1^{W_j}(g)$. $\square$

**Lemma (Ranks).** $\#\mathrm{CarrierIndex} = 3m \leq t$ and $\mathrm{rank}\,\widetilde W = r + 3m \leq t$.

Lean: `New.Data.card_carrierIndex_le_and_card_sum_padIndex_le` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* $t = 5r$ and $3m \leq r$. $\square$

**Lemma (Product of first minima).** If $\lambda_1^S(g_1) \geq (5b\sqrt b)^{-1/2}$ and $\lambda_1^{W_j}(g) \geq (5b^{24})^{-1/2}$, then $\lambda_1^S(g_1)\,\lambda_1^{\widetilde W}(g, 1) \geq b^{-13}$.

Lean: `New.Data.inv_pow_le_firstMinimum_mul` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* By the padding lemma, the product is at least $(5b\sqrt b)^{-1/2}(5b^{24})^{-1/2} = (25\,b^{25.5})^{-1/2}$. This is $b^{-12.75}/5$, which is at least $b^{-13}$, as the data make $b^{1/4} \geq 5$. $\square$

**Lemma (Powers of $b$).** $b^{-20n_*}\,b^{n_*} = b^{-19n_*}$.

Lean: `New.Data.inv_pow_twenty_mul_pow_nStar` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* $b > 0$. $\square$

### Sparse sums

**Theorem (Sparse sums).** Let $V$, $V'$ have ranks at most $t$, let $\chi$, $\chi'$ have weights $\gamma$, $e$, and let $Q$ be homogeneous of degree $d \leq b\sqrt b$. If $\lambda_1^V(g)\lambda_1^{V'}(g') \geq b^{-13}$, there is a datum $\Psi$ modulo $\varpi^2$ such that for all real points $h$, $h'$,
$$\bigl|\theta[\Psi, Q](g h, g' h') - c_Q(h, h')\bigr| \leq b^{-20n_*}\bigl(|h|\,|h'|\bigr)^{6n_*}|c_Q(1, 1)|.$$

Lean: `New.Data.exists_datum_norm_modKernel_sub_polyMatrixCoeff_le` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* We apply [the sparse kernel](/chapter/comparison-operator-1/#sparse-theta-kernels) (`New.Rows.exists_norm_modKernel_sub_fockInner_le`) with scale $c = q_1/\varpi^2$, separation $b^6$ and exponent $2n_*$. We check its hypotheses.

1. Integrality: if $z \equiv 0 \bmod \varpi^2$, then $z = \varpi^2 y$ and $c\,\alpha z = q_1\alpha y$, which is integral as $q_1\alpha$ is.
2. Separation: $|\Phi_w(c)| = q_1/M$, since $\varpi\bar\varpi = M$. The lemma on short vectors ([sparse theta kernels](/chapter/comparison-operator-1/#sparse-theta-kernels), `New.Rows.firstMinimum_mul_le_hom`) gives that the first minimum of the lattice of homomorphisms is at least $b^{-13}/(6\,\mathrm{cond}\,(ft)^2t^2)$. The data make $b^6 q_1/M$ smaller than $\sqrt{2\pi\,\mathrm{Im}\,\Phi_w(j)}$ times this.
3. Dimension: the number of variables is $f\,\mathrm{rank}V\,\mathrm{rank}V' \leq ft^2 < 2n_* = 4ft^3$.
4. The ratio: $100(d + 4n_*)/b^{12} \leq b^{-10}$, from $d \leq b\sqrt b$ and the data.

The sparse kernel then bounds the difference by $(b^{-10})^{2n_*}(|h||h'|)^{6n_*}|c_Q(1,1)|$, and $b^{-20n_*}$ is this factor. $\square$

### Step 1: integrals are combinations

**Proposition (Step 1).** Let $o$ put the signs $+1$ first, let $\varphi^\circ$ be rapidly decreasing of every level, and let $m_{u_1}$ be integrable. Let $g_1 \in U(S)$ and let $\Psi$ be a datum modulo $\varpi^2$. Let $\theta[\Psi, P]$ be the kernel of $(S, \widetilde W)$ with characters $\upsilon^m$ and $\beta_j$. Then there are numbers $c_i$ such that for every $g$ in $U(W_j)$,
$$\sum_i c_i\,\mathsf{F}_i(g) = \int_{U(S)_\infty}\varphi^\circ(g_1 h)\,\theta[\Psi, P]\bigl(g_1 h, (g, 1)\bigr)\,m_{u_1}(h)\,dh.$$

Lean: `New.Data.exists_sum_choiceFn_eq_integral` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Step (a), reproduction. We have $2\cdot 3m < 6m + 1$, so there is an embedding $e$ of the indices of $S$ into those of $W^\flat$. Let $\delta$ be the indicator of the inclusion matrix of $e$ modulo $\varpi^2$. For a row choice $r$, let $Q_r$ be the product of determinants that pairs the short rows of the class $r$ with the variables. The reproducing formula `New.Rows.reproducing_formula_modKernel` of [neighbours and reproduction](/chapter/siegel-weil/) gives numbers $c_r$ such that for every $\psi$ rapidly decreasing of level $\varpi^2$,
$$\int\psi(g_1 h)\,m_{u_1}(h)\,dh = \sum_r c_r\int_{[U(S)]}\psi\,\theta_{2,r},$$
where $\theta_{2,r}$ is the kernel of $(S, W^\flat)$ at the class $r$ with datum $\delta$ and polynomial $Q_r$. Its hypotheses are: $u_1 = (-\Delta'; 6m+1)$ is $K$-dominant, the power of one minor is holomorphic data (`New.Rows.prod_variableMinor_mem_holomorphicData`), and its translates lie in the span of the $Q_r$, since the short rows of each class form an invertible matrix (`New.Rows.realPairWeil_mem_span_pairedDetProd`).

Step (b), Fourier expansion. The function $z \mapsto \Psi(z_1)\delta(z_2)$ on matrices modulo $\varpi^2$ is $\sum_\Lambda f_\Lambda\,\psi_\Lambda$, where $\psi_\Lambda$ is the additive character of trace with $\Lambda$ (`New.exists_sum_smul_addChar_trace_eq`, [FiniteFourier.lean](lean:Lib/General/Analysis/FiniteFourier.lean#L147)). This is Fourier inversion on a finite group, as the trace character is primitive.

Step (c), seesaw. The product of a kernel of $(S, \widetilde W)$ and a kernel of $(S, W^\flat)$ is the kernel of $(S, \widetilde W \oplus W^\flat)$ with the product datum and polynomial (`New.modKernel_sum_right`, [the pair and its kernel](/chapter/theta-lifts-seesaw/)). The kernel is linear in the datum. So $\theta_1(g)\,\theta_{2,r} = \sum_\Lambda f_\Lambda\,\theta_{(\Lambda, r)}(g)$, where $\theta_{(\Lambda, r)}$ is the kernel in the definition of $\mathsf{F}_{(\Lambda, r)}$.

Step (d), level. $\varphi^\circ\theta_1(g)$ and $\varphi^\circ\theta_{(\Lambda, r)}(g)$ are rapidly decreasing of level $\varpi^2$ (`New.Rows.mul_modKernel_mem_rapidOfLevel`). So
$$\int\varphi^\circ\theta_1(g)\,\theta_{2,r} = \sum_\Lambda f_\Lambda\,\mathsf{F}_{(\Lambda, r)}(g).$$

Put $c_{(\Lambda, r)} = c_r f_\Lambda$. Then $\sum_i c_i\mathsf{F}_i(g) = \sum_r c_r\int\varphi^\circ\theta_1(g)\theta_{2,r}$, which is the integral of the claim by step (a) with $\psi = \varphi^\circ\theta_1(g)$. $\square$

### Step 3: the approximation

**Lemma (A reproducing integral).** Let $f$ be holomorphic of weight $(0; 3m)$ for $o$, and let the second character have weight $m - \mu_1^+$. If $f\,c_P(\cdot, 1)\,m_{u_1}$ is integrable, then
$$\int f(h)\,c_P(h, 1)\,m_{u_1}(h)\,dh = J\,f(1)\,c_P(1, 1),\qquad J = \int|m_{u_3}|^2.$$

Lean: `New.Data.integral_mul_polyMatrixCoeff_paddedMinorProd` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* By the factoring lemma the integrand is $\bigl(f\,m_{u_1}\,c_P(1,1)m_{u_2}\bigr)\overline{m_{u_3}}$. The product of holomorphic functions of weights $(0;3m)$, $u_1$ and $u_2$ is holomorphic of weight $u_3$, by the identity on the weights. The reproducing formula of [the holomorphic case](/chapter/discrete-series/#the-holomorphic-case-the-cusp-kernel-and-the-character-wave) (`New.IsHolOfWeight.integral_mul_conj_holMinorsPi`) gives $J$ times the value at $1$, which is $f(1)\,c_P(1,1)$ as $m_{u_1}(1) = m_{u_2}(1) = 1$. $\square$

**Theorem (Approximation).** There are a bounded function $\mathsf{F}^0$ on the real group of $W_j$ with $\mathsf{F}^0(1) \neq 0$, and for every $g$ with $\lambda_1(g) \geq (5b^{24})^{-1/2}$ numbers $c_i$, such that for all real $h$,
$$\Bigl|\sum_i c_i\,\mathsf{F}_i(g h) - \mathsf{F}^0(h)\Bigr| \leq 2b^{-19n_*}\,|\mathsf{F}^0(1)|\,|h|^{6n_*}.$$

Lean: `New.Data.exists_choiceFn_approx` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* By [the carrier](/chapter/comparison-operator-2/#the-carrier), $\varphi^\circ$ is rapidly decreasing of every level and holomorphic of weight $(0; 3m)$ for some $o$ that puts the signs $+1$ first. Take a peak $g_1$ of $\varphi^\circ$, so $|\varphi^\circ(x)| \leq 2|\varphi^\circ(g_1)|$ and $\lambda_1(g_1) \geq (5b\sqrt b)^{-1/2}$. Let $c_P$ have weights $m$ and $m - \mu_1^+$, with bound $B$ and $c_P(1,1) \neq 0$. Write $\iota h = (h, 1, 1)$ and
$$\mathsf{F}^0(h) = \int\varphi^\circ(g_1 h')\,c_P(h', \iota h)\,m_{u_1}(h')\,dh'.$$

The bound. Let $A$ be continuous with $|A(h')| \leq C|h'|^{6n_*}$. Then $|\varphi^\circ(g_1h')A(h')| \leq 2|\varphi^\circ(g_1)|C|h'|^{6n_*}$. By the weight bounds and the ranks, [integrals against $m_{u'}$](/chapter/comparison-operator-1/#isolation) applies with $u = u_3$, $u' = u_1$. So the integral of $\varphi^\circ(g_1\cdot)Am_{u_1}$ exists and has modulus at most $2|\varphi^\circ(g_1)|\,C\,b^{n_*}J$. Also $J > 0$ (`New.Data.integral_norm_holMinorsPi_sq_pos`, [ThetaKernelEstimates.lean](lean:New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean#L787), the positivity part of the weighted integral in [isolation](/chapter/comparison-operator-1/#isolation)).

With $A = c_P(\cdot, \iota h)$ and $C = B$ (as $|h'| \geq 1$), $\mathsf{F}^0$ is defined and bounded by $2|\varphi^\circ(g_1)|Bb^{n_*}J$. By the reproducing integral, $\mathsf{F}^0(1) = J\,\varphi^\circ(g_1)\,c_P(1,1)$, which is nonzero.

Now let $\lambda_1(g) \geq (5b^{24})^{-1/2}$. By the product of first minima, $\lambda_1^S(g_1)\lambda_1^{\widetilde W}(g, 1) \geq b^{-13}$. The ranks are at most $t$, $\upsilon^m$ has weight $m$, $\beta_j$ has weight $m - \mu_1^+$, and $P$ has degree at most $b\sqrt b$. So sparse sums give $\Psi$ with
$$\bigl|\theta[\Psi, P](g_1h', (g,1)\iota h) - c_P(h', \iota h)\bigr| \leq b^{-20n_*}(|h'||\iota h|)^{6n_*}|c_P(1,1)|.$$
By Step 1, with $m_{u_1}$ integrable by [isolation](/chapter/comparison-operator-1/#isolation), there are $c_i$ with $\sum_i c_i\mathsf{F}_i(x)$ equal to the integral of $\varphi^\circ(g_1h')\theta[\Psi, P](g_1h', (x, 1))m_{u_1}(h')$. As $(gh, 1) = (g, 1)\iota h$, the difference $\sum_i c_i\mathsf{F}_i(gh) - \mathsf{F}^0(h)$ is the integral of $\varphi^\circ(g_1h')A(h')m_{u_1}(h')$ with $A = \theta[\Psi, P] - c_P$. The bound with $C = b^{-20n_*}|\iota h|^{6n_*}|c_P(1,1)|$ and $|\iota h| \leq |h|$ give
$$\leq 2|\varphi^\circ(g_1)|\,b^{-20n_*}|h|^{6n_*}|c_P(1,1)|\,b^{n_*}J = 2b^{-19n_*}|\mathsf{F}^0(1)|\,|h|^{6n_*}. \qquad\square$$

**Remark (Formalization).** In Lean the function $\mathsf{F}^0$ is a Bochner integral. Where the integrand is not integrable, Lean gives the junk value $0$. The proof shows integrability for every $h$ before it uses the value, so the junk value does not occur.
