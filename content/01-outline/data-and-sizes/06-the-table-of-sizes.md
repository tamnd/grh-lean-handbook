---
title: The table of sizes
lean:
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/LevelAndTwists.lean
decls:
  - New.Data.HasLogBound
  - New.Data.lt_of_hasLogBound
  - New.Data.le_of_hasLogBound
  - New.Data.nat_le_of_hasLogBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The table of sizes

This section collects every size of the data in one table, which later chapters cite by row. It then explains the automation `HasLogBound` by which the source proves most rows.

### The table

All bounds hold for every choice of data $D$. In the last column, a name without a namespace is in `New.Data`. The letters are those of Sections 2 to 5: $L = \log x$, $\Delta = 2r^8$, $\kappa$ is the weight of a place, $\kappa^{(i)}$ and $\kappa_j$ are the shifted weights, and $s_\infty$ is the jet size.

| Quantity | Size | Lean |
|---|---|---|
| $C_P$ | $64 \leq C_P$ and $q_0, d, \varphi(q_0) \leq C_P$ | `le_constantBound` |
| $\log\log b$ | $10^{12} C_P \leq \log\log b \leq \log x / 100$ | (S1), (S2) |
| $x_1$ | $x^{10^6} \leq x_1$ | `x_pow_le_x₁` |
| $b$ | $x_1^{10^6} \leq b$ | `x₁_pow_le_b` |
| $\log b$ | $(\log x_1)^6 \leq \log b$ and $(\log b)^{100} \leq x$ | `logX₁_pow_le_logB`, `logB_pow_le_x` |
| $m$ | $\sqrt x \leq m \leq 2\sqrt x$, $x \leq m^2 \leq 4x$ | `m_mem`, `m_sq_mem_Icc` |
| $m$ | $10^4 \leq m$, $m$ even, $m = 2^{e+1}$ | `ten_thousand_le_m`, `m_even` |
| $s$ | $s = 22(e + 1) \leq 32 \log x$, $2^s = m^{22}$ | `towerExp_le`, `m_pow_eq_two_pow_towerExp` |
| $l_0$ | $27 s < l_0 \leq 81 s$, $m^{594} \leq 2^{l_0}$ | `New.mul_lt_l₀`, `New.l₀_le_mul`, `m_pow_le_two_pow_l₀` |
| $r$ | $x^5 \leq r \leq 3x^5$, $r = 3^{e+1}$, $r$ odd | `r_mem`, `r_odd` |
| $k = r + 1 - m$ | $r + 1 = k + m$, $100m \leq k \leq r \leq 2k$, $k$ even | `r_add_one`, `hundred_mul_m_le_k`, `k_le_r`, `r_le_two_mul_k`, `k_even` |
| $t = 5r$ | $r + 6 \leq t$, $t$ odd | `r_add_six_le_t`, `t_odd` |
| $n_j = k + j(t+1)$ | $n_j$ even, $x^{11/2} \leq n_m \leq e^{12} x^{11/2}$ | `n_even`, instance |
| $\tfrac12\Delta = r^8$ | $k + t + 1 \leq r^8$, $x^{40} \leq r^8 \leq e^{25}x^{40}$ | `k_add_t_add_one_le_halfGap`, instance |
| $\Delta = 2r^8$ | $x^{40} \leq \Delta \leq e^{27} x^{40}$ | instance |
| $\operatorname{towerDeg}(s) = \#\Phi_a$ | $x^{11} \leq \operatorname{towerDeg}(s) \leq x^{11}(\log b)^{1/5}$ | instance, `card_aPlaces` |
| $f$ | $x^{11} \leq m^{22} = 2^s \leq f \leq q_1$, $f$ even | `f_mem_Icc`, `f_even` |
| $q_1$ | $q_1 \leq x^{12}$ | `q₁_le` |
| $q_2$ | $q_2 \leq x^{33 q_0 d}$ | `q₂_le` |
| $\mathrm{rd}_E$ | $x^{10} \leq \mathrm{rd}_E \leq x^{12}$ | `rootDisc_mem_Icc` |
| $\Omega$ | $x^{-13} \leq \Omega \leq 1$ | `bigOmega_le_one`, instance |
| $h_E$ | $\log h_E \leq x^{30}$ | `log_classNumber_le` |
| $x_1^{3l_0^2}$ | $x_1^{3 l_0^2} \leq \sqrt b$ | `x₁_pow_le_sqrt_b` |
| $\Phi_b$ | $\operatorname{towerDeg}(s) \leq \#\Phi_b \log b$ | `towerDeg_le_card_bPlaces_mul` |
| $a = xb$ | $q_1 x_1 \mid a$, $x^{999} \leq a/x_1 \leq b/x^{999}$ | `q₁_mul_natX₁_dvd_a`, `a_div_x₁_mem_Icc` |
| $\kappa$ | $a/x_1 \leq \kappa \leq b$, $\kappa + x^{42} \leq 2b$, $q_1 \mid \kappa$ | `weight_mem_Icc`, `weight_add_x_pow_le_two_mul_b`, `q₁_dvd_weight` |
| $\kappa^{(i)}$, $i \leq 4m$ | $\kappa \leq \kappa^{(i)} \leq \kappa + x^{42}$, $\log\kappa^{(i)} \leq \log\kappa + 1/x$ | `shiftedWeight_mem_Icc`, `log_shiftedWeight_le` |
| $\kappa_j$, $j \leq 2m$ | $\kappa_j \leq 2b$, $\kappa \leq \kappa_j - \tfrac12\Delta$ | `liftWeight_le_two_mul_b`, `weight_le_liftWeight_sub` |
| $p_0, p_1$ | $b^{10} \leq p_i \leq b^{11}$, $b^2 < p_i < N$ | `levelPrime_mem`, `levelPrime_mem_Ioo` |
| $p_0, p_1$ | $p_i \equiv 1 \pmod{q_2^2}$, so $p_i \equiv 1 \pmod{q_1 d}$ | `levelPrime_modEq_one` |
| $M = p_0 p_1$ | $b^{20} \leq M \leq b^{22}$ | `M_mem_Icc` |
| $M/\Omega$ | $20\log b \leq \log(M/\Omega) \leq 23 \log b$ | `log_M_div_bigOmega_mem_Icc` |
| $M\,\mathrm{rd}_E/2\pi$ | $\lvert\log(M\,\mathrm{rd}_E/2\pi)\rvert \leq 23\log b$ | `abs_log_M_mul_rootDisc_le` |
| $N_-$ | $m\log b \leq \log N_- \leq 24 m \log b$ | `logLevelTarget_mem_Icc` |
| $N$ | $m\log b \leq \log N \leq 30 m\log b$, $b^{101} \leq N$ | `log_N_mem_Icc`, instance |
| $s_\infty(j)$, $j \leq a$ | $20 j\log b \leq s_\infty(j) \leq 25 j\log b$ | `jetSize_mem_Icc` |
| $\mathrm{err}$ | $\mathrm{err} = f a \log^3 b$ | `errorUnit` |

The word "instance" means that the bound is an instance of `New.Data.HasLogBound`, which the next subsection explains. The rows for $\mathrm{rd}_E$, $h_E$ and $N_-$ are the three rows with an outside input: the theorem on the root discriminant (Volume 9), the bound for the class number by Minkowski's method, and the bounds for the root discriminant and the weights in the theorem on $N_-$.

### The degree in $x$

On the logarithmic scale each quantity has a degree in $x$: the number $\delta$ with $\log F \approx \delta \log x$. The degree makes the table easy to remember.

Degree $0$ or nearly $0$: $s$, $l_0$, $q_0$, $d$, $C_P$ and $\log b \leq x^{1/100}$. Degree $\tfrac12$: $m$. Degree $5$: $r$, $k$, $t$. Degree $\tfrac{11}2$: $n_m$. Degree $11$: $2^s$, $f$, $\operatorname{towerDeg}(s) = \#\Phi_a$, and, after rounding, $q_1$, $\mathrm{rd}_E$ and $1/\Omega$. Degree $40$: $\tfrac12\Delta$ and $\Delta$. Degree at least $10^6$: $x_1$, $b$, $a$, the weights, $M$ and $N$.

A product has the sum of the degrees, and a sum has the larger degree. For example, the main amount is at least $x^4 f a$ (`New.Data.le_mainAmount`), while the error unit $f a \log^3 b$ exceeds $f a$ by at most the factor $x^{3/100}$. So the two differ by a factor of degree at least $3.97$.

### The automation

**Definition (Logarithmic bounds).** Let $D$ be data, $u$ a Boolean, $F$ and $l$ real numbers. The statement $\mathrm{HasLogBound}(D, u, F, l)$ is
$$\lvert F\rvert \leq e^{l} \ \text{ if } u \text{ is true}, \qquad e^{l} \leq F \ \text{ if } u \text{ is false}.$$
The two cases are written `HasLogUpper` and `HasLogLower`. The number $l$ is an upper or a lower exponent of $F$.

Lean: `New.Data.HasLogBound`, `New.Data.HasLogUpper`, `New.Data.HasLogLower` (New/Reduction/Data/Magnitudes.lean).

The statement does not depend on $D$; the argument $D$ lets instances and default proofs use the data. A lower exponent gives $F > 0$ (`New.Data.HasLogBound.pos`).

**Lemma (Comparison by exponents).** If $l$ is an upper exponent of $F$, $l'$ is a lower exponent of $G$, and $l < l'$, then $F < G$, and so $F \leq G$.

Lean: `New.Data.lt_of_hasLogBound`, `New.Data.le_of_hasLogBound`, `New.Data.nat_lt_of_hasLogBound`, `New.Data.nat_le_of_hasLogBound` (New/Reduction/Data/Magnitudes.lean).

*Proof.* $F \leq \lvert F\rvert \leq e^{l} < e^{l'} \leq G$. $\square$

**Remark (Formalization).** The lemma is simple, but the way the source uses it is not. The class has the exponent $l$ as an output parameter, so Lean finds $l$ by instance search from the shape of $F$. The source gives instances for the basic quantities, as in the table, and rules for building new ones:

1. $1$ has exponent $0$; $e^{c}$ has exponent $c$; a nonzero natural number $A$ has lower exponent $0$ and upper exponent $A$ (a rule of low priority);
2. a product $FG$ has exponent $l + l'$, a power $F^A$ has $A l$, and $\sqrt F$ has $l/2$;
3. a sum $F + G$ has lower exponent $\max(l, l')$ and upper exponent $\max(l, l') + 1$;
4. an inverse $F^{-1}$ has upper exponent $-l$ if $l$ is a lower exponent of $F$, and a quotient is a product with an inverse;
5. a difference $F - G$ has upper exponent $\max(l, l') + 1$;
6. $\log b$ and $\log x_1$ have exponents $\log\log b$ and $\log\log x_1$, and further rules treat $s$, $\log F$, finite sums and factorials.

Then `le_of_hasLogBound` has a default argument for $l < l'$. Its proof clears all hypotheses except $D$ and calls `grind` with the five scale inequalities (`New.Data.scale_inequalities`). The inequality $l < l'$ is linear in the six numbers $\log x$, $\log x_1$, $\log b$, $\log\log x_1$, $\log\log b$, $C_P$, with $\max$ and case splits, so `grind` decides it. In the source many rows of the table have the one line proof `D.le_of_hasLogBound` or `D.nat_le_of_hasLogBound`, for example `New.Data.q₁_le`, `New.Data.hundred_mul_m_le_k` and `New.Data.k_add_t_add_one_le_halfGap`.

The exponents are crude. The rule for sums adds $1$ at each step, and the rule for natural numbers gives the useless upper exponent $A$ when no better instance exists. The method works because the scale inequalities leave a large margin. In each comparison that the source proves in this way, the two exponents differ by much more than the constants that the rules add, and these constants are small against $\log x$.

**Example (The automation at work).** Consider the row $k + t + 1 \leq \tfrac12\Delta$ (`New.Data.k_add_t_add_one_le_halfGap`). Instance search finds:

1. the upper exponent $5L + 3$ of $k$ and the upper exponent $5L + 8$ of $t$;
2. by the rule for sums, the upper exponent $\max(5L + 3, 5L + 8) + 1 = 5L + 9$ of $k + t$;
3. by the same rule and the exponent $0$ of $1$, the upper exponent $\max(5L + 9, 0) + 1 = 5L + 10$ of $k + t + 1$;
4. the lower exponent $5L$ of $r$, so the lower exponent $8 \cdot 5L = 40L$ of $\tfrac12\Delta = r^8$.

The default argument must show $5L + 10 < 40L$. This holds since $L \geq 6.4 \cdot 10^{15}$ by the scale inequalities, and `grind` finds it. In the same way, the row for $n_m = k + m(t + 1)$ comes from the upper exponents $5L + 3$, $\tfrac12 L + 2$ and $5L + 8$ and gives $n_m \leq e^{5.5L + 12}$, while the lower exponents $5L - 2$, $\tfrac12 L$ and $5L$ give $n_m \geq e^{5.5 L}$.

