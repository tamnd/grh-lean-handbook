---
title: The reference table
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/Reduction/PrimeSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The reference table

This section is the table. It has seven groups: the parameters, the scales, the ranks, the field, the weights, the primes and the level, and the error terms. Each row gives a quantity, its bound exactly as Lean states it, the declaration with the file and the line, and a short note on where the argument uses the bound.

### Conventions of the table

The letters are those of [notation and conventions](/chapter/notation/) and of [the data and its sizes](/chapter/data-and-sizes/). Write $L = \log x$. The number $s$ is the exponent of the tower (`towerExp`), $l_0 = 3^{\lfloor \log_3 s \rfloor + 4}$, $\kappa$ is the weight of an infinite place $\sigma$ of $E$, $\kappa^{(i)} = \kappa + (i+1) r^8$ is a shifted weight, $\kappa_j = \kappa^{(2j)}$ is the weight of the $j$-th lift, and $\Delta = 2r^8$ is the gap.

A declaration whose name has no namespace is in `New.Data`. A file whose name has no folder is in `New/Reduction/Data/`. The abbreviations are AD for AdmissibleData.lean, FP for FieldsAndPlaces.lean, Mg for Magnitudes.lean, Sz for Sizes.lean, and LT for LevelAndTwists.lean. The word "field" means a field of the structure `New.Data` or `New.Parameters`. The word "instance" means an anonymous instance of the size automation `HasLogBound`. An instance with the exponent $l$ for the quantity $y$ says $\lvert y \rvert \leq e^l$ (the upper form) or $e^l \leq y$ (the lower form). The table writes the bound that the instance gives, for example $x^{40} \leq r^8 \leq e^{25} x^{40}$.

The column "Use" names a file of the source that cites the declaration by name, or says "automation" when the source uses the bound only through `le_of_hasLogBound` and `grind`. The column does not list every use. Files in the column are under `New/`.

### Group 1: the parameters

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| $18480 \mid q_0$ | field `New.Parameters.dvd_q₀`, FP:70 | the choice $q_0 = 18480\,q$ in `New.grh` |
| $d$ prime | field `New.Parameters.d_prime`, FP:72 | the field $K = \mathbb{Q}(\sqrt{-d})$ |
| $q_0 \mid 2(d+1)$, $q_0 \nmid d+1$ | field `New.Parameters.q₀_dvd_and_not_dvd`, FP:74 | the splitting of the primes in $E$ |
| $64 < d$ | `New.Parameters.sixty_four_lt_d`, FP:136 | `le_constantBound` |
| $64 \leq C_P$; $q_0, d, \varphi(q_0) \leq C_P$ | `le_constantBound`, Mg:56 | automation (Mg:164) |
| $C_P \leq \log b$ | instance, Mg:430 | automation |

### Group 2: the scales

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| (S1) $10^{12} C_P \leq \log\log b$ | field `constantBound_le`, AD:98 | all constants of $P$ |
| (S2) $100 \log\log b \leq L$ | field `mul_log_logB_le_logX`, AD:100 | $\log b$ against $x$ |
| (S3) $10^6 L \leq \log x_1$ | field `logX_le_logX₁`, AD:102 | $x$ against $x_1$ |
| (S4) $10^6 \log x_1 \leq \log b$ | field `logX₁_le_logB`, AD:104 | $x_1$ against $b$ |
| (S5) $6 \log\log x_1 \leq \log\log b$ | field `log_logX₁_le_log_logB`, AD:106 | powers of $\log x_1$ against $\log b$ |
| (S1) to (S5) together | `scale_inequalities`, Mg:77 | automation, in each `grind` call |
| $x^{10^6} \leq x_1$ | `x_pow_le_x₁`, Sz:46 | statement form only |
| $x_1^{10^6} \leq b$ | `x₁_pow_le_b`, Sz:52 | statement form only |
| $(\log x_1)^6 \leq \log b$ | `logX₁_pow_le_logB`, Sz:58 | statement form only |
| $(\log b)^{100} \leq x$ | `logB_pow_le_x`, Sz:63 | statement form only |

"Statement form only" means that the source does not cite the lemma by name. Its proofs use the logarithmic fields through the automation.

### Group 3: the ranks

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| $e^{L/2} \leq m \leq 2e^{L/2}$ | field `m_mem`, AD:114 | the saving $1/m$; the shape, $\varrho = m/2 - 1$ |
| $m = 2^{e+1}$, $s = 22(e+1)$ | field `exists_m_eq_two_pow`, AD:118 | $m^{22} = 2^s$ |
| $x \leq m^2 \leq 4x$ | `m_sq_mem_Icc`, Sz:69 | Determinant/Exchange/ConeImage |
| $10^4 \leq m$; $m$ even | `ten_thousand_le_m`, Mg:436; `m_even`, Mg:159 | UpperBound/Objects/Weights and others |
| $s \leq 32 L$; $s \neq 0$ | field `towerExp_le`, AD:122; `towerExp_ne_zero`, Sz:80 | `q₂_le` |
| $m^{22} = 2^s$ | `m_pow_eq_two_pow_towerExp`, Sz:108 | `f_mem_Icc`, `m_pow_le_two_pow_l₀` |
| $27 s < l_0$; $l_0 \leq 81 s$ | `New.mul_lt_l₀`, FP:92; `New.l₀_le_mul`, FP:97 | `x₁_pow_le_sqrt_b` |
| $m^{594} \leq 2^{l_0}$ | `m_pow_le_two_pow_l₀`, Sz:116 | UpperBound/Divisibility/MarkedPrimes |
| $x_1^{3 l_0^2} \leq \sqrt{b}$ | `x₁_pow_le_sqrt_b`, Sz:87 | UpperBound/Divisibility/MarkOperator |
| $e^{5L} \leq r \leq 3e^{5L}$ | field `r_mem`, AD:116 | the number of Bessel indices |
| $r = 3^{e'+1}$; $r$ odd | field `exists_r_eq_three_pow`, AD:120; `r_odd`, Mg:153 | UpperBound/Objects/Rows |
| $k = r + 1 - m$; $r + 1 = k + m$ | def `k`, AD:200; `r_add_one`, Mg:440 | the rank $k$ of the shape |
| $100 m \leq k \leq r \leq 2k$ | `hundred_mul_m_le_k`, Mg:572; `k_le_r`, Mg:445; `r_le_two_mul_k`, Sz:103 | UpperBound/Objects/Weights |
| $0 < k$; $k$ even | `k_pos`, Mg:576; `k_even`, Mg:586 | UpperBound/Objects/Parameters |
| $t = 5r$; $r + 6 \leq t$; $t$ odd | def `t`, AD:203; `r_add_six_le_t`, Mg:596; `t_odd`, Mg:593 | Determinant/Chain/ChainNorms |
| $n_j = k + j(t+1)$; $n_j$ even | def `n`, AD:225; `n_even`, UpperBound/Objects/Weights.lean:125 | the ranks of the lifts |
| $x^{5.5} \leq n_m \leq e^{12} x^{5.5}$ | instance, Mg:498 | automation |
| $k + t + 1 \leq r^8$ | `k_add_t_add_one_le_halfGap`, Mg:605 | UpperBound/Objects/Rows |
| $x^{40} \leq r^8 \leq e^{25} x^{40}$ | instance, Mg:520 | automation |
| $x^{40} \leq \Delta \leq e^{27} x^{40}$ | instance, Mg:525 | automation |

The instances for $m$, $r$, $k$ and $t$ are at Mg:420, 425, 448 and 456. They give $\sqrt{x} \leq m \leq e^2 \sqrt{x}$, $x^5 \leq r \leq e^3 x^5$, $e^{-2} x^5 \leq k \leq e^3 x^5$ and $x^5 \leq t \leq e^8 x^5$.

### Group 4: the field

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| $\operatorname{towerDeg}(s) = 3 l_0 2^s$ | `New.towerDeg_eq`, FP:106 | the order of the roots of unity |
| $x^{11} \leq \operatorname{towerDeg}(s) \leq x^{11} (\log b)^{1/5}$ | instance, Mg:472 | automation |
| $q_1 = q_0 \operatorname{towerDeg}(s)$; $q_1 \leq x^{12}$ | `New.Parameters.q₁`, FP:110; `q₁_le`, Sz:141 | Reduction/Data/Existence |
| $f = \operatorname{towerDeg}(s)\,\varphi(q_0)$ | `New.Parameters.numInfPlaces_E`, FP:353 | `hasLogBound_f` |
| $m^{22} \leq f \leq q_1$; $f$ even | `f_mem_Icc`, Sz:125; `f_even`, Sz:135 | Congruences/FirstOrder/DenominatorBound |
| $x^{11} \leq f \leq e^{C_P} x^{11} (\log b)^{1/5}$ | instance `hasLogBound_f`, Mg:487 | automation |
| $q_2 = (q_0 d)^{s+6} \leq x^{33 q_0 d}$ | `New.Parameters.q₂`, FP:175; `q₂_le`, Sz:146 | UpperBound/Objects/LiftChains |
| $x^{10} \leq \mathrm{rd}_E \leq x^{12}$ | `rootDisc_mem_Icc`, Derivatives/Field/ChosenPlaces.lean:433 | the instance for $\Omega$ |
| $x^{-13} \leq \Omega \leq 1$ | `bigOmega_le_one`, Sz:213; instance, LT:184 | `log_M_div_bigOmega_mem_Icc` |
| $\log h_E \leq x^{30}$ | `log_classNumber_le`, Sz:161 | Congruences/FitTwistsExist |
| $\operatorname{towerDeg}(s) \leq \#\Phi_b \log b$ | field `towerDeg_le_card_bPlaces_mul`, AD:132 | Reduction/OneSidedBound |
| $\Phi_b$ sparse | field `sparse`, AD:134 | Derivatives/Sharpness/NearPairs |
| $\#\Phi_a = \operatorname{towerDeg}(s)$ | `card_aPlaces`, Reduction/PrimeSums.lean:79 | the count of the $a$-places |

### Group 5: the weights

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| $a = xb$; $q_1 x_1 \mid a$ | `cast_a`, Mg:87; `q₁_mul_natX₁_dvd_a`, Mg:92 | `cast_offWeight`, `q₁_dvd_weight` |
| $q_1 x_1 \mid b$ | field `dvd_natB`, AD:124 | `q₁_mul_natX₁_dvd_a` |
| $a/x_1$ is exact | `cast_offWeight`, Mg:96 | `cast_weight` |
| $x^{999} \leq a/x_1 \leq b/x^{999}$ | `a_div_x₁_mem_Icc`, Sz:182 | statement form only |
| $\kappa = b$ on $\Phi_b$, $\kappa = a/x_1$ off $\Phi_b$ | field `weight_eq`, AD:138; `cast_weight`, Mg:112 | OneLift/HeckeValues/CharacterLift |
| $q_1 \mid \kappa$ | `q₁_dvd_weight`, Mg:127 | Derivatives/Field/ChosenPlaces |
| $a/x_1 \leq \kappa \leq a/x$ | `weight_mem_Icc`, LT:57 | Reduction/PrimeSums |
| $b/x_1 \leq \kappa \leq b$ | instance, LT:64; `weight_le_b`, LT:69 | automation |
| $\kappa + x^{42} \leq 2b$ | `weight_add_x_pow_le_two_mul_b`, LT:73 | Derivatives/Sharpness/Cases |
| $\kappa \leq \kappa_j - r^8$ | `weight_le_liftWeight_sub`, LT:79 | UpperBound/Divisibility/JetExponent |
| $i \leq 4m$: $\kappa \leq \kappa^{(i)} \leq \kappa + x^{42}$ | `shiftedWeight_mem_Icc`, LT:88 | `liftWeight_le_weight_add` |
| $i \leq 4m$: $\log \kappa^{(i)} \leq \log \kappa + 1/x$ | `log_shiftedWeight_le`, LT:97 | `log_liftWeight_le` |
| $j \leq 2m$: $\kappa_j \leq \kappa + x^{42}$ | `liftWeight_le_weight_add`, LT:109 | OneLift/HeckeValues/AlgebraicPartSize |
| $j \leq 2m$: $\kappa_j \leq 2b$ | `liftWeight_le_two_mul_b`, LT:114 | Determinant/AuxiliaryForms/Turns |
| $j \leq 2m$: $\log \kappa_j \leq \log \kappa + 1/x$ | `log_liftWeight_le`, LT:131 | Spanning/Unfolding/FillingAdmissible |

### Group 6: the primes and the level

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| $b^{10} \leq p_i \leq b^{11}$ | field `levelPrime_mem`, AD:148 | `M_mem_Icc`; `New.Data.filling` |
| $b^2 < p_i < N$ | `levelPrime_mem_Ioo`, Sz:206 | UpperBound/Size/ShortColumns |
| $p_i \equiv 1 \pmod{q_2^2}$; $p_0 \neq p_1$ | fields `levelPrime_modEq_one_q₂_sq`, AD:144, and `levelPrime_injective`, AD:146 | the splitting of $p_i$ in $E$ |
| $p_i \equiv 1 \pmod{q_1 d}$ | `levelPrime_modEq_one`, Mg:144 | Derivatives/Field/ChosenPlaces |
| $b^{20} \leq M \leq b^{22}$ | `M_mem_Icc`, Mg:508; instance, Mg:515 | `logLevelTarget_mem_Icc` |
| $20 \log b \leq \log(M/\Omega) \leq 23 \log b$ | `log_M_div_bigOmega_mem_Icc`, Sz:219 | UpperBound/Size/ArchimedeanSize |
| $\lvert \log(M\,\mathrm{rd}_E/2\pi) \rvert \leq 23 \log b$ | `abs_log_M_mul_rootDisc_le`, Sz:232 | UpperBound/Size/ArchimedeanSize |
| $\log N_- \in [m \log b, 24 m \log b]$ | `logLevelTarget_mem_Icc`, LT:212 | `log_N_mem_Icc` |
| $\log N \in [\log N_-, \log N_- + \sqrt{\log b}]$ | field `log_N_mem`, AD:160 | `log_N_mem_Icc_logLevelTarget` |
| $\log N \in [m \log b, 30 m \log b]$ | `log_N_mem_Icc`, LT:234 | `New.Data.N_le_pow` |
| $\sqrt{x} \log b \leq \log N \leq e^{32} \sqrt{x} \log b$ | instance, LT:242 | automation |
| $b^{101} \leq N$; $N$ prime | instance, LT:251; field `N_prime`, AD:156 | `levelPrime_mem_Ioo` |
| $N \equiv 1 \pmod{q_1 d}$ | `N_modEq_one`, LT:222 | the splitting of $N$ in $E$ |

Here $\log N_-$ is `logLevelTarget` (LT:198), the logarithm of $\bar\kappa^m (M\,\mathrm{rd}_E/2\pi)^{m-1} b^{-15/2}$, where $\bar\kappa$ is the geometric mean of the weights.

### Group 7: the error terms

| Quantity and bound | Lean, place | Use |
|-------------|------------------|---------|
| unit $f a (\log b)^3$ | def `errorUnit`, AD:255 | Theorems A(b) and B |
| $j \leq a$: $20 j \log b \leq s_\infty(j) \leq 25 j \log b$ | `jetSize_mem_Icc`, Reduction/PrimeSums.lean:235 | UpperBound/Size/ArchimedeanSize |
| main amount $\geq x^4 f a$ | `le_mainAmount`, Reduction/PrimeSums.lean:289 | `mainAmount_nonneg`, which `New.star_inequality` uses |
| $m \cdot$ remainder $\leq f a (\log b)^5$ | `New.star_inequality`, Reduction/MainInequality.lean:87 | `primeRemainder_le` |

Section 5 explains the error terms. The jet size is $s_\infty(j) = \log j! + j \log(M/\Omega)$ (`jetSize`, AD:259).

**Remark (Formalization).** The table gives each bound in the form of the source, so some rows overlap. For example, the instance for $\kappa$ at LT:64 says $b/x_1 \leq \kappa \leq b$, while `weight_mem_Icc` says $a/x_1 \leq \kappa \leq a/x$. These agree, since $a/x = b$ and $a/x_1 = xb/x_1 \geq b/x_1$. The instance is weaker at the lower end. The automation needs only the weaker form, because every use compares $\kappa$ with a power of $x$ or with $b$.

**Remark (Formalization).** Three rows describe instances that have no name. The source cannot cite them by name, and so the handbook cannot list them in `decls:`. The rows give the line of the instance. A reader finds the instance at that line, or asks Lean with `inferInstance` for a goal of the form `D.HasLogBound u y l`.

**Remark (Formalization).** The table states $b^{10} \leq p_i \leq b^{11}$ from the field `levelPrime_mem`, not from the lemma `levelPrime_mem_Ioo`. The lemma states only the weaker $b^2 < p_i < N$, and it is the form that UpperBound/Size/ShortColumns needs. The register of findings records this as F-119. The research note b, §1.4, gives the range of $p_i$ as $(b^2, N)$. That is the lemma, not the size of the data.

### The table in degrees

On the scale of $x$, the ranks and the field have the following degrees:

$$\begin{gathered}
\deg m = \tfrac12, \quad \deg r = \deg k = \deg t = 5, \quad \deg n_m = \tfrac{11}{2}, \\
\deg f = 11, \quad \deg \mathrm{rd}_E \in [10, 12], \quad \deg \Delta = 40.
\end{gathered}$$

The degree of $f$ is $11$ up to the factor $e^{C_P}(\log b)^{1/5}$, and $(\log b)^{1/5} \leq x^{1/500}$ by (S2). The number $\Omega$ has degree in $[-13, 0]$. All weights, primes and levels have a degree in $b$: $\kappa$ has degree $1$ up to a power of $x$ or $x_1$, the primes $p_i$ have degree in $[10, 11]$, $M$ has degree in $[20, 22]$, and $N$ has degree in $[m, 30m]$. So $N$ is the only quantity that is large on the scale of $b$: it is a power of $b$ whose exponent is about $\sqrt{x}$.
