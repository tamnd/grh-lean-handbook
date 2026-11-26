---
title: The sums over the primes
lean:
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.sum_padicValNat_mul_log_le
  - New.Selmer.sum_half_pow_mul_log_le
  - New.Selmer.prod_Ioc_natB_le_pow
  - New.Selmer.sum_defectBound_mul_log_le
  - New.Selmer.sum_localDefectBound_mul_log_le
  - New.Selmer.isNegligible_padicValNat_oddClassBound
  - New.Selmer.isNegligible_twistError
  - New.Selmer.isNegligible_denominatorError
  - New.Selmer.isNegligible_padicValNat_card_stdClasses
  - New.Selmer.sum_clearingBound_add_padicValNat_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The sums over the primes

Section 5 gives, at each prime $\ell$, the bounds $e'_\ell$ for the ratios and $\gamma_\ell$ for the denominators. A regular family needs bounds summed over all primes: $\sum_\ell e'_\ell \log \ell \leq x_1$ for the heights, and $\sum_\ell \gamma_\ell \leq \mathrm{denominatorBudget}$ for the denominators. This section proves both. Each sum is a weighted sum of $\ell$-adic valuations of fixed integers, plus the sum of $2^{-\ell}\log \ell$. Each weighted sum of valuations is at most the logarithm of the integer.

In this section $T$ is a finite set of primes. All the sums run over $\ell \in T$.

### The constants

The numbers are defined in other files. They are recalled here exactly, with $v_\ell$ = `padicValNat ℓ`, $b$ = `D.natB`, $h$ = `D.halfGap` $= r^8$ and $M$ = `D.M`.

| Name | Lean | Value |
|---|---|---|
| crystalline loss | `crystallineLoss h b ℓ` | $v_\ell\big((2b)! \cdot \Pi^{h^3}\big)$, $\Pi = \prod_{b - 30h^3 < k \leq b + 30h^3} k$ |
| local loss | `defectBound D ℓ` | $10^6 \frac{m}{k}\big(b\, v_\ell(M) + \mathrm{crystallineLoss}(h, b, \ell)\big)$ |
| local defect | `localDefectBound D ℓ` | $4 f \cdot \mathrm{defectBound}(\ell)$ |
| twist error $e'_\ell$ | `twistError ℓ D` | $(4f + 3)\, r\, v_\ell(N_g) + (1/2)^\ell$ |
| error $e_\ell$ | `denominatorError D ℓ` | $t\, v_\ell(\mathrm{odd}) + 8 f t\, v_\ell(N_g) + 2 v_\ell(N_g) + \big((4t + 1) h^{22} + h\big) v_\ell(N_g)$ |
| clearing bound $\beta_\ell$ | `clearingBound D ℓ` | $\mathrm{loc}_\ell + (1 + 2t)\, e'_\ell + e_\ell + v_\ell(N_g)$ |

Here $\mathrm{odd}$ = `oddClassBound D` is the chosen bound for the odd classes. The subtraction $b - 30h^3$ is truncated at $0$. The crystalline loss is in `New/Congruences/LocalLoss/Basic.lean`, the twist error in `New/Congruences/GaloisRepresentations/SelmerHypotheses.lean`, and the other three in `New/Congruences/FirstOrder/TraceRelations.lean`. [The constants](/chapter/denominator-bound/#the-constants) explains each term.

**Remark (Formalization).** The local loss, the local defect, the twist error and the clearing bound are in $\mathbb{R}_{\geq 0}$ (`NNReal`). The error $e_\ell$ is in $[0, \infty]$ (`ENNReal`), and the clearing bound uses `toNNReal`, which sends $\infty$ to $0$. This junk value does not occur: $e_\ell$ is the cast of a natural number (`denominatorError_eq_natCast`), so it is finite. The quotient $m/k$ is a division in `NNReal`, with $x/0 = 0$. The bounds below do not need $k \neq 0$, since the same quotient is on both sides.

### Two elementary sums

**Lemma (Valuations and logarithms).** Let $a \leq b$ be natural numbers. Then $\sum_{\ell \in T} v_\ell(a) \log \ell \leq \log b$.

Lean: `New.Selmer.sum_padicValNat_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* For a prime $\ell$, $v_\ell(a)$ is the exponent of $\ell$ in the factorization of $a$. Add the primes of the support of the factorization to $T$. The terms are $\geq 0$, so the sum can only grow. The sum over all primes of the factorization is $\log a$ (`log_nat_eq_sum_factorization`). At last, $\log a \leq \log b$, as the positive part of the logarithm is monotone. For $a = 0$ both $\log 0 = 0$ and $v_\ell(0) = 0$, so the claim holds with the junk values. $\square$

**Lemma (A geometric sum).** For every finite set $T$ of natural numbers, $\sum_{\ell \in T} 2^{-\ell} \log \ell \leq 2$.

Lean: `New.Selmer.sum_half_pow_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Since $\log y \leq y$ for $y \geq 0$, each term is at most $\ell\, 2^{-\ell}$. The terms are $\geq 0$, so the finite sum is at most the full sum
$$\sum_{n \geq 0} n\, 2^{-n} = \frac{1/2}{(1 - 1/2)^2} = 2. \qquad \square$$

### The local loss

**Lemma (The product in the crystalline loss).** With $B = b + 30 h^3$,
$$\prod_{k \in (b - 30h^3,\ b + 30h^3]} k \leq B^{60 h^3}.$$

Lean: `New.Selmer.prod_Ioc_natB_le_pow` (New/Congruences/FitTwistsExist.lean).

*Proof.* The interval has $(b + 30h^3) - (b - 30h^3)$ elements with truncated subtraction, and this is at most $60 h^3$ (`omega`). Each factor is at most $B$. So the product is at most $B^{\#\text{interval}} \leq B^{60h^3}$, where the last step uses $B \geq 1$. Here $h > 0$ follows from $k + t + 1 \leq h$. $\square$

**Lemma (Sum of the local loss).** 
$$\sum_{\ell \in T} \mathrm{defectBound}(\ell) \log \ell \leq 10^6 \frac{m}{k}\Big(b \log M + \log\big((2b)! \cdot (B^{60h^3})^{h^3}\big)\Big).$$

Lean: `New.Selmer.sum_defectBound_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Let $N_\Pi = (2b)! \cdot \Pi^{h^3}$. Then $\mathrm{crystallineLoss}(h, b, \ell) = v_\ell(N_\Pi)$, so the sum is
$$10^6 \frac{m}{k}\Big(b \sum_\ell v_\ell(M) \log \ell + \sum_\ell v_\ell(N_\Pi) \log \ell\Big),$$
after distributing the sum (`push_cast`, `ring`). By the lemma on valuations and logarithms, the first inner sum is at most $\log M$, with $a = b = M$. By the product lemma, $N_\Pi \leq (2b)! \cdot (B^{60h^3})^{h^3}$. So the second inner sum is at most the logarithm of this number. $\square$

**Lemma (Sum of the local defect).**
$$\sum_{\ell \in T} \mathrm{localDefectBound}(\ell) \log \ell \leq 4 \cdot 10^6\, e^{180} \Big(f \frac{m}{k}\, b \log b\Big).$$

Lean: `New.Selmer.sum_localDefectBound_mul_log_le` (New/Congruences/FitTwistsExist.lean).

Here $b = \exp(\log b)$ on the right is the real weight `D.b`. It equals `D.natB` as a real number (`cast_natB`).

*Proof.* The sum is $4f \sum_\ell \mathrm{defectBound}(\ell) \log \ell$. By the last lemma it is enough to bound the bracket:
$$b \log M + \log\big((2b)! \cdot (B^{60h^3})^{h^3}\big) \leq e^{180}\, b \log b.$$
The source proves this with `le_of_hasLogBound` (Section 2). The left side is a sum of the logarithms of numbers of the data, with log bounds from the instances of `New/Reduction/Data/Magnitudes.lean`. The source does not write the comparison out. In outline, $\log M$ and $\log B$ are small against $\log b$, $\log (2b)! \leq 2b \log 2b$, and $60 h^6 \log B$ is small against $b$. The constant $e^{180}$ is what the instances give. $\square$

### The negligible numbers

**Lemma (The odd classes are negligible).** The numbers $v_\ell(\mathrm{odd})$ are negligible with the exponent $2000$.

Lean: `New.Selmer.isNegligible_padicValNat_oddClassBound` (New/Congruences/FitTwistsExist.lean).

*Proof.* The numbers are $\geq 0$. By `oddClassBound_le` (`New/Congruences/FirstOrder/TraceRelations.lean`, line 82), $\mathrm{odd} \leq 2^{4(N_c + t + 3)^{27}} h_E$, where $N_c$ is the cyclotomic conductor and $h_E$ the class number of $E$. So by the lemma on valuations and logarithms,
$$\sum_\ell v_\ell(\mathrm{odd}) \log \ell \leq 4 (N_c + t + 3)^{27} \log 2 + \log h_E.$$
By `log_classNumber_le` (`New/Reduction/Data/Sizes.lean`, line 161), $\log h_E \leq x^{30}$. The rest is $\leq x^{2000}$ by `le_of_hasLogBound`. $\square$

**Lemma (The twist error is negligible).** The numbers $e'_\ell$ are negligible with the exponent $999$.

Lean: `New.Selmer.isNegligible_twistError` (New/Congruences/FitTwistsExist.lean).

*Proof.* The numbers are in `NNReal`, so they are $\geq 0$. The sum splits:
$$\sum_\ell e'_\ell \log \ell = (4f + 3)\, r \sum_\ell v_\ell(N_g) \log \ell + \sum_\ell 2^{-\ell} \log \ell \leq (4f + 3)\, r \log N_g + 2,$$
by the two elementary sums. The right side is $\leq x^{999}$ by `le_of_hasLogBound`. $\square$

**Lemma (The error is negligible).** The numbers $e_\ell$, as real numbers, are negligible with the exponent $4000$.

Lean: `New.Selmer.isNegligible_denominatorError` (New/Congruences/FitTwistsExist.lean).

*Proof.* The numbers are $\geq 0$, as `toReal` of $[0, \infty]$ is. Let $c = 8 f t + 2 + (4t + 1) h^{22} + h$. By `denominatorError_eq_natCast`, $e_\ell = t\, v_\ell(\mathrm{odd}) + c\, v_\ell(N_g)$ as real numbers. So
$$\sum_\ell e_\ell \log \ell = t \sum_\ell v_\ell(\mathrm{odd}) \log \ell + c \sum_\ell v_\ell(N_g) \log \ell \leq t\, x^{2000} + c \log N_g,$$
by the lemma on the odd classes and the lemma on valuations and logarithms. The right side is $\leq x^{4000}$ by `le_of_hasLogBound`. $\square$

**Lemma (The class numbers of $U(1)$ are negligible).** The numbers $v_\ell(h_{\mathrm{std}})$ are negligible with the exponent $30$.

Lean: `New.Selmer.isNegligible_padicValNat_card_stdClasses` (New/Congruences/FitTwistsExist.lean).

*Proof.* The numbers are $\geq 0$. First, $h_{\mathrm{std}} \leq \exp(x^{30})$. This is `card_stdClasses_le_exp` (`New/UpperBound/Size/Estimates.lean`, line 303), for $n$ = `Unit` and $K$ = `D.chosenLevel`. Its two hypotheses are these. The principal level of $\pi_M \pi_N$ lies in the chosen level, by `principalLevel_le_chosenLevel` (`New/UpperBound/Objects/LiftChains.lean`, line 510), since $\pi_M \mid \pi_M \pi_N$. And $\#\mathrm{Unit} = 1 \leq n_m$, by `nat_le_of_hasLogBound`. Now the lemma on valuations and logarithms gives $\sum_\ell v_\ell(h_{\mathrm{std}}) \log \ell \leq \log h_{\mathrm{std}} \leq x^{30}$, since $h_{\mathrm{std}} > 0$. $\square$

### The budget

**Theorem (The sum of the denominator bounds).** 
$$\sum_{\ell \in T} \big(\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell\big) \leq \mathrm{denominatorBudget} = \frac{f a \log^3 b}{m k}.$$

Lean: `New.Selmer.sum_clearingBound_add_padicValNat_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Unfold $\beta_\ell$ and split the sum into five sums. With $\mathrm{loc}_\ell$ = `localDefectBound D ℓ`, the left side is
$$\sum_\ell \mathrm{loc}_\ell \log \ell + (1 + 2t) \sum_\ell e'_\ell \log \ell + \sum_\ell e_\ell \log \ell + \sum_\ell v_\ell(N_g) \log \ell + \sum_\ell v_\ell(h_{\mathrm{std}}) \log \ell.$$
The cast of $e_\ell$ through `toNNReal` and back to $\mathbb{R}$ is `toReal` (`ENNReal.coe_toNNReal_eq_toReal`). Bound the five sums by the lemmas above:
$$\leq 4 \cdot 10^6 e^{180} \Big(f \frac{m}{k} b \log b\Big) + (1 + 2t)\, x^{999} + x^{4000} + \log N_g + x^{30}.$$
The right side is $\leq \mathrm{denominatorBudget}$ by `le_of_hasLogBound`. $\square$

The budget is $f a \log^3 b/(mk)$ with $a = x b$. The main term of the sum is $4 \cdot 10^6 e^{180} f (m/k)\, b \log b$. Its ratio to the budget is $4 \cdot 10^6 e^{180} m^2/(x \log^2 b)$, The source checks that the whole right side is below the budget with one use of `le_of_hasLogBound`, and this chapter does not repeat the check. The other terms are powers of $x$ and $\log N_g$, and they are far smaller than $b$.

### The exponents

The four negligible families have the exponents in this table. Only the twist error enters the heights. The others enter the budget.

| Numbers | Exponent | Bound of the sum | Used for |
|---|---|---|---|
| $v_\ell(\mathrm{odd})$ | $2000$ | $4(N_c + t + 3)^{27} \log 2 + x^{30}$ | the error $e_\ell$ |
| $e'_\ell$ | $999$ | $(4f + 3) r \log N_g + 2$ | the heights and the budget |
| $e_\ell$ | $4000$ | $t x^{2000} + c \log N_g$ | the budget |
| $v_\ell(h_{\mathrm{std}})$ | $30$ | $\log h_{\mathrm{std}}$ | the budget |
