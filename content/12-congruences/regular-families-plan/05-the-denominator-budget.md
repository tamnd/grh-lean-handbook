---
title: The denominator budget
lean:
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/LocalLoss/Basic.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.twistError
  - New.Selmer.crystallineLoss
  - New.Selmer.defectBound
  - New.Selmer.localDefectBound
  - New.Selmer.oddClassBound
  - New.Selmer.oddClassBound_le
  - New.Selmer.denominatorError
  - New.Selmer.clearingBound
  - New.Selmer.add_denominatorError_le_mul_clearingBound
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
## The denominator budget

This section defines every constant of the bound for denominators and proves that the constants fit the budget. This is Step 4 of the plan. The source does it in full in the top file `FitTwistsExist.lean`, and this section follows it line by line.

### The idea

All the constants are $\ell$-adic valuations of fixed integers, or small multiples of them. The main tool is the identity
$$\sum_{\ell} v_\ell(A) \log \ell = \log A$$
for a positive integer $A$, the sum over all primes. So a constant of the form $v_\ell(A)$ costs $\log A$ in total, summed with the weights $\log \ell$. The only constant that is not of this form is the term $2^{-\ell}$ of the twist error, and it costs at most $2$. The local loss is the largest term. It costs about $f (m/k)\, b \log b$, and this is less than the budget $f\, x b \log^3 b/(m k)$ because $m^2$ is about $x$.

### The constants

The integer $N_g$ = `D.chosenGroupOrder` is the order of the product of the groups $\mathrm{GL}_{r t}(k_w)$ over the chosen places $w$. It is the order of the finite group that acts on the forms at the chosen places.

**Definition (The twist error).** For a prime $\ell$, put
$$e'_\ell = \mathrm{twistError}(\ell) = (4f + 3)\, r\, v_\ell(N_g) + (1/2)^{\ell}.$$

Lean: `New.Selmer.twistError` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

The number $e'_\ell$ bounds three things at a good twist: the lengths of the Selmer groups, the ramification of the twist, and the valuations of the ratios of $L$-values. The term $(1/2)^{\ell}$ is positive. Without it, $e'_\ell$ would be $0$ for every prime $\ell$ that does not divide $N_g$, and the twisting theorem would then have to give Selmer groups of length $0$ and ratios that are units. The positive term gives room, and its sum with the weights $\log \ell$ is at most $2$.

**Definition (The crystalline loss).** For natural numbers $h$, $b$ and $l$, put
$$\mathrm{crystallineLoss}(h, b, l) = v_l\Big((2b)! \cdot \Big(\prod_{b - 30h^3 < k \leq b + 30h^3} k\Big)^{h^3}\Big).$$

Lean: `New.Selmer.crystallineLoss` (New/Congruences/LocalLoss/Basic.lean).

**Remark (Formalization).** The definition is `@[irreducible]`, so other proofs see only its stated properties. The lower end $b - 30h^3$ is a truncated subtraction of natural numbers: it is $0$ if $30 h^3 > b$. Then the product starts at $1$. For the data, $b$ is much larger than $30 h^3$, so this case does not occur, but the definition does not use this.

**Definition (The local defect bounds).** With $b$ = `D.natB` the weight as a natural number, $h$ = `D.halfGap` $= r^8$ and $M$ = `D.M` the product of the two level primes, put
$$\mathrm{defectBound}(l) = 10^6 \cdot \frac{m}{k} \cdot \big(b\, v_l(M) + \mathrm{crystallineLoss}(h, b, l)\big), \qquad \mathrm{localDefectBound}(\ell) = 4 f \cdot \mathrm{defectBound}(\ell).$$

Lean: `New.Selmer.defectBound` (New/Congruences/LocalLoss/Basic.lean).

Lean: `New.Selmer.localDefectBound` (New/Congruences/FirstOrder/TraceRelations.lean).

The local defect is the loss of the local conditions above $\ell$ and at the level. Its proof is in [the local loss](/chapter/local-loss/). The factor $m/k$ is a real quotient, not a quotient of natural numbers.

**Definition (The odd class bound).** The number `oddClassBound` $D$ is a positive integer whose $\ell$-adic valuation bounds the lengths of the groups of odd classes `shaOdd`, for all large coefficient rings, all Tate twists $e < t$ and all exponents $\nu$. It satisfies
$$\mathrm{oddClassBound}(D) \leq 2^{4(N + t + 3)^{27}} \cdot h_E,$$
where $N$ is the cyclotomic conductor of the data and $h_E$ is the class number of $E$.

Lean: `New.Selmer.oddClassBound` (New/Congruences/FirstOrder/TraceRelations.lean).

Lean: `New.Selmer.oddClassBound_le` (New/Congruences/FirstOrder/TraceRelations.lean).

**Remark (Formalization).** The number is chosen with `Classical.choose` from the library lemma `exists_length_shaOdd_le`. Its properties are only those of the lemma: it is not zero (`New.Selmer.oddClassBound_ne_zero`), the bound above holds, and the length bound holds eventually for large coefficient rings (`New.Selmer.eventually_length_shaOdd_le`). The group `shaOdd` is a group of Galois cohomology classes of $E$ with coefficients in Tate twists of $O/\ell^{\nu}$. It is defined in the library of the source, and it is not the Tate-Shafarevich group of an abelian variety.

**Definition (The error term).** Put
$$e_\ell = \mathrm{denominatorError}(\ell) = t\, v_\ell(\mathrm{odd}) + 8 f t\, v_\ell(N_g) + 2\, v_\ell(N_g) + \big((4t + 1) h^{22} + h\big)\, v_\ell(N_g),$$
with $\mathrm{odd} = \mathrm{oddClassBound}(D)$, as an element of $[0, \infty]$.

Lean: `New.Selmer.denominatorError` (New/Congruences/FirstOrder/TraceRelations.lean).

By its docstring, the four terms pay for the class group and the odd classes, the places above $p_0 p_1$, the idempotent and the automorphisms, and the congruences between the characters $O(-e)$.

**Definition (The clearing bound).** Put
$$\beta_\ell = \mathrm{clearingBound}(\ell) = \mathrm{localDefectBound}(\ell) + (1 + 2t)\, e'_\ell + e_\ell + v_\ell(N_g).$$

Lean: `New.Selmer.clearingBound` (New/Congruences/FirstOrder/TraceRelations.lean).

In Lean the term $e_\ell$ enters through `ENNReal.toNNReal`. Since $e_\ell$ is finite, this is its value.

The constants are in the table.

| Constant | Value | Sum with weights $\log \ell$ |
|---|---|---|
| $e'_\ell$ | $(4f+3) r v_\ell(N_g) + 2^{-\ell}$ | at most $x^{999}$ |
| $\mathrm{localDefectBound}(\ell)$ | $4f \cdot 10^6 (m/k)(b v_\ell(M) + \mathrm{crystallineLoss})$ | at most $4 \cdot 10^6 e^{180} f (m/k) b \log b$ |
| $v_\ell(\mathrm{odd})$ | | at most $x^{2000}$ |
| $e_\ell$ | combination of $v_\ell(\mathrm{odd})$ and $v_\ell(N_g)$ | at most $x^{4000}$ |
| $v_\ell(N_g)$ | | at most $\log N_g$ |
| $v_\ell(h_{\mathrm{std}})$ | | at most $x^{30}$ |
| $\beta_\ell$ | the sum of the rows above | with $v_\ell(h_{\mathrm{std}})$, at most the budget |

### The arithmetic lemma

**Lemma (The clearing bound per row).** Let $1 \leq r' \leq r$, $t' \leq t$, and $\mathrm{sel}, \mathrm{ram} \leq e'_\ell$ in $[0, \infty]$. Then
$$\mathrm{sel} + 2 t' \cdot \mathrm{ram} + r' \cdot \mathrm{localDefectBound}(\ell) + e_\ell + v_\ell(N_g) \leq r' \cdot \beta_\ell .$$

Lean: `New.Selmer.add_denominatorError_le_mul_clearingBound` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Since $r' \geq 1$, it is enough to bound each term by $r'$ times the matching term of $\beta_\ell$. We have $\mathrm{sel} + 2t' \cdot \mathrm{ram} \leq (1 + 2t)\, e'_\ell \leq r'(1 + 2t)\, e'_\ell$. The local term is $r' \cdot \mathrm{localDefectBound}(\ell)$ on both sides. Also $e_\ell \leq r' e_\ell$ and $v_\ell(N_g) \leq r' v_\ell(N_g)$. Add the four bounds. $\square$

The left side, without $v_\ell(N_g)$, is $\mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel})$ for a pair $O$ with $\#r = r'$ rows and the rank difference $t'$ (Section 4). The lemma is used once, with $\mathrm{sel} = \mathrm{ram} = e'_\ell$, in the proof of the operator form of the bound for denominators.

### Sums of valuations

**Lemma (Sums of valuations).** Let $T$ be a finite set of primes and $a \leq b$ natural numbers. Then
$$\sum_{l \in T} v_l(a) \log l \leq \log b .$$

Lean: `New.Selmer.sum_padicValNat_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* The valuation $v_l(a)$ is the exponent of $l$ in the factorization of $a$. The sum over $T$ is at most the sum over $T$ together with the prime factors of $a$, since all terms are nonnegative. That sum is $\log a$. Then $\log a \leq \log b$. For $a = 0$, all valuations are $0$ and the sum is $0 \leq \log b$, with the convention $\log 0 = 0$ of Mathlib. $\square$

**Lemma (The small terms).** For every finite set $T$ of natural numbers,
$$\sum_{l \in T} (1/2)^{l} \log l \leq 2 .$$

Lean: `New.Selmer.sum_half_pow_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Since $\log l \leq l$, each term is at most $l\,(1/2)^{l}$. The full series is $\sum_{l \geq 0} l\, z^{l} = z/(1 - z)^2$ with $z = 1/2$, which is $2$. A finite partial sum of nonnegative terms is at most the full sum. $\square$

### The local loss

**Lemma (The product in the crystalline loss).** With $b$ = `D.natB` and $h = r^8$,
$$\prod_{b - 30h^3 < k \leq b + 30h^3} k \leq (b + 30h^3)^{60 h^3}.$$

Lean: `New.Selmer.prod_Ioc_natB_le_pow` (New/Congruences/FitTwistsExist.lean).

*Proof.* The interval has at most $60 h^3$ elements, also with the truncated subtraction, and each factor is at most $b + 30h^3 \geq 1$. $\square$

**Lemma (The sum of the defect bounds).** For every finite set $T$ of primes,
$$\sum_{l \in T} \mathrm{defectBound}(l) \log l \leq 10^6 \frac{m}{k}\Big(b \log M + \log\big((2b)! \cdot ((b + 30h^3)^{60h^3})^{h^3}\big)\Big).$$

Lean: `New.Selmer.sum_defectBound_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Expand the definition. The sum is $10^6 (m/k)$ times $b \sum v_l(M) \log l + \sum v_l(P) \log l$, where $P = (2b)! \cdot (\prod k)^{h^3}$ and the crystalline loss is $v_l(P)$. The lemma on sums of valuations gives $\log M$ for the first sum. For the second, the previous lemma gives $P \leq (2b)! \cdot ((b + 30h^3)^{60h^3})^{h^3}$, and the lemma on sums of valuations applies again. $\square$

**Lemma (Bound for the local loss).** For every finite set $T$ of primes,
$$\sum_{l \in T} \mathrm{localDefectBound}(l) \log l \leq 4 \cdot 10^6 e^{180} \cdot f \cdot \frac{m}{k} \cdot b \log b .$$

Lean: `New.Selmer.sum_localDefectBound_mul_log_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* The sum is $4f$ times the sum of the defect bounds. It remains to bound the bracket $b \log M + \log((2b)! \cdot (b + 30h^3)^{60 h^6})$ by $e^{180}\, b \log b$. This is a comparison of sizes from [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes), and the source proves it with `New.Data.le_of_hasLogBound`. That lemma compares two quantities through bounds for their logarithms, and it checks the inequality between the exponents with the tactic `grind` and the list of scale inequalities of the data. The size of the terms is as follows. The term $\log (2b)!$ is at most $2b \log(2b)$. The level primes are small against $b$, so $b \log M$ is a small multiple of $b \log b$. The last term is $60 h^6 \log(b + 30h^3)$, and $h^6 = r^{48}$ is a power of $x$, far below $b$. $\square$

### The negligible terms

**Lemma (The odd classes are few).** The numbers $v_\ell(\mathrm{oddClassBound}(D))$ are negligible with the exponent $2000$.

Lean: `New.Selmer.isNegligible_padicValNat_oddClassBound` (New/Congruences/FitTwistsExist.lean).

*Proof.* The valuations are nonnegative. By the lemma on sums of valuations and the bound for the odd class bound, the weighted sum is at most $\log(2^{4(N+t+3)^{27}} h_E) = 4(N+t+3)^{27} \log 2 + \log h_E$. The class number has $\log h_E \leq x^{30}$ (`New.Data.log_classNumber_le`). The sum of the two terms is at most $x^{2000}$ by a comparison of sizes. $\square$

**Lemma (The twist errors are negligible).** The numbers $e'_\ell$ are negligible with the exponent $999$.

Lean: `New.Selmer.isNegligible_twistError` (New/Congruences/FitTwistsExist.lean).

*Proof.* The weighted sum is $(4f + 3) r \sum v_l(N_g) \log l + \sum (1/2)^{l} \log l$. The two lemmas on sums give at most $(4f+3) r \log N_g + 2$. This is at most $x^{999}$ by a comparison of sizes. $\square$

**Lemma (The error terms are negligible).** The real values of $e_\ell$ are negligible with the exponent $4000$.

Lean: `New.Selmer.isNegligible_denominatorError` (New/Congruences/FitTwistsExist.lean).

*Proof.* The value $e_\ell$ is a natural number (`New.Selmer.denominatorError_eq_natCast`). It is $t\, v_\ell(\mathrm{odd}) + c\, v_\ell(N_g)$, with $c = 8ft + 2 + (4t+1) h^{22} + h$. So the weighted sum is at most $t x^{2000} + c \log N_g$, by the lemma on the odd classes and the lemma on sums of valuations. This is at most $x^{4000}$ by a comparison of sizes. $\square$

**Lemma (The class numbers of $U(1)$).** Let $h_{\mathrm{std}}$ be the number of classes `StdClasses` of $U(1)$ at the level `D.chosenLevel`. The numbers $v_\ell(h_{\mathrm{std}})$ are negligible with the exponent $30$.

Lean: `New.Selmer.isNegligible_padicValNat_card_stdClasses` (New/Congruences/FitTwistsExist.lean).

*Proof.* By `New.Data.card_stdClasses_le_exp`, $h_{\mathrm{std}} \leq \exp(x^{30})$. The lemma on sums of valuations gives the weighted sum at most $\log h_{\mathrm{std}} \leq x^{30}$. $\square$

### The budget is enough

**Theorem (The clearing bounds fit the budget).** For every finite set $T$ of primes,
$$\sum_{\ell \in T} \big(\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell\big) \leq \mathrm{denominatorBudget} = \frac{f\, a \log^3 b}{m k}.$$

Lean: `New.Selmer.sum_clearingBound_add_padicValNat_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Split the sum into five sums: the local loss, $(1+2t)$ times the twist errors, the error terms, the valuations of $N_g$, and the valuations of $h_{\mathrm{std}}$. The lemmas above bound the sum by
$$4 \cdot 10^6 e^{180} f \frac{m}{k} b \log b + (1 + 2t) x^{999} + x^{4000} + \log N_g + x^{30}.$$
This is at most the budget by a comparison of sizes. $\square$

The comparison of the first term with the budget shows why the number $m$ of lifts must not be much larger than $\sqrt{x}$ here. The quotient of the first term by the budget, with $a = x b$, is
$$\frac{4 \cdot 10^6 e^{180} f (m/k)\, b \log b}{f\, x b \log^3 b/(m k)} = \frac{4 \cdot 10^6 e^{180}\, m^2}{x \log^2 b}.$$
If $m^2 \leq 4x$, the quotient is at most $16 \cdot 10^6 e^{180}/\log^2 b$, which is very small, since $\log b \geq 10^{12} \log x$. If $m$ were as large as $\sqrt{x} \log b$, the quotient would be of size $4 \cdot 10^6 e^{180}$, and this proof would fail. The other four terms are powers of $x$, or $\log N_g$, and they are far below the budget, which is of size $f\, b \log^3 b \cdot x^{-4.5}$ with $b \geq x^{10^{12}}$.

**Remark (Formalization).** All sums in this section are over finite sets $T$ of primes. The source never forms an infinite sum over all primes. This is the form of the definitions `IsDenominatorBound` and `IsNegligible` in Section 3, and of the definition of heights in Section 2.
