---
title: The error budget
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/PrimeSums.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
decls:
  - New.star_inequality
  - New.Data.primeRemainder_le
  - New.eventually_abs_primeRemainder_exp_le
  - New.eventually_primeRemainder_natCast_le
  - New.eventually_primeRemainder_le_rpow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The error budget

This section follows the error terms from the main inequality to the exponent $-\tfrac12 + \varepsilon$. At each step it names the size bound that pays for the step. The proofs themselves are in [the main inequality and the end of the proof](/chapter/main-inequality/) of Volume 1. Here the interest is in the sizes.

### The main inequality

**Theorem (Main inequality).** For all data $D$, $m \cdot \mathrm{rem} \leq f a (\log b)^5$, where $\mathrm{rem}$ is the total remainder of the data.

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

The theorem is at MainInequality.lean:87. The total remainder is a weighted sum of prime sums less their expected values. By `New.Data.totalRemainder_eq` (Reduction/PrimeSums.lean:177),
$$\mathrm{rem} = a\bigl(\#\Phi_b\,(R_{q_0}(x) - R_{q_0}(x_1)) + \#\Phi_a\, R_1(x_1)\bigr),$$
where $R_q$ is the prime remainder of [the weighted prime remainder](/chapter/weighted-prime-remainder/), $\Phi_b$ is the set of $b$-places and $\Phi_a$ is the set of $a$-places.

### The three errors per dimension

The proof compares an upper bound and a lower bound for the covolume of a lattice of dimension $\dim$. Per dimension, each bound is the main amount plus errors. The header of MainInequality.lean lists the errors in this table, copied here with the source's names:

| Source | Where | Amount |
|----------|-------------|-----------------------|
| size | Theorem A (a) | $f a (\log b)^4$ |
| index | Theorems A (b) and B | $20 \log(1 + 2b^2) \cdot f a (\log b)^3$ |
| covolume | Theorem C | $3 f a (\log b)^4$ |

The index enters twice, and the table shows the doubled amount. The unit $f a (\log b)^3$ is `New.Data.errorUnit` (AdmissibleData.lean:255).

In the proof, write $\ell = f a (\log b)^4$ (the variable `loss`) and $\iota = 10 \log(1 + 2b^2) \cdot f a (\log b)^3$ (the variable `indexPerDim`). The proof finds $n$ linearly independent forms. Each form has squared length at most $\exp(\mathrm{main} - m\,\mathrm{rem} + \ell)$, the index of the family is at most $\dim \cdot \iota$, and Theorem C gives
$$\dim\,(\mathrm{main} - 3\ell) \leq n\,(\mathrm{main} - m\,\mathrm{rem} + \ell) + 2\dim\,\iota.$$
With $n \leq \dim$ and $\mathrm{main} + \ell \geq 0$, the main amounts cancel, and
$$n \cdot m\,\mathrm{rem} \leq \dim \cdot (4\ell + 2\iota).$$

### The sizes that close the main inequality

Two size bounds close the proof.

First, the family is large: $n \geq (1 - 4/b^2)\dim$, from Theorem B (`New.Data.enough_forms`, Reduction/ShortAndEnough.lean:448). The proof uses $4/b^2 \leq \tfrac12$, so $\dim \leq 2n$. This needs only $b \geq 3$, a tiny part of what the scales give.

Second, the errors are of lower order: $\lvert 2(4\ell + 2\iota) \rvert \leq f a (\log b)^5$. The source proves it by `le_of_hasLogBound`. By hand, $\log(1 + 2b^2) \leq 2 \log b + 2$, so
$$2(4\ell + 2\iota) \leq f a (\log b)^3 \bigl(8 (\log b) + 40(2 \log b + 2)\bigr) = f a (\log b)^3 (88 \log b + 80),$$
and this is at most $f a (\log b)^5$ once $\log b \geq 89$. The scales give $\log b \geq 6.4 \cdot 10^{27}$ (Section 2). So the margin is huge.

Then $n \cdot m\,\mathrm{rem} \leq \dim \cdot (4\ell + 2\iota) \leq 2n (4\ell + 2\iota) \leq n f a (\log b)^5$, and division by $n > 0$ gives the theorem.

**Remark (Formalization).** The main amount is bounded below by $x^4 f a$ (`New.Data.le_mainAmount`, Reduction/PrimeSums.lean:289). The main inequality uses only its consequence $\mathrm{main} \geq 0$ (`New.Data.mainAmount_nonneg`, line 295). The lower bound $x^4 f a$ shows the scale of the cancellation: the main amount is larger than the final error $f a (\log b)^5$ by the factor $x^4 / (\log b)^5$, which is at least $x^{3.95}$ by (S2). The two sides of the comparison agree to this relative precision. The proof of $x^4 f a \leq \mathrm{main}$ compares $x^4 f a$ with $m k\, b \operatorname{towerDeg}(s)$. Since $f a = \varphi(q_0) \operatorname{towerDeg}(s)\, x b$, this is $\varphi(q_0)\, x^5 \leq m k$. It holds since $m k \geq e^{-2} x^{11/2}$ and $\varphi(q_0) \leq C_P$ is tiny against $\sqrt{x}$.

### From the main inequality to the prime remainder

**Lemma (The prime remainder at $x$).** For all data $D$,
$$R_{q_0}(x) \leq \frac{\varphi(q_0) (\log b)^6}{m} + \lvert R_{q_0}(x_1) \rvert + \log b \cdot \lvert R_1(x_1) \rvert.$$

Lean: `New.Data.primeRemainder_le` (New/Reduction/OneSidedBound.lean).

*Proof.* By the formula for $\mathrm{rem}$,
$$R_{q_0}(x) = \frac{\mathrm{rem}}{a\,\#\Phi_b} + R_{q_0}(x_1) - \frac{\#\Phi_a}{\#\Phi_b} R_1(x_1).$$
The main inequality gives $\mathrm{rem} \leq f a (\log b)^5 / m$. The field gives $f = \#\Phi_a\,\varphi(q_0)$ (`New.Data.f_eq_card_aPlaces_mul`, Reduction/PrimeSums.lean:83, with `New.Data.card_aPlaces`). The data give $\#\Phi_a = \operatorname{towerDeg}(s) \leq \#\Phi_b \log b$ (the field `towerDeg_le_card_bPlaces_mul`). So $\#\Phi_a/\#\Phi_b \leq \log b$, and the first term is at most $\varphi(q_0) (\log b)^6 / m$. Bound the other two terms by their absolute values. $\square$

The lemma is at OneSidedBound.lean:33. The size facts in it are the saving $1/m$ from the main inequality and the ratio $\#\Phi_a / \#\Phi_b \leq \log b$. The ratio costs one power of $\log b$. So the $b$-places must be a large share of all places: at least a fraction $1/\log b$. The construction gives this share while it keeps the $b$-places sparse (Section 4).

### The remainders at $x_1$

**Lemma (The remainders at a huge scale).** Let $\varepsilon > 0$. For every large enough integer $x$ and every $l \geq x^{\varepsilon/12}$, one has $\lvert R_{q_0}(e^l) \rvert \leq x^{-2}$ and $\lvert R_1(e^l) \rvert \leq x^{-2}$.

Lean: `New.eventually_abs_primeRemainder_exp_le` (New/Reduction/OneSidedBound.lean).

*Proof.* Choose a natural number $B \geq 24/\varepsilon$. The prime number theorem of the source (`New.eventually_abs_primeRemainder_le`, Reduction/Zeros/PrimeNumberTheorem.lean:217) gives $\lvert R_q(y) \rvert \leq (\log y)^{-B}$ for all large $y$, for $q = q_0$ and $q = 1$. At $y = e^l$ with $l \geq x^{\varepsilon/12}$, this is at most $x^{-\varepsilon B/12} \leq x^{-2}$. $\square$

The lemma is at OneSidedBound.lean:95. It is applied with $l = \log x_1 \geq x^{\varepsilon/12}$ (Section 4). This is the reason for the size of $x_1$. The prime number theorem in the source gives only a saving of a power of $\log y$, so $R(x_1)$ is small against $x^{-1/2}$ only when $\log x_1$ is a power of $x$. The scale inequality (S3), $\log x_1 \geq 10^6 \log x$, gives only $\lvert R(x_1) \rvert \leq (10^6 \log x)^{-B}$, which is not enough.

### The final bound

**Lemma (The one-sided bound at integers).** Let $0 < \varepsilon < 1/100$. For every large enough integer $x$,
$$R_{q_0}(x) \leq (64\,\varphi(q_0) + 3)\, x^{-1/2 + 6\varepsilon}.$$

Lean: `New.eventually_primeRemainder_natCast_le` (New/Reduction/OneSidedBound.lean).

*Proof.* Take $D$ with $D.x = x$, $\log b \leq 2x^\varepsilon$, $\sqrt{x} \leq m$ and $\log x_1 \geq x^{\varepsilon/12}$ (`New.eventually_exists_data_scales`). Insert the bounds into the lemma for $R_{q_0}(x)$:
$$R_{q_0}(x) \leq \frac{\varphi(q_0)\,(2x^\varepsilon)^6}{x^{1/2}} + x^{-2} + 2x^\varepsilon x^{-2} = 64\,\varphi(q_0)\, x^{-1/2 + 6\varepsilon} + x^{-2} + 2x^{-2 + \varepsilon}.$$
Both $x^{-2}$ and $x^{-2+\varepsilon}$ are at most $x^{-1/2 + 6\varepsilon}$. $\square$

The lemma is at OneSidedBound.lean:125. The exponent $6\varepsilon$ is the cost of $(\log b)^6$ with $\log b \approx x^\varepsilon$. The constant $64 = 2^6$ comes from $\log b \leq 2x^\varepsilon$.

**Theorem (One-sided bound).** Let $q_0 > 0$ be a multiple of $18480$, let $d \equiv q_0/2 - 1 \pmod{q_0}$ be a prime, and let $\varepsilon > 0$. Then $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for all large real $y$.

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

The theorem is at OneSidedBound.lean:200. Its proof takes $\delta = \min(1/200, \varepsilon/7)$, applies the integer bound with $\delta$, and passes from $\lfloor y \rfloor$ to $y$ with an error $26/y$. The constant $2(64\varphi(q_0) + 3) + 26$ is absorbed into $y^\delta$. This is the step where the condition $\varepsilon < 1/100$ of the construction disappears: the theorem holds for every $\varepsilon > 0$.

### The budget in one line

The whole budget is
$$R_{q_0}(x) \leq \underbrace{\varphi(q_0) \frac{(\log b)^6}{m}}_{\text{main inequality}} + \underbrace{(1 + \log b)\, x^{-2}}_{\text{remainders at } x_1}.$$

The first term needs $m$ large and $\log b$ small: $m \geq \sqrt{x}$ and $\log b \leq 2x^\varepsilon$. The second term needs $\log x_1$ large: $\log x_1 \geq x^{\varepsilon/12}$. The construction meets both needs with $\log x_1 \approx x^{\varepsilon/6}$ and $\log b \approx x^\varepsilon$, so $\log x_1 \approx (\log b)^{1/6}$. This is the order that (S5) records. Section 7 explains why the other scale conditions are needed by the parts of the proof between the data and the main inequality.
