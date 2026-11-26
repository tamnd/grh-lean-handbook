---
title: Near pairs and the losses
lean:
  - New/Derivatives/Sharpness/NearPairs.lean
decls:
  - New.Data.summable_posPart_sub_weight
  - New.Data.notMem_bPlaces_of_two_partners
  - New.Data.IsNearPair
  - New.Data.IsNearPair.ne_d
  - New.Data.IsNearPair.inert_and_odd
  - New.Data.IsNearPair.partner_eq
  - New.Data.IsNearPair.exponent_unique
  - New.Data.IsNearPair.eq_and_eq_of_partner_eq
  - New.Data.IsNearPair.end_ne_start
  - New.padicValNat_mono_of_dvd
  - New.padicValNat_factorial_eq_div_add
  - New.div_sub_one_le_padicValNat_factorial
  - New.Data.lossFactorCount
  - New.Data.lossProduct
  - New.Data.padicValNat_factorial_lossFactorCount_le
  - New.Data.padicValNat_factorial_le_add_lossProduct
  - New.Data.x_pow_le_lossFactorCount
  - New.Data.padicValNat_factorial_mem_Icc_of_le
  - New.Data.padicValNat_factorial_add_add_le
  - New.Data.lossFactorCount_div_sub_one_le
  - New.Data.partnerMinTerm
  - New.Data.partnerMinSum
  - New.Data.mul_sum_weight_sub_localPrimeSumTotal
  - New.Data.partnerMinTerm_add_le
  - New.Data.tsum_partnerMinTerm_add_le
  - New.Data.partnerMinTerm_le_of_not_isNearPair
  - New.Data.partnerMinSum_le
  - New.Data.error_le_padicValNat_lossProduct
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Near pairs and the losses

The second part of the gain is $kF(p)$, where $F(p) = \sum_\sigma s_p(\kappa(\sigma), \sigma)$ compares the weight of each place with the weights of its partners. If a place and all its partners had small weight, $F(p)$ would be close to $\gamma_p\sum_\sigma\kappa(\sigma)$, the full gain per box times the number of boxes. This section measures the difference. It is $v(\pi_p)\sum_\tau R_\tau$, and each $R_\tau$ is small apart from at most one term, the term of a near pair of $b$-places.

These results are used in Volume 11, in [the divisibility is sharp](/chapter/sharpness/). Theorem A does not use them. They sit in this chapter because their file is in this volume and they use the notions of Section 5.

### Background for near pairs

1. The $b$-places are sparse for the primes up to $kt$: for a prime $\ell \le kt$, with $q_1'$ the part of $q_1$ prime to $\ell$ and $0 < i < j < l_0$, there are no $\sigma, \tau, \rho \in \Phi_b$ and signs $\omega, \omega'$ with $\tau/\sigma \equiv \omega\ell^i$ and $\rho/\sigma \equiv \omega'\ell^j$ modulo $q_1'$ ([the data and its sizes](/chapter/data-and-sizes/), Section 4).
2. The numbers $q_0$ and $q_1$ have the same prime factors, so a prime $p \nmid q_1$ is prime to $q_0$ ([fields, places and twists](/chapter/fields-places-twists/), Section 4).
3. The sizes $27s < l_0 \le 81s$ and $k \le 2^s$ hold, with $s$ the tower exponent ([the data and its sizes](/chapter/data-and-sizes/), Section 6).

### Sparseness along the powers of minus p

**Lemma (Two partners).** Let $p \le k$ be a prime with $\chi_K(p) \ne 1$, and let $0 < i < j < l_0$. For every place $\sigma$, the three places $\sigma$, $u(-p)^i\sigma$ and $u(-p)^j\sigma$ are not all $b$-places.

Lean: `New.Data.notMem_bPlaces_of_two_partners` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* By fact 4 of Section 5, $p \nmid q_1$, so $-p$ is prime to $q_0$ by fact 2, and also prime to $q_1$. For every $n$, the class of $u(-p)^n\sigma/\sigma = u((-p)^n)$ modulo $q_1'$ is $(-1)^np^n$. Suppose the three places are $b$-places. Then $\tau = u(-p)^i\sigma$ and $\rho = u(-p)^j\sigma$, with the signs $(-1)^i$ and $(-1)^j$, contradict fact 1 for $\ell = p$. The fact applies since $p \le k \le kt$. $\square$

### Near pairs

**Definition (Near pair).** Let $p$ be a prime. A pair $(\tau, e)$ is a *near pair* if $e \in I_p$, $2e < l_0$, and both $\tau$ and its partner $u(-p^e)\tau$ are $b$-places. The place $\tau$ is the start and $u(-p^e)\tau$ is the end.

Lean: `New.Data.IsNearPair` (New/Derivatives/Sharpness/NearPairs.lean).

**Lemma.** For a near pair $(\tau, e)$: $p \ne d$, $\chi_K(p) = -1$, $e$ is odd and positive, and the end is $u(-p)^e\tau$.

Lean: `New.Data.IsNearPair.ne_d`, `New.Data.IsNearPair.inert_and_odd`, `New.Data.IsNearPair.partner_eq` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Both $b$-places have class $-1$, so the end has the class of the start, and $p \ne d$ by the lemma of Section 5 on the classes at $d$. Then $e \in I_p$ gives $\chi_K(p) = -1$ and $e$ odd. For odd $e$, $-p^e = (-p)^e$, and $u((-p)^e) = u(-p)^e$. $\square$

From now on let $p \le k$ be a prime with $\chi_K(p) \ne 1$.

**Lemma (One exponent at each start).** If $(\tau, e)$ and $(\tau, e')$ are near pairs, then $e = e'$.

Lean: `New.Data.IsNearPair.exponent_unique` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Suppose $e < e'$. Then $0 < e < e'$ and $e' < l_0/2 < l_0$. The places $\tau$, $u(-p)^e\tau$ and $u(-p)^{e'}\tau$ are $b$-places, against the lemma on two partners. $\square$

**Lemma (One pair at each end).** If $(\tau, e)$ and $(\tau', e')$ are near pairs with the same end, then $\tau = \tau'$ and $e = e'$.

Lean: `New.Data.IsNearPair.eq_and_eq_of_partner_eq` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* If $e = e'$, cancel $u(-p)^e$ in $u(-p)^e\tau = u(-p)^e\tau'$. Suppose $e < e'$. Cancel $u(-p)^e$ to get $\tau = u(-p)^{e'-e}\tau'$. The places $\tau'$, $u(-p)^{e'-e}\tau' = \tau$ and $u(-p)^{e'}\tau'$ are $b$-places, with $0 < e' - e < e' < l_0$. This is against the lemma on two partners. $\square$

**Lemma (Ends are not starts).** If $(\tau, e)$ and $(\tau', e')$ are near pairs, then the end of the first is not $\tau'$.

Lean: `New.Data.IsNearPair.end_ne_start` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Suppose $u(-p)^e\tau = \tau'$. The end of the second pair is $u(-p)^{e'}\tau' = u(-p)^{e+e'}\tau$. So $\tau$, $u(-p)^e\tau$ and $u(-p)^{e+e'}\tau$ are $b$-places, with $0 < e < e + e'$ and $e + e' < l_0/2 + l_0/2 = l_0$. This is against the lemma on two partners. $\square$

So the near pairs at $p$ are disjoint: no place is the start of two pairs, the end of two pairs, or the end of one and the start of another.

### Legendre's formula

Write $v$ for the $p$-adic valuation of natural numbers.

**Lemma.** If $a \mid b$ and $b \ne 0$, then $v(a) \le v(b)$. For every $n$, $v(n!) = \lfloor n/p\rfloor + v(\lfloor n/p\rfloor!)$, and so $n/p - 1 \le v(n!)$.

Lean: `New.padicValNat_mono_of_dvd`, `New.padicValNat_factorial_eq_div_add`, `New.div_sub_one_le_padicValNat_factorial` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* The first claim: $p^{v(a)} \mid a \mid b$. For the second, the multiples of $p$ up to $n$ are $p, 2p, \dots, \lfloor n/p\rfloor p$, and their product is $p^{\lfloor n/p\rfloor}\lfloor n/p\rfloor!$. The other factors of $n!$ are prime to $p$. The third claim follows from $\lfloor n/p\rfloor > n/p - 1$. $\square$

**Lemma (Legendre with digits).** If $n < p^K$, then $n/(p-1) - K \le v(n!) \le n/(p-1)$.

Lean: `New.padicValNat_factorial_mem_Icc` (Lib/General/Algebra/IntegralPowerSeries.lean).

*Proof.* By Legendre's formula, $(p-1)v(n!) = n - s_p(n)$, where $s_p(n)$ is the sum of the base $p$ digits of $n$. The number $n$ has at most $K$ digits, each at most $p - 1$. So $0 \le s_p(n) \le K(p-1)$. $\square$

**Lemma.** Let $p \ge 3$ and $n \le 2b$. Then $n/(p-1) - (\log b + 2) \le v(n!) \le n/(p-1)$. If $n_1 + n_2 + n_3 \le 2b$, then
$$v\bigl((n_1+n_2+n_3)!\bigr) \le v(n_1!) + v(n_2!) + v(n_3!) + 3(\log b + 2).$$

Lean: `New.Data.padicValNat_factorial_mem_Icc_of_le`, `New.Data.padicValNat_factorial_add_add_le` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Put $K = \lceil\log b\rceil + 1$. Then $n \le 2e^{\log b} < e\cdot e^{\log b} \le e^K \le p^K$, since $p \ge 3 > e$. The previous lemma gives the bounds with $K < \log b + 2$. For the second claim, apply the upper bound to the sum and the lower bound to each $n_i$. The main terms $n_i/(p-1)$ cancel. $\square$

### The loss product

**Definition (The loss product).** Put $n^\sharp = \lceil 6b/k\rceil$. For $l \in \mathbb{N}$ put $l^- = \max(l - n^\sharp, 0)$ and
$$B_l = (l^- + 1)(l^- + 2)\cdots(l^- + n^\sharp),$$
a product of $n^\sharp$ consecutive integers.

Lean: `New.Data.lossFactorCount`, `New.Data.lossProduct` (New/Derivatives/Sharpness/NearPairs.lean).

**Lemma.** $B_l \ne 0$, $v(n^\sharp!) \le v(B_l)$, $v(l!) \le v(l^-!) + v(B_l)$, and $n^\sharp/p - 1 \le v(B_l)$. Also $x^{42} \le n^\sharp$.

Lean: `New.Data.lossProduct_ne_zero`, `New.Data.padicValNat_factorial_lossFactorCount_le`, `New.Data.padicValNat_factorial_le_add_lossProduct`, `New.Data.lossFactorCount_div_sub_one_le`, `New.Data.x_pow_le_lossFactorCount` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* A product of $n^\sharp$ consecutive integers is $n^\sharp!$ times a binomial coefficient, so $n^\sharp! \mid B_l$. Next, $l^-!\,B_l = (l^- + n^\sharp)!$, and $l \le l^- + n^\sharp$, so $l! \mid l^-!\,B_l$. The third claim follows from the first, since $n^\sharp/p - 1 \le v(n^\sharp!)$. The size $x^{42} \le \lceil 6b/k\rceil$ is in the table of sizes. $\square$

**Remark (Formalization).** In `lossProduct` the subtraction $l - n^\sharp$ is in $\mathbb{N}$, so it is $l^- = \max(l - n^\sharp, 0)$ as above. The product is `Nat.ascFactorial`.

### The partner sums

**Definition (Partner sums).** For a place $\tau$ and $e \in I_p$ put $\mathrm{pm}_\tau(e) = \min\bigl(\kappa(\tau)/p^e, \kappa(u(-p^e)\tau)\bigr)$, and $\mathrm{pm}_\tau(e) = 0$ for $e \notin I_p$. Put $R_\tau = \sum_e\mathrm{pm}_\tau(e)$.

Lean: `New.Data.partnerMinTerm`, `New.Data.partnerMinSum` (New/Derivatives/Sharpness/NearPairs.lean).

The terms satisfy $0 \le \mathrm{pm}_\tau(e) \le \kappa(\tau)/p^e$ (`New.Data.partnerMinTerm_nonneg`, `New.Data.partnerMinTerm_le_div`). So the series converges, and $R_\tau \ge 0$.

**Theorem (The partner identity).** For every prime $p$,
$$\gamma_p\sum_{\tau\in\Phi}\kappa(\tau) - F(p) = v(\pi_p)\sum_{\tau\in\Phi}R_\tau.$$

Lean: `New.Data.mul_sum_weight_sub_localPrimeSumTotal` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Fix $\tau$, write $y = \kappa(\tau)$ and $z_e = \kappa(u(-p^e)\tau)$. By the lemma on the full gain (Section 5), $\sum_{e\in I_p}y/p^e = y\gamma_p/v(\pi_p)$. For real numbers, $y/p^e - (y/p^e - z_e)_+ = \min(y/p^e, z_e)$. Both series converge, so subtract them term by term:
$$R_\tau = \frac{y\gamma_p}{v(\pi_p)} - \sum_{e\in I_p}\Bigl(\frac{y}{p^e} - z_e\Bigr)_+ = \frac{y\gamma_p - s_p(y, \tau)}{v(\pi_p)}.$$
Multiply by $v(\pi_p) > 0$ and add over $\tau$. $\square$

### Bounds for one partner sum

The weight is $\kappa(\tau) = a/x_1$ off $\Phi_b$ and $\kappa(\tau) = b$ on $\Phi_b$ (`New.Data.weight_of_notMem`, `New.Data.weight_of_mem`).

**Lemma (Tail).** For every $n$ and $e$, $\mathrm{pm}_\tau(e + n) \le b/(p^n2^e)$. If $l_0 \le 2n$, then $\sum_{e\ge0}\mathrm{pm}_\tau(e + n) \le 2b/(kp)$.

Lean: `New.Data.partnerMinTerm_add_le`, `New.Data.tsum_partnerMinTerm_add_le` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* $\mathrm{pm}_\tau(e + n) \le \kappa(\tau)/p^{e+n} \le b/(2^ep^n)$, since $\kappa \le b$ and $p \ge 2$. The geometric series gives $\sum_e \le 2b/p^n$. If $l_0 \le 2n$, then $2n \ge l_0 > 27s$, so $n > s$ and $n = n' + 1$ with $n' \ge s$. By fact 3, $k \le 2^s \le 2^{n'} \le p^{n'}$. So $2b/p^n \le 2b/(kp)$. $\square$

**Lemma.** If $2e < l_0$ and $(\tau, e)$ is not a near pair, then $\mathrm{pm}_\tau(e) \le a/x_1$.

Lean: `New.Data.partnerMinTerm_le_of_not_isNearPair` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* If $\tau \notin \Phi_b$, then $\mathrm{pm}_\tau(e) \le \kappa(\tau) = a/x_1$. If $\tau \in \Phi_b$ and $e \in I_p$, then the partner is not in $\Phi_b$, since the pair is not near. So the second entry of the minimum is $a/x_1$. For $e \notin I_p$ the term is $0$. $\square$

**Theorem (Partner sum).** Let $c \ge 0$. Suppose that every near pair $(\tau, e)$ at $\tau$ has $e = e_0$ and $\kappa(\tau)/p^{e_0} \le c + 1$. Then
$$R_\tau \le c + 1 + l_0\frac{a}{x_1} + \frac{2b}{kp}.$$

Lean: `New.Data.partnerMinSum_le` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Cut the series at $n = \lfloor(l_0 + 1)/2\rfloor$, so $l_0 \le 2n \le l_0 + 1$. For $e < n$, $2e < l_0$. If $(\tau, e)$ is a near pair, then $e = e_0$ and $\mathrm{pm}_\tau(e) \le \kappa(\tau)/p^{e_0} \le c + 1$. Otherwise $\mathrm{pm}_\tau(e) \le a/x_1$ by the previous lemma. So $\sum_{e<n}\mathrm{pm}_\tau(e) \le c + 1 + n\,a/x_1$, and $n \le l_0$. The tail lemma bounds the rest by $2b/(kp)$. $\square$

The lemma on one exponent at each start shows that the hypothesis on $e_0$ holds for some $e_0$ at every place. Volume 11 supplies $c$.

**Theorem (The errors fit in the loss product).** Let $p \le k$ be a prime and $l \in \mathbb{N}$. Then
$$3(\log b + 2) + x^{42} + 1 + l_0\frac{a}{x_1} + \frac{2b}{kp} \le v(B_l).$$

Lean: `New.Data.error_le_padicValNat_lossProduct` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* The table of sizes gives four facts.

1. $3(\log b + 2) + x^{42} + 1 \le a/x_1$.
2. $1 \le (l_0 + 1)a/x_1$.
3. $(l_0 + 1)a/x_1 \le (81s + 1)a/x_1 \le b/k^2 \le b/(kp)$, using $l_0 \le 81s$ and $p \le k$.
4. $6b/(kp) \le n^\sharp/p$, since $6b/k \le \lceil 6b/k\rceil$.

By 1 and 3 the left side is at most $(l_0 + 1)a/x_1 + 2b/(kp) \le 3b/(kp)$. By 2 and 3, $1 \le b/(kp)$, so by 4, $3b/(kp) + 1 \le 4b/(kp) \le 6b/(kp) \le n^\sharp/p$. So the left side is at most $n^\sharp/p - 1 \le v(B_l)$, by the lemma on the loss product. $\square$

**Remark (Formalization).** The four size facts are calls to `le_of_hasLogBound` against the table in [the data and its sizes](/chapter/data-and-sizes/), Section 6. The bound $k \le 2^s$ in the tail lemma is one more call. The sums $R_\tau$ are `tsum`; they are summable by `New.Data.summable_partnerMinTerm`, so the junk value $0$ does not occur.

### An example of a partner sum

Let $p$ be inert with $p \le k$, and let $\tau \in \Phi_b$. The terms of $R_\tau$ are $\min(b/p^e, \kappa(u(-p^e)\tau))$ for odd $e$. At an odd $e < l_0/2$ whose partner is not a $b$-place, the term is at most $a/x_1$, which is tiny next to $b$. At the one exponent $e_0$ of a near pair, if there is one, the term is $\min(b/p^{e_0}, b) = b/p^{e_0}$, which can be large. This is the term that Volume 11 must pay for. Past $l_0/2$ all terms together are at most $2b/(kp)$, since $p^{l_0/2} \ge 2^{s} \ge k$. Without sparseness, a $b$-place could have many $b$-partners at small $e$, and each would add a term close to $b/p^e$.
