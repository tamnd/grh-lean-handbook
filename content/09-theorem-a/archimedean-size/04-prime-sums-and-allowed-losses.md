---
title: Prime sums and allowed losses
lean:
  - New/UpperBound/Size/Estimates.lean
decls:
  - New.Data.smallNonsplitPrimes
  - New.Data.localPrimeSum_eq_tsum
  - New.Data.posPart_div_sub_weight_eq_zero
  - New.Data.localPrimeSum_eq_zero
  - New.Data.gain_eq_zero
  - New.Data.primeSum_eq_sum_localPrimeSum
  - New.Data.localPrimeSumTotal_nonneg
  - New.Data.sum_localPrimeSumTotal_mul_log_le
  - New.Data.allowedLoss
  - New.Data.allowedLoss_nonneg
  - New.Data.exists_mul_sub_one_eq_or_mul_add_one_eq
  - New.Data.sum_allowedLoss_mul_log_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Prime sums and allowed losses

The exponent of the size bound contains the prime sums $s_{\mathrm{fin}}(y,\sigma)$, which are sums over integers $\nu \le a$. The divisibility side of Theorem A works one prime at a time, with the local sums $s_p(y,\sigma)$. This section groups the prime sum by primes, so that the two sides can be compared. It also defines the allowed losses and bounds their sum by the error unit $\mathrm{err}_0 = fa\log^3 b$.

### The local sums

Let $D$ be data. Let $\chi_K$ be the Legendre symbol modulo the prime $d$, so that $K = \mathbb Q(\sqrt{-d})$. Let $\kappa$ be the weight on the group $\Phi \cong (\mathbb Z/q_1)^\times$ of infinite places of $E$ ([places and weights](/chapter/data-and-sizes/#the-places-and-the-weights)). For an integer $\nu$, $u(\nu)$ is the place of the class of $\nu$ if $\nu$ is prime to $q_1$, and the identity place otherwise. The text writes $\nu\sigma$ for $u(\nu)\sigma$.

The prime sum is
$$s_{\mathrm{fin}}(y,\sigma) = \sum_{1\le\nu\le a}\Lambda(\nu)\bigl(1 - \chi_K(\nu)\bigr)\Bigl(\frac y\nu - \kappa(-\nu\sigma)\Bigr)_+$$
([the prime sums](/chapter/prime-sums/); Lean: `New.Data.primeSum`). Here $\Lambda$ is the von Mangoldt function and $t_+ = \max(t, 0)$.

The local sum at a prime $p$ is defined in [short columns and the gain](/chapter/short-columns-gain/) (Lean: `New.Data.localPrimeSum`):
$$s_p(y,\sigma) = v_p\sum_{e\in I_p}\Bigl(\frac y{p^e} - \kappa(-p^e\sigma)\Bigr)_+ .$$
Here $v_p = \tfrac12$ if $p = d$ and $v_p = 1$ otherwise. The set $I_p$ is the set of odd $e \ge 1$ if $p$ is inert in $K$, the set of all $e \ge 1$ if $p = d$, and empty if $p$ splits. The same chapter defines the total $F(p) = \sum_{\sigma\in\Phi}s_p(\kappa(\sigma),\sigma)$, the gain
$$\mathrm{gain}_p = m\Bigl(\sum_{\tau\in\Phi_a}s_p(a,\tau) + k\,F(p)\Bigr),$$
and the loss
$$\mathrm{loss}(p) = f\log^2 b\cdot\frac ap\cdot\begin{cases} m & \text{if } p \equiv \pm1 \bmod m,\\ 1 & \text{otherwise.}\end{cases}$$
In Lean, "$p \equiv \pm1 \bmod m$" is the statement that $m$ divides $p - 1$ or $p + 1$, with truncated subtraction.

**Lemma (The local sum as a sum over powers).** Let $p$ be prime. Then
$$s_p(y,\sigma) = \sum_{e\ge1}\frac{1 - \chi_K(p^e)}{2}\Bigl(\frac y{p^e} - \kappa(-p^e\sigma)\Bigr)_+ .$$

Lean: `New.Data.localPrimeSum_eq_tsum` (New/UpperBound/Size/Estimates.lean).

*Proof.* The set $I_p$ contains only $e \ge 1$, so the sum over $I_p$ is a sum over $e \ge 1$ with weight $1$ on $I_p$ and $0$ off it. It is enough to show that $(1 - \chi_K(p)^e)/2$ is $v_p$ for $e \in I_p$ and $0$ otherwise (`New.one_sub_chiK_pow_div_two`). There are three cases. If $p = d$, then $\chi_K(p) = 0$, so the number is $\tfrac12 = v_p$ for every $e \ge 1$. If $p$ splits, then $\chi_K(p) = 1$ and the number is $0$, and $I_p$ is empty. If $p$ is inert, then $\chi_K(p) = -1$, and the number is $1$ for odd $e$ and $0$ for even $e$. In each case it matches. $\square$

### Large primes contribute nothing

**Lemma (Positive parts vanish above $x_1$).** If $y \le a$ and $t \ge x_1$, then $(y/t - \kappa(\tau))_+ = 0$ for every place $\tau$.

Lean: `New.Data.posPart_div_sub_weight_eq_zero` (New/UpperBound/Size/Estimates.lean).

*Proof.* Every weight satisfies $\kappa(\tau) \ge a/x_1$ ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)). So $y/t \le a/t \le a/x_1 \le \kappa(\tau)$. $\square$

**Lemma (Local sums of large primes).** If $p \ge x_1$ is a natural number and $y \le a$, then $s_p(y,\sigma) = 0$.

Lean: `New.Data.localPrimeSum_eq_zero` (New/UpperBound/Size/Estimates.lean).

*Proof.* For $e \ge 1$, $p^e \ge p \ge x_1$, since $p \ge x_1 > 1$. Each term vanishes by the previous lemma. $\square$

**Lemma (Vanishing gain).** If $p$ splits in $K$, that is $\chi_K(p) = 1$, or if $p \ge x_1$, then $\mathrm{gain}_p = 0$.

Lean: `New.Data.gain_eq_zero` (New/UpperBound/Size/Estimates.lean).

*Proof.* The gain uses the local sums $s_p(a,\tau)$ and $s_p(\kappa(\sigma),\sigma)$. In both, $y \le a$, since $\kappa(\sigma) \le b \le a$. If $p$ splits, $I_p$ is empty and all local sums are $0$. If $p \ge x_1$, all local sums with $y \le a$ are $0$ by the previous lemma. So both parts of the gain vanish. $\square$

### The prime sum, prime by prime

**Theorem (The prime sum grouped by primes).** Let $U \ge \lceil x_1\rceil$ be a natural number and $y \le a$. Then
$$s_{\mathrm{fin}}(y,\sigma) = \sum_{p<U,\ p\text{ prime}}2\,s_p(y,\sigma)\log p .$$

Lean: `New.Data.primeSum_eq_sum_localPrimeSum` (New/UpperBound/Size/Estimates.lean).

*Proof.* Let $g(\nu) = \Lambda(\nu)(1 - \chi_K(\nu))(y/\nu - \kappa(-\nu\sigma))_+$ for natural $\nu$, so $s_{\mathrm{fin}}(y,\sigma) = \sum_{1\le\nu\le a}g(\nu)$.

*Support.* If $\nu \ge \lceil x_1\rceil$, then $\nu \ge x_1$ and $g(\nu) = 0$ by the lemma on positive parts. Also $g(0) = 0$, since $\Lambda(0) = 0$. As $\lceil x_1\rceil \le a$, $g$ vanishes outside $[1, a]$, and the finite sum equals the sum over all $\nu$. The function $\Lambda$ vanishes off the prime powers, so $g$ does too.

*Grouping.* A sum over prime powers $p^{e+1}$, $e \ge 0$, is a double sum over primes $p$ and exponents $e$. For a prime $p$, $\Lambda(p^{e+1}) = \log p$, and
$$\sum_{e\ge0}g(p^{e+1}) = \log p\sum_{e\ge1}\bigl(1 - \chi_K(p^e)\bigr)\Bigl(\frac y{p^e} - \kappa(-p^e\sigma)\Bigr)_+ = 2\,s_p(y,\sigma)\log p ,$$
by the lemma on the local sum as a sum over powers. For a prime $p \ge U$ every power $p^{e+1}$ is at least $U \ge \lceil x_1\rceil$, so its terms vanish. So only the primes $p < U$ remain. $\square$

The theorem is the bridge between [the prime sums](/chapter/prime-sums/) and the local divisibility. With $y = \kappa(\tau)$ or $y = a$ it applies to all the prime sums of the main amount, since $\kappa(\tau) \le b \le a$.

**Lemma (The total is nonnegative).** $F(p) \ge 0$ for every $p$.

Lean: `New.Data.localPrimeSumTotal_nonneg` (New/UpperBound/Size/Estimates.lean).

*Proof.* Each $s_p(\kappa(\sigma),\sigma)$ is $v_p > 0$ times a sum of positive parts. $\square$

**Proposition (The totals against the prime sums).** For every finite set $T$ of primes,
$$\sum_{p\in T}2F(p)\log p \le \sum_{\tau\in\Phi}s_{\mathrm{fin}}(\kappa(\tau),\tau).$$

Lean: `New.Data.sum_localPrimeSumTotal_mul_log_le` (New/UpperBound/Size/Estimates.lean).

*Proof.* Choose a natural number $U$ larger than every element of $T$ and larger than $\lceil x_1\rceil$. Then $T$ is a subset of the primes below $U$. Each term $2F(p)\log p$ is at least $0$, by the last lemma and $\log p \ge 0$. So the sum over $T$ is at most the sum over all primes $p < U$. Exchange the sums over $p$ and $\tau$:
$$\sum_{p<U}2F(p)\log p = \sum_\tau\sum_{p<U}2\,s_p(\kappa(\tau),\tau)\log p = \sum_\tau s_{\mathrm{fin}}(\kappa(\tau),\tau),$$
by the theorem, with $y = \kappa(\tau) \le a$. $\square$

### The allowed losses

The proof of Theorem A compares the gain at each prime with what the divisibility side gives. At the small nonsplit primes and at the level $N$ it may lose a little. The set of small nonsplit primes is
$$\mathcal S = \{p < \lceil x_1\rceil : p \text{ prime},\ \chi_K(p) \ne 1\}.$$

Lean: `New.Data.smallNonsplitPrimes` (New/UpperBound/Size/Estimates.lean).

For a natural number $p$ the condition $p < \lceil x_1\rceil$ is the same as $p < x_1$.

**Definition (Allowed loss).** The allowed loss at a natural number $p$ is
$$\mathrm{allowed}(p) = \begin{cases}2\,\mathrm{loss}(p) & \text{if } p\in\mathcal S,\\ 2mfb & \text{if } p\notin\mathcal S \text{ and } p = N,\\ 0 & \text{otherwise.}\end{cases}$$

Lean: `New.Data.allowedLoss` (New/UpperBound/Size/Estimates.lean).

**Lemma (Allowed losses are nonnegative).** $\mathrm{allowed}(p) \ge 0$ for every $p$.

Lean: `New.Data.allowedLoss_nonneg` (New/UpperBound/Size/Estimates.lean).

*Proof.* Each case is a product of nonnegative numbers. $\square$

**Lemma (Primes that are $\pm1$ modulo $m$).** Let $p \ge 2$ with $p \equiv \pm1 \bmod m$. Then there is a natural number $c$ with $1 \le c \le p$, $m \le \lfloor 2p/c\rfloor$, and $p = mc - 1$ or $p = mc + 1$.

Lean: `New.Data.exists_mul_sub_one_eq_or_mul_add_one_eq` (New/UpperBound/Size/Estimates.lean).

*Proof.* If $m \mid p + 1$, write $mc = p + 1$. If $m \mid p - 1$, write $mc + 1 = p$. In both cases $c \ge 1$, since $mc = 0$ would give $p + 1 = 0$ or $p = 1$. As $m \ge 10^4 \ge 2$, $2c \le mc \le p + 1$, so $c \le p$. Last, $mc \le p + 1 \le 2p$, so $m \le 2p/c$, and $m$ is an integer, so $m \le \lfloor 2p/c\rfloor$. $\square$

**Theorem (The sum of the allowed losses).** For every finite set $U$ of natural numbers,
$$\sum_{p\in U}\mathrm{allowed}(p)\log p \le fa\log^3 b = \mathrm{err}_0 .$$

Lean: `New.Data.sum_allowedLoss_mul_log_le` (New/UpperBound/Size/Estimates.lean).

*Proof.* Put $T = 4fa\log^2 b\,\log x_1$ and $J = \{1,\dots,\lfloor x_1\rfloor\}\times\{0,1,2,3\}$. For $(c, i) \in J$, let $\mathrm{served}(c,i)$ be the $i$-th of the four numbers $N$, $mc - 1$, $c$, $mc + 1$. The idea is that each term of the sum is at most $T/c$ for some $c$, and each $c$ serves at most four numbers.

*Claim.* For every $p$,
$$\mathrm{allowed}(p)\log p \le \sum_{(c,i)\in J,\ \mathrm{served}(c,i) = p}\frac Tc .$$
All terms on the right are positive, so it is enough to find one $(c,i) \in J$ with $\mathrm{served}(c,i) = p$ and $\mathrm{allowed}(p)\log p \le T/c$.

*Case $p\in\mathcal S$.* Then $p$ is prime and $p < x_1$, so $\log p \le \log x_1$. If $p \equiv \pm1 \bmod m$, the last lemma gives $c$ with $p = mc \mp 1$ and $m \le 2p/c$; take $i = 1$ or $i = 3$. Otherwise take $c = p$ and $i = 2$; then the factor $1$ of the loss is at most $2p/c = 2$. In both cases $1 \le c \le p \le \lfloor x_1\rfloor$, and the factor of the loss is at most $2p/c$. So
$$2\,\mathrm{loss}(p)\log p \le 2f\log^2 b\cdot\frac ap\cdot\frac{2p}c\cdot\log x_1 = \frac Tc .$$

*Case $p = N$, $p \notin\mathcal S$.* Take $c = 1$ and $i = 0$. By the table of sizes, $\log N \le 30m\log b$ and $m \le 2\sqrt x$. So
$$2mfb\log N \le 60m^2fb\log b \le 240\,xfb\log b = 240fa\log b .$$
This is at most $T = 4fa\log^2 b\log x_1$, since $60 \le \log b\,\log x_1$.

*Other $p$.* The left side is $0$.

*Summation.* Sum the claim over $p \in U$. The sets $\{(c,i) \in J : \mathrm{served}(c,i) = p\}$ for different $p$ are disjoint. So
$$\sum_{p\in U}\mathrm{allowed}(p)\log p \le \sum_{(c,i)\in J}\frac Tc = 4T\sum_{c=1}^{\lfloor x_1\rfloor}\frac1c \le 4T(1 + \log x_1),$$
by the bound $H_n \le 1 + \log n$ for the harmonic numbers. Last,
$$4T(1 + \log x_1) = 16fa\log^2 b\,\log x_1(1 + \log x_1) \le fa\log^3 b ,$$
since $16\log x_1(1 + \log x_1) \le 32\log^2 x_1 \le 32(\log b)^{1/3} \le \log b$ by the scale inequality (S5). $\square$

**Remark (Formalization).** The four served numbers are the list $[N, mc - 1, c, mc + 1]$, read with `List.get!`, and $mc - 1$ is truncated subtraction. Both are harmless: the index is always below $4$, and $mc \ge 1$. A number may be served twice, for example $N = c$. This only makes the right side larger. The last two inequalities of the proof are proved by `le_of_hasLogBound` of [the data and their sizes](/chapter/data-and-sizes/#the-table-of-sizes).

### An example

Take a prime $p \in \mathcal S$ with $p \equiv -1 \bmod m$, say $p = 2m - 1$ if it is prime. Then $c = 2$, and the loss is $f\log^2 b\cdot(a/p)\cdot m$. The factor $m/p$ is about $\tfrac12 = 1/c$. So the loss at $p$ is about $\tfrac12 fa\log^2 b$, much more than the loss $fa\log^2 b/p$ of a prime not of this form. Such primes are rare: for each $c$ there are at most two of them. This is why the harmonic sum over $c$ appears, and not a sum over primes.

For a nonsplit prime $p$ not $\equiv \pm1 \bmod m$, the term is $2f\log^2 b\cdot(a/p)\cdot\log p$. The sum of $\log p/p$ over primes $p < x_1$ is about $\log x_1$ by Mertens. The proof uses the cruder bound $\sum_{c\le x_1}2/c$, which needs no prime number theory.
