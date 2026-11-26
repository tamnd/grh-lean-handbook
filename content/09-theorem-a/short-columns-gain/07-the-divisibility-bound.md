---
title: The divisibility bound
lean:
  - New/UpperBound/Divisibility/JetExponent.lean
decls:
  - New.Data.lowColumns
  - New.Data.lowBoxes
  - New.Data.divisibilityBound
  - New.Data.longRow
  - New.Data.partnerTerm
  - New.Data.summable_partnerTerm
  - New.Data.heightOneColumns_eraseHeightOne
  - New.Data.lowColumnCount_eraseHeightOne
  - New.Data.lowBoxCount_eraseHeightOne
  - New.Data.mul_weight_le_lowBoxes
  - New.Data.lowColumns_le
  - New.Data.lowBoxes_le
  - New.Data.lowColumns_lowBoxes_bounds
  - New.Data.boxes_eq_aPlaces_add_low
  - New.Data.boxes_sub_boxes_eraseHeightOne
  - New.Data.one_add_logb_boxes_le
  - New.Data.posPart_sub_weight_le_posPart_longRow
  - New.Data.mul_posPart_weight_le
  - New.Data.min_longRow_add_lowColumns_add_min_lowBoxes_le
  - New.Data.sub_le_predictedDivisibility
  - New.Data.gammaPrime_mul_lowColumns_le
  - New.Data.localPrimeSum_add_le_mul_tsum_partnerTerm_add
  - New.Data.le_divisibilityBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The divisibility bound

This section defines the divisibility bound of stage $j$ at a prime $p$ and proves the theorem that only collisions lose (Section 1). The bound is the predicted divisibility of the diagrams of the source weight, read at the heights below the rank $n_{j+1}$. The gain is the same kind of sum, with the weights in place of the column counts. The proof compares the two sums term by term.

### The background

1. The column counts are $c_\tau(1) = a$ at the $a$-places and $0$ elsewhere, $c_\tau(k) = \kappa_1(\tau) - \lfloor(k + t + 1)/2\rfloor$, $c_\tau(h) = \Delta - (t + 1)$ for $h > k$ with $t + 1 \mid h - k$, and $c_\tau(h) = 0$ otherwise. So for $h \ne 1$, $c_\tau(h) \le [h = k]\,\kappa_1(\tau) + \Delta$ ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 3).
2. The lift weight satisfies $\kappa(\tau) \le \kappa_1(\tau) - \Delta/2$ and $\kappa_1(\tau) \le \kappa(\tau) + x^{42}$, and $a/x_1 \le \kappa(\tau) \le b \le a$ ([the data and its sizes](/chapter/data-and-sizes/), Section 4).
3. For column counts $\kappa_\tau(h)$, a height bound $N$ and a partner map $\mathrm{pr}$, put $a_\tau = \kappa_\tau(1)$, $a'_\tau = \sum_{h<N, h\ne1}\kappa_\tau(h)$ and $l_\tau = \sum_{h<N, h\ne1}h\,\kappa_\tau(h)$. The predicted divisibility at $p$ is
$$v(\pi_p)\sum_{e\in I_p}\sum_\tau\Bigl[\Bigl(\frac{a_\tau}{p^e} - a_{\tau'} - a'_{\tau'}\Bigr)_+ + \Bigl(\frac{l_\tau}{p^e} - l_{\tau'}\Bigr)_+ - \frac{a'_\tau}{p^e}\Bigr] - [p = d]\,\frac12\sum_\tau\bigl(\min(a_\tau, a_{\tau''} + a'_{\tau''}) + a'_\tau + \min(l_\tau, l_{\tau''})\bigr),$$
with $\tau' = \mathrm{pr}_e\tau$ and $\tau'' = \mathrm{pr}_0\tau$. Erasing the columns of height one at the places of a set $S$ sets $\kappa_\tau(1) = 0$ for $\tau \in S$. The number of boxes below $N$ is $\mathrm{boxes}(\kappa, N) = \sum_\tau(a_\tau + l_\tau)$ ([the count and the divisibility of standard data](/chapter/normal-forms/)).
4. $0 < v(\pi_p) \le 1$, and $\gamma_p \le 1/(p-1)$ (Section 5).
5. The sizes of [the data and its sizes](/chapter/data-and-sizes/), Section 6, among them $k \ge 100m$, $x^{42} \le b$, and the bounds on $n_m$, $\Delta$ and $m$ in terms of $x$.

Fix $j < m$ and write $n = n_{j+1}$. The partner map is $\mathrm{pr}_e\tau = u(-p^e)\tau$.

### Low columns and long rows

**Definition (Low columns and boxes).** At a place $\tau$, $c^{\mathrm{low}}_\tau = \sum_{h<n, h\ne1}c_\tau(h)$ is the number of low columns, and $l_\tau = \sum_{h<n, h\ne1}h\,c_\tau(h)$ is the number of boxes in them.

Lean: `New.Data.lowColumns`, `New.Data.lowBoxes` (New/UpperBound/Divisibility/JetExponent.lean).

**Definition (Long rows).** For a set $S$ of places, $L^S_\tau = a$ if $\tau \in \Phi_a \setminus S$ and $L^S_\tau = 0$ otherwise.

Lean: `New.Data.longRow` (New/UpperBound/Divisibility/JetExponent.lean).

**Lemma (Erasing the long rows).** Erase the columns of height one at the places of $S$ from the column counts $c$. Read below $n$, the result has $a_\tau = L^S_\tau$, $a'_\tau = c^{\mathrm{low}}_\tau$ and the same $l_\tau$.

Lean: `New.Data.heightOneColumns_eraseHeightOne`, `New.Data.lowColumnCount_eraseHeightOne`, `New.Data.lowBoxCount_eraseHeightOne` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Since $n > 1$, the height $1$ is below $n$, and $c_\tau(1)$ is $a$ on $\Phi_a$ and $0$ elsewhere, by fact 1. Erasing sets it to $0$ on $S$. That gives $L^S_\tau$. Erasing does not change the counts at the heights $h \ne 1$. $\square$

**Lemma (Sizes of the low columns).** For every place $\sigma$,
$$k\,\kappa(\sigma) \le l_\sigma \le k\,\kappa(\sigma) + x^{60}, \qquad c^{\mathrm{low}}_\sigma \le \kappa(\sigma) + x^{60}.$$

Lean: `New.Data.mul_weight_le_lowBoxes`, `New.Data.lowBoxes_le`, `New.Data.lowColumns_le`, `New.Data.lowColumns_lowBoxes_bounds` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* The height $k$ is below $n = k + (j + 1)(t + 1)$, and $k \ne 1$. So $l_\sigma \ge k\,c_\sigma(k)$. The table gives $\lfloor(k + t + 1)/2\rfloor \le \Delta/2$, so $c_\sigma(k) \ge \kappa_1(\sigma) - \Delta/2 \ge \kappa(\sigma)$ by fact 2. For the upper bounds, fact 1 gives
$$c^{\mathrm{low}}_\sigma \le \kappa_1(\sigma) + n\Delta, \qquad l_\sigma \le k\,\kappa_1(\sigma) + \frac{n(n-1)}{2}\Delta.$$
By fact 2, $\kappa_1 \le \kappa + x^{42}$. The table gives $x^{42} + n\Delta \le x^{60}$ and $kx^{42} + n^2\Delta \le x^{60}$, since $n \le n_m$. $\square$

**Lemma (Boxes).** $\mathrm{boxes}(c, n) = \#\Phi_a\cdot a + \sum_\sigma l_\sigma$. After erasing at $S$, the number of boxes falls by $\#(\Phi_a \cap S)\cdot a$.

Lean: `New.Data.boxes_eq_aPlaces_add_low`, `New.Data.boxes_sub_boxes_eraseHeightOne` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Split each sum $\sum_{h<n}h\,c_\sigma(h)$ into the term $h = 1$, which is $a$ on $\Phi_a$ and $0$ elsewhere, and the rest, which is $l_\sigma$. After erasing, the term $h = 1$ is $L^S_\sigma$. Then $\#\Phi_a - \#(\Phi_a\setminus S) = \#(\Phi_a \cap S)$. $\square$

**Lemma.** $1 + \log_p\max(\mathrm{boxes}(c, n), 1) \le (\log b)^2$.

Lean: `New.Data.one_add_logb_boxes_le` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Each $l_\sigma \le kb + x^{60}$ is at most the principal level $M$, by the table. So the maximum is at most $fa + fM + 1$. Since $\log p \ge \log 2 \ge \frac12$, the left side is at most $1 + 2\log(fa + fM + 1)$, and the table bounds this by $(\log b)^2$. $\square$

### The bound and its terms

**Definition (The divisibility bound).** Let $c^S$ be the column counts $c$ with the columns of height one erased at the places of $S$. Then
$$\mathrm{div}_p(j, S) = \mathrm{pred}_p(c^S, n) + \gamma_p\bigl(\mathrm{boxes}(c, n) - \mathrm{boxes}(c^S, n)\bigr) - f\,n^3\bigl(1 + \log_p\max(\mathrm{boxes}(c, n), 1)\bigr),$$
where $\mathrm{pred}_p$ is the predicted divisibility of fact 3, with the partner map $\mathrm{pr}_e\tau = u(-p^e)\tau$.

Lean: `New.Data.divisibilityBound` (New/UpperBound/Divisibility/JetExponent.lean).

The middle term gives back the full gain $\gamma_p$ for each erased box. The last term pays for the count of [the count and the divisibility of standard data](/chapter/normal-forms/).

**Definition (Partner terms).** For a place $\tau$ and $e \in I_p$, with $\tau' = u(-p^e)\tau$, put
$$T^S_\tau(e) = \Bigl(\frac{L^S_\tau}{p^e} - L^S_{\tau'} - c^{\mathrm{low}}_{\tau'}\Bigr)_+ + \Bigl(\frac{l_\tau}{p^e} - l_{\tau'}\Bigr)_+ - \frac{c^{\mathrm{low}}_\tau}{p^e},$$
and $T^S_\tau(e) = 0$ for $e \notin I_p$.

Lean: `New.Data.partnerTerm` (New/UpperBound/Divisibility/JetExponent.lean).

**Lemma.** For every $\tau$ the series $\sum_eT^S_\tau(e)$ converges absolutely.

Lean: `New.Data.summable_partnerTerm` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* For nonnegative reals, $|(\alpha - \alpha')_+ + (\beta - \beta')_+ - \gamma| \le \alpha + \beta + \gamma$. So $|T^S_\tau(e)| \le (L^S_\tau + l_\tau + c^{\mathrm{low}}_\tau)/p^e$ for $e \in I_p$. This series converges by the lemma on the full gain (Section 5). $\square$

**Remark (Formalization).** The sums over $e$ are `tsum` over $\mathbb{N}$. The lemma above shows that no junk value occurs. The exchange of $\sum_e$ with the finite sum over $\tau$ uses this summability.

**Lemma (The predicted divisibility).**
$$v(\pi_p)\sum_\tau\sum_eT^S_\tau(e) - f\cdot\frac{2a}{pm} \le \mathrm{pred}_p(c^S, n).$$

Lean: `New.Data.sub_le_predictedDivisibility` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* By the lemma on erasing the long rows, the first part of $\mathrm{pred}_p(c^S, n)$ is $v(\pi_p)\sum_e\sum_\tau T^S_\tau(e)$. Exchange the two sums. If $p \ne d$, there is nothing more. If $p = d$, the next lemma bounds each term of the correction by $3a/(dm)$. So the correction is at most $\frac12f\cdot3a/(dm) \le 2fa/(dm)$. $\square$

**Lemma (The correction at d).** For every place $\tau$, with $\tau'' = u(-1)\tau$,
$$\min\bigl(L^S_\tau, L^S_{\tau''} + c^{\mathrm{low}}_{\tau''}\bigr) + c^{\mathrm{low}}_\tau + \min(l_\tau, l_{\tau''}) \le \frac{3a}{dm}.$$

Lean: `New.Data.min_longRow_add_lowColumns_add_min_lowBoxes_le` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Put $u = a/(dm)$. The class of $\tau''$ is $-1$ times the class of $\tau$, and the two classes differ modulo $q_0$, by the lemma on classes at $d$ (Section 5) with $e = 0$. So $\tau$ and $\tau''$ are not both $a$-places, which have class $1$, and not both $b$-places, which have class $-1$. By the sizes of the low columns and the table, $c^{\mathrm{low}}_\sigma \le b + x^{60} \le u$ for every $\sigma$, and $l_\sigma \le k\,a/x_1 + x^{60} \le u$ for $\sigma \notin \Phi_b$. If $\tau \notin \Phi_a$, the first minimum is at most $L^S_\tau = 0$. Otherwise $L^S_{\tau''} = 0$, and the first minimum is at most $c^{\mathrm{low}}_{\tau''} \le u$. The second term is at most $u$. The last minimum is at most $l_\sigma \le u$ for the one of $\tau, \tau''$ that is not a $b$-place. $\square$

### Comparing the terms

The next two lemmas compare one term of the gain with one partner term. Let $p$ be a small nonsplit prime, $e \in I_p$ and $\tau' = u(-p^e)\tau$.

**Lemma (Long rows).** If $\tau \in \Phi_a$, then
$$\Bigl(\frac{a}{p^e} - \kappa(\tau')\Bigr)_+ + [e = 1,\ \tau \in S]\,\frac{a}{x_1} \le \Bigl(\frac{L^S_\tau}{p^e} - L^S_{\tau'} - c^{\mathrm{low}}_{\tau'}\Bigr)_+ + [\tau \in S]\,\frac{a}{p^e} + [(\tau, e) \text{ is a collision outside } S]\,\frac{a}{p^e} + x^{60}.$$
If $\tau \notin \Phi_a$, the left side is replaced by $0$ and the bound holds.

Lean: `New.Data.posPart_sub_weight_le_posPart_longRow` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* If $\tau \notin \Phi_a$, the right side is nonnegative. Let $\tau \in \Phi_a$. The left positive part is at most $a/p^e$, since $\kappa \ge 0$.

Case $\tau \in S$. The second term on the right is $a/p^e$. If the positive part on the left is $0$, the left side is at most $[e = 1]\,a/x_1 \le a/p^e$, since $p < x_1$. Otherwise, since $\kappa(\tau') \ge a/x_1$, the positive part is at most $a/p^e - a/x_1$, and the left side is at most $a/p^e$.

Case $\tau \notin S$. Then $L^S_\tau = a$. If $\tau' \in \Phi_a \setminus S$, then $(\tau, e)$ is a collision, and the third term on the right is $a/p^e$. Otherwise $L^S_{\tau'} = 0$, and $c^{\mathrm{low}}_{\tau'} \le \kappa(\tau') + x^{60}$. So
$$\frac{a}{p^e} - \kappa(\tau') \le \frac{a}{p^e} - c^{\mathrm{low}}_{\tau'} + x^{60} \le \Bigl(\frac{L^S_\tau}{p^e} - L^S_{\tau'} - c^{\mathrm{low}}_{\tau'}\Bigr)_+ + x^{60}.$$
The left side is the positive part of this, and $x^{60} \ge 0$. $\square$

**Lemma (Low columns).** For places $\tau, \tau'$ and $z > 0$,
$$k\Bigl(\frac{\kappa(\tau)}{z} - \kappa(\tau')\Bigr)_+ \le \Bigl(\frac{l_\tau}{z} - l_{\tau'}\Bigr)_+ + x^{60}.$$

Lean: `New.Data.mul_posPart_weight_le` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* The left side is $\max(k\kappa(\tau)/z - k\kappa(\tau'), 0)$. By the sizes of the low columns, $k\kappa(\tau) \le l_\tau$ and $l_{\tau'} \le k\kappa(\tau') + x^{60}$. So $k\kappa(\tau)/z - k\kappa(\tau') \le l_\tau/z - l_{\tau'} + x^{60}$. $\square$

**Lemma.** $\gamma_p\,c^{\mathrm{low}}_\tau \le a/(pm)$.

Lean: `New.Data.gammaPrime_mul_lowColumns_le` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* $\gamma_p \le 1/(p-1) \le 2/p$, and $c^{\mathrm{low}}_\tau \le \kappa(\tau) + x^{60} \le b + x^{60}$. The table gives $2(b + x^{60}) \le a/m$. $\square$

### One place

**Theorem (The gain at one place).** Let $p$ be a small nonsplit prime and $\tau$ a place. Put $v = v(\pi_p)$ and $E_\tau = \sum_e[(\tau, e) \text{ is a collision outside } S]\,a/p^e$. Then
$$[\tau\in\Phi_a]\,s_p(a, \tau) + k\,s_p(\kappa(\tau), \tau) + v[\tau \in \Phi_a\cap S]\frac{a}{x_1} \le v\Bigl(\sum_eT^S_\tau(e) + E_\tau + 2\lceil\log_p\lceil x_1\rceil\rceil x^{60}\Bigr) + \gamma_p\bigl(c^{\mathrm{low}}_\tau + [\tau\in\Phi_a\cap S]\,a\bigr).$$

Lean: `New.Data.localPrimeSum_add_le_mul_tsum_partnerTerm_add` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Divide by $v > 0$. Write $K = \lceil\log_p\lceil x_1\rceil\rceil$. Each term is now the sum of a series in $e$, as follows.

1. $s_p(y, \tau)/v = \sum_{e\in I_p}(y/p^e - \kappa(\tau'))_+$, for $y = a$ and $y = \kappa(\tau)$.
2. $[\tau\in\Phi_a\cap S]\,a/x_1$ is a series with one term, at $e = 1$.
3. $\gamma_p\bigl(c^{\mathrm{low}}_\tau + [\tau\in\Phi_a\cap S]a\bigr)/v = \sum_{e\in I_p}\bigl(c^{\mathrm{low}}_\tau + [\tau\in\Phi_a\cap S]a\bigr)/p^e$, by the lemma on the full gain.
4. $2Kx^{60} = \sum_{e<K}2x^{60}$.

All these series converge, and so does $E_\tau$, whose terms are at most $a/p^e$ on $I_p$. Compare the terms at each $e$.

Case $e \notin I_p$. Then $e \ne 1$, since $1 \in I_p$ (Section 5). The left term is $0$, and each right term is at least $0$.

Case $e \in I_p$ and $e < K$. The partner term plus the term $c^{\mathrm{low}}_\tau/p^e$ of item 3 is the sum of the two positive parts in $T^S_\tau(e)$. Add the lemma on long rows and the lemma on low columns with $z = p^e$. The sum of the right sides is at most the right term at $e$, and the term $2x^{60}$ of item 4 is present since $e < K$.

Case $e \in I_p$ and $e \ge K$. Then $p^e \ge p^K \ge \lceil x_1\rceil \ge x_1$. For $y \le a$ and every $\sigma$, $y/p^e \le a/x_1 \le \kappa(\sigma)$, so both positive parts on the left vanish. Also $e \ne 1$, since $p < x_1$. The left term is $0$. The right term is the sum of two positive parts and nonnegative terms, so it is at least $0$.

The comparison of the terms gives the comparison of the sums. Multiply back by $v$. $\square$

### The theorem

**Theorem (Only collisions lose).** Let $p$ be a small nonsplit prime, let $j < m$, and let $S$ be a set of places. Then
$$\frac{\mathrm{gain}_p}{m} - \mathrm{coll}_p(S) + v(\pi_p)\,\#(\Phi_a\cap S)\frac{a}{x_1} - \frac{f(\log b)^2a}{pm} \le \mathrm{div}_p(j, S).$$

Lean: `New.Data.le_divisibilityBound` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Put $u = a/(pm)$, $v = v(\pi_p)$ and $K = \lceil\log_p\lceil x_1\rceil\rceil$. There are four estimates.

1. $v\cdot 2Kx^{60} \le u$. Since $\lceil x_1\rceil < p^{\lceil x_1\rceil}$, $K \le \lceil x_1\rceil < x_1 + 1$. With $v \le 1$ and $p < x_1$, the table gives $2(x_1 + 1)x^{60} \le u$.
2. $n^3\bigl(1 + \log_p\max(\mathrm{boxes}(c, n), 1)\bigr) \le n^3(\log b)^2 \le u$, by the lemma on boxes and the table.
3. $vE_\tau \le E_\tau$, since $v \le 1$ and $E_\tau \ge 0$.
4. $5 \le (\log b)^2$.

By the theorem on one place, estimate 1, estimate 3 and $\gamma_p c^{\mathrm{low}}_\tau \le u$, for each $\tau$:
$$[\tau\in\Phi_a]s_p(a, \tau) + k\,s_p(\kappa(\tau), \tau) + v[\tau\in\Phi_a\cap S]\frac{a}{x_1} \le v\sum_eT^S_\tau(e) + \gamma_p[\tau\in\Phi_a\cap S]a + E_\tau + 2u.$$
Add over the $f$ places. The left side becomes $\mathrm{gain}_p/m + v\,\#(\Phi_a\cap S)\,a/x_1$, by the definition of the gain. On the right, $\sum_\tau E_\tau = \mathrm{coll}_p(S)$. So
$$\frac{\mathrm{gain}_p}{m} + v\,\#(\Phi_a\cap S)\frac{a}{x_1} \le v\sum_\tau\sum_eT^S_\tau(e) + \gamma_p\,\#(\Phi_a\cap S)\,a + \mathrm{coll}_p(S) + 2fu.$$
Now bound $\mathrm{div}_p(j, S)$ from below. By the lemma on boxes, its middle term is $\gamma_p\,\#(\Phi_a\cap S)\,a$. By estimate 2, its last term is at least $-fu$. By the lemma on the predicted divisibility, its first term is at least $v\sum_\tau\sum_eT^S_\tau(e) - 2fu$. So
$$v\sum_\tau\sum_eT^S_\tau(e) + \gamma_p\,\#(\Phi_a\cap S)\,a \le \mathrm{div}_p(j, S) + 3fu.$$
Combine the two inequalities. The total error is $5fu$, and $5fu \le f(\log b)^2a/(pm)$ by estimate 4. $\square$

**Remark (Formalization).** The estimates 1, 2 and 4, and the size facts in the lemmas of this section, are calls to `le_of_hasLogBound` against the table. Two instances supply the sizes of $n_{j+1}$ and of $p < x_1$. The natural number $\lceil\log_p\lceil x_1\rceil\rceil$ is `Nat.clog p ⌈x₁⌉₊`. The column count $c_\tau(k) = \kappa_1(\tau) - \lfloor(k+t+1)/2\rfloor$ uses subtraction in $\mathbb{N}$. The lower bound $c_\tau(k) \ge \kappa(\tau)$ in the lemma on the sizes of the low columns shows that this subtraction does not truncate.

### Where the bound is used

The theorem is used in [divisibility prime by prime](/chapter/divisibility/). There $S$ is the set of places whose long rows a chain has spent. For a prime that is not exceptional, the theorem on collisions (Section 5) gives $m\,\mathrm{coll}_p(\emptyset) \le \mathrm{loss}_p$, and the lemma $f(\log b)^2a/p \le \mathrm{loss}_p$ bounds the last error. So, for $S = \emptyset$ and such a prime, the theorem gives $\mathrm{div}_p(j, \emptyset) \ge \mathrm{gain}_p/m - 2\,\mathrm{loss}_p/m$.

### An example

Take $S = \emptyset$, an inert $p$ and an $a$-place $\tau$ whose partners $u(-p^e)\tau$ for odd $e$ are not $a$-places. Then $L_\tau = a$ and $L_{\tau'} = 0$. The first part of $T_\tau(e)$ is $(a/p^e - c^{\mathrm{low}}_{\tau'})_+$, while the gain has $(a/p^e - \kappa(\tau'))_+$. These differ by at most $x^{60}$, since $c^{\mathrm{low}}_{\tau'}$ is $\kappa(\tau')$ up to $x^{60}$. Now suppose instead that $u(-p^e)\tau$ is also an $a$-place for one odd $e$. Then the partner term has $(a/p^e - a - c^{\mathrm{low}}_{\tau'})_+ = 0$, but the gain has $(a/p^e - a/x_1)_+$, which is close to $a/p^e$. This gap is the collision term $a/p^e$. It is why the theorem subtracts $\mathrm{coll}_p(S)$, and why Section 5 needs $o_0(p)$ to be large when $p$ is not $\pm1$ modulo the lifts.
