---
title: The gain and its measures
lean:
  - New/UpperBound/Size/ShortColumns.lean
  - New/UpperBound/Divisibility/JetExponent.lean
  - New/Derivatives/Sharpness/NearPairs.lean
decls:
  - New.Data.localPrimeSum
  - New.Data.localPrimeSumTotal
  - New.Data.gain
  - New.Data.IsSmallNonsplit
  - New.Data.IsPlusMinusOneModLifts
  - New.Data.loss
  - New.Data.ceilLogLifts
  - New.Data.transferExponent
  - New.Data.collisionExponent
  - New.Data.o₀
  - New.Data.IsExceptional
  - New.Data.IsCollision
  - New.Data.collisionSum
  - New.Data.le_loss
  - New.Data.ne_d_of_placeClass_eq
  - New.Data.placeOfInt_mul_mem_aPlaces_iff
  - New.Data.IsCollision.ne_and_odd_and_dvd
  - New.Data.collisionSum_le
  - New.Data.mul_collisionSum_le_loss
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The gain and its measures

The arithmetic half of the chapter starts here. This section fixes the numbers attached to a prime $p$, restates the gain of [Theorem A and its plan](/chapter/theorem-a-plan/), and defines the loss and the collisions. It ends with the bound $m\,\mathrm{coll}_p(\emptyset) \le \mathrm{loss}_p$ for every prime $p < x_1$ that does not split and is not exceptional.

### Background for the gain

1. The infinite places of $E$ form a group $\Phi \cong (\mathbb{Z}/q_1)^\times$. For an integer $\nu$ the place $u(\nu)$ is the place of $\nu \bmod q_1$ if $\nu$ is prime to $q_1$, and the identity place otherwise. For $m \mid q_1$ the class of a place modulo $m$ is its image in $(\mathbb{Z}/m)^\times$, the class of $u(\nu)$ modulo $q_0$ is $\nu \bmod q_0$ for $\nu$ prime to $q_0$, and $u(\nu)^e = u(\nu^e)$ ([fields, places and twists](/chapter/fields-places-twists/), Section 4).
2. The $a$-places are the places of class $1$ modulo $q_0$, the $b$-places $\Phi_b$ are a set of places of class $-1$, and the weight is $\kappa = b$ on $\Phi_b$ and $\kappa = a/x_1$ elsewhere, with $a/x_1 \le \kappa \le b$ ([the data and its sizes](/chapter/data-and-sizes/), Section 4).
3. For every $n \ge 0$, $d^n \not\equiv -1 \pmod{q_0}$ ([fields, places and twists](/chapter/fields-places-twists/), Section 2).
4. A prime $p \mid q_1$ has $\chi_K(p) = 1$, and a prime $p \ne d$ splits in $K$ if and only if $\chi_K(p) = 1$ ([fields, places and twists](/chapter/fields-places-twists/), Section 2).
5. The partner of $\tau$ at the exponent $e$ is $\tau'_e = u(-p^e)\tau$ ([the CM curve, its formal group and the normal form](/chapter/cm-formal-group/), Section 6).

### The numbers at a prime

Let $p$ be a prime. As in [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/), Section 1, $v(\pi_p)$ is $\frac12$ if $p = d$ and $1$ otherwise, $q_p$ is $p^2$ if $p$ is inert and $p$ otherwise, and $\rho_p = v(\pi_p)/(q_p - 1)$. The set $I_p$ is the set of odd $e \ge 1$ if $\chi_K(p) = -1$, the set of all $e \ge 1$ if $p = d$, and empty otherwise.

**Definition (The full gain per box).** $\gamma_p = 1/(p-1) - \rho_p$.

Lean: `New.gammaPrime` (Lib/CM/FormalGroup/PrimeNotation.lean).

If $p$ splits, $\rho_p = 1/(p-1)$ and $\gamma_p = 0$. If $p$ is inert, $\gamma_p = 1/(p-1) - 1/(p^2-1) = p/(p^2-1)$. If $p = d$, $\gamma_p = 1/(d-1) - 1/(2d-2) = 1/(2d-2)$. In all cases $0 \le \gamma_p \le 1/(p-1) \le 1$ (`New.gammaPrime_nonneg`, `New.gammaPrime_le_one_div`, `New.gammaPrime_le_one`).

**Lemma (The full gain as a series).** $\gamma_p = \sum_{e\in I_p}v(\pi_p)\,p^{-e}$. So for every real $c$, $\sum_{e\in I_p}c\,p^{-e} = c\,\gamma_p/v(\pi_p)$.

Lean: `New.hasSum_gammaPrime`, `New.hasSum_div_pow_positivePartnerExponents` (Lib/CM/FormalGroup/PrimeNotation.lean).

*Proof.* If $p$ splits, both sides are $0$. If $p$ is inert, $\sum_{e \text{ odd}}p^{-e} = p^{-1}/(1 - p^{-2}) = p/(p^2-1)$. If $p = d$, $\frac12\sum_{e\ge1}d^{-e} = \frac12\cdot 1/(d-1)$. The second claim follows on multiplying by $c/v(\pi_p)$. $\square$

**Lemma.** If $\chi_K(p) \ne 1$, then $1 \in I_p$.

Lean: `New.one_mem_positivePartnerExponents` (Lib/CM/FormalGroup/PrimeNotation.lean).

*Proof.* Then $p = d$ or $\chi_K(p) = -1$, and $1$ is odd. $\square$

### The gain

These definitions are those of [Theorem A and its plan](/chapter/theorem-a-plan/), Section 3. They are restated here, since the proofs of Sections 6 and 7 work with each term.

**Definition (The local prime sum).** For a real $y$ and a place $\sigma$,
$$s_p(y, \sigma) = v(\pi_p)\sum_{e\in I_p}\Bigl(\frac{y}{p^e} - \kappa\bigl(u(-p^e)\sigma\bigr)\Bigr)_+.$$
The total is $F(p) = \sum_{\sigma\in\Phi}s_p(\kappa(\sigma), \sigma)$.

Lean: `New.Data.localPrimeSum`, `New.Data.localPrimeSumTotal` (New/UpperBound/Size/ShortColumns.lean).

**Definition (The gain).** $\mathrm{gain}_p = m\bigl(\sum_{\tau\in\Phi_a}s_p(a, \tau) + k\,F(p)\bigr)$.

Lean: `New.Data.gain` (New/UpperBound/Size/ShortColumns.lean).

The series in $s_p$ converges: its terms are at most $y/p^e$ (`New.Data.summable_posPart_sub_weight`). The first part of the gain measures the long rows of the diagrams: at an $a$-place a diagram has $a$ columns of height $1$. The second part measures the $k$ columns of height $k$ that each place carries at each lift.

**Remark (Formalization).** The sums over $e \in I_p$ are `tsum` over $\mathbb{N}$ with the term $0$ for $e \notin I_p$. A `tsum` of a family that is not summable is $0$, but the families here are summable at every prime. For $\nu$ not prime to $q_1$ the place $u(\nu)$ is the identity place. By fact 4 this happens for $\nu = -p^e$ only if $\chi_K(p) = 1$, and then $I_p$ is empty.

### Classes of primes and the loss

**Definition (Small nonsplit primes).** A natural number $p$ is *small nonsplit* if $p < x_1$ and $\chi_K(p) \ne 1$.

Lean: `New.Data.IsSmallNonsplit` (New/UpperBound/Size/ShortColumns.lean).

**Definition.** The number $p$ is *$\pm1$ modulo the lifts* if $m \mid p - 1$ or $m \mid p + 1$.

Lean: `New.Data.IsPlusMinusOneModLifts` (New/UpperBound/Size/ShortColumns.lean).

**Definition (The loss).** $\mathrm{loss}_p = f\,(\log b)^2\,\dfrac{a}{p}\,\mu_p$, where $\mu_p = m$ if $p$ is $\pm1$ modulo the lifts, and $\mu_p = 1$ otherwise.

Lean: `New.Data.loss` (New/UpperBound/Size/ShortColumns.lean).

**Lemma.** $f(\log b)^2\,a/p \le \mathrm{loss}_p$.

Lean: `New.Data.le_loss` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* $\mu_p \ge 1$, since $m \ge 10^4$. The other factors are nonnegative. $\square$

**Definition (The logarithm of m at p).** $\mathfrak r_p$ is the least natural number with $m \le p^{\mathfrak r_p}$.

Lean: `New.Data.ceilLogLifts` (New/UpperBound/Size/ShortColumns.lean).

**Definition (Exponents).** The transfer exponent is $\nu_p = \mathfrak r_p f(n_m + \mathfrak r_p)$, and the collision exponent is $j_p = \lceil 2mfa/p\rceil$.

Lean: `New.Data.transferExponent`, `New.Data.collisionExponent` (New/UpperBound/Size/ShortColumns.lean).

These two numbers are used in [divisibility prime by prime](/chapter/divisibility/), where the gain is moved from stage to stage. This chapter only defines them.

**Definition (The order at p).** $o_0(p)$ is the order of the class of $u(-p)$ modulo $q_0$. For $p$ prime to $q_0$ it is the order of $-p$ in $(\mathbb{Z}/q_0)^\times$.

Lean: `New.Data.o₀` (New/UpperBound/Size/ShortColumns.lean).

**Definition (Exceptional primes).** The prime $p$ is *exceptional* if $\chi_K(p) = -1$, $p$ is not $\pm1$ modulo the lifts, $o_0(p)$ is odd, and $o_0(p) \le \mathfrak r_p$.

Lean: `New.Data.IsExceptional` (New/UpperBound/Size/ShortColumns.lean).

For an exceptional prime, $e = o_0(p)$ is odd, so it lies in $I_p$, and $u(-p^e) = u(-p)^e$ has class $1$. So for every $a$-place $\tau$ the partner $u(-p^e)\tau$ is again an $a$-place, and $(\tau, e)$ is a collision at a small exponent. Those primes are treated apart in [divisibility prime by prime](/chapter/divisibility/).

**Remark (Formalization).** In $m \mid p - 1$ the subtraction is in $\mathbb{N}$, so for $p = 0$ it reads $m \mid 0$. The definitions are used only at primes. For $p \mid q_1$ the value $u(-p)$ is the identity place, so $o_0(p) = 1$. The loss uses `if` with classical decidability.

### Collisions

**Definition (Collision).** Let $S$ be a set of places. A pair $(\tau, e)$ is a *collision outside $S$* if $e \in I_p$, and both $\tau$ and $u(-p^e)\tau$ are $a$-places not in $S$. The collision sum is
$$\mathrm{coll}_p(S) = \sum_{\tau\in\Phi}\ \sum_{e\,:\,(\tau, e)\text{ collision}}\frac{a}{p^e}.$$

Lean: `New.Data.IsCollision`, `New.Data.collisionSum` (New/UpperBound/Size/ShortColumns.lean).

**Lemma.** If the place $u(-p^e)\sigma$ has the same class modulo $q_0$ as $\sigma$, then $p \ne d$.

Lean: `New.Data.ne_d_of_placeClass_eq` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Suppose $p = d$. The prime $d$ is prime to $q_0$, so the class of $u(-d^e)$ is $-d^e \bmod q_0$, and the hypothesis says $-d^e \equiv 1$. Then $d^e \equiv -1 \pmod{q_0}$, against fact 3. $\square$

**Lemma.** Let $e$ be odd and $\tau \in \Phi_a$. Then $u(-p^e)\tau \in \Phi_a$ if and only if $o_0(p) \mid e$.

Lean: `New.Data.placeOfInt_mul_mem_aPlaces_iff` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* For odd $e$, $-p^e = (-p)^e$, so $u(-p^e) = u(-p)^e$ by fact 1. The class of $\tau$ is $1$, so the class of the product is the $e$-th power of the class of $u(-p)$. It is $1$ if and only if the order $o_0(p)$ divides $e$. $\square$

**Lemma.** If $(\tau, e)$ is a collision outside $S$, then $p \ne d$, $e$ is odd, and $o_0(p) \mid e$.

Lean: `New.Data.IsCollision.ne_and_odd_and_dvd` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Both $\tau$ and $u(-p^e)\tau$ have class $1$, so $p \ne d$ by the lemma before the previous one. As $e \in I_p$ and $p \ne d$, $\chi_K(p) = -1$ and $e$ is odd. The previous lemma gives $o_0(p) \mid e$. $\square$

**Lemma (Collision sum).** Let $o \ge 0$, and suppose that every collision $(\tau, e)$ outside $S$ has $e \ge o$. Then $\mathrm{coll}_p(S) \le 2fa/p^o$.

Lean: `New.Data.collisionSum_le` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* Fix $\tau$. Write the exponents as $e = o + l$ with $l \ge 0$. The term at $e$ is at most $\frac{a}{p^o}\cdot p^{-l} \le \frac{a}{p^o}\cdot 2^{-l}$, since $p \ge 2$. The geometric series gives $\sum_l 2^{-l} = 2$, so the inner sum is at most $2a/p^o$. There are $f$ places $\tau$. $\square$

**Theorem (Collisions cost one loss).** Let $p$ be a small nonsplit prime that is not exceptional. Then $m\,\mathrm{coll}_p(\emptyset) \le \mathrm{loss}_p$.

Lean: `New.Data.mul_collisionSum_le_loss` (New/UpperBound/Divisibility/JetExponent.lean).

*Proof.* The table of sizes gives $2 \le (\log b)^2$, so $2fa\mu_p/p \le \mathrm{loss}_p$. Two cases.

1. $p$ is $\pm1$ modulo the lifts. Every $e \in I_p$ is at least $1$. The lemma on the collision sum with $o = 1$ gives $m\,\mathrm{coll}_p(\emptyset) \le 2mfa/p = 2fa\mu_p/p$.
2. $p$ is not $\pm1$ modulo the lifts. Let $(\tau, e)$ be a collision. By the previous lemma, $p \ne d$, $e$ is odd and $o_0(p) \mid e$. As $p \ne d$ and $\chi_K(p) \ne 1$, $\chi_K(p) = -1$. A divisor of an odd number is odd, so $o_0(p)$ is odd. The prime is not exceptional, so $o_0(p) > \mathfrak r_p$. So $e \ge o_0(p) \ge \mathfrak r_p + 1$. The lemma on the collision sum with $o = \mathfrak r_p + 1$ and $m \le p^{\mathfrak r_p}$ give
$$m\,\mathrm{coll}_p(\emptyset) \le p^{\mathfrak r_p}\cdot\frac{2fa}{p^{\mathfrak r_p + 1}} = \frac{2fa}{p} = \frac{2fa\mu_p}{p}.$$

In both cases the bound is at most $\mathrm{loss}_p$. $\square$

### An example of the gain

As a model, take $d = 7$. The parameters of the data need a much larger $d$, but the arithmetic at one prime is the same. Let $p = 3$, which is inert since $3$ is not a square modulo $7$. Then $v(\pi_3) = 1$, $\rho_3 = 1/8$, $\gamma_3 = 1/2 - 1/8 = 3/8$, and $I_3 = \{1, 3, 5, \dots\}$. The series of the lemma on the full gain is $3^{-1} + 3^{-3} + \cdots = (1/3)/(1 - 1/9) = 3/8$.

For the local prime sum at an $a$-place with $y = a$, the term at $e$ is $(a/3^e - \kappa(u(-3^e)\tau))_+$. If $u(-3^e)\tau \notin \Phi_b$, the weight is $a/x_1$, and the term is positive while $3^e < x_1$. If $u(-3^e)\tau \in \Phi_b$, the weight is $b = a/x$, and the term is positive only while $3^e < x$. A collision at $e$ is a term where the partner is again an $a$-place. That happens only if $o_0(3)$ divides $e$. In the case where $3$ is not $\pm1$ modulo $m$ and not exceptional, the first collision has $e > \mathfrak r_3$, so $3^e > m$. The term $a/3^e$ is then less than $a/m$, and the $m$ lifts together lose at most about $2fa/3$.
