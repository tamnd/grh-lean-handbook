---
title: Exceptional primes and induced primes
lean:
  - New/UpperBound/Divisibility/MarkedPrimes.lean
decls:
  - New.Data.ceilLogLifts_le_towerExp
  - New.Data.ceilLogLifts_le_l₀
  - New.Data.two_pow_dvd_right_of_dvd_mul
  - New.Data.IsExceptional.m_dvd_orderOf
  - New.Data.IsExceptional.q_eq_pow_orderOf
  - New.Data.IsExceptional.star_ne
  - New.Data.IsSmallNonsplit.not_dvd_M_mul_N
  - New.Data.inducedPlace
  - New.Data.inducedPlace_mul
  - New.Data.inducedPlace_neg_pow_mul_of_odd
  - New.Data.inducedPlace_eq_or_star_iff
  - New.Data.HasExceptionalOrbits
  - New.Data.IsExceptional.hasExceptionalOrbits
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exceptional primes and induced primes

This section studies the primes of $E$ above an exceptional prime $p$. Each infinite place $\tau$ induces one of them, $w_\tau$. The main results say which places induce the same prime or the conjugate prime, that $w_\tau$ is never self-conjugate, and that its norm is $p^o$ with $m \mid o$. Section 3 builds marked sets from these primes.

### Exceptional primes

The classes of primes come from [short columns and the gain](/chapter/short-columns-gain/). A prime $p$ is *small and non-split* if $p < x_1$ and $\chi_K(p) \ne 1$. It is $\pm 1$ modulo $m$ if $m \mid p - 1$ or $m \mid p + 1$. Let $r_p = \lceil \log_p m \rceil$ be the least natural number $r$ with $m \le p^r$. Let $o_0$ be the order of the class of $[-p]$ in $(\mathbb Z/q_0)^\times$. Then $p$ is *exceptional* if

$$\chi_K(p) = -1, \qquad p \not\equiv \pm 1 \pmod m, \qquad o_0 \text{ is odd}, \qquad o_0 \le r_p.$$

The first condition says that $p$ is inert in $K$. Write $o$ for the order of $[-p]$ in the group $\Phi \cong (\mathbb Z/q_1)^\times$. The reduction from $q_1$ to $q_0$ is a homomorphism, so $o_0 \mid o$.

**Remark (Formalization).** The place $[\nu]$ named by an integer is the identity place when $\nu$ is not prime to $q_1$. This junk value does not occur here: an inert prime does not divide $q_1 d$, by [the field E at the primes](/chapter/field-at-primes/). The number $r_p$ is `Nat.clog p m`. In "$m \mid p - 1$" the subtraction is truncated at $0$; for a prime $p \ge 2$ it is the true difference.

**Lemma.** $r_p \le s$, where $2^s = m^{22}$.

Lean: `New.Data.ceilLogLifts_le_towerExp` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Write $m = 2^{e+1}$ and $s = 22(e+1)$. Then $m = 2^{e+1} \le 2^s \le p^s$, since $p \ge 2$. So the least $r$ with $m \le p^r$ is at most $s$. $\square$

**Lemma.** $r_p \le l_0$, where $l_0$ is the least power of $3$ above $27s$.

Lean: `New.Data.ceilLogLifts_le_l₀` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* By the table of sizes, $m \le m^{594} \le 2^{l_0} \le p^{l_0}$. $\square$

The first lemma also gives an instance of the size automation of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes): $r_p$ has the order of magnitude of at most $\log \log x_1$.

### The order of $-p$

The next lemma is the step at $2$ of the main lemma. It compares $2$-adic valuations.

**Lemma.** Let $e, s, q, o$ be natural numbers with $2e < s$. If $2^s \mid qo$ and $2^{e+1} \nmid q$, then $2^{e+1} \mid o$.

Lean: `New.Data.two_pow_dvd_right_of_dvd_mul` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* From $2^s \mid qo$ we get $qo \ne 0$ or $qo = 0$. If $q = 0$, then $2^{e+1} \mid q$, a contradiction. If $o = 0$, the claim holds. Otherwise $v_2(q) + v_2(o) = v_2(qo) \ge s$ and $v_2(q) \le e$. So $v_2(o) \ge s - e > e$, and $v_2(o) \ge e + 1$. $\square$

The input from lifting the exponent is this. If $\nu \in \mathbb Z$, $o > 0$ and $\nu^o \equiv 1 \pmod{2^{s+1}}$, then $2^s$ divides $(\nu - 1)o$ or $(\nu + 1)o$. It is the lemma `New.two_pow_dvd_or_of_pow_eq_one` of the source (Lib/General/NumberTheory/ImaginaryQuadraticField.lean). It follows from the classical formula $v_2(\nu^{2o} - 1) = v_2(\nu^2 - 1) + v_2(o)$ for odd $\nu$.

**Lemma.** Let $p$ be exceptional. Then $m$ divides the order $o$ of $[-p]$ in $\Phi$.

Lean: `New.Data.IsExceptional.m_dvd_orderOf` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Write $m = 2^{e+1}$ and $s = 22(e+1)$. Since $p$ is inert, $p \nmid q_1$. The number $2^{s+1}$ divides $q_1$, and the class of $[-p]$ modulo $2^{s+1}$ is $-p$. Since $[-p]^o = 1$, we get $(-p)^o \equiv 1 \pmod{2^{s+1}}$. Lifting the exponent gives $2^s \mid (-p - 1)o$ or $2^s \mid (-p + 1)o$. In absolute values these are $2^s \mid (p+1)o$ and $2^s \mid (p-1)o$. Since $p \not\equiv \pm 1 \pmod m$, neither $p + 1$ nor $p - 1$ is divisible by $2^{e+1}$. Also $2e < 22(e+1) = s$. The previous lemma gives $2^{e+1} \mid o$ in both cases. $\square$

So $o$ is even, and $o$ is large: $o \ge m \ge \sqrt x$. In contrast, $o_0 \le r_p$ is small.

### Induced primes

**Definition (Induced prime).** For $\sigma \in \Phi$, the induced prime $w_\sigma$ is the prime of $E$ induced by the embedding $\iota_p \circ \sigma : E \to \mathbb C_p$. Here $\sigma$ is read as the complex embedding that the CM type selects at $\sigma$. The prime is the centre on $\mathcal O_E$ of the valuation ring $\{y \in E : |\iota_p \sigma(y)|_p \le 1\}$.

Lean: `New.Data.inducedPlace` (New/UpperBound/Divisibility/MarkedPrimes.lean).

The prime $w_\sigma$ lies above $p$, because $|p|_p < 1$ (`New.Data.p_mem_inducedPlace`). The group $\Phi = \mathrm{Gal}(E/K)$ acts on primes. In the source this action is the pullback: $\tau \cdot w$ is the prime $\{y : \tau(y) \in w\}$.

**Lemma.** For $\sigma, \tau \in \Phi$, $w_{\sigma\tau} = \tau \cdot w_\sigma$.

Lean: `New.Data.inducedPlace_mul` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The embedding of $\sigma\tau$ is the composite of the embedding of $\sigma$ with $\tau$ (`New.Parameters.phi_mul`). So $y$ lies in $w_{\sigma\tau}$ if and only if $\tau(y)$ lies in $w_\sigma$. $\square$

The decomposition group of a prime above an inert $p$ is known from [the field E at the primes](/chapter/field-at-primes/): if $\chi_K(p) = -1$ and $w$ lies above $p$, then $v \cdot w = w$ if and only if $v$ is an even power of $[-p]$ ([Lemma](/decl/New.Parameters.smul_eq_self_iff_of_inert/)), and $v \cdot w = \bar w$ if and only if $v$ is an odd power of $[-p]$ ([Lemma](/decl/New.Parameters.smul_eq_star_iff_of_inert/)). The Frobenius of $w$ over $\mathbb Q$ is the pair $([-p], c)$, where $c$ is complex conjugation.

**Lemma.** Let $\chi_K(p) = -1$ and let $e$ be odd. For every $\sigma \in \Phi$, $w_{[-p^e]\sigma} = \bar w_\sigma$.

Lean: `New.Data.inducedPlace_neg_pow_mul_of_odd` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* By the previous lemma $w_{[-p^e]\sigma} = [-p^e] \cdot w_\sigma$. Since $e$ is odd, $-p^e = (-p)^e$, so $[-p^e] = [-p]^e$ is an odd power of $[-p]$. It sends $w_\sigma$ to $\bar w_\sigma$. $\square$

**Lemma.** Let $\chi_K(p) = -1$ and $\sigma, \tau \in \Phi$. Then $w_\sigma = w_\tau$ or $w_\sigma = \bar w_\tau$ if and only if $\sigma = [-p]^i \tau$ for some $i \ge 0$.

Lean: `New.Data.inducedPlace_eq_or_star_iff` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Write $w_\sigma = (\sigma\tau^{-1}) \cdot w_\tau$. By the decomposition group, this equals $w_\tau$ if and only if $\sigma\tau^{-1}$ is an even power of $[-p]$, and equals $\bar w_\tau$ if and only if it is an odd power. Every $i \ge 0$ is even or odd. $\square$

**Lemma.** Let $p$ be exceptional and $w$ a prime of $E$ above $p$. Then the norm of $w$ is $p^o$, where $o$ is the order of $[-p]$.

Lean: `New.Data.IsExceptional.q_eq_pow_orderOf` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* For inert $p$ the norm is $p^{\mathrm{lcm}(o, 2)}$ ([Lemma](/decl/New.Parameters.q_eq_pow_lcm_of_inert/)). By the lemma on the order, $2 \mid m \mid o$, so $\mathrm{lcm}(o, 2) = o$. $\square$

**Lemma.** Let $p$ be exceptional and $w$ a prime of $E$ above $p$. Then $\bar w \ne w$.

Lean: `New.Data.IsExceptional.star_ne` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Suppose $\bar w = w$. The identity place fixes $w$, so it sends $w$ to $\bar w$. By the decomposition group, $1 = [-p]^i$ for an odd $i$. Then $o \mid i$. But $2 \mid m \mid o$, so $i$ is even, a contradiction. $\square$

So every prime of $E$ above an exceptional prime is split over the maximal real subfield $E^+$: it differs from its conjugate.

**Example.** Let the order of $[-p]$ be $o = 2u$. The orbit of $\tau$ under $[-p]$ is $\tau, [-p]\tau, \dots, [-p]^{2u-1}\tau$. The places at even steps induce $w_\tau$, and those at odd steps induce $\bar w_\tau$. Each of the two primes is induced by exactly $u$ places of the orbit. The primes of $E$ above $p$ have norm $p^{2u}$, and there are $2f/(2u) = f/u$ of them.

### The size of $p$

**Lemma.** Let $p < x_1$ with $\chi_K(p) \ne 1$. Then $p \nmid M$, $p \ne N$ and $p \nmid MN$.

Lean: `New.Data.IsSmallNonsplit.not_dvd_M_mul_N` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The primes $p_0$, $p_1$ and $N$ are at least $x_1$ by the table of sizes. So $p$ differs from all three. Since $M = p_0p_1$ and all four numbers are prime, $p$ divides neither $M$ nor $MN$. $\square$

### The orbit properties together

The source collects the properties above in one structure, which later chapters cite.

**Definition.** For a prime $p$, the property $\mathrm{HasExceptionalOrbits}(p)$ is the conjunction of:

1. $o_0$ is odd, and $o_0 \le r_p \le l_0$;
2. $m$ divides the order $o$ of $[-p]$;
3. each induced prime $w_\tau$ has norm $p^o$;
4. for each $\tau$ and each odd $e$, $w_{[-p^e]\tau} = \bar w_\tau$;
5. for each $\tau$, $\bar w_\tau \ne w_\tau$;
6. for all $\sigma, \tau$: $w_\sigma \in \{w_\tau, \bar w_\tau\}$ if and only if $\sigma = [-p]^i\tau$ for some $i \ge 0$.

Lean: `New.Data.HasExceptionalOrbits` (New/UpperBound/Divisibility/MarkedPrimes.lean).

**Theorem.** If $p$ is exceptional, then $\mathrm{HasExceptionalOrbits}(p)$ holds.

Lean: `New.Data.IsExceptional.hasExceptionalOrbits` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Item 1 is the definition and the bound $r_p \le l_0$. Item 2 is the lemma on the order. Items 3 and 5 are the two lemmas on primes above $p$, applied to $w_\tau$, which lies above $p$. Items 4 and 6 are the lemmas on induced primes, with $\chi_K(p) = -1$. $\square$

The mark operator of [divisibility prime by prime](/chapter/divisibility/) uses this theorem.
