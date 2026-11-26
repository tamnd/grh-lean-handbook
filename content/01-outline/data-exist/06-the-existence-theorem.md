---
title: The existence theorem
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.Parameters.IsAdmissibleData
  - New.Parameters.IsLargeScale.exists_isAdmissibleData
  - New.Parameters.IsAdmissibleData.exists_hasFields
  - New.eventually_exists_data_of_isAdmissibleData
  - New.eventually_exists_data
  - New.eventually_exists_data_scales
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The existence theorem

This section assembles the pieces. It first defines *admissible data*: explicit ranks and scales, together with any places and primes that have the required properties. It shows that admissible data exist at a large scale when the windows for primes are filled, and that admissible data are the fields of a term of the type of data. The theorem on primes in windows fills the windows, and this gives the existence theorem.

### Admissible data

**Definition (Admissible data).** Let $P$ be parameters, $x \in \mathbb{N}$ and $W \in \mathbb{R}$. Let $m, r, s, b, N \in \mathbb{N}$, let $T \subseteq \Phi$ be finite, let $p_0, p_1 \in \mathbb{N}$, let $\alpha$ be an integer of $K$ and let $\beta$ be an integer of $E$. These objects are *admissible data at $x$ and $W$* if the following hold.

1. $m$ is the least power of $2$ with $m \geq \sqrt{x}$.
2. $r$ is the least power of $3$ with $r \geq x^5$.
3. $2^s = m^{22}$.
4. $b$ is the least natural number with $q_1 \lfloor e^W \rfloor \mid b$ and $e^{W^6} < b$.
5. Every $\sigma \in T$ has class $-1$ modulo $q_0$.
6. $\operatorname{towerDeg}(s) \leq \#T \cdot \log b$.
7. $T$ is sparse for the primes up to $(r + 1 - m)(5r)$.
8. $p_0$ and $p_1$ are prime, $p_i \equiv 1 \pmod{q_2^2}$, $p_0 \neq p_1$, and $p_i \in [b^{10}, b^{11}]$.
9. $\alpha\bar\alpha = p_0 p_1$.
10. $N$ is prime, $N \equiv 1 \pmod{q_2^2}$, and $\log N_- \leq \log N \leq \log N_- + \sqrt{\log b}$, where $\log N_-$ is formed with $s$, $m$, the weights $\kappa(\tau) = b$ for $\tau \in T$ and $\kappa(\tau) = \lfloor xb/\lfloor e^W \rfloor \rfloor$ otherwise, $M = p_0 p_1$ and $\log b$.
11. $\beta\bar\beta = N$.

Lean: `New.Parameters.IsAdmissibleData` (New/Reduction/Data/Existence.lean).

Lean writes the two primes as a family `g : Fin 2 → ℕ`, and its comments call them $p_0$ and $p_1$. This book writes $p_0$, $p_1$, as in the data.

The ranks, the exponent and the scales are determined by $x$ and $W$. The places and the primes are any with the properties. This split is the point of the definition: the existence theorem can state the exact values of $x_1$, $b$, $m$ and $r$, while it leaves the places and the primes free.

### Admissible data exist

**Proposition (Admissible data at a large scale).** Let $W$ be a [large scale](/decl/New.Parameters.IsLargeScale/) for $y = \log x$ with exponent $n$. Assume that for every $k > 1$ with $(q_0 d)^k \leq W^{n + 7}$ and every $U \in [W, W^{n + 7}]$ there is a prime $p \equiv 1 \pmod{(q_0 d)^k}$ with $\log p \in [U, U + W]$. Then admissible data at $x$ and $W$ exist.
Lean: `New.Parameters.IsLargeScale.exists_isAdmissibleData` (New/Reduction/Data/Existence.lean).

*Proof.* The large scale gives $W \geq 1$, $y \geq 100$ and $2 \cdot 10^6 y \leq W$. Condition 1 of the large scale gives $\log W \leq y/600$, so $W \leq e^{y/2}$.

*Ranks.* [The lemma on the ranks](/decl/New.exists_isLeast_two_pow_three_pow/) gives $m$, $r$, $s$ with $e^{y/2} = \sqrt{x} \leq m$, $r \leq 3x^5$, $2^s = m^{22}$ and $s \leq 32 y$. At the large scale, $2^s \leq W^n$, so also $m \leq m^{22} = 2^s \leq W^n$.

*Places.* [The sparse set from the ranks](/decl/New.Parameters.exists_isSparse_of_ranks/) applies, with the hypotheses $W \leq e^{y/2} \leq m$, $2^s \leq W^n$, $10^6 y \leq W$ and conditions 8 and 9 of the large scale. It gives $T$ of class $-1$ modulo $q_0$, sparse for the primes up to $(r + 1 - m)(5r)$, with $\operatorname{towerDeg}(s) \leq \#T \cdot W^6$.

*Scales.* [The lemma on the scale $b$](/decl/New.exists_isLeast_dvd_log_log_mem_Icc/) with $q = q_1$ gives the least $b$ with $q_1 \lfloor e^W \rfloor \mid b$ and $b > e^{W^6}$, and $L = \log b \in [W^6, W^6 + 1]$. Then $\operatorname{towerDeg}(s) \leq \#T \cdot W^6 \leq \#T \cdot L$, which is property 6. Also $W^2 \leq L$ and $2 \cdot 10^8\, W \leq L$. Put $x_1 = \lfloor e^W \rfloor$. Then $x \leq x_1$, since $\log x \leq W$, and $x_1 \leq b$, since $x_1 \mid b$. So the weights lie in $[1, b]$.

*Windows.* Every window $[U, U + W]$ with $L \leq U \leq 24 m L$ holds a prime $p \equiv 1 \pmod{q_2^2}$. Indeed $q_2^2 = (q_0 d)^{2(s + 6)}$ with $2(s + 6) > 1$, and $q_2^2 \leq W^n \leq W^{n + 7}$ by condition 7. The point $U$ lies in $[W, W^{n+7}]$: first $U \geq L \geq W^6 \geq W$, and second $24 L \leq 24(W^6 + 1) \leq W^7$ because $W \geq 2 \cdot 10^8$, so $U \leq m \cdot 24L \leq W^n W^7$. The hypothesis then gives the prime.

*Primes.* For $p_0$, $p_1$, the windows with $U \in [10L, 11L] \subseteq [L, 24mL]$ are filled, and $(2h + 2)W \leq W^2 \leq L$ by condition 4. [The lemma on two primes](/decl/New.Parameters.exists_prime_pair_norm/) gives $p_0 \neq p_1$ and $\alpha$. Their product $M = p_0 p_1$ lies in $[b^{20}, b^{22}]$. For $N$, the windows with $U \in [mL, 24mL]$ are filled, $m \geq 2$, $W^2 \leq L$, the weights lie in $[1, e^L]$, and the large scale gives $q_1 d \leq e^L$. [The lemma on the prime $N$](/decl/New.Parameters.exists_prime_log_mem_Icc_mul_star_eq/) gives $N$ and $\beta$.

All eleven properties now hold. Properties 1 and 2 come from $e^{y/2} = \sqrt{x}$ and $e^{5y} = x^5$ for $x > 0$. $\square$

### Admissible data are data

A term $D$ of the type of data contains, besides the objects above, the five scale inequalities and the ranges of $m$ and $r$. At a large scale they all follow.

**Lemma (The fields of the data).** Let $W$ be a large scale for $\log x$ with exponent $n$, and let admissible data at $x$ and $W$ be given. There is a term $D$ of the type of data whose fields are the given objects, with $x_1 = \lfloor e^W \rfloor$ and the weights of property 10. It satisfies $W - 1 \leq \log x_1$ and $W^6 \leq \log b \leq W^6 + 1$.
Lean: `New.Parameters.IsAdmissibleData.exists_hasFields` (New/Reduction/Data/Existence.lean).

*Proof.* The ranges $m \in [\sqrt{x}, 2\sqrt{x}]$, $r \in [x^5, 3x^5]$ and $s \leq 32 \log x$ come from the lemma on the ranks, since a least power is unique. The bounds $\log x_1 \in [W - 1, W]$ and $\log b \in [W^6, W^6 + 1]$, $\log\log b \in [6\log W, 6 \log W + 1]$ come from Section 5. The five scale inequalities follow:

| inequality of the data | proof at a large scale |
|---|---|
| $10^{12} C_P \leq \log\log b$ | $10^{12} C_P \leq \log W \leq 6 \log W \leq \log\log b$ |
| $100 \log\log b \leq \log x$ | $100 \log\log b \leq 100(6 \log W + 1) \leq \log x$ |
| $10^6 \log x \leq \log x_1$ | $10^6 \log x \leq W - 1 \leq \log x_1$, by $2 \cdot 10^6 \log x \leq W$ |
| $10^6 \log x_1 \leq \log b$ | $10^6 \log x_1 \leq 10^6 W \leq W^6 \leq \log b$ |
| $6 \log\log x_1 \leq \log\log b$ | $6 \log \log x_1 \leq 6 \log W \leq \log\log b$ |

The other fields are the properties of the admissible data. $\square$

**Theorem (Admissible data are fields of the data).** Let $0 < \varepsilon < 1/100$. For every large integer $x$ the following holds. Any admissible data at $x$ and $W = x^{\varepsilon/6}$ are the fields of some term $D$ of the type of data. This $D$ satisfies $x^{\varepsilon/6} - 1 \leq \log x_1$ and $x^\varepsilon \leq \log b \leq x^\varepsilon + 1$.
Lean: `New.eventually_exists_data_of_isAdmissibleData` (New/Reduction/Data/Existence.lean).

*Proof.* [A large scale exists](/decl/New.Parameters.exists_eventually_isLargeScale/): $W = x^{\varepsilon/6}$ is a large scale for $\log x$ with some exponent $n$, for every large $x$. Apply [the lemma on the fields](/decl/New.Parameters.IsAdmissibleData.exists_hasFields/), and use $(x^{\varepsilon/6})^6 = x^\varepsilon$. $\square$

### Statement and proof

**Theorem (Existence of the data).** Let $P$ be parameters and $0 < \varepsilon < 1/100$. For every large integer $x$ there is a term $D$ of the type of data for $P$ such that:

1. the length of $D$ is $x$;
2. $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$;
3. $b$ is the least natural number with $q_1 x_1 \mid b$ and $\exp(x^\varepsilon) < b$;
4. $m$ is the least power of $2$ with $m \geq \sqrt{x}$;
5. $r$ is the least power of $3$ with $r \geq x^5$;
6. $x^{\varepsilon/6} - 1 \leq \log x_1$;
7. $x^\varepsilon \leq \log b \leq x^\varepsilon + 1$.

Lean: `New.eventually_exists_data` (New/Reduction/Data/Existence.lean).

*Proof.* Let $n$ be the exponent of [the large scales](/decl/New.Parameters.exists_eventually_isLargeScale/). Put $Q = q_0 d$, which is divisible by $4$, and $A = n + 7$. [The theorem on windows](/decl/New.exists_prime_modEq_one_log_mem/) holds for every large $W$, and $W = x^{\varepsilon/6}$ tends to infinity with $x$. So for every large $x$ three things hold at once: $W$ is a large scale for $\log x$ with exponent $n$; every window $[U, U + W]$ with $U \in [W, W^{n+7}]$ holds a prime $\equiv 1 \pmod{(q_0 d)^k}$ for each $k > 1$ with $(q_0 d)^k \leq W^{n+7}$; and the theorem that admissible data are fields applies. [The proposition on admissible data](/decl/New.Parameters.IsLargeScale.exists_isAdmissibleData/) gives admissible data at $x$ and $W$. [The theorem on fields](/decl/New.eventually_exists_data_of_isAdmissibleData/) gives $D$. Its fields are the admissible data, so items 2 to 5 are properties 1, 2 and 4 of the admissible data, rewritten with $x_1 = \lfloor e^W \rfloor$ and $W^6 = x^\varepsilon$. Items 6 and 7 are part of the theorem on fields. $\square$

The proof is short because the earlier statements are exactly what it needs. The finding F-097 of the [register of findings](/chapter/register-of-findings/) asks whether the uniformity of the theorem on windows is what the data need. Here the two statements meet: the theorem on windows is applied with $Q = q_0 d$ and $A = n + 7$, and its conclusion is the hypothesis of the proposition. Lean accepts this step, if the reported checks hold.

### What the end of the proof uses

**Corollary (The scales at $x$).** Let $0 < \varepsilon < 1/100$. For every large integer $x$ there is a term $D$ of the type of data with length $x$ and
$$\log b \leq 2x^\varepsilon, \qquad x^{1/2} \leq m, \qquad x^{\varepsilon/12} \leq \log x_1.$$
Lean: `New.eventually_exists_data_scales` (New/Reduction/OneSidedBound.lean).

*Proof.* Take $D$ from [the existence theorem](/decl/New.eventually_exists_data/). Then $\log b \leq x^\varepsilon + 1 \leq 2x^\varepsilon$, since $x \geq 1$. The bound $\sqrt{x} \leq m$ is part of the range of $m$. For the last bound, let $x$ be so large that $t = x^{\varepsilon/12} \geq 2$. Then $\log x_1 \geq x^{\varepsilon/6} - 1 = t^2 - 1 \geq 2t - 1 \geq t$. $\square$

The corollary is the input to [the main inequality and the end of the proof](/chapter/main-inequality/). There the source bounds
$$R_{q_0}(x) \leq \frac{\varphi(q_0) (\log b)^6}{m} + |R_{q_0}(x_1)| + \log b\, |R_1(x_1)|.$$
The first term is at most $\varphi(q_0)\, 64\, x^{6\varepsilon} / \sqrt{x}$. The prime number theorem with error $(\log y)^{-B}$ for some $B \geq 24/\varepsilon$ gives $|R_{q_0}(x_1)|, |R_1(x_1)| \leq (\log x_1)^{-B} \leq x^{-B\varepsilon/12} \leq x^{-2}$ for large $x$. The source then gets $R_{q_0}(x) \leq (64 \varphi(q_0) + 3) x^{-1/2 + 6\varepsilon}$. The bound $x^{\varepsilon/12} \leq \log x_1$ is why $x_1$ must be so large: the prime number theorem must already be very precise at $x_1$.

### A sense of the sizes

**Example (The thresholds).** Take $q_0 = 18480$ and $d = 9239$. Then $d$ is prime and $d = q_0/2 - 1$, so these are parameters. Take $\varepsilon = 1/200$, so $W = x^{1/1200}$. The exponent $n$ must satisfy $n/1200 > 99 \cdot 18480 \cdot 9239$, so $n > 2.02 \cdot 10^{13}$. Condition 8 of a large scale, $(5184 \log x)^n \leq x^{1/1200}$, then asks for $\log x \geq 1200\, n \log(5184 \log x)$. This needs $\log x$ at least about $1.2 \cdot 10^{18}$. Condition 2 and the threshold of the theorem on windows add more. So the existence theorem speaks about $x$ beyond $\exp(10^{18})$. This is no defect: the one-sided bound is a statement about all large $x$, and the plan needs only that the threshold exists.

**Remark (Formalization).** Four points matter for the meaning. First, every statement of this section is eventual along the filter `atTop` of the natural numbers, and no threshold is computed. The thresholds come from `Filter.Eventually` statements in the large scales and in the theorem on windows, and the latter has no explicit threshold (Section 4). Second, the term $D$ is an existential witness. The theorem pins down $x$, $x_1$, $b$, $m$ and $r$ exactly, with $s$ fixed by $2^s = m^{22}$, but not the places or the primes. The fields of $D$ are matched with the admissible data by `New.Data.HasFields`, which uses heterogeneous equality where the type of a field depends on $s$. Third, $D$ stores $\log x$, $\log x_1$ and $\log b$ as real fields with $e^{\log x} = x$, and the scale inequalities are stated in logarithms, for example $6 \log\log x_1 \leq \log\log b$ for $(\log x_1)^6 \leq \log b$. Fourth, the weight off $\Phi_b$ is the natural-number quotient $\lfloor x b / x_1 \rfloor$, as in Section 5. Since $x_1$ divides $b$, the quotient is exact: $xb/x_1 = x \cdot (b/x_1)$.
