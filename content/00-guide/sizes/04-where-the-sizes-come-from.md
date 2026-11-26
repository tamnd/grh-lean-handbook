---
title: Where the sizes come from
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/OneSidedBound.lean
  - Lib/Analytic/Primes.lean
decls:
  - New.eventually_exists_data
  - New.Parameters.IsLargeScale
  - New.Parameters.exists_eventually_isLargeScale
  - New.log_floor_exp_mem_Icc
  - New.Parameters.IsLargeScale.exists_isLeast_dvd_log_log_mem_Icc
  - New.Parameters.IsAdmissibleData.exists_hasFields
  - New.eventually_exists_data_scales
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Where the sizes come from

The structure `New.Data` asks for the five scale inequalities. It does not say how large $x_1$ and $b$ are in terms of $x$. The construction of the data at the end of the proof gives the exact values. These values matter twice. They show that the five inequalities can hold together. They also give two bounds that the five inequalities do not give, and that the last step of the proof needs: $\log b \leq 2x^\varepsilon$ and $\log x_1 \geq x^{\varepsilon/12}$. The full construction is the subject of [the data exist](/chapter/data-exist/). This section extracts the sizes from it.

### The existence theorem

**Theorem (Existence of the data).** Let $P$ be parameters and let $0 < \varepsilon < 1/100$. For every large enough integer $x$ there are data $D$ with

1. $D.\mathrm{natX} = x$;
2. $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$;
3. $b$ is the least natural number with $q_1 x_1 \mid b$ and $\exp(x^\varepsilon) < b$;
4. $m$ is the least power of $2$ with $\sqrt{x} \leq m$, and $r$ is the least power of $3$ with $x^5 \leq r$;
5. $x^{\varepsilon/6} - 1 \leq \log x_1$ and $x^\varepsilon \leq \log b \leq x^\varepsilon + 1$.

Lean: `New.eventually_exists_data` (New/Reduction/Data/Existence.lean).

The theorem is at Existence.lean:898. The second item is the statement `D.natX₁ = ⌊exp ((x : ℝ) ^ (ε / 6))⌋₊`, so $x_1$ is the floor of $\exp(x^{\varepsilon/6})$, with the natural floor $\lfloor\cdot\rfloor_+$ of Mathlib. In the third item, $q_1 = q_0 \operatorname{towerDeg}(s)$ is the order of the root of unity of the field of the data, and $s$ is fixed by $2^s = m^{22}$.

*Proof sketch.* The proof has three steps, which the rest of this section describes. First, $W = x^{\varepsilon/6}$ is a large scale for $y = \log x$ (`New.Parameters.exists_eventually_isLargeScale`). Second, admissible data exist at $x$ and $W$ (`New.Parameters.IsLargeScale.exists_isAdmissibleData`, Existence.lean:820), given prime windows from `New.exists_prime_modEq_one_log_mem` (Lib/Analytic/Primes.lean:389) with the exponent $n + 7$. Third, admissible data are the fields of some $D$, and the five inequalities hold (`New.Parameters.IsAdmissibleData.exists_hasFields`). $\square$

### Large scales

**Definition (Large scale).** Let $P$ be parameters, $n$ a natural number, and $y, W$ real numbers. Then $W$ is a large scale for $y$ with exponent $n$ if

1. $100(6 \log W + 1) \leq y$;
2. $10^{12} C_P \leq \log W$;
3. $2 \cdot 10^6 \, y \leq W$;
4. $2 h_K + 2 \leq W$, where $h_K$ is the class number of $K = \mathbb{Q}(\sqrt{-d})$;
5. $0 < n$ and $n + 1 \leq W$;
6. $99\, q_0 d\, y \leq n \log W$;
7. $(5184\, y)^n \leq W$;
8. $7776\, y\, n\, 2^n \leq W$.

Lean: `New.Parameters.IsLargeScale` (New/Reduction/Data/Existence.lean).

The structure is at Existence.lean:621. In the construction $y = \log x$. Condition 1 will give (S2), condition 2 will give (S1), and condition 3 will give (S3). Condition 4 is for a pigeonhole argument in the class group of $K$, which gives an integer $\alpha$ of $K$ with $\alpha\bar\alpha = p_0 p_1$. Condition 6 gives $q_2^2 \leq W^n$ for $s \leq 32 y$ (`New.Parameters.q₂_sq_le`, Existence.lean:425), so the moduli of the primes are below the range of the prime windows. Conditions 7 and 8 give room for a set of Behrend's type, from which the sparse set of $b$-places is made.

**Lemma (A large scale exists).** Let $0 < \varepsilon < 1/100$. There is a natural number $n$ such that, for every large enough integer $x$, $W = x^{\varepsilon/6}$ is a large scale for $y = \log x$ with exponent $n$.

Lean: `New.Parameters.exists_eventually_isLargeScale` (New/Reduction/Data/Existence.lean).

*Proof.* Choose $n > 0$ with $99 q_0 d < n \varepsilon/6$. Then condition 6 reads $99 q_0 d \log x \leq n (\varepsilon/6) \log x$, which holds. Conditions 2 to 5, 7 and 8 say that $W = x^{\varepsilon/6}$ is at least a constant, or a constant times a power of $\log x$. These hold for large $x$, since every power of $\log x$ is $o(x^{\varepsilon/6})$. Condition 1 reads $100(\varepsilon \log x + 1) \leq \log x$, that is $(1 - 100\varepsilon) \log x \geq 100$. It holds for large $x$ because $\varepsilon < 1/100$. $\square$

The lemma is at Existence.lean:647. Condition 1 is the only place where the bound $\varepsilon < 1/100$ enters. So the hypothesis $\varepsilon < 1/100$ of the existence theorem is the inequality (S2) in disguise. Section 7 returns to this point.

### The scales $x_1$ and $b$

**Lemma (The logarithm of a floor).** For $W \geq 0$, $W - 1 \leq \log \lfloor \exp W \rfloor_+ \leq W$.

Lean: `New.log_floor_exp_mem_Icc` (New/Reduction/Data/Existence.lean).

*Proof.* Write $F = \lfloor \exp W \rfloor_+$. Since $\exp W \geq 1$, $F \geq 1$. The upper bound is $F \leq \exp W$. For the lower bound, $\exp W < F + 1 \leq 2F \leq eF$, so $\exp(W - 1) \leq F$. $\square$

The lemma is at Existence.lean:435. With $W = x^{\varepsilon/6}$ it gives $x^{\varepsilon/6} - 1 \leq \log x_1 \leq x^{\varepsilon/6}$.

**Lemma (The scale $b$).** Let $W$ be a large scale for $y$ with exponent $n$, and let $s \leq 32y$. Let $b$ be the least multiple of $q_1 \lfloor \exp W \rfloor_+$ with $\exp(W^6) < b$. Then $\exp(\log b) = b$, $W^6 \leq \log b \leq W^6 + 1$, and $6 \log W \leq \log\log b \leq 6 \log W + 1$.

Lean: `New.Parameters.IsLargeScale.exists_isLeast_dvd_log_log_mem_Icc` (New/Reduction/Data/Existence.lean).

*Proof.* Write $c = q_1 \lfloor \exp W \rfloor_+$. The large scale gives $q_1 \leq W^n$ for $s \leq 32y$, and $1 \leq W$, $n + 1 \leq W$. So $c \leq W^n \exp W \leq \exp((n+1)W) \leq \exp(W^2) \leq \exp(W^6)$. The least multiple of $c$ above $\exp(W^6)$ is at most $\exp(W^6) + c \leq 2\exp(W^6) \leq e\exp(W^6)$. So $W^6 \leq \log b \leq W^6 + 1$. Take logarithms once more, with $\log(W^6 + 1) \leq \log(W^6) + 1$, which holds since $W^6 + 1 \leq e W^6$. $\square$

The lemma is at Existence.lean:715. With $W = x^{\varepsilon/6}$ it gives $x^\varepsilon \leq \log b \leq x^\varepsilon + 1$ and $\log\log b \in [\varepsilon \log x, \varepsilon \log x + 1]$.

### The five inequalities in the construction

**Lemma (Admissible data are data).** Let $W$ be a large scale for $\log x$ with exponent $n$, and let admissible data at $x$ and $W$ be given. There are data $D$ whose fields are the given objects, with $x_1 = \lfloor\exp W\rfloor_+$, and with $W - 1 \leq \log x_1$ and $W^6 \leq \log b \leq W^6 + 1$.

Lean: `New.Parameters.IsAdmissibleData.exists_hasFields` (New/Reduction/Data/Existence.lean).

*Proof of the five inequalities.* The lemma is at Existence.lean:734. Write $y = \log x$. The proof has $W - 1 \leq \log x_1 \leq W$, $W^6 \leq \log b$, and $6 \log W \leq \log\log b$. It first shows $2 \cdot 10^8 W \leq \log b$ from $W^6 \leq \log b$, $W \geq 2 \cdot 10^6 y$ and $y \geq 100$. Then:

- (S1): $10^{12} C_P \leq \log W \leq 6 \log W \leq \log\log b$, by condition 2 and $\log W \geq 0$.
- (S2): $100 \log\log b \leq 100(6 \log W + 1) \leq y$, by condition 1.
- (S3): $10^6 y \leq 2 \cdot 10^6 y - 1 \leq W - 1 \leq \log x_1$, by condition 3 and $y \geq 100$.
- (S4): $10^6 \log x_1 \leq 10^6 W \leq 2 \cdot 10^8 W \leq \log b$.
- (S5): $6 \log\log x_1 \leq 6 \log W \leq \log\log b$, since $\log x_1 \leq W$.

Each step is one `linarith` call in the source. $\square$

The proof shows which condition of a large scale pays for which scale inequality. It also shows the margins. In the construction, (S3) and (S4) hold with huge room: $\log x_1 \approx x^{\varepsilon/6}$ is far above $10^6 \log x$, and $\log b \approx x^\varepsilon$ is far above $10^6 x^{\varepsilon/6}$. But (S2) and (S5) are close to tight. For (S5), $6 \log\log x_1 \approx 6 \log W = \varepsilon \log x$ and $\log\log b \approx \varepsilon \log x$ as well. For (S2), $100 \log\log b \approx 100\varepsilon \log x$, which is close to $\log x$ when $\varepsilon$ is close to $1/100$.

### The ranks and the primes in the construction

The structure `New.Parameters.IsAdmissibleData` (Existence.lean:552) fixes the ranks and the scales and lets the places and the primes be any with the listed properties:

- $m$ is the least power of $2$ with $m \geq \sqrt{x}$. So $\sqrt{x} \leq m < 2\sqrt{x}$.
- $r$ is the least power of $3$ with $r \geq x^5$. So $x^5 \leq r < 3x^5$.
- $2^s = m^{22}$.
- $b$ is the least multiple of $q_1 x_1$ above $\exp(W^6)$.
- The $b$-places $T$ are $\equiv -1$ modulo $q_0$, their number satisfies $\operatorname{towerDeg}(s) \leq \#T \log b$, and $T$ is sparse for the primes up to $k t$.
- $p_0 \neq p_1$ are primes $\equiv 1 \pmod{q_2^2}$ in $[b^{10}, b^{11}]$, and $p_0 p_1 = \alpha\bar\alpha$ for an integer $\alpha$ of $K$.
- $N$ is a prime $\equiv 1 \pmod{q_2^2}$ with $\log N \in [\log N_-, \log N_- + \sqrt{\log b}]$, and $N = \beta\bar\beta$ for an integer $\beta$ of $E$.

The primes come from windows. The lemma `New.exists_prime_modEq_one_log_mem` (Lib/Analytic/Primes.lean:389) says: let $4 \mid M$ and fix $A$; for all large $W$, whenever $1 < k$, $M^k \leq W^A$ and $W \leq U \leq W^A$, there is a prime $p \equiv 1 \pmod{M^k}$ with $U \leq \log p \leq U + W$. The source cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, for this kind of result, and proves it directly. With $M = q_0 d$ and $A = n + 7$, the windows have length $W = x^{\varepsilon/6}$. For $p_0, p_1$, the lemma `New.Parameters.exists_prime_pair_norm` (Existence.lean:310) uses the windows $[U, U + W]$ with $10 \log b \leq U \leq 11 \log b$, and it finds two distinct primes in $[b^{10}, b^{11}]$ whose product is a norm from $K$. For $N$, one window of length $W$ fits in the interval $[\log N_-, \log N_- + \sqrt{\log b}]$, since $\sqrt{\log b} \geq W^3 \geq W$. The start $\log N_-$ is at most $24 m \log b$, and this upper bound is what keeps $U \leq W^{n+7}$.

**Remark (Formalization).** The data $D$ of `New.eventually_exists_data` are not unique. The places $T$, the primes $p_0, p_1, N$ and the integers $\alpha, \beta$ are any with the listed properties, and the theorem asserts only that some $D$ exists. The ranks and the scales are unique: each is the least element of an explicit set (`IsLeast`). So every later statement about $x_1$, $b$, $m$ and $r$ in the construction is about explicit numbers. Statements about $p_i$ and $N$ use only their properties.

### The two bounds that the last step needs

**Lemma (The scales for the final bound).** Let $0 < \varepsilon < 1/100$. For every large enough integer $x$ there are data $D$ with $D.x = x$, $\log b \leq 2 x^\varepsilon$, $x^{1/2} \leq m$ and $x^{\varepsilon/12} \leq \log x_1$.

Lean: `New.eventually_exists_data_scales` (New/Reduction/OneSidedBound.lean).

*Proof.* Take $D$ from the existence theorem. Then $\log b \leq x^\varepsilon + 1 \leq 2x^\varepsilon$ since $x \geq 1$. The bound $\sqrt{x} \leq m$ is the field `m_mem`. For the last bound, $x^{\varepsilon/6} = (x^{\varepsilon/12})^2$ and $x^{\varepsilon/12} \geq 2$ for large $x$, so $x^{\varepsilon/12} \leq x^{\varepsilon/6} - x^{\varepsilon/12} \leq x^{\varepsilon/6} - 1 \leq \log x_1$. $\square$

The lemma is at OneSidedBound.lean:74. The two bounds are not consequences of the five scale inequalities. The inequality (S2) gives only $\log b \leq x^{1/100}$, and (S3) gives only $\log x_1 \geq 10^6 \log x$. Section 5 shows why the last step needs the stronger forms.
