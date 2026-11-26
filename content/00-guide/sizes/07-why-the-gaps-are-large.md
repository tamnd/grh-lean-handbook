---
title: Why the gaps are large
lean:
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Existence.lean
  - New/Derivatives/Sharpness/NearPairs.lean
  - New/Determinant/Twist/LongForms.lean
decls:
  - New.Data.a_div_x₁_mem_Icc
  - New.Data.logX₁_pow_le_logB
  - New.Data.error_le_padicValNat_lossProduct
  - New.mul_rank_lt_two_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Why the gaps are large

The scales of the data are far apart: $x_1 \geq x^{10^6}$, $b \geq x_1^{10^6}$, and $\log b \leq x^{1/100}$. This section asks, for each gap, which proofs use it and how much of it they use. The answer is often that a proof uses only a small part of the gap. The source does not optimize the exponents. It chooses round numbers that are large enough for every use at once. This section gives the reading of this chapter. The source does not state these reasons in one place, and the list of uses below is not complete.

### The gap from $x$ to $x_1$

Two kinds of proofs need $x_1$ to be large against $x$.

The first kind is analytic. Section 5 shows that the remainders at $x_1$ must be at most $x^{-2}$. With the prime number theorem of the source, this needs $\log x_1 \geq x^{\varepsilon/12}$. This is a much larger gap than (S3) asks: $\log x_1$ must be a power of $x$, not a multiple of $\log x$. The construction meets it with $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$. The inequality (S3) does not record this need. It is a property of the construction, given by `New.eventually_exists_data_scales`, and not a field of the data.

The second kind is algebraic. These proofs need only a fixed power of $x$ below $x_1$:

- In the long forms of Theorem C, the proof uses $x^{99} + x^{202} b^2 \leq 2x_1^2 b^2$ (Determinant/Twist/LongForms.lean:97). This needs $x_1 \geq x^{101}$, up to a constant.
- In the near pairs, the proof uses $(81 s + 1)\, a/x_1 \leq b/k^2$, with $s$ the exponent of the tower. Since $a = x b$, this is $(81 s + 1)\, x k^2 \leq x_1$. With $k \leq e^3 x^5$ and $s \leq 32 \log x$, it needs $x_1$ to be at least a constant times $x^{11} \log x$.

**Lemma (The errors at one place).** Let $p \leq k$ be a prime and let $l$ be a natural number. Then
$$3(\log b + 2) + x^{42} + 1 + l_0\, \frac{a}{x_1} + \frac{2b}{kp} \leq v_p(B_l),$$
where $l_0 = l_0(s)$ for the exponent $s$ of the tower and $B_l$ is the loss product of index $l$.

Lean: `New.Data.error_le_padicValNat_lossProduct` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* The lemma is at NearPairs.lean:449. The proof has three size steps. First, $3(\log b + 2) + x^{42} + 1 \leq a/x_1$. Second, $(l_0 + 1)\, a/x_1 \leq b/(k p)$, from $l_0 \leq 81 s$ and $p \leq k$. Third, $6 b/(kp)$ is at most the count of loss factors divided by $p$. Each size step is proved by `le_of_hasLogBound`. $\square$

The first step needs $a/x_1 \geq x^{42}$, the second needs $a/x_1$ small against $b/k^2$. So $a/x_1 = xb/x_1$ must lie between $x^{42}$ and $b/x^{11}$, up to logarithms. The table gives more.

**Lemma (The off weight).** For all data $D$, $x^{999} \leq a/x_1 \leq b/x^{999}$.

Lean: `New.Data.a_div_x₁_mem_Icc` (New/Reduction/Data/Sizes.lean).

*Proof.* The lemma is at Sizes.lean:182. Write $a / x_1 = \exp(\log x + \log b - \log x_1)$. The lower bound needs $\log b - \log x_1 \geq 998 \log x$, which follows from (S4), since $\log b - \log x_1 \geq (10^6 - 1) \log x_1$. The upper bound needs $\log x_1 \geq 1000 \log x$, which follows from (S3). $\square$

So (S3) and (S4) give the exponent $999$ on both sides, where the uses above ask about $42$ and $11$. The exponent $10^6$ in (S3) is far more than the algebraic uses need. The analytic use needs more than any fixed power, and the construction gives it in another way.

### The gap from $x_1$ to $b$

Several proofs need $b$ to be large against $x_1$:

- the lower bound $a/x_1 \geq x^{999}$ above;
- the cost of completing a family in Theorem C, $4(2x_1^2 + 1/b) \leq b$ (`New.Data.mul_completion_cost_le`, Section 6);
- the inverse ratios in Theorem C, $2 m^2 t\, x_1 \leq b$ (LongForms.lean:231).

Each of these needs at most $x_1^3$ below $b$. The gap $b \geq x_1^{10^6}$ is far larger. The reason for a large gap is in the logarithms. The scales $\log x_1$ and $\log b$ enter the errors as powers of logarithms, and (S4) makes $\log x_1 \leq 10^{-6} \log b$. So a term with $\log x_1$ is a small part of a term with $\log b$. For example, the remainders at $x_1$ cost $\log b \cdot \lvert R_1(x_1) \rvert$ in Section 5, and this cost uses that $\log x_1$ is large, while the first term uses that $\log b$ is small. The two needs are compatible only because $\log x_1 \approx x^{\varepsilon/6}$ and $\log b \approx x^{\varepsilon}$ are different powers of $x$.

### The upper bound on $\log b$

The inequality (S2) says $\log b \leq x^{1/100}$, that is $(\log b)^{100} \leq x$ (`New.Data.logB_pow_le_x`, Sizes.lean:63). Its main use is in the final bound. The main inequality saves $1/m \approx x^{-1/2}$ and loses $(\log b)^6$, so the result is
$$R_{q_0}(x) \lesssim \varphi(q_0) \frac{(\log b)^6}{\sqrt{x}}.$$
For this to tend to $0$, $\log b$ must be a small power of $x$. The construction takes $\log b \approx x^\varepsilon$ with $\varepsilon < 1/100$, and (S2) is the form of this condition in the data. Other uses compare a power of $\log b$ with a power of $x$:

- the errors are of lower order in the main inequality, which compares $f a (\log b)^5$ with the main amount $x^4 f a$ (Section 5);
- $10^{30}\bigl((r + k)^2 \log b^3\bigr)^3 \leq r^7$ (`New.Data.rank_sq_mul_log_le`, Section 6);
- $2^\varrho \geq b^{10}$, from $\varrho \approx \sqrt{x}/2$ and $10 \log b \leq 10 x^{1/100}$ (Section 6).

The last one is the use with the least margin in the exponent: $\log b$ against $\sqrt{x}$. The others compare $\log b$ with $x$ or with $x^5$.

### The fifth inequality

The inequality (S5) says $(\log x_1)^6 \leq \log b$.

**Lemma (The sixth power of $\log x_1$).** For all data $D$, $(\log x_1)^6 \leq \log b$.

Lean: `New.Data.logX₁_pow_le_logB` (New/Reduction/Data/Sizes.lean).

*Proof.* The lemma is at Sizes.lean:58. Take logarithms and apply (S5). $\square$

A search of the source finds no use of this lemma by name. The inequality (S5) is used through the size automation. One use is the degree of the tower. The instance at Magnitudes.lean:472 gives
$$x^{11} \leq \operatorname{towerDeg}(s) \leq x^{11} (\log b)^{1/5}.$$
Here $\operatorname{towerDeg}(s) = 3^{\lfloor \log_3 s \rfloor + 5}\, 2^s$ and $2^s = m^{22} \leq 2^{22} x^{11}$. The proof bounds $3^{\lfloor \log_3 s\rfloor}$ by $s + 1$, and $s + 1$ by $e \log x_1$. So it needs $3^5 \cdot 2^{22} \cdot e \log x_1 \leq (\log b)^{1/5}$. By (S5), $\log x_1 \leq (\log b)^{1/6}$, and this leaves the factor $(\log b)^{1/30}$ for the constant $3^5 \cdot 2^{22} \cdot e$. That factor is huge by (S1). The inequality (S4) alone gives only $\log x_1 \leq 10^{-6} \log b$, and $10^{-6}\log b$ is far above $(\log b)^{1/5}$. So (S4) is not enough here: the use needs $\log x_1$ below a power of $\log b$ less than $1$, and (S5) gives the power $\tfrac16$.

### Why $m \approx \sqrt{x}$

The number $m$ of lifts lies in $[\sqrt{x}, 2\sqrt{x}]$ and is a power of $2$ (the field `exists_m_eq_two_pow`, AdmissibleData.lean:118). Three conditions bound it.

- From below, by the saving. The final bound is $(\log b)^6/m$. A larger $m$ gives a better bound, and $m \geq \sqrt{x}$ gives the exponent $-\tfrac12$.
- From below, by the sparseness. The construction needs $2 l_0 (k t + 1) < 2^s = m^{22}$ (`New.mul_rank_lt_two_pow`, below). With $k t \approx 5 x^{10}$, this needs $m^{22}$ to be large against $x^{10} \log x$, so $m$ must be at least about $x^{5/11}$.
- From above, by the filling data. They ask $1000 (2\varrho + 2)^9 = 1000\, m^9 \leq k$, and $k \approx x^5$. So $m$ must be at most about $x^{5/9}$.

So the conditions of this chapter allow $m$ between about $x^{5/11}$ and $x^{5/9}$. The choice $m \approx \sqrt{x}$ lies in this range. The exponent $\tfrac12$ of the final result is the exponent of $m$. A larger exponent for $m$ would give a better saving. The book does not discuss here whether the other parts of the proof allow a larger $m$.

**Lemma (The sparseness bound).** Let $y > 0$ with $10^6 y \leq e^y$. Let $m$, $r$, $s$ be natural numbers with $e^{y/2} \leq m$, $r \leq 3 e^{5y}$, $2^s = m^{22}$ and $l_0(s) \leq 2592\, y$. Then
$$2\, l_0(s) \bigl((r + 1 - m)(5r) + 1\bigr) < 2^s.$$

Lean: `New.mul_rank_lt_two_pow` (New/Reduction/Data/Existence.lean).

*Proof.* The lemma is at Existence.lean:405. The source bounds $(r + 1 - m)(5r) + 1 \leq 46\, e^{10 y}$ and $l_0 \leq 2592\, y$. Then the left side is at most $2 \cdot 2592 \cdot 46\, y\, e^{10y}$, while $2^s = m^{22} \geq e^{11 y}$. The ratio is $e^{y}$ against a constant times $y$, and $10^6 y \leq e^y$ closes the proof. $\square$

Here $y = \log x$, $k = r + 1 - m$ and $t = 5r$. The margin is one power of $x$: $m^{22} \approx x^{11}$ against $k t \approx x^{10}$. This explains the size of the exponent $22$ in $2^s = m^{22}$. With $m \approx \sqrt{x}$, the power $m^{22} \approx x^{11}$ is larger than $x^{10}$ by one power of $x$. The power $m^{20} \approx x^{10}$ would leave no margin.

### Why $r \approx x^5$

The rank $r$ lies in $[x^5, 3x^5]$, and $k = r + 1 - m$, $t = 5r$. The filling data ask $1000\, m^9 \leq k$ and $n^7 \leq k$, where $m^9 \leq 2^9 x^{9/2}$. So $k$ must be large against $x^{9/2}$. With $k \approx x^5$, the margin is $x^{1/2}$. From above, the sparseness bound of the last subsection needs $2 l_0 (k t + 1) < m^{22}$. With $k t \approx 5 r^2$ and $m^{22} \leq 2^{22} x^{11}$, this needs $r^2$ small against $x^{11}/\log x$, so $r$ must be at most about $x^{11/2}$. The choice $r \approx x^5$ meets both.

### The primes and the level

The primes $p_0$, $p_1$ lie in $[b^{10}, b^{11}]$ by the field `levelPrime_mem`. So $M = p_0 p_1 \in [b^{20}, b^{22}]$. The filling data ask $b^{19} \leq M \leq b^{23}$, and the interval of the data lies inside with a margin of one power of $b$ at each end. The level $N$ has $\log N \in [m \log b, 30 m \log b]$, and the admissible filling data ask $N \leq b^{60 n}$ with $2n = m$. This one has no margin (Section 6). So the constant $30$ in the bound for $\log N$ is not a round number chosen with room: the filling data need exactly this constant or a smaller one.

### A summary

| Gap | Size in the data | Largest use found here |
|----------|----------------|-------------------|
| $x \to x_1$, algebraic | $x_1 \geq x^{10^6}$ | $x_1 \geq x^{101}$ (long forms) |
| $x \to x_1$, analytic | $\log x_1 \approx x^{\varepsilon/6}$ | $\log x_1 \geq x^{\varepsilon/12}$ (remainders) |
| $x_1 \to b$ | $b \geq x_1^{10^6}$ | $b \geq x^{998} x_1$ (off weight) |
| $\log b$ and $x$ | $(\log b)^{100} \leq x$ | $(\log b)^6 / \sqrt{x} \to 0$, $b^{10} \leq 2^\varrho$ |
| $\log x_1$ and $\log b$ | $(\log x_1)^6 \leq \log b$ | the degree of the tower |
| $m$ | $[\sqrt{x}, 2\sqrt{x}]$ | between $x^{5/11}$ and $x^{5/9}$ |
| $M$ | $[b^{20}, b^{22}]$ | $[b^{19}, b^{23}]$ (filling) |
| $N$ | $\log N \leq 30 m \log b$ | $N \leq b^{60 n}$, no margin |
