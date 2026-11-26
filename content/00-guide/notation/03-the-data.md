---
title: The scales, the ranks, the weights and the primes
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Existence.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Reduction/PrimeSums.lean
decls:
  - New.Data.x
  - New.Data.x₁
  - New.Data.b
  - New.Data.scale_inequalities
  - New.eventually_exists_data
  - New.Data.m
  - New.Data.r
  - New.Data.towerExp
  - New.Data.k
  - New.Data.t
  - New.Data.n
  - New.Data.posRank
  - New.Data.r_add_one
  - New.Data.halfGap
  - New.Data.gap
  - New.Data.reducedHalfGap
  - New.Data.a
  - New.Data.aPlaces
  - New.Data.bPlaces
  - New.Data.card_aPlaces
  - New.Data.weight
  - New.Data.weight_eq
  - New.Data.offWeight
  - New.Data.shiftedWeight
  - New.Data.liftWeight
  - New.Data.liftWeight_eq
  - New.Data.levelPrime
  - New.Data.M
  - New.Data.piMBar
  - New.Data.N
  - New.Data.piN
  - New.Data.logLevelTarget
  - New.Parameters.logLevelMin
  - New.Data.E
  - New.Data.q₁
  - New.Data.f
  - New.Data.rootDisc
  - New.Data.cyclotomicConductor
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scales, the ranks, the weights and the primes

This section gives the letters of the data $D$ for the parameters $P$. Lean asks most of them only to lie in ranges, and this section gives the ranges as Lean states them. Volume 1, [the data and its sizes](/chapter/data-and-sizes/), proves the derived sizes, and Volume 1, [the data exist](/chapter/data-exist/), constructs the data.

### The three scales

The data have three scales $x \leq x_1 \leq b$. Each is a natural number, and each has a real logarithm that the data store with it.

**Definition (The scales).** The scales are natural numbers $x$, $x_1$, $b$ with real numbers $\log x$, $\log x_1$, $\log b$ such that $e^{\log x} = x$, $e^{\log x_1} = x_1$ and $e^{\log b} = b$. The number $x$ is the length of the prime sum, $x_1$ is the second cut-off, and $b$ is the weight at the $b$-places.

Lean: `New.Data.x` (New/Reduction/Data/AdmissibleData.lean), `New.Data.x₁` (New/Reduction/Data/AdmissibleData.lean), `New.Data.b` (New/Reduction/Data/AdmissibleData.lean).

In the source, `D.natX`, `D.natX₁` and `D.natB` are the natural numbers, `D.logX`, `D.logX₁` and `D.logB` are their logarithms, and `D.x`, `D.x₁` and `D.b` are the real numbers `exp D.logX` and so on. The book writes $x$, $x_1$, $b$ for all three forms. Where the difference matters, as in a quotient of natural numbers, the text says which form it uses.

**Definition (The five scale inequalities).** The data satisfy
$$\text{(S1)}\ \ 10^{12} C_P \leq \log\log b, \qquad \text{(S2)}\ \ 100 \log\log b \leq \log x, \qquad \text{(S3)}\ \ 10^6 \log x \leq \log x_1,$$
$$\text{(S4)}\ \ 10^6 \log x_1 \leq \log b, \qquad \text{(S5)}\ \ 6 \log\log x_1 \leq \log\log b.$$

Lean: `New.Data.scale_inequalities` (New/Reduction/Data/Magnitudes.lean).

These are the fields `constantBound_le`, `mul_log_logB_le_logX`, `logX_le_logX₁`, `logX₁_le_logB` and `log_logX₁_le_log_logB` of the data. In exponential form they say $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$ and $(\log x_1)^6 \leq \log b$. The book uses the labels (S1) to (S5), as Volume 1 does.

### The exponent ε

The exponent $\varepsilon$ is not part of the parameters or of the data. It is a real number with $0 < \varepsilon < 1/100$, and it appears only in the existence theorem.

**Theorem (Existence of data).** Let $P$ be parameters and $0 < \varepsilon < 1/100$. For every large natural number $x$ there are data $D$ with $\mathrm{natX} = x$, $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$, $b$ the least multiple of $q_1 x_1$ that exceeds $\exp(x^\varepsilon)$, $m$ the least power of $2$ with $m \geq \sqrt x$, and $r$ the least power of $3$ with $r \geq x^5$. These data satisfy $x^{\varepsilon/6} - 1 \leq \log x_1$ and $x^\varepsilon \leq \log b \leq x^\varepsilon + 1$.

Lean: `New.eventually_exists_data` (New/Reduction/Data/Existence.lean).

The book writes $\varepsilon$ (with `\varepsilon`) for this exponent and for nothing else. The bound $y^{-1/2 + \varepsilon}$ of the remainder in the main theorem uses the same letter; Volume 1, [the main inequality](/chapter/main-inequality/), relates the two.

### The ranks and the gap

**Definition (The ranks).** The number $m$ of lifts and the rank $r$ of the target are natural numbers with $\sqrt x \leq m \leq 2\sqrt x$ and $x^5 \leq r \leq 3x^5$. The number $m$ is $2^{e+1}$ for some $e \in \mathbb{N}$, and the tower exponent is $s = 22(e+1)$, so $2^s = m^{22}$. The number $r$ is $3^{e'+1}$ for some $e' \in \mathbb{N}$. The data also ask $s \leq 32 \log x$ and $q_1 x_1 \mid b$.

Lean: `New.Data.m` (New/Reduction/Data/AdmissibleData.lean), `New.Data.r` (New/Reduction/Data/AdmissibleData.lean), `New.Data.towerExp` (New/Reduction/Data/AdmissibleData.lean).

**Definition (Derived ranks).** Put
$$k = r + 1 - m, \qquad t = 5r, \qquad n_j = k + j(t + 1), \qquad \mathrm{posRank}(j) = k + j - 1.$$
The number $k$ is the rank of the source, and $n_j$ is the rank of the space $X_j$ of Section 5. The number $k + j - 1$ is the number of plus signs of the space $W_j$.

Lean: `New.Data.k` (New/Reduction/Data/AdmissibleData.lean), `New.Data.t` (New/Reduction/Data/AdmissibleData.lean), `New.Data.n` (New/Reduction/Data/AdmissibleData.lean), `New.Data.posRank` (New/Reduction/Data/AdmissibleData.lean).

**Lemma.** $r + 1 = k + m$. That is, the truncated subtraction in $k = r + 1 - m$ is exact.

Lean: `New.Data.r_add_one` (New/Reduction/Data/Magnitudes.lean).

*Proof.* By the ranges, $m \leq 2\sqrt x \leq x^5 \leq r$, since $x \geq 4$ by (S1) and (S2). Then $(r + 1 - m) + m = r + 1$ in $\mathbb{N}$. $\square$

The source proves the parities in `New/Reduction/Data/Magnitudes.lean`: $m$ is even, $r$ is odd, so $k$ is even and $t$ is odd.

**Definition (The gap).** The half gap is $\Delta/2 = r^8$, and the gap is $\Delta = 2 r^8$. The reduced half gap is $\Delta/2 - (t + 1)/2$, a difference of natural numbers.

Lean: `New.Data.halfGap` (New/Reduction/Data/AdmissibleData.lean), `New.Data.gap` (New/Reduction/Data/AdmissibleData.lean), `New.Data.reducedHalfGap` (New/Reduction/Data/AdmissibleData.lean).

The book writes $\Delta$ and $\Delta/2$. The source has the names `gap` and `halfGap`, and the comments of `New/UpperBound/Objects/Rows.lean` write $h$ and $h_2$ for them.

### The long order and the two sets of places

**Definition (The long order).** $a = x b$, as a product of natural numbers. The prime sums of Section 4 run over $1 \leq \nu \leq a$.

Lean: `New.Data.a` (New/Reduction/Data/AdmissibleData.lean).

**Definition (The $a$-places and the $b$-places).** The set $\Phi_a$ is the set of places $\tau$ with $\mathrm{cl}_{q_0}(\tau) = 1$. The set $\Phi_b$ is a set of places, given with the data, with $\mathrm{cl}_{q_0}(\sigma) = -1$ for every $\sigma \in \Phi_b$, with $\mathrm{towerDeg}(s) \leq \#\Phi_b \cdot \log b$, and sparse for the primes up to $kt$ (Section 2).

Lean: `New.Data.aPlaces` (New/Reduction/Data/AdmissibleData.lean), `New.Data.bPlaces` (New/Reduction/Data/AdmissibleData.lean).

**Lemma.** $\#\Phi_a = \mathrm{towerDeg}(s)$.

Lean: `New.Data.card_aPlaces` (New/Reduction/PrimeSums.lean).

*Proof.* The map $\mathrm{cl}_{q_0} : (\mathbb{Z}/q_1\mathbb{Z})^\times \to (\mathbb{Z}/q_0\mathbb{Z})^\times$ is onto, so its kernel has $\varphi(q_1)/\varphi(q_0)$ elements. By the proof of the formula for $f$ in Section 2, this is $q_1/q_0 = \mathrm{towerDeg}(s)$. $\square$

So $f = \#\Phi_a \cdot \varphi(q_0)$, and $\Phi_a$ is a subgroup of $\Phi$. The set $\Phi_b$ is not a subgroup. It lies in the coset of the places $\equiv -1 \bmod q_0$, and it is a choice of the data. Volume 1 calls $\Phi_b$ also $T$ in the definition of a sparse set; the book writes $\Phi_b$.

### The weights

**Definition (The weight).** The weight of a place $\tau$ is the natural number
$$\kappa(\tau) = \begin{cases} b & \text{if } \tau \in \Phi_b, \\ \lfloor a / x_1 \rfloor & \text{otherwise.} \end{cases}$$

Lean: `New.Data.weight` (New/Reduction/Data/AdmissibleData.lean), `New.Data.weight_eq` (New/Reduction/Data/AdmissibleData.lean), `New.Data.offWeight` (New/Reduction/Data/AdmissibleData.lean).

**Remark (Formalization).** The quotient $a/x_1$ in `weight_eq` is a quotient of natural numbers, so it rounds down. The source also has the name `D.offWeight` for it. At a $b$-place the weight is $b = a/x$ exactly, since $a = xb$. The weight is a field of the data with the property `weight_eq`, not a definition, but the property fixes it.

**Definition (The shifted weights).** For $i \in \mathbb{N}$ and a place $\sigma$, put
$$\kappa^{(i)}(\sigma) = \kappa(\sigma) + (i + 1)\,\Delta/2, \qquad \kappa_j(\sigma) = \kappa^{(2j)}(\sigma).$$
The number $\kappa_j(\sigma)$ is the weight at $\sigma$ of the character of the $j$-th lift.

Lean: `New.Data.shiftedWeight` (New/Reduction/Data/AdmissibleData.lean), `New.Data.liftWeight` (New/Reduction/Data/AdmissibleData.lean).

**Lemma.** $\kappa_j(\sigma) = \kappa(\sigma) + j\Delta + \Delta/2$.

Lean: `New.Data.liftWeight_eq` (New/Reduction/Data/Magnitudes.lean).

*Proof.* $\kappa^{(2j)}(\sigma) = \kappa(\sigma) + (2j + 1)\Delta/2 = \kappa(\sigma) + j\Delta + \Delta/2$. $\square$

So $\kappa_0 = \kappa + \Delta/2$, not $\kappa$. The comment of `New.Data.untwistedLiftChar_hasWeight` writes $\kappa_j = \kappa_0 + j\Delta$ with this $\kappa_0$, and the comment of `New.Data.targetParameter` writes $\kappa_s$ for $\kappa + (s + 1/2)\Delta$ with a half-integer $s$. The book writes $\kappa$ for the weight and $\kappa_j$ only for $j \in \mathbb{N}$, so $\kappa_0$ always means $\kappa + \Delta/2$.

### The primes and the level

**Definition (The principal level).** The primes $p_0 \neq p_1$ satisfy $p_i \equiv 1 \bmod q_2^2$ and $b^{10} \leq p_i \leq b^{11}$. The principal level is $M = p_0 p_1$. The data give an integer $\bar\pi_M$ of $K$ with $\bar\pi_M \pi_M = M$, where $\pi_M$ is the conjugate of $\bar\pi_M$.

Lean: `New.Data.levelPrime` (New/Reduction/Data/AdmissibleData.lean), `New.Data.M` (New/Reduction/Data/AdmissibleData.lean), `New.Data.piMBar` (New/Reduction/Data/AdmissibleData.lean).

The source writes `D.levelPrime 0` and `D.levelPrime 1` for $p_0$ and $p_1$, `D.piMBar` for $\bar\pi_M$, and `star D.piMBar` for $\pi_M$.

**Definition (The lower end of the level).** Let $\bar\kappa$ be the geometric mean of the weights over all $f$ places. Put
$$\log N_- = m \cdot \frac{1}{f}\sum_{\tau \in \Phi} \log \kappa(\tau) + (m - 1) \log\frac{M\, \mathrm{rd}_E}{2\pi} - \frac{15}{2} \log b,$$
that is, $N_- = \bar\kappa^m (M\,\mathrm{rd}_E/2\pi)^{m-1} b^{-15/2}$.

Lean: `New.Parameters.logLevelMin` (New/Reduction/Data/AdmissibleData.lean), `New.Data.logLevelTarget` (New/Reduction/Data/LevelAndTwists.lean).

The source has two names for $\log N_-$. The name `P.logLevelMin` takes the weights and $M$ as arguments, so that the data can ask for it before $N$ exists. The name `D.logLevelTarget` reads them from the data. The lemma `New.Data.logLevelTarget_eq_logLevelMin` says that they agree.

**Definition (The level).** The level $N$ is a prime with $N \equiv 1 \bmod q_2^2$ and $\log N_- \leq \log N \leq \log N_- + \sqrt{\log b}$. The data give an integer $\pi_N$ of $E$ with $\pi_N \bar\pi_N = N$.

Lean: `New.Data.N` (New/Reduction/Data/AdmissibleData.lean), `New.Data.piN` (New/Reduction/Data/AdmissibleData.lean).

**Remark (Formalization).** The three primes $p_0$, $p_1$ and $N$ are fields of the data. Lean states only their properties, and the existence theorem chooses them. So a statement about $p_0$ holds for every choice. The book writes $\bar\pi_M$ for an integer of $K$ and $\pi_N$ for an integer of $E$; the bar always means the complex conjugate.

### Letters of the data that come from the parameters

For the data, the source reads the objects of Section 2 at the tower exponent $s$ of the data. The names are `D.E` for $E$, `D.q₁` for $q_1$, `D.f` for $f$, `D.rootDisc` for $\mathrm{rd}_E$, and `D.cyclotomicConductor` for $q_1 d$. The field $E$ lies in the cyclotomic field of order $q_1 d$.

Lean: `New.Data.E` (New/Reduction/Data/AdmissibleData.lean), `New.Data.q₁` (New/Reduction/Data/AdmissibleData.lean), `New.Data.f` (New/Reduction/Data/AdmissibleData.lean), `New.Data.rootDisc` (New/Reduction/Data/AdmissibleData.lean), `New.Data.cyclotomicConductor` (New/Reduction/Data/AdmissibleData.lean).

### The main sizes

The table gives the sizes that a reader needs most often to read a definition. Each row is a theorem of the source in `New.Data`, and Volume 0, [the table of sizes](/chapter/sizes/), has the full list.

| Letter | Size | Lean |
|---|---|---|
| $m$ | $x \leq m^2 \leq 4x$, $10^4 \leq m$ | `m_sq_mem_Icc`, `ten_thousand_le_m` |
| $f$, $q_1$ | $m^{22} \leq f \leq q_1 \leq x^{12}$ | `f_mem_Icc`, `q₁_le` |
| $q_2$ | $q_2 \leq x^{33 q_0 d}$ | `q₂_le` |
| $a/x_1$ | $x^{999} \leq a/x_1 \leq b/x^{999}$ | `a_div_x₁_mem_Icc` |
| $\kappa$ | $a/x_1 \leq \kappa \leq a/x$ | `weight_mem_Icc` |
| $\kappa_j$ | $\kappa_j \leq 2b$ for $j \leq 2m$ | `liftWeight_le_two_mul_b` |
| $M$ | $b^{20} \leq M \leq b^{22}$ | `M_mem_Icc` |
| $p_i$ | $b^2 < p_i < N$ | `levelPrime_mem_Ioo` |
| $\Omega$ | $\Omega \leq 1$ | `bigOmega_le_one` |
| $N_-$ | $m \log b \leq \log N_- \leq 24 m \log b$ | `logLevelTarget_mem_Icc` |
| $N$ | $m \log b \leq \log N \leq 30 m \log b$ | `log_N_mem_Icc` |
| $N$, $p_i$ | $\equiv 1 \bmod q_1 d$ | `N_modEq_one`, `levelPrime_modEq_one` |

**Example.** Take $x = 10^{10^{20}}$ and $\varepsilon = 1/200$ in the existence theorem, and assume that this $x$ is large enough for it. Then $\log x \approx 2.3 \cdot 10^{20}$, $m$ is the least power of $2$ above $10^{5 \cdot 10^{19}}$, and $\log b \approx x^{1/200}$. Every scale inequality then compares numbers of very different sizes, and the book writes them as inequalities of logarithms for this reason. With $\log x_1 \approx x^{1/1200}$ and $\log b \approx x^{1/200}$, (S5) holds with almost no room: $6 \log\log x_1 \approx \log\log b$. The existence theorem gives no explicit bound for "large", so the example shows only the orders of size.
