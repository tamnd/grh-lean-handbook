---
title: Short tight frames
lean:
  - New/Derivatives/Vacuum/ShortVectors.lean
decls:
  - New.Parameters.ceilLogQ₁
  - New.Parameters.cyclotomicQuotient
  - New.Parameters.dualVector
  - New.Parameters.trace_coeff_cyclotomicQuotient_div_mul_pow
  - New.Parameters.sum_dualVector_mul_conj
  - New.Parameters.sum_mul_conj_dualVector
  - New.Parameters.q₁_dvd_pow_ceilLogQ₁
  - New.Parameters.finiteImage_dualVector_mem
  - New.Parameters.isCoprime_of_pow_add_conj_pow_eq
  - New.Parameters.exists_pow_add_conj_pow_eq_intCast
  - New.Parameters.dualResolutionFactor
  - New.Parameters.isTightFrame_sumElim_inv_pow_orbit
  - New.Parameters.exists_isTightFrame_factor_eq_add
  - New.Parameters.exists_isTightFrame_coprime
  - New.Parameters.norm_map_zeta_mul_dualVector
  - New.Parameters.HasUnitLinearForm
  - New.Parameters.exists_hasUnitLinearForm
  - New.Parameters.exists_isTightFrame_of_coprime
  - New.Parameters.norm_coeff_cyclotomic_le
  - New.Parameters.norm_phi_coeff_cyclotomicQuotient_le
  - New.Parameters.norm_quadGen_le
  - New.Parameters.norm_phi_dualVector_le
  - New.Parameters.ceilLogQ₁_le
  - New.Data.one_le_norm_phi_relDifferentGen
  - New.Data.hasLogUpper_pow_ceilLogQ₁
  - New.Data.le_b_of_eq_dualResolutionFactor
  - New.Data.exists_short_isTightFrame_coprime
  - New.Data.exists_isTightFrame
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Short tight frames

Sections 4 and 5 need a tight frame of a given length $M$ whose multiplicities are large. The powers of $\zeta$ give frames of every length $kq_1$ (Section 2), but $M = p_0 p_1$ is a product of two large primes and is prime to $q_1$. This section builds a second frame of a length $h$ prime to $q_1$, with $h \le b$, and then combines the two frames to reach every large length. It also finds, for every prime $p$, one member $y$ of the frame for which the linear form $\mathrm{periodFactor} \cdot \overline{\tau(y)}$ is a $p$-adic unit at every place $\tau$. The theorem of complex multiplication at $p$ in Section 6 and the sharpness argument in [sharpness](/chapter/sharpness/) use this unit.

The plan is as follows. The trace dual basis of the powers of $\zeta$ is a basis $e_i$ of $E/K$. Its orbits form frames, and the pairs $(\zeta^{-i}, e_i)$ have cross terms that add up to a multiple of $\delta_{\sigma\tau}$. If one replaces each pair by its sum, the length changes by an integer $t$. A factor $\bar\beta^j$ puts the $e_i$ into $\mathfrak{a}_0$, and it makes $t = \beta^j + \bar\beta^j$, which is prime to $q_1$.

Throughout, $f = \varphi(q_1) = [E : K]$, $P = \Phi_{q_1}$ is the cyclotomic polynomial of order $q_1$, and $P'(\zeta)$ generates the different of $E/K$ (Section 2).

### The dual basis

**Definition.** Let $j$ be the least integer with $2^j \ge q_1$. Let $b_0, \dots, b_{f-1} \in \mathcal{O}_E$ be the coefficients of the quotient
$$\frac{P(X)}{X - \zeta} = \sum_{i=0}^{f-1} b_i X^i ,$$
a monic polynomial of degree $f - 1$. Put
$$e_i = \frac{\bar\beta^{\,j}\, b_i}{P'(\zeta)} .$$

Lean: `New.Parameters.ceilLogQ₁`, `New.Parameters.cyclotomicQuotient`, `New.Parameters.dualVector` (New/Derivatives/Vacuum/ShortVectors.lean).

**Lemma (Euler).** For $0 \le i, k < f$,
$$\mathrm{tr}_{E/K}\Bigl(\frac{b_i}{P'(\zeta)}\, \zeta^k\Bigr) = \delta_{ik} .$$

Lean: `New.Parameters.trace_coeff_cyclotomicQuotient_div_mul_pow` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The polynomial $P$ is the minimal polynomial of $\zeta$ over $K$, since $[E : K] = f = \deg P$. Let $\zeta_1, \dots, \zeta_f$ be its roots, the conjugates of $\zeta$ over $K$. For $k < f$, Lagrange interpolation at these $f$ distinct points gives
$$X^k = \sum_{r=1}^{f} \frac{P(X)}{(X - \zeta_r)\, P'(\zeta_r)}\, \zeta_r^{\,k} ,$$
since both sides have degree less than $f$ and agree at every $\zeta_r$. The coefficient of $X^i$ in $P(X)/(X - \zeta_r)$ is the conjugate of $b_i$ by the $K$-embedding that takes $\zeta$ to $\zeta_r$. So the coefficient of $X^i$ on the right is the sum of the conjugates of $b_i \zeta^k / P'(\zeta)$, which is the trace. On the left it is $\delta_{ik}$. $\square$

**Proposition (Dual basis).** For all places $\sigma$, $\tau$,
$$\sum_{i < f} \sigma(e_i)\, \overline{\tau(\zeta^{-i})} = \bar\beta^{\,j}\, \delta_{\sigma\tau}, \qquad \sum_{i < f} \sigma(\zeta^{-i})\, \overline{\tau(e_i)} = \beta^{j}\, \delta_{\sigma\tau} .$$

Lean: `New.Parameters.sum_dualVector_mul_conj`, `New.Parameters.sum_mul_conj_dualVector` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The trace is $\sum_\rho \rho$ over the places (Section 2). Let $A$ be the $f \times f$ matrix with entries $A_{\rho i} = \rho(b_i / P'(\zeta))$ and $B$ the matrix with $B_{\rho k} = \rho(\zeta^k)$. Euler's lemma says $A^{\mathsf T} B = 1$. Both matrices are square, so $B A^{\mathsf T} = 1$, and the transpose gives $A B^{\mathsf T} = 1$, that is,
$$\sum_{i < f} \sigma\Bigl(\frac{b_i}{P'(\zeta)}\Bigr)\, \tau(\zeta^i) = \delta_{\sigma\tau} .$$
Now $\overline{\tau(\zeta^{-i})} = \tau(\zeta^i)$, since $|\tau(\zeta)| = 1$, and $\sigma(\bar\beta^{\,j}) = \bar\beta^{\,j}$, since $\sigma$ is the identity on $K$. This gives the first identity. The second is the complex conjugate of the first with $\sigma$ and $\tau$ exchanged. $\square$

### The dual basis lies in the lattice

**Lemma.** The integer $q_1$ divides $\bigl((d+1)/4\bigr)^j$.

Lean: `New.Parameters.q₁_dvd_pow_ceilLogQ₁` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Let $p^e$ be the exact power of a prime $p$ in $q_1$. Then $p^e \le q_1 \le 2^j \le p^j$, so $e \le j$. It is enough to show that $p$ divides $(d+1)/4$. The primes of $q_1 = q_0 \cdot 3^{\lfloor \log_3 s \rfloor + 5} \cdot 2^s$ are the primes of $q_0$, since $6 \mid 18480 \mid q_0$. From $d \equiv q_0/2 - 1 \pmod{q_0}$ one gets $d + 1 = (q_0/2)(2k+1)$ for an integer $k$, so $(d+1)/4 = (q_0/8)(2k+1)$. As $16 \mid q_0$, every prime of $q_0$ divides $q_0/8$. $\square$

**Proposition.** Every $e_i$ lies in $\mathfrak{a}_0$.

Lean: `New.Parameters.finiteImage_dualVector_mem` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Use the criterion of Section 2 at each finite place $w$. If $\beta \in w$, then $P'(\zeta)\, e_i = \bar\beta^{\,j} b_i$ is integral. If $\beta \notin w$, then $\beta$ is a unit at $w$. The element $P'(\zeta)$ divides $q_1$ in $\mathcal{O}_E$, so $q_1 / P'(\zeta)$ is integral, and $q_1$ divides $(\beta\bar\beta)^j = ((d+1)/4)^j$ by the lemma. So
$$e_i = \beta^{-j}\, b_i \cdot \frac{q_1}{P'(\zeta)} \cdot \frac{(\beta\bar\beta)^j}{q_1}$$
is integral at $w$. $\square$

### The cross terms

**Lemma.** The number $t = \beta^j + \bar\beta^{\,j}$ is an integer. If $j \ne 0$, then $t$ is prime to $q_1$.

Lean: `New.Parameters.exists_pow_add_conj_pow_eq_intCast`, `New.Parameters.isCoprime_of_pow_add_conj_pow_eq` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The number $t$ is an algebraic integer of $K$ fixed by complex conjugation, so $t \in \mathbb{Z}$. Let $p$ be a prime that divides $q_1$ and $t$. By the proof of the last lemma, $p$ divides $\beta\bar\beta$. Let $\mathfrak{p}$ be a prime of $\mathcal{O}_K$ above $p$. Then $\beta \in \mathfrak{p}$ or $\bar\beta \in \mathfrak{p}$, and $\beta + \bar\beta = 1$. So one of $\beta$, $\bar\beta$ is $0$ and the other is $1$ modulo $\mathfrak{p}$. As $j \ne 0$, $t \equiv 1 \pmod{\mathfrak{p}}$, which contradicts $p \mid t$. $\square$

**Example.** Take $d = 7$. Then $\beta = (1 + \sqrt{-7})/2$, $\beta + \bar\beta = 1$ and $\beta\bar\beta = 2$, so $t_n = \beta^n + \bar\beta^n$ satisfies $t_n = t_{n-1} - 2t_{n-2}$. The values from $n = 0$ are $2, 1, -3, -5, 1, 11, 9, -13$. All $t_n$ with $n \ge 1$ are odd, so they are prime to $\beta\bar\beta = 2$. The value $t_0 = 2$ shows that the condition $j \ne 0$ is necessary.

**Definition.** The *dual resolution factor* is
$$h_0 = q_1\Bigl(1 + \sum_{i<f} \sum_\tau |\tau(e_i)|^2\Bigr) + \beta^j + \bar\beta^{\,j} \in \mathbb{C} .$$

Lean: `New.Parameters.dualResolutionFactor` (New/Derivatives/Vacuum/ShortVectors.lean).

By Section 2, each $\nu_i = \sum_\tau |\tau(e_i)|^2$ is a natural number, since $e_i \in \mathfrak{a}_0$. So $h_0$ is an integer.

**Lemma.** The powers $\zeta^{-i}$, $0 \le i < q_1$, together with the orbits of all $e_i$, $i < f$, with multiplicities $1$, form a tight frame of length $q_1(1 + \sum_i \nu_i)$.

Lean: `New.Parameters.isTightFrame_sumElim_inv_pow_orbit` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The element $\zeta^{-1}$ is a primitive $q_1$-th root of unity, so its powers form a frame of length $q_1$. The orbit of $e_i$ is a frame of length $q_1 \nu_i$. Join the frames (Section 2). $\square$

**Proposition.** There is a tight frame with multiplicities $1$ of a length $h \in \mathbb{N}$ with $h = q_1(1 + \sum_i \nu_i) + t$. It contains the vector $\zeta e_{f-1}$.

Lean: `New.Parameters.exists_isTightFrame_factor_eq_add` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* In the frame of the lemma, pair $\zeta^{-i}$ with the member $e_i = \zeta^0 \cdot 1(e_i)$ of the orbit of $e_i$, for $i < f$. These pairs are disjoint, since $f \le q_1$. Their cross terms are
$$\sum_{i<f} \Bigl(\sigma(\zeta^{-i})\, \overline{\tau(e_i)} + \sigma(e_i)\, \overline{\tau(\zeta^{-i})}\Bigr) = (\beta^j + \bar\beta^{\,j})\, \delta_{\sigma\tau} = t\, \delta_{\sigma\tau}$$
by the dual basis proposition. The lemma on replacing pairs (Section 2) gives the frame of length $h$. The member $\zeta \cdot 1(e_{f-1})$ of the orbit of $e_{f-1}$ is in no pair, since $q_1 > 1$, so it stays in the frame. $\square$

**Theorem (A frame of length prime to $q_1$).** There is a tight frame with multiplicities $1$ of a length $h \in \mathbb{N}$ with $h = h_0$ and $\gcd(h, q_1) = 1$. It contains the vector $\zeta e_{f-1}$.

Lean: `New.Parameters.exists_isTightFrame_coprime` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Take the frame of the proposition. Then $h \equiv t \pmod{q_1}$. As $q_1 > 1$, $j \ge 1$, and $t$ is prime to $q_1$ by the lemma. $\square$

### A unit linear form

**Definition.** Let $p$ be a prime with the chosen embedding $\iota_p$. A vector $y \in E$ has a *unit linear form* at $p$ if $|\iota_p(\mathrm{periodFactor} \cdot \overline{\tau(y)})| = 1$ for every place $\tau$.

Lean: `New.Parameters.HasUnitLinearForm` (New/Derivatives/Vacuum/ShortVectors.lean).

**Lemma.** Let $\phi$ be a $p$-adic embedding of $E$ whose prime contains $\beta$. Then $|\phi(\zeta e_{f-1})| = 1/|\phi(P'(\zeta))|$.

Lean: `New.Parameters.norm_map_zeta_mul_dualVector` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The leading coefficient $b_{f-1}$ is $1$, so $\zeta e_{f-1} = \zeta \bar\beta^{\,j}/P'(\zeta)$. Here $\zeta$ is a unit, and $\bar\beta = 1 - \beta$ is a unit at the prime of $\phi$. $\square$

**Proposition.** For every prime $p$, the vector $y = 1$ or the vector $y = \zeta e_{f-1}$ has a unit linear form at $p$.

Lean: `New.Parameters.exists_hasUnitLinearForm` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Let $\phi_\tau(y) = \iota_p(\tau(\bar y))$ as in Section 3. Then $\phi_\tau(\beta) = \iota_p(\bar\beta)$ for every $\tau$, since $\tau$ is the identity on $K$. So the prime of $\phi_\tau$ contains $\beta$ for all $\tau$ or for no $\tau$, depending on whether $|\iota_p(\bar\beta)| < 1$. By Section 3, $|\iota_p(\mathrm{periodFactor})| = |\phi_\tau(\alpha)|^{-1}$.

If $|\iota_p(\bar\beta)| = 1$, then $\alpha$ is $1$ at the prime of each $\phi_\tau$, so $|\iota_p(\mathrm{periodFactor})| = 1$, and $y = 1$ works.

Otherwise $\alpha = 1/P'(\zeta)$ at the prime of each $\phi_\tau$, so $|\iota_p(\mathrm{periodFactor})| = |\phi_\tau(P'(\zeta))|$. For $y = \zeta e_{f-1}$, $|\iota_p(\overline{\tau(y)})| = |\phi_\tau(y)| = 1/|\phi_\tau(P'(\zeta))|$ by the lemma. The product has absolute value $1$. $\square$

### Every large length

**Proposition (Coin problem).** Let $(v_i)$, with multiplicities $1$, be a tight frame of a length $h$ prime to $q_1$. Let $R, m \in \mathbb{N}$ with $m \ge q_1 h + R(q_1 + h)$. Then the powers $\zeta^i$, $0 \le i < q_1$, together with the $v_i$, form a tight frame of length $m$ with multiplicities $c$ that are all at least $R$.

Lean: `New.Parameters.exists_isTightFrame_of_coprime` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Put $n = m - R(q_1 + h) \ge q_1 h$. As $h$ is invertible modulo $q_1$, there is $b$ with $0 \le b < q_1$ and $bh \equiv n \pmod{q_1}$. Then $n - bh \ge q_1 h - (q_1 - 1)h > 0$ is a multiple $a q_1$ with $a \in \mathbb{N}$. So $m = (a + R) q_1 + (b + R) h$. The powers of $\zeta$ with multiplicity $a + R$ form a frame of length $(a + R)q_1$, and the $v_i$ with multiplicity $b + R$ form one of length $(b+R)h$. Join them. $\square$

### The size of the frame

The length $h_0$ must be at most $b$. The bounds are crude, and the data of [the data and their sizes](/chapter/data-and-sizes/) make $b$ large against $d$, $q_0$ and $s$.

**Lemma (Bounds).** For every place $\tau$ and every $i$:

1. every coefficient of $P$ has absolute value at most $2^{q_0}$;
2. $|\tau(b_i)| \le q_1 2^{q_0}$;
3. $|\beta| \le d$;
4. if $|\tau(P'(\zeta))| \ge 1$, then $|\tau(e_i)| \le d^j q_1 2^{q_0}$;
5. $j \le q_0 + 3s + 10$.

Lean: `New.Parameters.norm_coeff_cyclotomic_le`, `New.Parameters.norm_phi_coeff_cyclotomicQuotient_le`, `New.Parameters.norm_quadGen_le`, `New.Parameters.norm_phi_dualVector_le`, `New.Parameters.ceilLogQ₁_le` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* (1) Every prime of $q_1$ divides $q_0$, so $P(X) = \Phi_{q_0}(X^{q_1/q_0})$, and the nonzero coefficients of $P$ are those of $\Phi_{q_0}$. The roots of $\Phi_{q_0}$ have absolute value $1$, so its $k$-th coefficient is at most $\binom{\varphi(q_0)}{k} \le 2^{q_0}$ in absolute value. (2) Division by $X - \zeta$ gives $b_i = \sum_{k > i} \zeta^{k-i-1} c_k$, where the $c_k$ are the coefficients of $P$. There are at most $f \le q_1$ terms. (3) $|\beta| \le 1/2 + \sqrt d/2 \le d$. (4) Combine (2) and (3) with $|\bar\beta| = |\beta|$. (5) $q_1 = q_0 \cdot 3^{\lfloor \log_3 s\rfloor + 5} \cdot 2^s$, with $q_0 \le 2^{q_0}$ and $3^{\lfloor \log_3 s\rfloor + 5} \le 4^{s+5}$. So $q_1 \le 2^{q_0 + 3s + 10}$. $\square$

**Lemma.** For admissible data with $s$ the tower exponent:

1. $|\tau(P'(\zeta))| \ge 1$ for every place $\tau$;
2. $d^j \le b^{1/100}$;
3. if $h \in \mathbb{N}$ and $h = h_0$, then $h \le b$.

Lean: `New.Data.one_le_norm_phi_relDifferentGen`, `New.Data.hasLogUpper_pow_ceilLogQ₁`, `New.Data.le_b_of_eq_dualResolutionFactor` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* (1) Let $\delta_E$ be the generator of the different of $E$ from [the field E at the primes](/chapter/field-at-primes/), a unit times $P'(\zeta)\sqrt{-d}$. Then $|\tau(\delta_E)| = |\tau(P'(\zeta))|\sqrt d$, and the data give a lower bound for $|\tau(\delta_E)|$ that exceeds $\sqrt d$. (2) By the bound on $j$, $d^j \le e^{(q_0 + 3s + 10)d}$, and the ranges of the data give $(q_0 + 3s + 10) d \le \log b / 100$. (3) By (1) and the bounds, $\sum_i \sum_\tau |\tau(e_i)|^2 \le q_1 f (d^j q_1 2^{q_0})^2$, and $|t| \le 2|\beta|^j \le 2 d^j$. So $h$ is at most a fixed polynomial in $q_1$, $f$, $2^{q_0}$ and $d^j$. The ranges of the data and (2) make it at most $b$. $\square$

### The theorems for the data

**Theorem (Short frame).** For admissible data there are $h \in \mathbb{N}$ and a tight frame $(v_i)$ with multiplicities $1$ of length $h$ such that $\gcd(h, q_1) = 1$, $1 \le h \le b$, and for every prime $p$ some $y$ among the powers $\zeta^i$, $0 \le i < q_1$, and the $v_i$ has a unit linear form at $p$.

Lean: `New.Data.exists_short_isTightFrame_coprime` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Take the frame of length prime to $q_1$. As $q_1 > 1$ and $\gcd(h, q_1) = 1$, $h \ne 0$. The last lemma gives $h \le b$. For each $p$, the unit linear form is carried by $y = 1 = \zeta^0$ or by $y = \zeta e_{f-1}$, which is a member $v_{i_0}$. $\square$

**Theorem (Tight frame of length $M$).** For admissible data, with $M = p_0 p_1$ the principal level, there is a tight frame $(v_i)$ of length $M$ with multiplicities $c_i \ge 6fb$, such that for every prime $p$ some $v_i$ has a unit linear form at $p$.

Lean: `New.Data.exists_isTightFrame` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* Take the short frame of length $h \le b$ and $R = \lceil 6fb \rceil$. The primes $p_0$, $p_1$ lie in $[b^{10}, b^{11}]$, so $M \ge b^{20}$. With $h \le b$, the ranges of the data make $q_1 h + R(q_1 + h) \le M$. The coin problem gives multiplicities $c_i \ge R \ge 6fb$ for the powers of $\zeta$ and the $v_i$. The unit linear form is carried by a member of this joint family. $\square$

**Remark (Formalization).** The frames are existential. Lean chooses an index type for each, and the length $h$ is any natural number equal to the complex number $h_0$, so $h$ is unique but the frame is not. The unit linear form is checked against the embedding $\iota_p$ fixed by the instance for $p$, and it quantifies over the places of the CM type. The weight $b$ is the real number $e^{\log b}$, so $h \le b$ and $6fb \le c_i$ are inequalities of real numbers. The field is $E = K(\zeta)$ with the exponent $s$ of the data. The bound (4) needs the hypothesis $|\tau(P'(\zeta))| \ge 1$, and only the data supply it. In the theorem of length $M$, the source states the comparison of $q_1 h + R(q_1+h)$ with $M$ as a comparison of logarithmic sizes, and Lean accepts it, if the reported checks hold.
