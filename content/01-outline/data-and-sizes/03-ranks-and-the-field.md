---
title: Ranks, the tower and the field
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
  - New/UpperBound/Objects/Weights.lean
decls:
  - New.Data.m_mem
  - New.Data.m_sq_mem_Icc
  - New.Data.k
  - New.Data.r_add_one
  - New.Data.f_mem_Icc
  - New.Data.q₁_le
  - New.Data.q₂_le
  - New.Data.x₁_pow_le_sqrt_b
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ranks, the tower and the field

This section defines the number $m$ of theta lifts, the rank $r$ of the target, and the exponent $s$ that selects the field $E$. It then defines the derived ranks $k$, $t$, the gap $\Delta$ and the ranks $n_j$, and proves the inequalities and parities between them. The last part bounds the invariants of $E$: the number $f$ of infinite places, the modulus $q_1$, and the modulus $q_2$ of the congruences of the primes.

### The ranks and the exponent of the tower

**Definition (The ranks).** The data contain natural numbers $m$, $r$ and $s$ with these properties:

1. $\sqrt x \leq m \leq 2\sqrt x$;
2. $x^5 \leq r \leq 3x^5$;
3. there is $e \in \mathbb{N}$ with $m = 2^{e+1}$ and $s = 22(e + 1)$;
4. there is $e \in \mathbb{N}$ with $r = 3^{e+1}$;
5. $s \leq 32 \log x$;
6. $q_1 x_1$ divides $b$, where $q_1 = q_1(s)$.

Here $\sqrt x = \exp(\tfrac12 \log x)$ and $x^5 = \exp(5 \log x)$.

Lean: `New.Data.m_mem`, `New.Data.r_mem`, `New.Data.exists_m_eq_two_pow`, `New.Data.exists_r_eq_three_pow`, `New.Data.towerExp_le`, `New.Data.dvd_natB` (New/Reduction/Data/AdmissibleData.lean).

The number $m$ is the length of the chain of theta lifts. The number $r$ is the rank of the hermitian spaces $W_j$ of the target. Here $W_j$ is the diagonal hermitian space of rank $r$ over $E$ with the sign $+1$ on the first $\operatorname{posRank}(j) = k + j - 1$ basis numbers and $-1$ on the others (`New.Data.spaceW`, `New.Data.signsW`; Volume 0, [the notation](/chapter/notation/), Section 5). The number $s$ is `New.Data.towerExp`. Property 3 says that $m$ is a power of $2$ with positive exponent and that $2^s = m^{22}$. The field of the data is $E = E(s)$. So the field grows with $x$, and its degree is tied to $m$.

Recall from [fields, places and twists](/chapter/fields-places-twists/) the numbers that $s$ determines:
$$l_0 = 3^{\lfloor \log_3 s\rfloor + 4}, \qquad \operatorname{towerDeg}(s) = 3 l_0 \, 2^s, \qquad q_1 = q_0 \operatorname{towerDeg}(s), \qquad q_2 = (q_0 d)^{s + 6}.$$
For $s \geq 1$ the number $l_0$ is the least power of $3$ above $27s$, and $27 s < l_0 \leq 81 s$ (`New.mul_lt_l₀`, `New.l₀_le_mul`). The field $E = K(\zeta_{q_1})$ has $f = \operatorname{towerDeg}(s)\,\varphi(q_0)$ infinite places ([Lemma](/decl/New.Parameters.numInfPlaces_E/)), and $q_1 d$ divides $q_2$ (`New.Parameters.q₁_mul_d_dvd_q₂`).

**Remark.** Property 5 nearly follows from property 1. Since $m = 2^{e+1} \leq 2\sqrt x$, one has $e + 1 \leq 1 + \log x / (2 \log 2)$, so
$$s = 22(e+1) \leq 22 + \frac{11}{\log 2}\log x \leq 22 + 15.9 \log x,$$
and this is at most $32 \log x$ as soon as $\log x \geq 2$. The source keeps property 5 as a field, so that a bound for $s$ is at hand without this computation.

**Lemma (The size of $m$).** The data satisfy:

1. $x \leq m^2 \leq 4x$;
2. $s \neq 0$, and $m^{22} = 2^s$;
3. $m^{594} \leq 2^{l_0}$;
4. $10^4 \leq m$, and $m$ is even.

Lean: `New.Data.m_sq_mem_Icc`, `New.Data.towerExp_ne_zero`, `New.Data.m_pow_eq_two_pow_towerExp`, `New.Data.m_pow_le_two_pow_l₀` (New/Reduction/Data/Sizes.lean); `New.Data.ten_thousand_le_m`, `New.Data.m_even` (New/Reduction/Data/Magnitudes.lean).

*Proof.* Part 1: square $\sqrt x \leq m \leq 2\sqrt x$. Part 2: $s = 22(e + 1) \geq 22$, and $2^s = (2^{e+1})^{22} = m^{22}$. Part 3: $m^{594} = (m^{22})^{27} = 2^{27 s}$, and $27 s < l_0$. Part 4: $m \geq \sqrt x = \exp(\tfrac12 \log x)$, and $\log x \geq 100 \log\log b \geq 100 \cdot 10^{12} \cdot 64$ by (S2), (S1) and $C_P \geq 64$. So $m$ is far above $10^4$. A power $2^{e+1}$ with $e \geq 0$ is even. $\square$

Part 3 is used in the divisibility part of Theorem A.

### The derived ranks

**Definition (The derived ranks).** For data $D$ put
$$k = r + 1 - m, \qquad t = 5r, \qquad \tfrac12\Delta = r^8, \qquad \Delta = 2 r^8,$$
$$n_j = k + j(t + 1), \qquad \operatorname{posRank}(j) = k + j - 1 \qquad (j \in \mathbb{N}).$$
The number $k$ is the rank of the source of the chain of lifts. The number $\Delta$ is the gap between the weights of consecutive lifts. The number $\operatorname{posRank}(j)$ is the number of plus signs of the diagonal hermitian space $W_j$ of rank $r$ in the $j$-th step of the chain. The source also uses $\tfrac12 \Delta - \tfrac12 (t + 1)$, which it calls the reduced half gap.

Lean: `New.Data.k`, `New.Data.t`, `New.Data.halfGap`, `New.Data.gap`, `New.Data.n`, `New.Data.posRank`, `New.Data.reducedHalfGap` (New/Reduction/Data/AdmissibleData.lean).

**Remark (Formalization).** The subtraction in $k = r + 1 - m$ is the truncated subtraction of natural numbers: it gives $0$ if $m > r + 1$. The next proposition shows $m \leq r + 1$, so the subtraction is exact. In the reduced half gap the source uses truncated subtraction and the integer part of $(t+1)/2$. Since $t$ is odd, $(t+1)/2$ is exact, and $\tfrac12(t+1) \leq r^8$, so this subtraction is exact as well.

**Proposition (Inequalities and parities of the ranks).** The data satisfy:

1. $r + 1 = k + m$;
2. $100\, m \leq k$, and $k > 0$;
3. $k \leq r \leq 2k$;
4. $r + 6 \leq t$;
5. $k + t + 1 \leq \tfrac12 \Delta = r^8$;
6. $r$ and $t$ are odd; $m$, $k$ and every $n_j$ are even.

Lean: `New.Data.r_add_one`, `New.Data.hundred_mul_m_le_k`, `New.Data.k_pos`, `New.Data.k_le_r`, `New.Data.r_add_six_le_t`, `New.Data.k_add_t_add_one_le_halfGap`, `New.Data.r_odd`, `New.Data.t_odd`, `New.Data.k_even` (New/Reduction/Data/Magnitudes.lean); `New.Data.r_le_two_mul_k` (New/Reduction/Data/Sizes.lean); `New.Data.n_even` (New/UpperBound/Objects/Weights.lean).

*Proof.* The proofs compare $m \leq 2\sqrt x$ with $r \geq x^5$, where $x$ is huge.

Part 1. One has $m \leq 2\sqrt x \leq x^5 + 1 \leq r + 1$. So the truncated subtraction is exact, and $k + m = r + 1$.

Part 2. One has $k = r + 1 - m \geq x^5 + 1 - 2\sqrt x$, and $100 m \leq 200\sqrt x$. Since $x^5 \geq 202\sqrt x$, one gets $100 m \leq k$. Then $k \geq 100 m > 0$.

Part 3. From part 1 and $m \geq 10^4 \geq 1$, $k = r + 1 - m \leq r$. From parts 1 and 2, $r < r + 1 = k + m \leq k + k/100$, so $r \leq 2k$.

Part 4. One has $r = 3^{e+1} \geq 3$, so $t = 5r \geq r + 12 \geq r + 6$.

Part 5. One has $k + t + 1 \leq r + 5r + 1 \leq 18 x^5 + 1$, while $r^8 \geq x^{40}$. Since $x \geq 2$, $18 x^5 + 1 \leq x^{40}$.

Part 6. A power of $3$ is odd, so $r$ and $t = 5r$ are odd, and $m$ is even by the lemma above. By part 1, $k = r + 1 - m$ is a sum of the even number $r + 1$ and the even number $-m$, so $k$ is even. Then $t + 1$ is even, so $n_j = k + j(t + 1)$ is even. $\square$

### The invariants of the field

**Proposition (The number of places and the modulus).** The data satisfy
$$x^{11} \leq m^{22} = 2^s \leq f \leq q_1 \leq x^{12},$$
and $f$ is even.

Lean: `New.Data.f_mem_Icc`, `New.Data.q₁_le`, `New.Data.f_even` (New/Reduction/Data/Sizes.lean).

*Proof.* The bound $x^{11} \leq m^{22}$ is the eleventh power of $x \leq m^2$. Next, $f = \operatorname{towerDeg}(s)\varphi(q_0) = 3^{\lfloor\log_3 s\rfloor + 5}\, 2^s \varphi(q_0)$. So $2^s \leq f$, since the other two factors are at least $1$. Since $\varphi(q_0) \leq q_0$, one gets $f \leq \operatorname{towerDeg}(s)\, q_0 = q_1$. The number $f$ is even, since $2^s$ with $s \neq 0$ divides it.

For $q_1 \leq x^{12}$, bound the three factors of $q_1 = q_0 \cdot 3 l_0 \cdot 2^s$. First, $q_0 \leq C_P \leq 10^{-12}\log\log b \leq \log x$ by (S1) and (S2). Second, $3 l_0 \leq 243 s \leq 243 \cdot 32 \log x$. Third, $2^s = m^{22} \leq 2^{22} x^{11}$. So
$$q_1 \leq 2^{22} \cdot 7776 \, (\log x)^2 \, x^{11} \leq x^{12},$$
since $x \geq 2^{22} \cdot 7776 \, (\log x)^2$ for $\log x \geq 6.4 \cdot 10^{15}$. $\square$

**Proposition (The modulus of the congruences).** The modulus $q_2 = (q_0 d)^{s+6}$ satisfies
$$q_2 \leq x^{33\, q_0 d}.$$

Lean: `New.Data.q₂_le` (New/Reduction/Data/Sizes.lean).

*Proof.* One has $s + 6 \leq 32 \log x + 6 \leq 33 \log x$, since $\log x \geq 6$. Also $q_0 d \leq \exp(q_0 d)$. So $q_2 \leq \exp\bigl((s + 6) q_0 d\bigr) \leq \exp(33 \log x \cdot q_0 d) = x^{33 q_0 d}$. $\square$

The exponent $33 q_0 d$ is a constant of the parameters. So $q_2$ is a fixed power of $x$. The primes of Section 5 lie in a residue class modulo $q_2^2$.

**Lemma (A power of $x_1$ below $\sqrt b$).** The data satisfy
$$x_1^{3 l_0^2} \leq \sqrt b .$$

Lean: `New.Data.x₁_pow_le_sqrt_b` (New/Reduction/Data/Sizes.lean).

*Proof.* Take logarithms. One must show $3 l_0^2 \log x_1 \leq \tfrac12 \log b$. By $l_0 \leq 81 s$ and $s \leq 32 \log x \leq 32 \log x_1$,
$$3 l_0^2 \log x_1 \leq 3 \cdot 81^2 \cdot 32^2 (\log x_1)^3 \leq 2.1 \cdot 10^{7} (\log x_1)^3 .$$
By (S5), $(\log x_1)^6 \leq \log b$. Since $\log x_1 \geq 6.4 \cdot 10^{21}$, one has $2.1 \cdot 10^7 (\log x_1)^3 \leq \tfrac12 (\log x_1)^6 \leq \tfrac12 \log b$. $\square$

Here (S5) is needed, since (S4) alone does not bound $(\log x_1)^3$ by $\log b$. The bound is used in the divisibility part of Theorem A.
