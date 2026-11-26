---
title: The theorem on windows
lean:
  - Lib/Analytic/Primes.lean
  - New/Reduction/Data/Existence.lean
decls:
  - New.exists_prime_modEq_one_log_mem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The theorem on windows

This section proves the theorem of the chapter from the results of Sections 3 to 5. It then lists the thresholds of the proof, shows how the data of Volume 1 use the theorem, and compares it with the theorem of Siegel and Walfisz. In the source the modulus is called $M$. This book writes $Q$, since $M = p_0 p_1$ is the principal level of the data.

### The statement

**Theorem (Primes in windows).** Let $Q \geq 1$ and $A$ be natural numbers with $4 \mid Q$. Then there is $W_0$ with the following property. Let $W \geq W_0$ be real, let $k > 1$ be a natural number with $Q^k \leq W^A$, and let $U \in [W, W^A]$. Then there is a prime $p$ with
$$p \equiv 1 \pmod{Q^k} \qquad\text{and}\qquad U \leq \log p \leq U + W.$$
Lean: `New.exists_prime_modEq_one_log_mem` (Lib/Analytic/Primes.lean).

The theorem is uniform in $k$ and in $U$: one threshold $W_0$, which depends only on $Q$ and $A$, serves for every modulus $Q^k \leq W^A$ and every start $U \in [W, W^A]$. The window $[U, U + W]$ for $\log p$ is the interval $[e^U, e^{U + W}]$ for $p$. In terms of $y = e^U$, the theorem gives a prime $p \equiv 1 \pmod q$ in $[y, ye^W]$ for every $q = Q^k$ with $q \leq W^A$ and every $y$ with $W \leq \log y \leq W^A$.

### The proof

The proof follows the plan of Section 1. Put $X = \sqrt{W}$, so that $W = X^2$. The phrase "for large $W$" becomes "for large $X$", since $W \mapsto \sqrt{W}$ tends to infinity. In the new variable the hypotheses read
$$q = Q^k \leq X^{2A}, \qquad X^2 \leq U \leq X^{2A},$$
and the window is $[U, U + X^2]$. Let $b(n) = \Lambda(n)$ for $n$ not prime and $b(n) = 0$ for $n$ prime, and let $C = \sum_n b(n)n^{-3/4}$, which is finite by the [lemma on the prime powers](/decl/New.summable_vonMangoldt_not_prime/).

*The threshold.* Take $X$ so large that the five conditions of the table hold.

| condition on $X$ | source | used for |
|---|---|---|
| the [lemma on no zeros near 1](/decl/New.eventually_norm_logDeriv_entireL_le_near_one/) holds with the exponent $2A$ | Section 3 | $L^\ast \neq 0$ and $\lvert (L^\ast)'/L^\ast\rvert \leq X$ on $\lvert s - 1\rvert \leq 1/X$ |
| $e^{X/4}/X^{4A} > 3e^2$ | $e^{X/4}$ grows faster than every power | the final inequality |
| $X \geq 200$ | (H5) of Section 5 | the bound on the circle |
| $X \geq C$ | (H4) of Section 5 | the bound on the circle |
| $X > 0$ | | $W = X^2$ |

Each condition holds for all large $X$, so all five hold for $X \geq X_0$. Put $W_0 = X_0^2$. Fix $W \geq W_0$, $k > 1$ with $q = Q^k \leq W^A$, and $U \in [W, W^A]$.

*The generating function.* Let $a = a_q$ be $\Lambda$ on the class $1$ modulo $q$, and let $F = F_q$. By the [lemma on the generating function](/decl/New.hasSum_residueClass_one/), the series of $a$ at $1 + z$ has the sum $F(z)/z$ for $\operatorname{Re} z > 0$. This is (H2) of Section 5, and (H1) holds since $a \geq 0$.

*The disc.* Let $|z| \leq 1/X$ and let $\chi$ be a character modulo $q$. The lemma on no zeros near 1, at $s = 1 + z$ with $|s - 1| = |z| \leq 1/X$ and $Q^k \leq X^{2A}$, gives $L^\ast(1 + z, \chi) \neq 0$ and $|(L^\ast)'/L^\ast(1 + z, \chi)| \leq X$. So $|z\,(L^\ast)'/L^\ast(1 + z, \chi)| \leq (1/X)X = 1$, and the [bound for the generating function](/decl/New.norm_one_sub_mul_sum_div_totient_le/) gives $|F(z)| \leq 2$. This is (H3). The conditions $X \geq C$, $X \geq 200$ and $X^2 \leq U$ are (H4) and (H5).

*The contradiction.* Suppose that no prime $p \equiv 1 \pmod q$ has $\log p \in [U, U + X^2]$. Let $P(z) = \sum_{n < \lceil e^U\rceil} a(n)n^{-1-z}$ and
$$G(z) = \frac{F(z) - zP(z)}{\exp\bigl(2 - Uz - \tfrac{X}{4}(1 + Xz)^2\bigr)}.$$

1. *The window.* Let $\log n \in [U, U + X^2]$. If $n$ is prime, then $n \not\equiv 1 \pmod q$ by the assumption, so $a(n) = 0 \leq |b(n)|$. If $n$ is not prime, then $a(n) \leq \Lambda(n) = b(n)$. So $|a(n)| \leq |b(n)|$ in the window.
2. *The circle.* By step 1, the [bound on the circle](/decl/New.norm_sub_mul_sum_term_le/) applies. For $|z| = 1/X$ it gives $|F(z) - zP(z)| \leq 3U\exp(\operatorname{Re} E(z))$, and $|\exp(E(z))| = \exp(\operatorname{Re} E(z))$. So $|G(z)| \leq 3U$ on the circle.
3. *The maximum principle.* By the disc step and the [lemma on analyticity](/decl/New.analyticOnNhd_sub_mul_sum_term/) with $r = 1/X$ and $N = \lceil e^U\rceil$, the numerator of $G$ is analytic on the closed disc $|z| \leq 1/X$. The exponential does not vanish, so $G$ is analytic there. By the maximum principle, $|G(0)| \leq 3U$.
4. *The centre.* At $z = 0$ the terms with the factor $z$ vanish, so $F(0) = 1/\varphi(q)$, and the exponent is $2 - X/4$. So $|G(0)| = e^{X/4}e^{-2}/\varphi(q)$.
5. *The size.* Since $\varphi(q) \leq q \leq X^{2A}$ and $U \leq X^{2A}$,
$$3U\varphi(q)e^2 \leq 3e^2X^{4A} < e^{X/4},$$
by the second condition of the table. So $3U < e^{X/4}e^{-2}/\varphi(q) = |G(0)|$.

Steps 3 and 5 contradict each other. So the window holds a prime $p \equiv 1 \pmod q$. $\square$

The upper bound $U \leq W^A$ is used only in step 5. The lower bound $U \geq W$ is used only in (H5), through $X^2 \leq U$. The bound $Q^k \leq W^A$ is used twice: in the lemma on no zeros near 1, and in step 5 through $\varphi(q) \leq q$. The condition $k > 1$ is used only in the lemma on no zeros near 1, where the [lemma on squares](/decl/New.factorsThrough_sq_of_sq_eq_one/) needs $k \geq 2$.

**Example.** The threshold of the theorem is enormous. The lemma on no zeros near 1 applies the zero-free region with $l = (2A + 1)\log X$, and that region requires $l \geq 10^{10}$ and $2l^{25} \leq X$. For $A = 1$ the first condition alone asks for $\log X \geq 10^{10}/3$. The lemma also needs $1/l$ to be smaller than the radius of a disc about $s = 1$ on which the L-functions of the real characters modulo $Q^2$ stay away from $0$. The source shows that such a radius exists, by continuity, but it does not compute it. So the source gives no explicit value of $W_0$. The second condition of the table is mild by comparison: for $A = 1$ it holds for $X \geq 120$, since $e^{30} \approx 1.07 \cdot 10^{13}$ and $3e^2 \cdot 120^4 \approx 4.6 \cdot 10^{9}$.

### The primes of the data

The data of Volume 1 use the theorem once, in [the existence of the data](/decl/New.eventually_exists_data/). The theorem is applied with $Q = q_0 d$ and $A = n + 7$, where $n$ is the exponent of [the large scales](/decl/New.Parameters.IsLargeScale/), and with $W = x^{\varepsilon/6}$. Since $x^{\varepsilon/6}$ tends to infinity with $x$, the conclusion holds at $W = x^{\varepsilon/6}$ for every large $x$. Here $4 \mid q_0 d$, since $4 \mid 18480 \mid q_0$.

The lemma on [the existence of admissible data](/decl/New.Parameters.IsLargeScale.exists_isAdmissibleData/) takes the conclusion of the theorem at this $W$ as its hypothesis, word for word. It then specializes it. Let $L = \log b$, so that $W^6 \leq L \leq W^6 + 1$. For every $U \in [L, 24mL]$:

- the exponent is $k = 2(s + 6) > 1$, and $q_2^2 = (q_0 d)^{2(s + 6)} \leq W^n \leq W^{n + 7}$;
- $U \geq L \geq W^2 \geq W$;
- $U \leq 24mL \leq m \cdot W^7 \leq W^{n + 7}$, since $24L \leq W^7$ and $m \leq W^n$.

So every window $[U, U + W]$ with $U \in [L, 24mL]$ holds a prime $p \equiv 1 \pmod{q_2^2}$. Two lemmas pick the primes of the data from these windows.

**Lemma (Two level primes).** Let $P$ be parameters, let $s \in \mathbb{N}$, and let $W > 0$ and $L$ be real with $(2h + 2)W \leq L$, where $h$ is the class number of $K$. Suppose that for every $U \in [10L, 11L]$ there is a prime $p \equiv 1 \pmod{q_2^2}$ with $\log p \in [U, U + W]$. Then there are primes $p_0 \neq p_1$ and an integer $\alpha$ of $K$ with $\alpha\bar\alpha = p_0p_1$, such that for $i = 0, 1$, $p_i \equiv 1 \pmod{q_2^2}$ and $e^{10L} \leq p_i \leq e^{11L}$.
Lean: `New.Parameters.exists_prime_pair_norm` (New/Reduction/Data/Existence.lean), with the conditions on $p_i$ in `New.Parameters.IsPrincipalLevelPrime`.

*Proof of the part on windows.* For $0 \leq i \leq h$ let $U_i = 10L + 2iW$. Since $2iW + W \leq (2h + 1)W \leq L$, the window $[U_i, U_i + W]$ lies in $[10L, 11L]$, and the hypothesis gives a prime $p_i'$ in it. The windows are disjoint, since $U_i + W < U_{i + 1}$. So the $h + 1$ primes $p_i'$ are distinct, and each lies in $[e^{10L}, e^{11L}]$. Each splits in $K$, since $p_i' \equiv 1 \pmod{q_2^2}$. A pigeonhole argument in the class group of $K$, which has $h$ elements, gives two of them whose product is a norm. [The data exist](/chapter/data-exist/) in Volume 1 gives this argument in full. $\square$

The admissible data take the two primes of this lemma as $p_0$ and $p_1$. The field `levelPrime_mem` is the bound $b^{10} \leq p_i \leq b^{11}$, which is $e^{10L} \leq p_i \leq e^{11L}$. The hypothesis $(2h + 2)W \leq L$ holds, since the large scales give $2h + 2 \leq W$ and $W^2 \leq L$.

For the level $N$, the lemma on [the prime N](/decl/New.Parameters.exists_prime_log_mem_Icc_mul_star_eq/) uses one window, with the start $U = \log N_-$. This number lies in $[mL, 24mL]$, so the window holds a prime $N \equiv 1 \pmod{q_2^2}$ with $\log N \in [\log N_-, \log N_- + W]$. Since $W^2 \leq L$, this gives $\log N \in [\log N_-, \log N_- + \sqrt{L}]$, which is the condition of the data. The integer $\beta$ of $E$ with $\beta\bar\beta = N$ comes from the congruence $N \equiv 1 \pmod 4$ and is not part of this chapter.

The use of the windows is coarse. The windows have length $W = x^{\varepsilon/6}$, and the data need only $W \leq \sqrt{L}$ for $N$ and $(2h + 2)W \leq L$ for $p_0$ and $p_1$. The data also need the upper bound $U \leq 24mL$ only because the theorem asks for $U \leq W^A$.

### Comparison with Siegel and Walfisz

The theorem is a special case of the theorem of Siegel and Walfisz of Section 2. Take $B = A$. If $q \leq W^A$ and $U \geq W$, then $q \leq U^A = (\log y)^A$ for $y = e^U$. The theorem of Siegel and Walfisz gives
$$\psi(e^{U + W}; q, 1) - \psi(e^U; q, 1) = \frac{e^{U + W} - e^U}{\varphi(q)} + O_A\Bigl(e^{U + W}\exp\bigl(-c\sqrt{U}\bigr)\Bigr),$$
and the main term is larger than the error term as soon as $\varphi(q) \leq U^A$ is small against $\exp(c\sqrt{U})$. The prime powers add $O(e^{(U + W)/2})$. So the window holds a prime for large $U$, with an ineffective threshold. The source says the same in the comment to its theorem.

The theorem of the source is weaker in three ways: it treats only the moduli $Q^k$, only the class $1$, and it gives one prime instead of an asymptotic count. It is not weaker in its uniformity, since the lemma on no zeros near 1 is uniform in $k$. Its proof avoids the theorem of Siegel. The real characters modulo $Q^k$ come from the fixed modulus $Q^2$, so their L-functions are finitely many fixed functions, and continuity at $s = 1$ replaces the lower bound for $L(1, \chi)$. In principle every constant of the proof is effective, but the source does not compute the radius for the real characters.

Finding F-097 of the [register of findings](/chapter/register-of-findings/) asks whether the uniformity of the theorem is what the data need. The specialization above answers it for the reader. The hypothesis of the lemma on the existence of admissible data is the conclusion of the theorem with $Q = q_0d$, $A = n + 7$ and $W = x^{\varepsilon/6}$, and that lemma checks $k > 1$, $q_2^2 \leq W^{n + 7}$ and $[L, 24mL] \subseteq [W, W^{n + 7}]$ itself. Lean accepts this application if the checks that the source reports hold. This book did not rerun them.

**Remark (Formalization).** Seven points of the Lean form matter.

1. The theorem is stated with the filter `atTop` as an eventual statement in $W$. It asserts that some $W_0$ exists, and it gives no value of $W_0$. The data use it only as an eventual statement in $x$.
2. The window is closed: `Real.log p ∈ Set.Icc U (U + W)`. The start set `Set.Icc W (W ^ A)` is closed too.
3. The prime is an existential witness. The data choose it with `choose` in the lemma on two level primes, so the primes $p_0$, $p_1$ and $N$ of the data are not canonical.
4. The theorem asks for $k > 1$. The case $k = 1$ is not needed, and the lemma on squares is stated only for $k \geq 2$.
5. For $A = 0$ the theorem is vacuous, since $Q^k \geq 4^2 > 1 = W^0$. For $A = 1$ the start set is the single point $U = W$.
6. The function $a_q$ is Mathlib's `ArithmeticFunction.vonMangoldt.residueClass`, with $a_q(0) = 0$. The constant $C$ is taken by `obtain` from the summability, so the proof never names its value.
7. The source writes the modulus as `M` with `[NeZero M]`. Since $4 \mid 0$, the divisibility does not exclude $M = 0$, so Lean asks for the instance separately. This book writes $Q$ for it, and the data use $Q = q_0d$.
