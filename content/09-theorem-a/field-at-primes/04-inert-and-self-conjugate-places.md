---
title: Inert primes and self-conjugate places
lean:
  - New/Derivatives/Field/PrimeDecomposition.lean
  - New/Derivatives/Field/WeilData.lean
decls:
  - New.Parameters.not_dvd_q₁_mul_d_of_inert
  - New.Parameters.smul_eq_self_iff_of_inert
  - New.Parameters.smul_eq_star_iff_of_inert
  - New.Parameters.q_eq_pow_lcm_of_inert
  - New.Parameters.natCast_dvd_pow_sub_galOfPlaceInt_star
  - New.Parameters.betaKInE_mul_star_notMem_of_star_eq
  - New.Parameters.not_dvd_q₁_of_star_eq
  - New.Parameters.natCast_eq_neg_one_of_star_eq
  - New.Parameters.chiK_eq_one_of_modEq_one
  - New.Parameters.not_dvd_q₁_mul_d_of_modEq_one
  - New.Parameters.frobElem_eq_one
  - New.Parameters.smul_ne_star
  - New.Parameters.q_eq_of_modEq_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Inert primes and self-conjugate places

The gain of Theorem A comes from the nonsplit primes: the primes $p$ with $\chi_K(p) = -1$. At such a prime the Frobenius pair has sign $-1$, so a power of the Frobenius exchanges a place $w$ and its conjugate $\bar w$ whenever the exponent is odd. This section makes that precise. It then proves a congruence for self-conjugate places, and it treats the primes $p \equiv 1 \bmod q_1 d$, which are the opposite case.

### Inert primes

**Lemma.** If $\chi_K(p) = -1$, then $p \nmid q_1 d$.

Lean: `New.Parameters.not_dvd_q₁_mul_d_of_inert` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* A prime that divides $q_1$ has $\chi_K(p) = 1$ (Lean: `New.Parameters.chiK_eq_one_of_dvd`, from [fields, places and twists](/chapter/fields-places-twists/)). The only prime that divides $d$ is $d$, and $\chi_K(d) = 0$. $\square$

So all the theorems of Section 3 apply to an inert prime, and $\mathrm{Frob}_p = (v_{-p}, -1)$.

**Theorem (Stabilizer of an inert place).** Let $\chi_K(p) = -1$, let $w$ be a place above $p$, and let $v \in \Phi$.

1. $v \cdot w = w$ if and only if $v = v_{-p}^n$ for some even $n \in \mathbb{N}$.
2. $v \cdot w = \bar w$ if and only if $v = v_{-p}^n$ for some odd $n \in \mathbb{N}$.

Lean: `New.Parameters.smul_eq_self_iff_of_inert`, `New.Parameters.smul_eq_star_iff_of_inert` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* We have $\mathrm{Frob}_p^n = (v_{-p}^n, (-1)^n)$. By the decomposition theorem of Section 3, $v \cdot w = w$ if and only if $(v, 1) = \mathrm{Frob}_p^n$ for some $n$, that is, $v = v_{-p}^n$ and $(-1)^n = 1$. This is part 1. Part 2 is the same with the sign $-1$, so $n$ is odd. $\square$

The two parts can both hold for the same $v$. If the order $o$ of $v_{-p}$ is odd, then $v_{-p}^{n} = v_{-p}^{n + o}$, and one of $n$ and $n + o$ is even and the other is odd. In that case $v_{-p}^n \cdot w = w = \bar w$ for every $n$. This is the case of a self-conjugate place. If $o$ is even, the parity of $n$ is fixed by $v$, and $w \ne \bar w$.

**Theorem (Norm of an inert place).** Let $\chi_K(p) = -1$ and let $w$ be a place above $p$. Then $q_w = p^{\mathrm{lcm}(o, 2)}$, where $o$ is the order of $v_{-p}$ in $\Phi$, that is, the order of $-p$ in $(\mathbb{Z}/q_1)^\times$.

Lean: `New.Parameters.q_eq_pow_lcm_of_inert` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* By Section 3, $q_w = p^m$ with $m$ the order of $\mathrm{Frob}_p = (v_{-p}, -1)$. The order of a pair in a product of monoids is the least common multiple of the orders of the coordinates. The order of $-1$ in $\mathbb{Z}$ under multiplication is $2$. $\square$

So the residue degree of an inert place is always even, as it must be: the place lies over the prime $p\mathcal{O}_K$ of norm $p^2$.

The next statement is a congruence modulo $p$ itself, not modulo one place. It is the form that the mark operator of [divisibility prime by prime](/chapter/divisibility/) uses.

**Theorem (The Frobenius congruence).** Let $\chi_K(p) = -1$ and let $n$ be odd. Let $\tau = \sigma_{v_{-p^n}}$. Then for every $y \in \mathcal{O}_E$,
$$p \mid y^{p^n} - \tau(\bar y).$$

Lean: `New.Parameters.natCast_dvd_pow_sub_galOfPlaceInt_star` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Let $Q = \mathcal{O}_E / p\mathcal{O}_E$. It is a ring of characteristic $p$; it is not a field, and not always a domain, but the first lemma of the subsection "The Frobenius modulo a prime" of Section 3 does not need a domain. Apply it to the quotient map $\pi : \mathcal{O}_E \to Q$, with $v = v_{-p^n}$, the exponent $n$, and $(c, e)$ the conjugation with the sign $-1$. Condition 1 says $\pi(\sigma_v \zeta) = \pi(\sigma_{v_{-p^n}} \zeta)$, which is true. Condition 2 says $\chi_K(p)^n \cdot (-1) \cdot \pi(\sqrt{-d}) = \pi(\sqrt{-d})$. As $n$ is odd, $\chi_K(p)^n \cdot (-1) = (-1)^n(-1) = 1$, so it is also true. The lemma gives $\pi(\tau x) = \pi(\bar x)^{p^n}$ for all $x$. Put $x = \bar y$. Then $\pi(\tau \bar y) = \pi(y)^{p^n}$, which is the claim. $\square$

Only the hypothesis $p \nmid q_1$ is used in the first lemma of Section 3. That holds by the first lemma of this section.

### Self-conjugate places

A finite place $w$ is self-conjugate if $\bar w = w$. In the model of Section 1, all places above $11$ are self-conjugate. The next statements say where such places can lie.

**Lemma.** Let $w$ be a self-conjugate finite place. Then $\beta_K \bar\beta_K \notin w$.

Lean: `New.Parameters.betaKInE_mul_star_notMem_of_star_eq` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* If $\beta_K \bar\beta_K \in w$, then $w$ contains $\beta_K$ or $\bar\beta_K$, as $w$ is prime. Since $\bar w = w$, $x \in w$ if and only if $\bar x \in w$. So $w$ contains both, and their sum $1$. That is false. $\square$

**Lemma.** Let $w$ be a self-conjugate place above a prime $p$. Then $p \nmid q_1$.

Lean: `New.Parameters.not_dvd_q₁_of_star_eq` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* A prime that divides $q_1$ divides $(d+1)/4$ (Lean: `New.Parameters.dvd_d_add_one_div_four_of_dvd_q₁`). By Section 1, $(d+1)/4 = \beta_K\bar\beta_K$. So $p \mid q_1$ would give $\beta_K\bar\beta_K \in w$, against the last lemma. $\square$

**Theorem (Self-conjugate places).** Let $w$ be a self-conjugate place above a prime $p$. Then $p \equiv -1 \bmod 2^{s+1}$.

Lean: `New.Parameters.natCast_eq_neg_one_of_star_eq` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Since $\bar w = w$, the place $1 \cdot w = w$ is the pullback of $w$ along the conjugation. By the last lemma, $p \nmid q_1$. There are three cases, by the value of $\chi_K(p)$.

Case $p = d$. Section 3 gives $n \in \mathbb{N}$ with $\sigma_1 x \equiv \bar x^{d^n} \bmod w$ for all $x$ (the lemma before the decomposition theorem). The first lemma of the subsection "The Frobenius modulo a prime", which needs only $d \nmid q_1$, gives $\pi(\zeta) = \pi(\sigma_{v_{-d^n}} \zeta)$. The second lemma of that subsection gives $v_{-d^n} = 1$. Reduce the class of $-d^n$ to $\mathbb{Z}/q_0$, which is possible since $q_0 \mid q_1$ (Lean: `New.Parameters.placeClass_placeOfInt`). Then $d^n \equiv -1 \bmod q_0$. This is false for every $n$ (Lean: `New.Parameters.d_pow_ne_neg_one`). Indeed $d + 1 \equiv q_0/2 \bmod q_0$, so $(d+1)^2 \equiv 0$ and $d^2 \equiv -2(d+1) + 1 \equiv 1 \bmod q_0$. The powers of $d$ modulo $q_0$ are $1$ and $d$, and neither is $-1$: the first since $q_0 > 2$, the second since $d + 1 \not\equiv 0$.

Case $\chi_K(p) = 1$. Then $p \nmid q_1 d$, and by Section 3, $(1, -1)$ is a power of $\mathrm{Frob}_p = (v_p, 1)$. The second coordinate of every power is $1$, not $-1$. So this case is impossible.

Case $\chi_K(p) = -1$. By the stabilizer theorem above, part 2 with $v = 1$, there is an odd $n$ with $v_{-p}^n = 1$. Let $u$ be the class of $-p$ in $(\mathbb{Z}/2^{s+1})^\times$; it exists since $2^{s+1} \mid q_1$. Then $u^n = 1$. The group $(\mathbb{Z}/2^{s+1})^\times$ has order $\varphi(2^{s+1}) = 2^s$, so $u^{2^s} = 1$. As $n$ and $2^s$ are coprime, $u = 1$, that is, $-p \equiv 1 \bmod 2^{s+1}$. $\square$

**Remark (Formalization).** The case $p = d$ is a real case in the proof. The decomposition theorem of Section 3 assumes $p \nmid q_1 d$, so the source cannot use it for $p = d$, where $w$ is ramified over $d$. It uses the two lemmas before that theorem, which need only $p \nmid q_1$. In the language of a textbook, the argument shows that the conjugation acts on the residue field of $w$ as a power of the Frobenius, and that on $\zeta$ this would need $-1$ to be a power of $d$ modulo $q_0$.

### Primes congruent to 1 modulo $q_1 d$

The level $N$ and the primes $p_0$, $p_1$ of [data and sizes](/chapter/data-and-sizes/) satisfy $p \equiv 1 \bmod q_1 d$. Such primes split completely in $E$.

**Lemma.** Let $p \equiv 1 \bmod q_1 d$. Then $\chi_K(p) = 1$. If $p$ is prime, then $p \nmid q_1 d$ and $\mathrm{Frob}_p = 1$.

Lean: `New.Parameters.chiK_eq_one_of_modEq_one`, `New.Parameters.not_dvd_q₁_mul_d_of_modEq_one`, `New.Parameters.frobElem_eq_one` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* From $p \equiv 1 \bmod d$, $\chi_K(p) = \chi_K(1) = 1$. If a prime $p$ divides $q_1 d$, then $p \mid 1$, which is false. From $p \equiv 1 \bmod q_1$, $v_p = v_1 = 1$. So $\mathrm{Frob}_p = (v_p, 1) = (1, 1)$. $\square$

The first and third parts of the lemma do not need $p$ prime. The third part is a statement on the definition of $\mathrm{Frob}_p$ only.

**Theorem.** Let $p \equiv 1 \bmod q_1 d$ be prime and let $w$ be a place above $p$.

1. $q_w = p$.
2. For every $v \in \Phi$, $v \cdot w \neq \bar w$.

Lean: `New.Parameters.q_eq_of_modEq_one` (New/Derivatives/Field/WeilData.lean), `New.Parameters.smul_ne_star` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* By Section 3, $q_w = p^m$ with $m$ the order of $\mathrm{Frob}_p = 1$, so $m = 1$. By the decomposition theorem, $v \cdot w = \bar w$ would make $(v, -1)$ a power of $1$, and every power of $1$ has second coordinate $1$. $\square$

So there are $2f$ places above $p$, and $\Phi$ acts on them freely with two orbits, which are exchanged by the conjugation. Section 5 turns this into a bijection between $\Phi$ and one of the orbits.

### Examples in the model

In the model of Section 1, $d = 23$ and $q_1 = 12$, so the analogue of $2^{s+1}$ is $4$.

**Example.** Take $p = 7$. Then $(7/23) = -(23/7) = -(2/7) = -1$, so $7$ is inert. As $-7 \equiv 5 \bmod 12$, $\mathrm{Frob}_7 = (v_5, -1)$. The class $5$ has order $o = 2$, so $q_w = 7^{\mathrm{lcm}(2,2)} = 49$, and there are $8/2 = 4$ places above $7$. The stabilizer of $w$ in $\Phi$ is $\{v_5^n : n \text{ even}\} = \{1\}$. The places $v$ with $v \cdot w = \bar w$ are the odd powers of $v_5$, that is, $v_5$ alone. So $\bar w = v_5 \cdot w \ne w$. Here $7 \equiv -1 \bmod 4$, and still the places above $7$ are not self-conjugate. The congruence of the theorem on self-conjugate places is a necessary condition, not a sufficient one.

**Example.** Take $p = 11$. As $-11 \equiv 1 \bmod 12$, $\mathrm{Frob}_{11} = (1, -1)$, and $o = 1$ is odd. So $1 \cdot w = \bar w$, that is, $w$ is self-conjugate, and $q_w = 11^{\mathrm{lcm}(1, 2)} = 121$. The theorem on self-conjugate places gives $11 \equiv -1 \bmod 4$, which holds. The Frobenius congruence with $n = 1$ says $11 \mid y^{11} - \bar y$ for all $y \in \mathcal{O}_E$, since $\tau = \sigma_{v_{-11}} = \sigma_1$ is the identity.

**Example.** Take $p = 5$. As $-5 \equiv 7 \bmod 12$, $\mathrm{Frob}_5 = (v_7, -1)$, with $o = 2$. The places above $5$ are not self-conjugate, and $5 \not\equiv -1 \bmod 4$, as the theorem requires. The Frobenius congruence with $n = 1$ says $5 \mid y^5 - \sigma_7(\bar y)$. For $y = \zeta$, this is $5 \mid \zeta^5 - \zeta^{-7}$, and $\zeta^{-7} = \zeta^5$, so the difference is $0$.

**Example.** The smallest prime $p \equiv 1 \bmod 12 \cdot 23 = 276$ is $277$. It splits completely in $E$, into $8$ places of norm $277$, and no $v \in \Phi$ sends a place above $277$ to its conjugate.
