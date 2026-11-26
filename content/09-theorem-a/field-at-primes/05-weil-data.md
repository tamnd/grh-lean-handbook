---
title: Split places and the Weil data of E
lean:
  - New/Derivatives/Field/WeilData.lean
decls:
  - New.Parameters.smul_eq_self_iff_eq_one
  - New.Parameters.star_mem_iff_notMem
  - New.Parameters.intValuation_eq_of_mul_star
  - New.Parameters.eq_of_smul_eq_or_smul_eq_star
  - New.Parameters.nonempty_infinitePlace_equiv_finPlace
  - New.diagonalAtPlaces
  - New.diagonalAtPlaces_eq
  - New.diagonalAtPlaces_apply
  - New.Parameters.valuation_map_relDifferentGen
  - New.Parameters.valuation_star_relDifferentGen
  - New.Parameters.betaKInE_mem_or_star_mem
  - New.Parameters.α
  - New.Parameters.alpha_apply
  - New.Parameters.inv_alpha_apply
  - New.Parameters.inv_alpha_mem
  - New.Parameters.v_alpha_apply
  - New.Parameters.v_star_alpha_apply
  - New.Parameters.v_alpha_mul_star_mul_relDifferentGen
  - New.Parameters.q₁_mul_alpha_mem
  - New.Parameters.twelve_dvd_q₁
  - New.Parameters.norm_zeta_pow_eq_one
  - New.Parameters.norm_zeta_sub_one_eq_one
  - New.Parameters.v_neg_inv_sqrtNegDInE_mul_alpha_mul_star
  - New.Parameters.weilData_j_eq
  - New.Parameters.phi_weilData_j
  - New.Parameters.traceOne_eq_betaKInE
  - New.Parameters.v_weilData_j_mul_alpha_mul_star
  - New.Parameters.vacuumRoot
  - New.Parameters.vacuumRoot_pow_numInfPlaces
  - New.Parameters.exists_chiFin_alpha_pow_mem
  - New.Parameters.exists_vacuumRoot_pow_mem
  - New.Parameters.ideleAbs_alpha_eq_prod
  - New.Parameters.norm_gal_vacuumRoot
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Split places and the Weil data of E

This section has two parts. The first part counts the places above a prime $p \equiv 1 \bmod q_1 d$ that divide a given element. The lift chains of [the objects of the upper bound](/chapter/upper-bound-objects/) use this count to index the places above the level by $\Phi$. The second part builds the Weil data of $E$: an imaginary element $\jmath$, a finite idele $\alpha$, and a splitting character $\upsilon$. From $\alpha$ it defines the number $s_0$ and computes the absolute values of its conjugates. The general notion of Weil data is in [local duality](/chapter/local-duality/).

### Places above a split prime

In this subsection $p$ is a prime with $p \equiv 1 \bmod q_1 d$. By Section 4, $\mathrm{Frob}_p = 1$, every place $w$ above $p$ has $q_w = p$, and no $v \in \Phi$ sends $w$ to $\bar w$.

**Lemma.** Let $w$ be a place above $p$ and $v \in \Phi$. Then $v \cdot w = w$ if and only if $v = 1$.

Lean: `New.Parameters.smul_eq_self_iff_eq_one` (New/Derivatives/Field/WeilData.lean).

*Proof.* By the decomposition theorem of Section 3, $v \cdot w = w$ if and only if $(v, 1)$ is a power of $\mathrm{Frob}_p = (1, 1)$, that is, $v = 1$. $\square$

**Lemma.** Let $u, v \in \Phi$ and let $w$ be a place above $p$. If $v \cdot w = u \cdot w$ or $v \cdot w = \overline{u \cdot w}$, then $u = v$.

Lean: `New.Parameters.eq_of_smul_eq_or_smul_eq_star` (New/Derivatives/Field/WeilData.lean).

*Proof.* The place $u \cdot w$ is again above $p$, and $(u^{-1}v) \cdot (u \cdot w) = v \cdot w$. So the hypothesis says that $u^{-1}v$ fixes $u \cdot w$ or sends it to its conjugate. The second case is impossible by Section 4. In the first case $u^{-1} v = 1$ by the last lemma. $\square$

So the $2f$ places above $p$ are the places $v \cdot w$ and $\overline{v \cdot w}$ for $v \in \Phi$, and these $2f$ places are distinct. To select one place from each pair, the source uses an element $a$ with $a\bar a = pc$.

**Lemma.** Let $w$ be a place above $p$. Let $a \in \mathcal{O}_E$ and $c \in \mathbb{N}$ with $a\bar a = pc$ and $\gcd(p, c) = 1$.

1. $\bar a \in w$ if and only if $a \notin w$.
2. If $a \in w$, then $\mathrm{ord}_w(a) = 1$.

Lean: `New.Parameters.star_mem_iff_notMem`, `New.Parameters.intValuation_eq_of_mul_star` (New/Derivatives/Field/WeilData.lean).

*Proof.* As $p \in w$, $a\bar a = pc \in w$, so $w$ contains $a$ or $\bar a$. Suppose $w$ contains both. Then $pc \in w^2$. As $w$ is prime and $w \mid p$, the element $c$ is not in $w$: otherwise $w$ contains $1 = xp + yc$ for integers $x, y$. So $p \in w^2$, against the lemma on ramification of Section 3. This proves part 1. For part 2, $\bar a$ and $c$ are units at $w$ by part 1 and by $\gcd(p,c) = 1$. So $\mathrm{ord}_w(a) = \mathrm{ord}_w(a\bar a) = \mathrm{ord}_w(p) = 1$, again by Section 3. $\square$

**Theorem (The places that divide $a$).** Let $a \in \mathcal{O}_E$ and $c \in \mathbb{N}$ with $a\bar a = pc$ and $\gcd(p, c) = 1$. Then there is a bijection between $\Phi$ and the set of finite places $w$ with $a \in w$ and $p \in w$.

Lean: `New.Parameters.nonempty_infinitePlace_equiv_finPlace` (New/Derivatives/Field/WeilData.lean).

*Proof.* Fix a place $w$ above $p$. For $v \in \Phi$, let $\mathrm{pl}(v)$ be $v \cdot w$ if $a \in v \cdot w$, and $\overline{v \cdot w}$ otherwise. By part 1 of the last lemma, applied to $v \cdot w$, the place $\mathrm{pl}(v)$ contains $a$ in both cases, and it contains $p$. The map is injective: if $\mathrm{pl}(u) = \mathrm{pl}(v)$, then $v \cdot w$ is $u \cdot w$ or $\overline{u \cdot w}$, and $u = v$ by the lemma before. The map is surjective: a place $w'$ with $a, p \in w'$ is $v \cdot w$ or $\overline{v \cdot w}$ for some $v$, by the transitivity lemma of Section 3. In the first case $a \in v \cdot w$, so $\mathrm{pl}(v) = w'$. In the second case $a \notin v \cdot w$ by part 1, so again $\mathrm{pl}(v) = w'$. $\square$

**Remark (Formalization).** The statement is `Nonempty` of an equivalence. So the source asserts that a bijection exists, but it names no bijection, and the bijection of the proof depends on the choice of $w$. A user that needs a fixed bijection must pick one with a choice. The places counted are those with $a \in w$ and $p \in w$; these are the places above $p$ that divide $a$. Places that divide $a$ but lie over primes of $c$ are not counted.

**Example.** In the model of Section 1 ($d = 23$, $q_1 = 12$), take $p = 829$. It is prime, and $829 = 1 + 3 \cdot 276 \equiv 1 \bmod 12 \cdot 23$. In $\mathcal{O}_K$, the element $a = 1 + 6\sqrt{-23}$ has $a\bar a = 1 + 36 \cdot 23 = 829$. So $c = 1$. The prime $829$ has $8$ places in $E$, all of norm $829$. Exactly $4 = f$ of them divide $a$, one in each conjugate pair, and $\Phi$ permutes these $4$ places simply transitively.

### The idele $\alpha$

Write $\delta = \delta_{E/K} = \Phi_{q_1}'(\zeta)$ for the generator of the different of $E/K$ from Section 2. The idele $\alpha$ is $\delta^{-1}$ at the places that divide $\beta_K$, and $1$ at the other places. To write it the source uses one general map.

**Definition (Diagonal at a set of places).** Let $E$ be a number field and $S$ a set of finite places. For $x \in E$, $\mathrm{diag}_S(x)$ is the finite adele whose component at $w$ is $x$ if $w \in S$, and $1$ otherwise. With $e_S$ the idempotent of $S$, $\mathrm{diag}_S(x) = e_S x + (1 - e_S)$. The map $\mathrm{diag}_S$ is multiplicative.

Lean: `New.diagonalAtPlaces`, `New.diagonalAtPlaces_eq`, `New.diagonalAtPlaces_apply` (New/Derivatives/Field/WeilData.lean).

As $\mathrm{diag}_S$ is a monoid homomorphism, it maps units to units. For any $S$, $\mathrm{diag}_S(x)$ is a finite adele even when $S$ is infinite, since $x$ is a unit at almost all places.

**Lemma.** Let $w$ be a finite place of $E$.

1. For every injective ring endomorphism $\phi$ of $\mathcal{O}_E$, $|\phi(\delta)|_w = |\delta|_w$.
2. $|\delta|_{\bar w} = |\delta|_w$.
3. If $\delta \in w$, then $\beta_K \in w$ or $\bar\beta_K \in w$.

Lean: `New.Parameters.valuation_map_relDifferentGen`, `New.Parameters.valuation_star_relDifferentGen`, `New.Parameters.betaKInE_mem_or_star_mem` (New/Derivatives/Field/WeilData.lean).

*Proof.* For part 1, $\phi(\zeta)$ is again a primitive root of unity of order $q_1$, and $\phi(\delta) = \Phi_{q_1}'(\phi(\zeta))$. By Section 2, both $\delta$ and $\phi(\delta)$ generate the different of $E/K$. So they generate the same ideal and have the same valuation everywhere. Part 2 is part 1 for $\phi$ the conjugation, since $|\bar x|_{\bar w} = |x|_w$. For part 3, $\delta \mid q_1$ by Section 2, and every prime of $q_1$ divides $(d+1)/4 = \beta_K\bar\beta_K$. So $q_1 \mid ((d+1)/4)^{q_1}$, and $\delta$ divides $(\beta_K\bar\beta_K)^{q_1}$. A prime $w$ that contains $\delta$ contains $\beta_K\bar\beta_K$, and so one of the factors. $\square$

**Definition (The idele $\alpha$).** Let $S = \{w : \beta_K \in w\}$. The finite idele $\alpha$ is $\mathrm{diag}_S(\delta^{-1})$. So $\alpha_w = \delta^{-1}$ if $\beta_K \in w$, and $\alpha_w = 1$ otherwise, and $\alpha^{-1}_w$ is $\delta$ or $1$.

Lean: `New.Parameters.α`, `New.Parameters.alpha_apply`, `New.Parameters.inv_alpha_apply` (New/Derivatives/Field/WeilData.lean).

**Theorem (Properties of $\alpha$).** Let $w$ be a finite place of $E$.

1. $\alpha^{-1}$ is integral at every place.
2. $|\alpha_w|_w$ is $|\delta|_w^{-1}$ if $\beta_K \in w$, and $1$ otherwise.
3. $|\bar\alpha_w|_w$ is $|\delta|_w^{-1}$ if $\bar\beta_K \in w$, and $1$ otherwise.
4. $\alpha\bar\alpha\delta$ is a unit at every place.
5. $q_1\alpha$ is integral at every place.

Lean: `New.Parameters.inv_alpha_mem`, `New.Parameters.v_alpha_apply`, `New.Parameters.v_star_alpha_apply`, `New.Parameters.v_alpha_mul_star_mul_relDifferentGen`, `New.Parameters.q₁_mul_alpha_mem` (New/Derivatives/Field/WeilData.lean).

*Proof.* Part 1 holds because $\delta$ and $1$ are integral. Part 2 is the definition. For part 3, the component of $\bar\alpha$ at $w$ is the conjugate of $\alpha_{\bar w}$. It is $\delta^{-1}$, conjugated, if $\beta_K \in \bar w$, that is, if $\bar\beta_K \in w$. Then part 2 of the last lemma gives the valuation. For part 4, there are four cases. No place contains both $\beta_K$ and $\bar\beta_K$ (Section 1). If $w$ contains one of them, one of $\alpha$ and $\bar\alpha$ cancels $\delta$ and the other is a unit. If $w$ contains neither, $\delta$ is a unit at $w$ by part 3 of the last lemma. For part 5, write $q_1 = \delta \gamma$ with $\gamma \in \mathcal{O}_E$. The component of $q_1 \alpha$ is $\gamma$ or $\delta\gamma$. $\square$

### Roots of unity as quotients of units

A splitting character for $E$ exists if every root of unity of $E$ has the form $\eta/\bar\eta$ with a unit $\eta$ of norm $1$ over $K$ ([local duality](/chapter/local-duality/), the theorem `New.nonempty_splittingChar`). The source proves this hypothesis for $E$ with an explicit unit. The statement `New.Parameters.exists_unit_prod_phi_eq_one_and_mul_star_eq` is stated and proved in [local duality](/chapter/local-duality/). Here are its inputs.

**Lemma.** $12 \mid q_1$. For every $k \in \mathbb{N}$, $N_{E/K}(\zeta^k) = 1$. And $N_{E/K}(\zeta - 1) = 1$.

Lean: `New.Parameters.twelve_dvd_q₁`, `New.Parameters.norm_zeta_pow_eq_one`, `New.Parameters.norm_zeta_sub_one_eq_one` (New/Derivatives/Field/WeilData.lean).

*Proof.* $12 \mid 18480 \mid q_0 \mid q_1$. The cyclotomic polynomial $\Phi_{q_1}$ is irreducible over $K$ ([fields, places and twists](/chapter/fields-places-twists/)), so it is the minimal polynomial of $\zeta$ over $K$. It has even degree as $q_1 > 2$, so $N_{E/K}(\zeta) = (-1)^{\deg}\Phi_{q_1}(0) = 1$. Also $N_{E/K}(\zeta - 1) = \Phi_{q_1}(1)$. As $2$ and $3$ divide $q_1$, the order $q_1$ is not a prime power. For every $n > 1$, $\prod_{e \mid n,\, e > 1} \Phi_e(1) = 1 + 1 + \cdots + 1 = n$, the value at $1$ of $(X^n - 1)/(X - 1)$. For $n = \ell^k$ a prime power this gives $\Phi_{\ell^k}(1) = \ell$ by induction on $k$. For $n$ not a prime power, the prime powers $e > 1$ that divide $n$ already give the product $n$, so the product of $\Phi_e(1)$ over the other divisors $e > 1$ is $1$. Each $\Phi_e(1)$ with $e > 1$ is a positive integer: it is an integer, and it is the product of the numbers $1 - \xi$ over the primitive $e$-th roots of unity $\xi$, which come in conjugate pairs or are real and less than $1$. So all these values are $1$, and $\Phi_n(1) = 1$. $\square$

With $q_1 = 4m$ and $i = \zeta^m$, the unit is $\eta = i(\zeta - 1)$. It has norm $1$ over $K$ by the lemma. And $\zeta\bar\eta = \zeta(-i)(\zeta^{-1} - 1) = i(\zeta - 1) = \eta$. For the root of unity $\zeta^k$ one takes $\eta^k$. Every root of unity of $E$ is a power of $\zeta$ ([fields, places and twists](/chapter/fields-places-twists/)).

**Example.** In the model, $q_1 = 12$, $m = 3$ and $i = \zeta^3$. The unit is $\eta = \zeta^4 - \zeta^3$, and $\Phi_{12}(1) = 1 - 1 + 1 = 1$.

### The Weil data of $E$

**Lemma (Self-duality).** Let $w$ be a finite place of $E$. Then the order at $w$ of $(-1/\sqrt{-d})\alpha\bar\alpha$ is minus the order at $w$ of the different $\mathfrak{D}_E$ of $E/\mathbb{Q}$.

Lean: `New.Parameters.v_neg_inv_sqrtNegDInE_mul_alpha_mul_star` (New/Derivatives/Field/WeilData.lean).

*Proof.* By Section 2, $\mathfrak{D}_E$ is generated by $\delta\sqrt{-d}$. By part 4 of the theorem on $\alpha$, the order of $\alpha\bar\alpha$ is minus the order of $\delta$. So the order of $(-1/\sqrt{-d})\alpha\bar\alpha$ is $-\mathrm{ord}_w(\sqrt{-d}) - \mathrm{ord}_w(\delta) = -\mathrm{ord}_w(\mathfrak{D}_E)$. $\square$

In Lean the statement is $|\cdot|_w = \exp(m)$ with $m$ the multiplicity of $w$ in $\mathfrak{D}_E$: the multiplicative valuation of an element of order $-m$.

The Weil data of $E$ are the instance `New.Parameters.instWeilDataE`, stated in [local duality](/chapter/local-duality/). Its fields are:

1. $\jmath = -1/\sqrt{-d}$, with $\bar\jmath = -\jmath$ and positive imaginary part at every place of $\Phi$;
2. the idele $\alpha$ above, with the self-duality of the last lemma;
3. the integrality of $(1 - \jmath^{-1})/2$;
4. a splitting character $\upsilon$, from `New.nonempty_splittingChar` applied to the units of the last subsection;
5. the condition that $\upsilon$ is $-1$ at the uniformizer of a self-conjugate place, from `New.Cohomology.upsilon_atUniformizer_eq_neg_one`.

**Lemma.** For the Weil data of $E$:

1. $\jmath = -1/\sqrt{-d}$;
2. $\Phi_v(\jmath) = i/\sqrt{d}$ for every $v \in \Phi$;
3. $(1 - \jmath^{-1})/2 = \beta_K$;
4. at every finite place, the order of $\jmath\alpha\bar\alpha$ is minus the order of $\mathfrak{D}_E$.

Lean: `New.Parameters.weilData_j_eq`, `New.Parameters.phi_weilData_j`, `New.Parameters.traceOne_eq_betaKInE`, `New.Parameters.v_weilData_j_mul_alpha_mul_star` (New/Derivatives/Field/WeilData.lean).

*Proof.* Part 1 is the definition. For part 2, $\Phi_v(\sqrt{-d}) = i\sqrt{d}$, and $-1/(i\sqrt d) = i/\sqrt d$. For part 3, $\jmath^{-1} = -\sqrt{-d}$, so $(1 - \jmath^{-1})/2 = (1 + \sqrt{-d})/2$. Part 4 is the self-duality field. $\square$

**Remark (Formalization).** The splitting character $\upsilon$ is picked with `.some` from a `Nonempty` statement. So the Weil data of $E$ depend on a choice that Lean does not name. This is finding F-043 of the register, with the open question Q-18: does any statement depend on the splitting character that the instance picks? This chapter does not answer the question. The statements of this section on $\jmath$ and $\alpha$ do not use $\upsilon$. The number $s_0$ below uses $\upsilon$, but the absolute values of its conjugates do not depend on it, since $\upsilon$ has absolute value $1$.

### The number $s_0$

Let $\chi_{\mathrm{fin}}(x) = \upsilon(x)|x|^{-1/2}$ for a finite idele $x$, extended by $1$ at infinity (Lean: `New.chiFin`). Here $|x|$ is the idele norm.

**Definition (The number $s_0$).** $s_0 = \left(\chi_{\mathrm{fin}}(\alpha)^{-1}\right)^{1/f}$, the principal $f$-th root in $\mathbb{C}$.

Lean: `New.Parameters.vacuumRoot` (New/Derivatives/Field/WeilData.lean).

**Remark (Formalization).** The root is the principal branch $z^{1/f} = \exp(\log z / f)$ of the complex power, with $\log$ the principal logarithm. A textbook would say "an $f$-th root". All statements below hold for every $f$-th root, since they use only $s_0^f$ and the absolute value $|s_0|$.

**Lemma.**

1. $s_0^f = \chi_{\mathrm{fin}}(\alpha)^{-1}$.
2. Some power $\chi_{\mathrm{fin}}(\alpha)^k$ with $k > 0$ lies in $K$.
3. Some power $s_0^n$ with $n > 0$ lies in $K$.
4. $|\alpha| = \prod_{v \in \Phi} |\delta|_v$, where $\alpha$ is extended by $1$ at infinity.

Lean: `New.Parameters.vacuumRoot_pow_numInfPlaces`, `New.Parameters.exists_chiFin_alpha_pow_mem`, `New.Parameters.exists_vacuumRoot_pow_mem`, `New.Parameters.ideleAbs_alpha_eq_prod` (New/Derivatives/Field/WeilData.lean).

*Proof.* Part 1 holds for the principal root. For part 2, the Weil data give $k > 0$ and $y \in E^\times$ with $\chi_{\mathrm{fin}}(\alpha)^k = \prod_v \Phi_v(\bar y)$ (Lean: `New.WeilData.exists_chiFin_pow_eq_prod`). The product over $\Phi$ is the norm $N_{E/K}(\bar y) \in K$. Part 3 follows from parts 1 and 2 with $n = fk$. For part 4, let $x = \alpha\bar\alpha\delta$, an idele with component $\delta$ at the infinite places. By part 4 of the theorem on $\alpha$, $x$ is a unit at every finite place. So $|x| = \prod_v |\delta|_v^2$, where the square is the normalized absolute value at a complex place. Also $|\bar\alpha| = |\alpha|$ and $|\delta| = 1$ by the product formula. So $|\alpha|^2 = |x| = (\prod_v |\delta|_v)^2$, and both sides are positive. $\square$

**Theorem (The size of $s_0$).** For every automorphism $\sigma$ of $\mathbb{C}$ that fixes $K$,
$$|\sigma(s_0)|^2 = \mathrm{rd}_E / \sqrt{d}.$$

Lean: `New.Parameters.norm_gal_vacuumRoot` (New/Derivatives/Field/WeilData.lean).

*Proof.* By part 3 of the lemma, $\sigma$ fixes $s_0^n$, so $|\sigma(s_0)|^n = |s_0|^n$ and $|\sigma(s_0)| = |s_0|$. As $\upsilon$ has absolute value $1$, $|\chi_{\mathrm{fin}}(\alpha)|^{-2} = |\alpha|$. With part 1 and part 4 of the lemma,
$$|s_0|^{2f} = |\alpha| = \prod_{v} |\delta|_v = \prod_v \frac{|\varpi|_v}{\sqrt d} = \frac{\mathrm{rd}_E^f}{\sqrt d^{\,f}}.$$
The third step uses $|\varpi|_v = |\delta|_v \sqrt d$ and the fourth uses $\prod_v |\varpi|_v = \mathrm{rd}_E^f$, both from Section 2. Take $f$-th roots of positive numbers. $\square$

The scale of [the integral vacuum](/chapter/integral-vacuum/) uses this theorem.

**Example.** In the model, $\mathrm{rd}_E = 2\sqrt{69}$ and $\sqrt d = \sqrt{23}$, so the same computation would give $|s_0|^2 = 2\sqrt 3 = |\delta|_v$. The model has no Weil data of the kind above, as it is not an instance of the parameters, so this is only the arithmetic of the formula.
