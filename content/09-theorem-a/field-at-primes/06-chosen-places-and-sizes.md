---
title: Chosen places, residue characters and sizes
lean:
  - New/Derivatives/Field/ChosenPlaces.lean
decls:
  - New.Data.piM
  - New.Data.ChosenPlace
  - New.Data.piM_mul_star
  - New.Data.piMBar_ne_zero
  - New.Data.piM_ne_zero
  - New.Data.exists_piM_mul_star_eq_levelPrime_mul_coprime
  - New.Data.exists_levelPrime_mem_of_isChosen
  - New.Data.isChosen_iff
  - New.Data.q_eq_levelPrime
  - New.Data.finite_isChosen
  - New.Data.exists_mulChar_orderOf_eq_sq_of_isChosen
  - New.Data.chiMLocalRoot
  - New.Data.orderOf_chiMLocalRoot
  - New.Data.chiMLocal_of_isChosen
  - New.Data.chiMLocal_eq_one_of_not_isChosen
  - New.Data.chiMLocal_zpow_mul_pow_eq_one
  - New.Data.chiZero_hasWeight
  - New.Data.chiM_hasWeight
  - New.Data.finite_criticalPair
  - New.Parameters.exists_abs_log_le_and_apply_deltaE_eq
  - New.Parameters.abs_log_deltaE_sub_log_rootDiscr_le
  - New.Data.hasLogBound_deltaE
  - New.Data.hasLogBound_rootDisc
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Chosen places, residue characters and sizes

This section works with admissible data $D$, not only with parameters. The data give the scales $x$, $b$, the exponent $s$ of the tower, two primes $p_0 \ne p_1$, and an integer $\bar\pi_M \in \mathcal{O}_K$ with $\bar\pi_M \pi_M = M = p_0 p_1$; all of these are in [data and sizes](/chapter/data-and-sizes/). The primes satisfy $p_i \equiv 1 \bmod q_2^2$, and so $p_i \equiv 1 \bmod q_1 d$, since $q_1 d \mid q_2$. The section has three parts: the chosen places above $M$ and their residue characters, the finiteness of pairs, and the size of $\varpi$ and of $\mathrm{rd}_E$ at the infinite places.

### The chosen places

**Definition (Chosen places).** Let $\pi_M \in \mathcal{O}_E$ be the complex conjugate of the image of $\bar\pi_M$. A finite place $w$ of $E$ is chosen if $\pi_M \in w$. For $i \in \{0, 1\}$, the chosen places above $p_i$ are the finite places $w$ with $\pi_M \in w$ and $p_i \in w$.

Lean: `New.Data.piM`, `New.Data.ChosenPlace` (New/Derivatives/Field/ChosenPlaces.lean). The predicate is `New.Data.IsChosen`, from [fields, places and twists](/chapter/fields-places-twists/).

**Lemma.**

1. $\pi_M \bar\pi_M = M$ in $\mathcal{O}_E$.
2. $\bar\pi_M \neq 0$ in $\mathcal{O}_K$, and $\pi_M \ne 0$ in $\mathcal{O}_E$.
3. For $i \in \{0, 1\}$ there is $c \in \mathbb{N}$ with $\pi_M\bar\pi_M = p_i c$ and $\gcd(p_i, c) = 1$.

Lean: `New.Data.piM_mul_star`, `New.Data.piMBar_ne_zero`, `New.Data.piM_ne_zero`, `New.Data.exists_piM_mul_star_eq_levelPrime_mul_coprime` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Part 1: the map $\mathcal{O}_K \to \mathcal{O}_E$ commutes with complex conjugation, since $E$ is a CM field over the imaginary quadratic field $K$ ([CM fields](/chapter/cm-fields/)). So $\pi_M\bar\pi_M$ is the image of $\bar\pi_M \pi_M = M$, where now the bar on the right is conjugation in $K$. Part 2: if $\bar\pi_M = 0$, then $M = 0$, but $M = p_0p_1 > 0$. The map $\mathcal{O}_K \to \mathcal{O}_E$ and the conjugation are injective. Part 3: take $c = p_{1-i}$. The two primes are distinct, so they are coprime. $\square$

So $\pi_M$ satisfies the hypothesis of the theorem on the places that divide $a$ of Section 5, with $p = p_i$ and $a = \pi_M$. That theorem gives a bijection between $\Phi$ and the chosen places above $p_i$. In particular there are $f$ chosen places above $p_0$ and $f$ above $p_1$.

**Lemma.**

1. Every chosen place lies above $p_0$ or $p_1$. So $w$ is chosen if and only if $w$ is chosen and lies above some $p_i$.
2. Every place above $p_i$ has norm $q_w = p_i$.
3. There are finitely many chosen places.

Lean: `New.Data.exists_levelPrime_mem_of_isChosen`, `New.Data.isChosen_iff`, `New.Data.q_eq_levelPrime`, `New.Data.finite_isChosen` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* For part 1, a chosen place contains $\pi_M\bar\pi_M = p_0p_1$, so it contains one of the factors. Part 2 is the theorem of Section 4 for primes $p \equiv 1 \bmod q_1 d$, with $p_i \equiv 1 \bmod q_1 d$ (Lean: `New.Data.levelPrime_modEq_one`). For part 3, a chosen place is a prime factor of the nonzero ideal $(\pi_M)$, and a nonzero ideal of a Dedekind domain has finitely many prime factors. $\square$

### The residue characters $\omega_w$

Let $\mathbb{F}_w = \mathcal{O}_E/w$ be the residue field at $w$, and let $q_2 = (q_0 d)^{s+6}$.

**Lemma.** At a chosen place $w$, the residue field $\mathbb{F}_w$ has a multiplicative character $T : \mathbb{F}_w \to \mathbb{C}$ of order exactly $q_2^2$.

Lean: `New.Data.exists_mulChar_orderOf_eq_sq_of_isChosen` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* The place $w$ lies above some $p_i$, so $\#\mathbb{F}_w = p_i$ and $\#\mathbb{F}_w^\times = p_i - 1$. The data give $q_2^2 \mid p_i - 1$ (Lean: `New.Data.dvd_levelPrime_sub_one`). The group $\mathbb{F}_w^\times$ is cyclic of order $p_i - 1$. For a generator $g$, the map $g^n \mapsto e^{2\pi i n/q_2^2}$ is well defined because $q_2^2 \mid p_i - 1$, and it has order $q_2^2$. $\square$

**Definition (The residue characters).** At a chosen place $w$, $T_w$ is a character of order $q_2^2$, picked from the last lemma. The residue character $\omega_w$ is $T_w^{q_2}$ if $w$ is chosen, and the trivial character otherwise.

Lean: `New.Data.chiMLocalRoot`, `New.Data.orderOf_chiMLocalRoot`, `New.Data.chiMLocal_of_isChosen`, `New.Data.chiMLocal_eq_one_of_not_isChosen` (New/Derivatives/Field/ChosenPlaces.lean). The character $\omega_w$ is `New.Data.chiMLocal`, defined in [fields, places and twists](/chapter/fields-places-twists/).

**Remark (Formalization).** The character $T_w$ is picked with `choose` from an existence statement. There are $\varphi(q_2^2)$ characters of order $q_2^2$ on $\mathbb{F}_w$, and the source does not say which one it picks. The value $\omega_w = T_w^{q_2}$ depends on the pick. The source uses only the order of $\omega_w$, the support of $\omega$ and the triviality of $\omega_w$ on $q_1$-th roots of unity. A textbook would say "fix a character $T_w$ of order $q_2^2$".

By [fields, places and twists](/chapter/fields-places-twists/), $\omega_w$ has order $q_2$ at a chosen place, and $\omega_w(x) = 1$ when $x^{q_1} = 1$. The order is $q_2^2/\gcd(q_2^2, q_2) = q_2$.

**Lemma.** Let $\psi$ be a family of characters $\psi_w$ of the residue fields, let $n \in \mathbb{Z}$, and let $w$ be a finite place with $\psi_w = 1$. Then $(\omega^n\psi)_w^{\,q_2} = 1$.

Lean: `New.Data.chiMLocal_zpow_mul_pow_eq_one` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* $(\omega^n\psi)_w = \omega_w^n$. At a chosen place $\omega_w$ has order $q_2$, so $\omega_w^{n q_2} = 1$. At another place $\omega_w = 1$. $\square$

### The characters $\chi_0$ and $\chi_M$

The characters $\chi_0$ and $\chi_M$ of $U(1)(\mathbb{A}_E)$ are defined in [fields, places and twists](/chapter/fields-places-twists/), from an existence theorem for characters of a given weight and tame part. We recall the notion in one line. A character $\mu$ has weight $e$ and tame part $\psi$ if almost all $\psi_w$ are trivial and $\mu(u) = \prod_v u_v^{e(v)} \prod_w \psi_w(u \bmod w)$ for every $u$ with integral finite part. The weight of the lift at level $0$ is $w_0(v) = \kappa(v) + \Delta/2$.

**Lemma.**

1. $\chi_0$ has weight $v \mapsto -w_0(v)$ and trivial tame part.
2. $\chi_M$ has weight $0$ and tame part $\omega$.

Lean: `New.Data.chiZero_hasWeight`, `New.Data.chiM_hasWeight` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* The characters are defined as the objects picked by `choose` from `New.Data.exists_char_hasWeight` with $(a, n) = (1, 0)$ and $(a, n) = (0, 1)$. That theorem gives a character of weight $-a\,w_0$ and tame part $\omega^n$. For $n = 0$ the tame part is $\omega^0 = 1$, and for $a = 0$ the weight is $0$. $\square$

**Remark (Formalization).** Both $\chi_0$ and $\chi_M$ are picked with `choose`. Two characters with the same weight and tame part differ by a character of weight $0$ and trivial tame part, and there are finitely many of these (Lean: `New.AutChar.finite_setOf_hasWeight`), but they need not be trivial. So $\chi_0$ and $\chi_M$ are fixed only up to such a character. The source uses only the two lemmas above.

The existence theorem needs that the formula $\prod_v u_v^{e(v)}\prod_w\psi_w(u \bmod w)$ gives $1$ on every integral $\gamma \in E$ with $\gamma\bar\gamma = 1$. Such a $\gamma$ is a root of unity, so a power of $\zeta$. At the infinite places the product is a norm from $E$ to $K$ of a power of $\zeta$, which is $1$, as $w_0 \equiv \Delta/2 \bmod q_1$ at every place. At a finite place $\gamma \bmod w$ is a $q_1$-th root of unity, so $\omega_w$ is $1$ on it. These steps are proved in [fields, places and twists](/chapter/fields-places-twists/).

### Finiteness of pairs

A pair for the data is a character $\nu$ of $U(1)(\mathbb{A}_E)$ of weight $-c$ and tame part $\psi$, with $\psi_w = 1$ off the chosen places, together with an integer $z$ with $1 \le z \le t$ and $z \le c(v) \le 4b$ for every $v \in \Phi$. The structure `New.Data.CriticalPair` is stated in [twists and critical pairs](/chapter/twists-critical-pairs/), which uses the pairs in Theorem C.

**Theorem (Finiteness of pairs).** There are finitely many pairs.

Lean: `New.Data.finite_criticalPair` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Let $S$ be the finite set of chosen places. Send a pair to the triple $(c, z, \psi|_S)$. The function $c$ takes values in $\{0, \ldots, \lfloor 4b\rfloor\}$ on the finite set $\Phi$, the integer $z$ is in $[1, t]$, and $\psi|_S$ is a family of characters of the finite groups $\mathbb{F}_w^\times$ for $w \in S$. So the triples lie in a finite set. Two pairs with the same triple have the same $\psi$, since $\psi_w = 1$ off $S$ for both. So the pairs over a given triple have characters in the set of characters of weight $-c$ and tame part $\psi$, which is finite by `New.AutChar.finite_setOf_hasWeight`. A pair is fixed by its character and its triple, since the other fields are proofs. So each fiber is finite, and so is the set of pairs. $\square$

**Remark (Formalization).** The file uses `attribute [local instance low] Fintype.ofFinite`. It turns every `Finite` type into a `Fintype` by a choice, so that finite sums and products over finite types can be written. This is finding F-026 of the register. Its `Finset.univ` need not be definitionally equal to that of another `Fintype` instance on the same type. The value of a sum or product does not depend on the instance.

### The sizes of $\varpi$ and of $\mathrm{rd}_E$

Section 2 gives $|\varpi|_v = |\delta|_v\sqrt d$ and $\prod_v |\varpi|_v = \mathrm{rd}_E^f$. To bound $|\delta|_v$ one uses that $q_1 = q_0 \cdot \mathrm{towerDeg}(s)$, where every prime of $\mathrm{towerDeg}(s)$ divides $q_0$. Then $\Phi_{q_1}(X) = \Phi_{q_0}(X^{\mathrm{towerDeg}(s)})$ (Lean: `New.Parameters.expand_towerDeg_cyclotomic`).

**Lemma.** For every $v \in \Phi$ there is $A > 0$ with $|\log A| \le C_P$ and
$$|\varpi|_v = A \cdot \mathrm{towerDeg}(s) \cdot \sqrt d.$$

Lean: `New.Parameters.exists_abs_log_le_and_apply_deltaE_eq` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Let $T = \mathrm{towerDeg}(s)$, let $\zeta_v = \Phi_v(\zeta)$, and let $\xi = \zeta_v^T$, a primitive $q_0$-th root of unity. By the chain rule,
$$\Phi_{q_1}'(\zeta_v) = \Phi_{q_0}'(\xi) \cdot T\zeta_v^{T-1}.$$
As $|\zeta_v| = 1$, $|\delta|_v = A \cdot T$ with $A = |\Phi_{q_0}'(\xi)|$. Then $A > 0$, since $\delta \ne 0$. The number $|\log A|$ is one term of the sum $\sum_w |\log|\Phi_{q_0}'(w)||$ over the primitive $q_0$-th roots of unity, which is a term of $C_P$; the other terms of $C_P$ are at least $0$. Last, $|\varpi|_v = |\delta|_v\sqrt d$. $\square$

**Theorem.** For every $v \in \Phi$, $|\log|\varpi|_v - \log\mathrm{rd}_E| \le 2C_P$.

Lean: `New.Parameters.abs_log_deltaE_sub_log_rootDiscr_le` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Let $Q = \log(T\sqrt d)$. By the lemma, $|\log|\varpi|_w - Q| \le C_P$ for every $w \in \Phi$. As $\mathrm{rd}_E^f = \prod_w |\varpi|_w$, the number $\log\mathrm{rd}_E$ is the mean of the numbers $\log|\varpi|_w$. So $|\log \mathrm{rd}_E - Q| \le C_P$. The triangle inequality gives the claim. $\square$

**Theorem (Sizes at infinity).** For every $v \in \Phi$, $x^{10} \le |\varpi|_v \le x^{12}$, and $x^{10} \le \mathrm{rd}_E \le x^{12}$.

Lean: `New.Data.hasLogBound_deltaE`, `New.Data.hasLogBound_rootDisc` (New/Derivatives/Field/ChosenPlaces.lean). The bound for $\mathrm{rd}_E$ as an interval is `New.Data.rootDisc_mem_Icc`, stated in [data and sizes](/chapter/data-and-sizes/).

*Proof.* By the lemma, $\log|\varpi|_v = \log A + \log T + \tfrac12\log d$. The table of [data and sizes](/chapter/data-and-sizes/) gives $x^{11} \le T \le x^{11}(\log b)^{1/5}$. The terms $|\log A| \le C_P$ and $\tfrac12 \log d \le \tfrac12\log C_P$ are small against $\log x$, and so is $\tfrac15\log\log b$, by the scale inequalities of the data. So $10\log x \le \log|\varpi|_v \le 12\log x$. For $\mathrm{rd}_E$, take the product over the $f$ places: $x^{10f} \le \mathrm{rd}_E^f \le x^{12f}$, and take $f$-th roots. $\square$

**Remark (Formalization).** The two bounds are instances of the class `New.Data.HasLogBound` of [data and sizes](/chapter/data-and-sizes/). For $u$ true it says $|F| \le \exp(l)$, and for $u$ false it says $\exp(l) \le F$. The source writes the exponent as $(\text{if } u \text{ then } 12 \text{ else } 10) \cdot \log x$, so that one instance gives both bounds. As instances, the bounds are found by instance search when later chapters bound products of sizes. The proof of the bound for $|\varpi|_v$ is found in the same way, factor by factor, and the final comparison of exponents is done by the tactic `grind` with the scale inequalities.

The bounds are far from sharp. The theorem above shows that $|\varpi|_v$ and $\mathrm{rd}_E$ differ by a factor at most $e^{2C_P}$, which does not depend on $x$.

**Example.** In the model of Section 1, $q_0$ plays no role, but the computation is the same with $q_1 = 12 = 6 \cdot 2$, in the place of $q_0$ the number $6$, $T = 2$, and the cyclotomic polynomial $\Phi_6(X) = X^2 - X + 1$. Then $\Phi_{12}(X) = \Phi_6(X^2)$, and $\Phi_{12}'(\zeta) = \Phi_6'(\zeta^2) \cdot 2\zeta = (2\zeta^2 - 1) \cdot 2\zeta$, as in Section 1. Here $A = |2\zeta^2 - 1| = \sqrt 3$, so $|\delta|_v = 2\sqrt3$ and $|\varpi|_v = 2\sqrt3\sqrt{23} = \mathrm{rd}_E$ at every place.
