---
title: Moduli and ratios of Hecke values
lean:
  - New/Determinant/Chain/Moduli.lean
decls:
  - New.Data.card_residueRing_twistModulus
  - New.Data.lRatioProd
  - New.Data.lRatioProd_nonneg
  - New.Data.CriticalPair.ofReal_lRatioProd
  - New.Data.CriticalPair.L_inv
  - New.Data.CriticalPair.L_mul_inv
  - New.Data.CriticalPair.lRatioProd_eq_prod_norm_div
  - New.Data.CriticalPair.lValueProd_mul_inv_eq
  - New.Data.CriticalPair.lRatioProd_one_pow
  - New.Data.HasAbsUpToNormPower
  - New.Data.HasAbsUpToNormPower.mul
  - New.Data.HasAbsUpToNormPower.prod
  - New.Data.HasAbsUpToNormPower.inv
  - New.Data.HasAbsUpToNormPower.const
  - New.Data.HasAbsUpToNormPower.of_norm_sq_eq_mul_card_zpow
  - New.Data.HasAbsUpToNormPower.exists_norm_div_eq
  - New.Data.CriticalPair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd
  - New.Data.IsRamifiedRatio
  - New.Data.IsRamifiedRatio.nonneg
  - New.Data.IsRamifiedRatio.apply_one
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod
  - New.Data.quotientPair
  - New.Data.quotientPair_character
  - New.Data.quotientRatio
  - New.Data.isRamifiedRatio_quotientRatio
  - New.Data.isPrimitiveMulChar_of_isTameFor
  - New.Data.CriticalPair.isTameFor_mul_and_lValueProd_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Moduli and ratios of Hecke values

The constants of the squares of the triangle are not computed. Only their absolute values are known, and only up to a constant and a power of $\mathrm{Nm}\,Q$. This section defines this kind of knowledge, the relation $M$ of Section 2, and proves the facts about products of ratios of Hecke values that the theorem on the norm of the chain needs.

We use the critical pairs $p = (\nu, z)$, their ratios and their lower points $p_{\downarrow z'}$ from [twists, critical pairs and regular families](/chapter/twists-critical-pairs/). Write $S$ for the set of chosen places, $\varpi$ for the product of the chosen places, and $\mathfrak{m} = \varpi^e Q$ for the modulus `twistModulus` of a tame character $\vartheta$ with $e \in \mathbb{N}$. Write $L_*(S', \chi, z)$ for the product of $L$-values of [products of L-values of a twist](/chapter/twists-critical-pairs/), `lValueProd`.

**Lemma (Order of the residue ring).** For $e \in \mathbb{N}$ and a tame character $\vartheta$,
$$\#(O_E/\varpi^e Q) = \Big(\prod_{w \in S} q_w\Big)^e\,\mathrm{Nm}\,Q.$$

Lean: `New.Data.card_residueRing_twistModulus` (New/Determinant/Chain/Moduli.lean).

*Proof.* The modulus is a product of powers of distinct primes, so the residue ring is the product of the local residue rings, by the Chinese remainder theorem. The factor at a chosen place $w$ has $q_w^e$ elements, and the factor at a place of $Q$ has $q_w$ elements. The product of the $q_w$ over $Q$ is $\mathrm{Nm}\,Q$. $\square$

### The product of ratios

**Definition (Product of ratios).** For a character $\nu$ of $U(1)(\mathbb{A}_E)$, $s \in \mathbb{N}$ and a tame character $\vartheta$ with modulus $Q$,
$$\Lambda(\nu, s, \vartheta) = \prod_{z=1}^{s}\frac{|L^{S \cup Q}(z, (\nu\vartheta)^{-1})|}{|L^{S}(z, \nu^{-1})|}.$$

Lean: `New.Data.lRatioProd` (New/Determinant/Chain/Moduli.lean).

**Lemma (Basic properties).** $\Lambda(\nu, s, \vartheta) \geq 0$. For a critical pair $p = (\nu, z)$, $\Lambda(\nu, z, \vartheta) = \prod_{z'=1}^{z}\mathrm{ratio}(p_{\downarrow z'}, \vartheta)$.

Lean: `New.Data.lRatioProd_nonneg`, `New.Data.CriticalPair.ofReal_lRatioProd` (New/Determinant/Chain/Moduli.lean).

*Proof.* Each factor is a quotient of absolute values. For $1 \leq z' \leq z$ the lower point $p_{\downarrow z'}$ has the point $z'$, and its ratio with the sign $1$ is the factor at $z'$. $\square$

The next two lemmas remove the inverses in the definition. They cite one result of [critical pairs and the ratio](/chapter/twists-critical-pairs/): if a character $\nu$ of weight $e$ has a tame part $\psi$ with $\psi_v = 1$ for $v \notin S'$, then $L^{S'}(\cdot, \nu^{-1}) = L^{S'}(\cdot, \nu)$ (`New.AutChar.HasWeight.L_inv`).

**Lemma (Inverse of a pair).** For a critical pair $p = (\nu, z)$, $L^S(\cdot, \nu^{-1}) = L^S(\cdot, \nu)$. For a tame character $\vartheta$ with modulus $Q$, $L^{S \cup Q}(\cdot, (\nu\vartheta)^{-1}) = L^{S \cup Q}(\cdot, \nu\vartheta)$.

Lean: `New.Data.CriticalPair.L_inv`, `New.Data.CriticalPair.L_mul_inv` (New/Determinant/Chain/Moduli.lean).

*Proof.* The tame part $\psi$ of a critical pair has $\psi_w = 1$ at every place that is not chosen. So the cited result applies with $S' = S$. The product $\nu\vartheta$ has the weight of $\nu$ plus the weight of $\vartheta$, and its tame part is the product of the tame parts. At a place $w \notin S \cup Q$ both tame parts are $1$. So the cited result applies with $S' = S \cup Q$. $\square$

**Corollary (Without inverses).** For a critical pair $p = (\nu, z)$, $s \in \mathbb{N}$ and $\vartheta$,
$$\Lambda(\nu, s, \vartheta) = \prod_{i=1}^{s}\left|\frac{L^{S \cup Q}(i, \nu\vartheta)}{L^{S}(i, \nu)}\right|.$$

Lean: `New.Data.CriticalPair.lRatioProd_eq_prod_norm_div` (New/Determinant/Chain/Moduli.lean).

*Proof.* Apply the lemma to each factor, and use $|a/b| = |a|/|b|$. $\square$

**Proposition (The product of $L$-values at a twist).** For a critical pair $p = (\nu, z)$ and a tame character $\vartheta$ with modulus $Q$,
$$L_*\big(S \cup Q, (\nu\vartheta)^{-1}, z\big) = L_*(S, \nu, z)\,(\mathrm{Nm}\,Q)^{z^2}\,\Lambda(\nu, z, \vartheta)^2.$$

Lean: `New.Data.CriticalPair.lValueProd_mul_inv_eq` (New/Determinant/Chain/Moduli.lean).

*Proof.* The factorization of $L_*$ at a twist, from [products of L-values of a twist](/chapter/twists-critical-pairs/) with the sign $1$, gives the left side as $(\mathrm{Nm}\,Q)^{z^2}\,L_*(S, \nu^{-1}, z)\,\prod_{z'=1}^{z}\mathrm{ratio}(p_{\downarrow z'}, \vartheta)^2$. The product of the squared ratios is $\Lambda(\nu, z, \vartheta)^2$ by the basic properties. The lemma on the inverse of a pair gives $L_*(S, \nu^{-1}, z) = L_*(S, \nu, z)$, since $L_*$ depends on the character only through its partial $L$-values. $\square$

**Lemma (The trivial twist).** For a critical pair $p = (\nu, z)$ and every $n \in \mathbb{N}$, $\Lambda(\nu, z, 1^n) = 1$.

Lean: `New.Data.CriticalPair.lRatioProd_one_pow` (New/Determinant/Chain/Moduli.lean).

*Proof.* The power $1^n$ of the trivial twist is the trivial character, with $Q = \emptyset$. So each factor is $|L^S(z', \nu^{-1})|/|L^S(z', \nu^{-1})|$. Its denominator is not zero, since the ratio of the lower point $p_{\downarrow z'}$ is not zero ([critical pairs and the ratio](/chapter/twists-critical-pairs/)). So each factor is $1$. $\square$

### Absolute values up to a norm power

**Definition (Absolute value up to a norm power).** Let $c$ be a complex function and $f$ a real function on the $m$-fold twists. Then $c$ has absolute value $f$ up to a norm power if there are $C \in \mathbb{R}$ and $k \in \mathbb{Z}$ with
$$|c(\vartheta)|^2 = C\,(\mathrm{Nm}\,Q)^k\,f(\vartheta)^2$$
for every $m$-fold twist $\vartheta$ with modulus $Q$.

Lean: `New.Data.HasAbsUpToNormPower` (New/Determinant/Chain/Moduli.lean).

**Remark (Formalization).** The constant $C$ may be $0$. Then $c$ vanishes at every twist. The relation alone cannot exclude this case. The theorem on the norm of the chain excludes it at the end, from the injectivity of the chain (Section 6, finding F-071).

This relation is the relation $M(c, f)$ of Section 2 for the triangle of lifts.

**Lemma (Rules).** The relation has these properties.

1. If $c$ has absolute value $f$ and $c'$ has $f'$, then $cc'$ has $ff'$.
2. If $c_a$ has absolute value $F_a$ for each $a$ in a finite set $s$, then $\prod_{a \in s} c_a$ has $\prod_{a \in s} F_a$.
3. If $c$ has absolute value $f$, then $c^{-1}$ has $f^{-1}$.
4. A constant function has absolute value $1$. In particular, $1$ has absolute value $1$.
5. If $|c(\vartheta)|^2 = C\,\#(O_E/\varpi^e Q)^k$ for all $\vartheta$, with $e \in \mathbb{N}$, $C \in \mathbb{R}$ and $k \in \mathbb{Z}$ independent of $\vartheta$, then $c$ has absolute value $1$.

Lean: `New.Data.HasAbsUpToNormPower.mul`, `New.Data.HasAbsUpToNormPower.prod`, `New.Data.HasAbsUpToNormPower.inv`, `New.Data.HasAbsUpToNormPower.const`, `New.Data.HasAbsUpToNormPower.of_norm_sq_eq_mul_card_zpow` (New/Determinant/Chain/Moduli.lean).

*Proof.* 1. Take $CC'$ and $k + k'$. Since $\mathrm{Nm}\,Q \neq 0$, $(\mathrm{Nm}\,Q)^{k}(\mathrm{Nm}\,Q)^{k'} = (\mathrm{Nm}\,Q)^{k+k'}$. 2. Induction on $s$, from rule 4 for the empty set and rule 1. 3. Take $C^{-1}$ and $-k$. 4. Take $|a|^2$ and $0$. 5. By the lemma on the order of the residue ring, take $C\,\big((\prod_{w \in S} q_w)^e\big)^k$ and $k$. $\square$

Rule 3 uses $0^{-1} = 0$ where $C = 0$ or $f(\vartheta) = 0$. Both sides are then $0$.

**Proposition (Division by the trivial twist).** Let $c$ have absolute value $f$ up to a norm power, with $f \geq 0$, $f(1) = 1$ and $c(1) \neq 0$. Then there is $e \in \mathbb{Z}$ with
$$\left|\frac{c(\vartheta)}{c(1)}\right| = (\mathrm{Nm}\,Q)^{e/2}\,f(\vartheta)$$
for every $m$-fold twist $\vartheta$.

Lean: `New.Data.HasAbsUpToNormPower.exists_norm_div_eq` (New/Determinant/Chain/Moduli.lean).

*Proof.* Let $C$ and $k$ be as in the definition. At $\vartheta = 1$ we have $Q = \emptyset$, so $|c(1)|^2 = C$. Take $e = k$. Both sides of the claim are nonnegative, so it suffices to compare squares. The square of the left side is $C\,(\mathrm{Nm}\,Q)^k f(\vartheta)^2 / C$. The square of the right side is $(\mathrm{Nm}\,Q)^k f(\vartheta)^2$, since $\big((\mathrm{Nm}\,Q)^{k/2}\big)^2 = (\mathrm{Nm}\,Q)^k$ for the real power of a positive number. $\square$

**Proposition (Products of $L$-values have absolute value a product of ratios).** Let $p = (\nu, z)$ be a critical pair, $e \neq 0$, $n \in \mathbb{N}$ and $C \in \mathbb{R}$. Let $c$ satisfy
$$|c(\vartheta)|^2 = C\,L_*\big(\text{places of } \varpi^e Q, (\nu\vartheta^n)^{-1}, z\big)$$
for every $m$-fold twist $\vartheta$. Then $c$ has absolute value $\vartheta \mapsto \Lambda(\nu, z, \vartheta^n)$ up to a norm power.

Lean: `New.Data.CriticalPair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd` (New/Determinant/Chain/Moduli.lean).

*Proof.* For $e \neq 0$ the places of $\varpi^e Q$ are $S \cup Q$, and $\vartheta^n$ has the modulus $Q$. The proposition on the product of $L$-values at a twist, for $\vartheta^n$, gives $|c(\vartheta)|^2 = C\,L_*(S, \nu, z)\,(\mathrm{Nm}\,Q)^{z^2}\,\Lambda(\nu, z, \vartheta^n)^2$. Take the constant $C\,L_*(S, \nu, z)$ and $k = z^2$. $\square$

### Ramified ratios and their heights

**Definition (Ramified ratio).** A real function $F$ on the $m$-fold twists is a ramified ratio if there are a ramified critical pair $p = (\nu, z)$ and $1 \leq n \leq m$ with $F(\vartheta) = \Lambda(\nu, z, \vartheta^n)$ for every $\vartheta$.

Lean: `New.Data.IsRamifiedRatio` (New/Determinant/Chain/Moduli.lean).

**Lemma (Ramified ratios at the trivial twist).** A ramified ratio $F$ has $F \geq 0$ and $F(1) = 1$.

Lean: `New.Data.IsRamifiedRatio.nonneg`, `New.Data.IsRamifiedRatio.apply_one` (New/Determinant/Chain/Moduli.lean).

*Proof.* The basic properties and the lemma on the trivial twist. $\square$

**Theorem (Heights of products of ratios).** Let $\theta$ be a family of $m$-fold twists with small ratios, $e \in \mathbb{Z}$, and $F_a$ a ramified ratio for each $a$ in a finite set $s$. Then the family
$$\iota \longmapsto \Big((\mathrm{Nm}\,Q_{\theta(\iota)})^{e/2}\prod_{a \in s}F_a(\theta(\iota))\Big)^{-1}$$
has height at most $\#s \cdot t \cdot x_1$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod` (New/Determinant/Chain/Moduli.lean).

*Proof.* Heights are those of [twisted lattices](/chapter/twisted-lattices/). Fix $a \in s$ with the pair $p = (\nu, z)$ and the power $n$. By the basic properties, $F_a(\vartheta)^{-1} = \prod_{z'=1}^{z}\mathrm{ratio}(p_{\downarrow z'}, \vartheta^n)^{-1}$. Each lower point of a ramified pair is ramified, since it has the same tame part. The condition of small ratios bounds the height of $\iota \mapsto \mathrm{ratio}(p_{\downarrow z'}, \theta(\iota)^n)^{-1}$ by $x_1$. Heights add under products, so the inverse of $F_a$ has height at most $z\,x_1 \leq t\,x_1$, as $z \leq t$ for a critical pair. The product over $s$ has height at most $\#s \cdot t \cdot x_1$. Last, $\mathrm{Nm}\,Q_{\theta(\iota)}$ is prime to the prime of $\iota$, by the first condition of small ratios. So the lemma on powers of units of [products of L-values of a twist](/chapter/twists-critical-pairs/) multiplies the family by $(\mathrm{Nm}\,Q_{\theta(\iota)})^{-e/2}$ and keeps the bound. $\square$

### The quotient ratios

The characters of the lifts at the trivial twist are $\mu_j = \chi_0\,(\upsilon^{-\Delta}\chi_M)^j$, a geometric progression (`New.Data.untwistedLiftChar`). Here $\upsilon$ is the fixed splitting character on the norm one ideles, $\Delta$ is the gap of the data, and $\chi_M$ has weight $0$ and the tame part $\omega$ of the data.

**Definition (Quotient pair).** For $1 \leq n \leq m$ the quotient pair is the critical pair with the character $(\upsilon^{-\Delta}\chi_M)^n$, the weight $-n\Delta$ at every infinite place, the tame part $\omega^n$ and the point $z = t$.

Lean: `New.Data.quotientPair` (New/Determinant/Chain/Moduli.lean).

The conditions of a critical pair hold: $t \leq \Delta \leq n\Delta$ and $n\Delta \leq m\Delta \leq 4b$ by the sizes of the data. The tame part $\omega^n$ is $\neq 1$ exactly at the chosen places, for $1 \leq n \leq m$ (`New.Data.isRamified_quotientPair`). So the quotient pair is ramified.

**Lemma (The quotient pair is a quotient).** For $1 \leq n \leq m$ and every $i$, the character of the quotient pair is $\mu_{i+n}/\mu_i$.

Lean: `New.Data.quotientPair_character` (New/Determinant/Chain/Moduli.lean).

*Proof.* $\mu_{i+n}/\mu_i = (\upsilon^{-\Delta}\chi_M)^{i+n}/(\upsilon^{-\Delta}\chi_M)^i$, and the factor $\chi_0$ cancels. $\square$

**Definition (Quotient ratio).** For $i, j \in \mathbb{N}$ and an $m$-fold twist $\vartheta$, $\rho_{ij}(\vartheta) = \Lambda(\mu_j/\mu_i, t, \vartheta^{j-i})$, with the truncated difference $j - i$.

Lean: `New.Data.quotientRatio` (New/Determinant/Chain/Moduli.lean).

**Proposition (Quotient ratios are ramified ratios).** For $i < j \leq m$, $\rho_{ij}$ is a ramified ratio, with the quotient pair for $n = j - i$.

Lean: `New.Data.isRamifiedRatio_quotientRatio` (New/Determinant/Chain/Moduli.lean).

*Proof.* Write $j = i + n$ with $1 \leq n \leq j \leq m$. By the last lemma $\rho_{ij}(\vartheta) = \Lambda(\text{character of the quotient pair}, t, \vartheta^n)$, and the quotient pair is ramified. $\square$

### Two facts for the commutation relations

Section 5 uses Gauss sums modulo $\varpi Q$ and the tameness of the characters in the squares. A character $\nu$ is tame for $(\mathfrak{m}, \gamma, \chi)$ if it has weight $\gamma$ and a tame part $(\psi_w)$ with $\psi_w \neq 1$ exactly at the places $w \mid \mathfrak{m}$, and $\chi = \prod_{w \mid \mathfrak{m}}\psi_w$ on $O_E/\mathfrak{m}$ ([the exchange identity, part 2](/chapter/exchange-identity-2/)). A character $\chi$ of a finite ring is primitive if for every $a \neq 0$ some $c$ has $\chi(1 + ca) \notin \{0, 1\}$.

**Lemma (Tame characters are primitive).** If $\nu$ is tame for $(\varpi Q, \gamma, \chi)$, then $\chi$ is primitive.

Lean: `New.Data.isPrimitiveMulChar_of_isTameFor` (New/Determinant/Chain/Moduli.lean).

*Proof.* Let $a \neq 0$ in $O_E/\varpi Q$. The modulus is a product of distinct primes, so by the Chinese remainder theorem the residue of $a$ at some place $w \mid \varpi Q$ is not $0$. Since $\psi_w \neq 1$, there is a unit $x$ of the residue field at $w$ with $\psi_w(x) \neq 1$. Take $b$ with residue $(x - 1)/a$ at $w$, and let $c$ be $b$ times the idempotent that is $1$ at $w$ and $0$ at the other places. Then $1 + ca$ has the residue $x$ at $w$ and $1$ at the other places. So $\chi(1 + ca) = \psi_w(x)$, which is neither $0$ nor $1$. $\square$

**Proposition (Tame twists of a pair).** Let $p = (\nu, z)$ be a ramified critical pair of weight $-c_p$, $\xi$ a twist with modulus $Q$ and $e \neq 0$. Then $\nu\xi$ is tame for $\varpi^e Q$ with weight $-c_p$, and $(\nu\xi)^{-1}$ is tame for $\varpi^e Q$ with weight $c_p$. For both signs $\epsilon = \pm 1$,
$$L_*\big(\text{places of }\varpi^e Q, (\nu\xi)^{\epsilon}, z\big) = L_*(S, \nu, z)\,(\mathrm{Nm}\,Q)^{z^2}\,\Lambda(\nu, z, \xi)^2.$$

Lean: `New.Data.CriticalPair.isTameFor_mul_and_lValueProd_eq` (New/Determinant/Chain/Moduli.lean).

*Proof.* The tame part of $\nu\xi$ is $\psi_p\psi_\xi$. It is $\neq 1$ at the chosen places, where $\psi_p \neq 1$ and $\psi_\xi = 1$, and at the places of $Q$, where $\psi_\xi \neq 1$ and $\psi_p = 1$. It is $1$ elsewhere. This gives the tameness of $\nu\xi$, and the inverse is tame with the inverse character and the opposite weight. For $\epsilon = -1$ the formula is the proposition on the product of $L$-values at a twist. For $\epsilon = 1$, the lemma on the inverse of a pair replaces $L^{S\cup Q}(\cdot, \nu\xi)$ by $L^{S \cup Q}(\cdot, (\nu\xi)^{-1})$. $\square$

The source also states the tameness of $(\nu\vartheta^n)^{-1}$ for $1 \leq n \leq m$ separately (`New.Data.CriticalPair.isTameFor_inv_mul_pow`). It is the proposition for the twist $\vartheta^n$.
