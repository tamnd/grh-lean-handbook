---
title: Heights of inverse ratios
lean:
  - New/OneLift/HeckeValues/TwistedValueHeights.lean
decls:
  - New.Data.heightLe_inv_ratio
  - New.Data.isMainPair_lowerPoint_exchangePair_none
  - New.Data.isRamified_lowerPoint_exchangePair
  - New.Data.heckeValueProd_eq_mul_prod_ratio_sq
  - New.Data.exists_heckeValueProd_eq_mul_prod_ratio
  - New.Data.heightLe_inv_heckeValueProd_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Heights of inverse ratios

This section proves the two height bounds of the chapter. The first is the theorem that [regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists) states and leaves to this chapter: at a main pair the inverse ratios have height at most $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$. The second bounds the inverse quotient of the Hecke values $\Gamma_j(\vartheta)/\Gamma_j(1)$ of the three exchanges.

Throughout, $\theta$ is a regular family of $m$-fold twists, one for each $\iota = (\ell, \iota)$ with $\iota : \mathbb{C} \simeq \bar{\mathbb{Q}}_\ell$, and $\vartheta_\iota = \theta(\iota)^j$. Heights are those of [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers): a family $y$ has height at most $c$ if some $H \neq 0$ has $|\sigma H| \leq e^\alpha$ for all $\sigma$ and $|\iota(H y_\iota)| \leq \ell^{h(\ell)}$ for all $\iota$, with $\alpha + \sum_{\ell\in T}h(\ell)\log\ell \leq c$ for every finite set $T$ of primes. Heights add under products (`HeightLe.mul`, `HeightLe.prod`, `HeightLe.pow`).

Recall the sizes ([the data and its sizes](/chapter/data-and-sizes/)): $\mathrm{denominatorBudget} = fa\log^3 b/(mk)$ and
$$\mathrm{directionAmount} = \sum_\tau\big(\mathrm{jetSize}(\kappa_\tau) - \mathrm{primeSum}(\kappa_\tau, \tau)\big).$$

### The inverse ratio at a main pair

**Theorem (Height of the inverse ratio).** Let $\theta$ be regular, $j \in [1, m]$ and $p$ a main pair for $j$. The family $\iota \mapsto \mathrm{ratio}(p, \vartheta_\iota)^{-1}$ has height at most $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$.

Lean: `New.Data.heightLe_inv_ratio` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Step 1 (a ramified flat pair). By the lemma on flat pairs of Section 5, applied on four indices to the character $(\chi_M, \omega)$ of weight $0$, there is a flat pair $q_2$ with tame part $\omega = $ `D.chiMLocal`. It is ramified, since $\omega$ is nontrivial exactly at the chosen places. Write $\rho_\iota = \mathrm{ratio}(q_2, \vartheta_\iota)$; it is nonzero and real.

Step 2 (the constant). Take $c_0$ from the theorem on a form with small pairing of Section 6, for $p$ and $q_2$. By the sizes of the data, $fmb/k + 3x^{34} \leq \mathrm{denominatorBudget}$. So $|\sigma c_0| \leq e^{\mathrm{denominatorBudget}}$ for all $\sigma$.

Step 3 (two test forms). Fix $\iota$ with prime $\ell$. The modulus of $\vartheta_\iota$ is prime to $\ell$, since the family has small ratios. Apply Section 6 twice: at the place $\iota$, and at the place $\iota\circ\mathrm{conj}$. This gives test forms $\Xi_\iota$ and $\Xi'_\iota$ with
$$|\iota(c_0\rho_\iota)|\,\ell^{-F(\ell)} \leq |\iota\langle\Xi_\iota, \varphi_\iota\rangle|,\qquad |\iota(\bar c_0\rho_\iota)|\,\ell^{-F(\ell)} \leq |\iota\langle\varphi_\iota, \Xi'_\iota\rangle|,$$
where $\varphi_\iota$ is the lift of $\nu\vartheta_\iota$ and $\rho_\iota$ is real (`star_ratio`). Multiply:
$$|\iota(c_0\bar c_0\rho_\iota^2)|\,\ell^{-2F(\ell)} \leq |\iota(\langle\Xi_\iota, \varphi_\iota\rangle\langle\varphi_\iota, \Xi'_\iota\rangle)|.$$
In particular the product of pairings $P_\iota$ is nonzero.

Step 4 (four factors). Let $\mathrm{pr}$ be the projection to the line $\mathbb{C}\varphi_\iota$. Then $\langle\mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle = P_\iota/\|\varphi_\iota\|^2$. By the formula $\mathrm{ratio} = \mathrm{algPart}(\vartheta)/\mathrm{algPart}(1)$ with $\mathrm{algPart}(\vartheta) = \|\varphi_\vartheta\|^2/\mathrm{Nm}\,Q^{2z-1}$ ([the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part)),
$$\mathrm{ratio}(p, \vartheta_\iota)^{-1} = \mathrm{Nm}\,Q^{2z-1}\cdot\|\varphi_1\|^2\cdot\langle\mathrm{pr}\,\Xi_\iota, \mathrm{pr}\,\Xi'_\iota\rangle\cdot\rho_\iota^{-2}\cdot\frac{\rho_\iota^2}{P_\iota}.$$
The first factor is an integer, so $|\iota(\cdot)| \leq 1$ there and it can be dropped. We bound the heights of the other four.

(a) $\|\varphi_1\|^2$, constant in $\iota$: height at most $\mathrm{denominatorBudget} - \sum_\tau\mathrm{jetSize}(\kappa_\tau)$, by the theorem on the height of the untwisted norm of Section 5.

(b) Projections. The regular family gives a denominator bound $\gamma$ for $j$ with $\sum_{\ell\in T}\gamma(\ell) \leq \mathrm{denominatorBudget}$. Its second condition (`HasDenominatorsLe.mainPair`) says that $|\iota\langle\mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle| \leq e^{\gamma(\ell)}$ for test forms of a main pair; the line of the normalized lift equals the line of $\varphi_\iota$, since they differ by a nonzero scalar. So the height is at most $\mathrm{denominatorBudget}$ (`HeightLe.of_le`).

(c) $\rho_\iota^{-2}$. The family has small ratios and $q_2$ is ramified, so $\rho_\iota^{-1}$ has height at most $x_1$, and its square at most $2x_1$.

(d) $\rho_\iota^2/P_\iota$. Use the multiplier criterion `HeightLe.of_mul_le` with $H = c_0\bar c_0$, $\alpha = 2\cdot\mathrm{denominatorBudget}$ and $e(\ell) = 2F(\ell)\log\ell$. The archimedean bound is Step 2, for $\sigma$ and for $\sigma\circ\mathrm{conj}$. The bound at $\iota$ is Step 3, rewritten as $|\iota(H\rho^2/P)| \leq e^{2F(\ell)\log\ell}$. The sum $\sum_{\ell\in T}2F(\ell)\log\ell$ is at most $\sum_\tau\mathrm{primeSum}(\kappa_\tau, \tau)$ for every finite set $T$ of primes (`sum_localPrimeSumTotal_mul_log_le`, [the archimedean size](/chapter/archimedean-size/)). So the height is at most $2\cdot\mathrm{denominatorBudget} + \sum_\tau\mathrm{primeSum}(\kappa_\tau, \tau)$.

Step 5 (adding). The heights add to
$$4\cdot\mathrm{denominatorBudget} + 2x_1 - \sum_\tau\mathrm{jetSize}(\kappa_\tau) + \sum_\tau\mathrm{primeSum}(\kappa_\tau, \tau).$$
Since $x_1 \leq \mathrm{denominatorBudget}$ by the sizes of the data, this is at most $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$. $\square$

The proof has the shape of the model case of [the plan](/chapter/theorem-c-plan/#the-model-case). The lower bound for $\|\varphi_\vartheta\|^2$ at $\iota$ comes from a congruence: if $\|\varphi_\vartheta\|^2$ were very divisible at $\ell$, the pairings with integral test forms would be too, against the explicit nonvanishing of Section 6. The test forms must be orthogonal to the false lifts so that the projection bound (b) applies.

**Remark (Formalization).** The test forms $\Xi_\iota, \Xi'_\iota$ are obtained by `choose` from Section 6, and the denominator bound $\gamma$ by `obtain`. Only the stated properties are used. The second test form uses the place $\iota\circ\mathrm{conj}$, so that the conjugate pairing $\langle\varphi, \Xi'\rangle$ gets the bound with $\bar c_0$.

### The Hecke values of the three exchanges

This part uses the third forward result, from [the comparison operator, part 2](/chapter/comparison-operator-2/). We state the definitions once.

**Definition (Pairs of the three exchanges; forward).** Let $j \in [1, m]$, $k = r + 1 - m$, $t = 5r$ and $n_j = j + (t - 11m - 1)/2$. The pair `exchangePair j none` has character $\mu^0_j\upsilon^{n_j}$, of weight $-(w_j - n_j)$, tame part $\omega^j$ and point $z_* = 7(m/2) + k/2$. For a sign $s$, the pair `exchangePair j (some s)` has character $\upsilon^{-z_s}\chi_M^{sj}$, constant weight $-z_s$, tame part $\omega^{sj}$ and point $z_s$, with $z_1 = m$ and $z_{-1} = m/2$. The Hecke value $\Gamma_j(\vartheta)$ = `heckeValueProd j ϑ` is the product over the three pairs $(\nu_i, z_i)$ of
$$\prod_{w\in S}q_w^{z_i^2}\prod_{1\leq z\leq z_i}|L^S(z, (\nu_i\vartheta^{s_i})^{-1})|^2,$$
where $S$ is the set of chosen places and places of $Q$, and $s_i = 1$ for $i = $ none.

Lean: `New.Data.exchangePair`, `New.Data.mainPairPoint`, `New.Data.signPoint`, `New.Data.heckeValueProd` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

For a pair $p$ and $z$, the pair $p.\mathrm{lowerPoint}(z)$ has the character of $p$ and the point $\max(1, \min(z, z_p))$ ([products of L-values of a twist](/chapter/twists-critical-pairs/#products-of-l-values-of-a-twist)).

**Lemma (Main pairs of the third exchange).** For $7(m/2) < z \leq z_*$, the pair $(\nu_j, z)$ = `(exchangePair j none).lowerPoint z` is a main pair for $j$.

Lean: `New.Data.isMainPair_lowerPoint_exchangePair_none` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* We check the conditions of a main pair. The point is $z$. Since $m \geq 10000$ and $100m \leq k$, $m < z \leq z_* \leq r$ and $2 \leq z$, so the pair has lift rank on $2z$ indices. The tame part is $\omega^j$. The weight is $c = w_j - n_j \leq w_j$. Finally $w_j + r \leq c + t$ means $n_j \leq t - r = 4r$, which holds since $n_j \leq m + 5r/2$. $\square$

**Lemma (Ramified pairs).** For every $i$ and $z$, `(exchangePair j i).lowerPoint z` is ramified.

Lean: `New.Data.isRamified_lowerPoint_exchangePair` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The tame part is $\omega^{\pm j}$ with $1 \leq j \leq m$. It is nontrivial exactly at the chosen places (`chiMLocal_zpow_ne_one_iff_isChosen`). $\square$

**Lemma (The Hecke value as a product of ratios).**
$$\Gamma_j(\vartheta) = \mathrm{Nm}\,Q^{\sum_i z_i^2}\Big(\prod_i\prod_{1\leq z\leq z_i}\mathrm{ratio}\big((\nu_i, z), \vartheta, s_i\big)\Big)^2\,\Gamma_j(1).$$

Lean: `New.Data.heckeValueProd_eq_mul_prod_ratio_sq` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* For each pair, `lValueProd_eq_mul_prod_ratio_sq` of [products of L-values of a twist](/chapter/twists-critical-pairs/#products-of-l-values-of-a-twist) writes its factor as $\mathrm{Nm}\,Q^{z_i^2}$ times the untwisted factor times the squared ratios. At $\vartheta = 1$ the set $Q$ is empty, so $\Gamma_j(1)$ is the product of the untwisted factors. Multiply over $i$. $\square$

**Theorem (Main and ramified factors).** There are $e \in \mathbb{N}$, finite sets $A$ and $B$ with $2\#A = k$ and $\#B = 5m$, main pairs $p_a$ for $j$ ($a \in A$), ramified pairs $q_b$ and signs $s_b$, none depending on $\vartheta$, with
$$\Gamma_j(\vartheta) = \mathrm{Nm}\,Q^e\Big(\prod_{a\in A}\mathrm{ratio}(p_a, \vartheta)\prod_{b\in B}\mathrm{ratio}(q_b, \vartheta, s_b)\Big)^2\Gamma_j(1)$$
for every twist $\vartheta$.

Lean: `New.Data.exists_heckeValueProd_eq_mul_prod_ratio` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Take $e = \sum_i z_i^2$, $A = (7(m/2), z_*]$ with $p_a = (\nu_j, a)$, and $B$ the pairs $(i, z)$ with $0 < z \leq 7(m/2)$ for $i = $ none and $0 < z \leq z_s$ for $i = s$. Then $\#A = k/2$, since $k$ is even. $\#B = 7(m/2) + m + m/2 = 5m$, since $m$ is even. The two lemmas above give the properties. Splitting $[1, z_*]$ at $7(m/2)$ turns the previous lemma into the formula. $\square$

**Theorem (Height of the Hecke values).** Let $\theta$ be regular and $j \in [1, m]$. The family $\iota \mapsto (\Gamma_j(\vartheta_\iota)/\Gamma_j(1))^{-1}$ has height at most
$$10\,m\,x_1 + k\,\big(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}\big).$$

Lean: `New.Data.heightLe_inv_heckeValueProd_div` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Take the data of the previous theorem. By the theorem on the inverse ratio, each $\mathrm{ratio}(p_a, \vartheta_\iota)^{-1}$ has height at most $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$. By small ratios, each $\mathrm{ratio}(q_b, \vartheta_\iota, s_b)^{-1}$ has height at most $x_1$. The square of the product has height at most $2(\tfrac{k}{2}(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}) + 5m\,x_1)$, which is the bound. If $\Gamma_j(1) \neq 0$, the inverse quotient is this square times $\mathrm{Nm}\,Q^{-e}$; the norm of $\theta(\iota)^j$ is that of $\theta(\iota)$. If the quotient is $0$, so is its inverse. Powers of a norm prime to $\ell$ do not change the height (`IsRegularFamily.heightLe_of_eq_zpow_mul`, [regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists)). $\square$

**Remark (Formalization).** In Lean, $x^{-1}$ and $x/0$ are $0$. So the inverse quotient is $0$ when $\Gamma_j(1) = 0$, and the height bound for the family $0$ holds trivially. The source does not use this case: the $L$-values in $\Gamma_j$ are nonzero by the field `HasWeight.L_ne_zero`. The pair `lowerPoint` clamps the point to $[1, z_p]$ to make the definition total; every use above has $1 \leq z \leq z_p$.
