---
title: The three pairs and the Hecke product
lean:
  - New/OneLift/ComparisonOperator/ThreeExchanges.lean
decls:
  - New.Data.signPoint
  - New.Data.mainPairPoint
  - New.Data.k_add_six_le_t
  - New.Data.signPoint_mem_Icc
  - New.Data.mainPairPoint_mem_Icc
  - New.Data.k_add_t_add_one_le_liftWeight
  - New.Data.liftWeight_le_four_mul_b
  - New.Data.exponent_add_mainPairPoint_le_liftWeight
  - New.Data.chiMLocal_zpow_eq_one_of_not_isChosen
  - New.Data.exchangePair
  - New.Data.heckeValueProd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three pairs and the Hecke product

Each of the three exchanges costs a constant. The modulus of each constant is a product of Hecke $L$-values of one character at the integers $1, \ldots, z$. This section fixes the three pairs $(\nu, z)$ and their product $\Gamma_j(\vartheta)$.

Background in one line each. A *critical pair* $(\nu, z)$ is a character $\nu$ of $U(1)(\mathbb{A}_E)$ of weight $-c$, with tame part trivial off the chosen places, and an integer $1 \leq z \leq t$ with $z \leq c(v) \leq 4b$ for every infinite place $v$ ([critical pairs](/chapter/twists-critical-pairs/#critical-pairs-and-the-ratio)). The product $L_*(S, \chi, e)$ is $(\prod_{w \in S} q_w)^{e^2}\prod_{z=1}^{e}|L^S(z, \chi)|^2$ ([products of L-values](/chapter/twists-critical-pairs/#products-of-l-values-of-a-twist)). The data give $k = r + 1 - m$, $t = 5r$, $m \geq 10000$ and $100m \leq k$ ([the data and its sizes](/chapter/data-and-sizes/)). The character $\chi$ = `New.Data.chiM` has weight $0$, and its tame part $\omega$ is trivial off the chosen places. The weight of the character of the $j$-th lift at $v$ is $w_j(v)$ = `New.Data.liftWeight`, and $\mu_j^0$ = `New.Data.untwistedLiftChar` is the untwisted part of that character. The letter $\upsilon$ is the splitting character `upsilonU1` on $U(1)$.

### The points

**Definition (The points).** For a sign $s$, the point $z_s$ is $m$ if $s = 1$ and $\lfloor m/2\rfloor$ if $s = -1$. The main point is $z_* = 7\lfloor m/2\rfloor + \lfloor k/2\rfloor$.

Lean: `New.Data.signPoint`, `New.Data.mainPairPoint` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

The sign $-1$ belongs to the first exchange, the sign $1$ to the second, and the main point to the third.

**Lemma (The points lie in the range).** We have $k + 6 \leq t$. For each sign $s$, $1 \leq z_s \leq t$, and $1 \leq z_* \leq t$.

Lean: `New.Data.k_add_six_le_t`, `New.Data.signPoint_mem_Icc`, `New.Data.mainPairPoint_mem_Icc` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* The data give $k \leq r$ and $r + 6 \leq t$, so $k + 6 \leq t$. As $m \geq 10000$, $z_s \geq \lfloor m/2\rfloor \geq 1$ and $z_* \geq 1$. Next $z_s \leq m \leq k \leq t$. For the main point, $z_* \leq 7m/2 + k/2$. From $100m \leq k$ we get $7m/2 \leq k/2$, so $z_* \leq k \leq t$. $\square$

**Lemma (Bounds on the lift weight).** For every natural number $j$ and every infinite place $v$, $k + t + 1 \leq w_j(v)$. For a lift index $j$, that is $1 \leq j \leq m$, also $w_j(v) \leq 4b$.

Lean: `New.Data.k_add_t_add_one_le_liftWeight`, `New.Data.liftWeight_le_four_mul_b` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* The weight is $w_j(v) = \kappa(v) + j\cdot\mathrm{gap} + \mathrm{halfGap}$ with $\kappa(v) \geq 0$ (`New.Data.liftWeight_eq`), and $\mathrm{halfGap} \geq k + t + 1$ (`New.Data.k_add_t_add_one_le_halfGap`). For $j \leq m \leq 2m$, the data give $w_j(v) \leq 2b$ (`New.Data.liftWeight_le_two_mul_b`), and $2b \leq 4b$ as $b = \exp(\log b) > 0$. $\square$

**Lemma (Room for the main pair).** Let $1 \leq j \leq m$ and $n = j + \lfloor (t - 11m - 1)/2 \rfloor$. Then $n + z_* \leq w_j(v)$ for every infinite place $v$.

Lean: `New.Data.exponent_add_mainPairPoint_le_liftWeight` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* As $j \leq m$ and $t \geq 11m + 1$,
$$n + z_* \leq m + \frac{t - 11m - 1}{2} + \frac{7m}{2} + \frac{k}{2} = \frac{t + k - 2m - 1}{2} \leq k + t + 1 \leq w_j(v),$$
by the previous lemma. The floors only lower the left side. $\square$

**Lemma (Powers of the tame part).** For every integer $n$ and every finite place $w$ that is not chosen, $\omega^n(w) = 1$.

Lean: `New.Data.chiMLocal_zpow_eq_one_of_not_isChosen` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* $\omega(w) = 1$ at a place that is not chosen, and $1^n = 1$. $\square$

### The pairs

**Definition (The pairs of the exchanges).** Let $1 \leq j \leq m$. The three pairs are indexed by $\mathrm{none}$ and the two signs.

1. For $\mathrm{none}$, let $n = j + \lfloor (t - 11m - 1)/2\rfloor$. The character is $\nu_* = \mu_j^0\,\upsilon^n$, of weight $-(w_j(v) - n)$ at $v$, with tame part $\omega^j$. The point is $z_*$.
2. For a sign $s$, the character is $\nu_s = \upsilon^{-z_s}\,\chi^{sj}$, of weight $-z_s$ at every place, with tame part $\omega^{sj}$. The point is $z_s$.

Each is a critical pair.

Lean: `New.Data.exchangePair` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof that these are critical pairs.* For $\mathrm{none}$: $\mu_j^0$ has weight $-w_j$ and $\upsilon^n$ has weight $n$, so $\nu_*$ has weight $-(w_j - n)$. The subtraction is not truncated, since $n \leq n + z_* \leq w_j(v)$ by the lemma on room. The tame part is trivial off the chosen places by the lemma on powers. The point is in $[1, t]$. The condition $z_* \leq w_j(v) - n$ is the lemma on room, and $w_j(v) - n \leq w_j(v) \leq 4b$.

For a sign $s$: $\upsilon^{z_s}$ has weight $z_s$, so its inverse has weight $-z_s$, and $\chi^{sj}$ has weight $0$. The tame part is trivial off the chosen places. The point lies in $[1, t]$, and $c(v) = z_s$, so $z_s \leq c(v)$ holds with equality. Last, $z_s \leq t \leq k + t + 1 \leq w_j(v) \leq 4b$. $\square$

**Definition (The Hecke product).** For a twist $\vartheta$ with set of places $Q$, let $S$ be the union of the chosen places and $Q$. Then
$$\Gamma_j(\vartheta) = L_*\bigl(S, (\nu_*\vartheta)^{-1}, z_*\bigr)\cdot L_*\bigl(S, (\nu_1\vartheta)^{-1}, m\bigr)\cdot L_*\bigl(S, (\nu_{-1}\vartheta^{-1})^{-1}, \lfloor m/2\rfloor\bigr).$$
In Lean the product runs over $i$ in `Option ℤˣ`, and the power of $\vartheta$ is `i.getD 1`, so $\mathrm{none}$ gets $\vartheta^1$.

Lean: `New.Data.heckeValueProd` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Remark (Formalization).** The value $\Gamma_j(\vartheta)$ is a real number cast to $\mathbb{C}$. It is not divided by $\Gamma_j(1)$. The ratio $\rho_j(\vartheta)$ of [the definition of a comparison operator](/chapter/theorem-c-plan/#the-four-inputs) is formed later, in [the height of one lift determinant](/chapter/lift-volume-height/). Each factor is positive when the $L$-values do not vanish. The source shows this for critical pairs in [critical pairs](/chapter/twists-critical-pairs/#critical-pairs-and-the-ratio) (`New.Data.CriticalPair.L_mul_ne_zero`).

**Example (Sizes of the points).** Take $m = 10000$ and $r = 10^6$. Then $k = r + 1 - m = 990001$, $t = 5 \cdot 10^6$, $z_1 = 10000$, $z_{-1} = 5000$ and $z_* = 7 \cdot 5000 + 495000 = 530000$. For $j = 1$, the exponent of $\upsilon$ in $\nu_*$ is $n = 1 + \lfloor(5\cdot 10^6 - 110001)/2\rfloor = 2444950$. The lemma on room asks $n + z_* = 2974950 \leq w_1(v)$, and indeed $w_1(v) \geq k + t + 1 = 5990002$. So the main pair has the point $z_* \approx k/2$, far from both ends of $[1, t]$.

The three exchanges, in the order of the next two sections, use the pair of sign $-1$ (the first exchange, of rank $m$ and point $m/2$), the pair of sign $1$ (the second exchange, of rank $3m$ and point $m$) and the main pair (the third exchange, with point $z_*$). The character identities that link each exchange to its pair are in [Section 4](/chapter/comparison-operator-2/#the-third-exchange).
