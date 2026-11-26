---
title: Safe moves and the walk
lean:
  - New/Congruences/Lifting/SafeMoves.lean
  - New/Congruences/Lifting/SidePoints.lean
decls:
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafe_of_orders
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_orders
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_orders
  - New.Lift.KummerChart.PairingSide.ruleBound
  - New.Lift.KummerChart.PairingSide.shiftedOrders_raisedOrdersAtZero_add_ruleBound
  - New.Lift.KummerChart.PairingSide.antitone_raisedOrdersAtZero
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_killsCokernel
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_killsCokernel
  - New.Lift.KummerChart.PairingSide.standardDepth
  - New.Lift.KummerChart.PairingSide.plainDepth
  - New.Lift.KummerChart.PairingSide.stopOrders
  - New.Lift.KummerChart.PairingSide.standardPoints
  - New.Lift.KummerChart.PairingSide.stopPoints
  - New.Lift.KummerChart.PairingSide.LiesOver
  - New.Lift.KummerChart.PairingSide.ruleBound_le_inf_add_shiftedOrders
  - New.Lift.KummerChart.PairingSide.ruleBound_zero_le_inf_add_standardDepth
  - New.Lift.KummerChart.PairingSide.SidePairing.exists_isSafePath_of_stop
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_cocycle
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_isSafePath
  - New.Lift.KummerChart.PairingSide.isSafeMoveFst_sum
  - New.Lift.KummerChart.PairingSide.isSafeMoveSnd_sum
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_stops
  - New.Lift.KummerChart.PairingSide.eq_ite_add_one_of_isLeast_cut
  - New.Lift.KummerChart.PairingSide.isSafePath_refl
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_stops_at_all_letters
  - New.Lift.KummerChart.PairingSide.mem_stopPoints_of_down
  - New.Lift.KummerChart.PairingSide.mem_stopPoints_of_le
  - New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveSnd
  - New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveFst
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_up
  - New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_neg_le_jumps
  - New.Lift.KummerChart.PairingSide.ruleBound_zero_le_inf_add_plainDepth
  - New.Lift.FitsWindows
  - New.Lift.KummerChart.PairingSide.jump_le_of_fitsWindows
  - New.Lift.KummerChart.PairingSide.neg_le_jump_of_fitsWindows
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Safe moves and the walk

The pairing lemma asks for safe moves. This section turns safety into a sum of integers: the orders of the moved vector, the depth of the vector at rest, and the orders of a point of the Tate dual side must add up to a positive number. It then puts the moves together along the Frobenius orbits of the letters. This is *the walk*.

Fix two sides $S$, $S'$ with lattices $Y$, $Y'$, a pairing $P$ of $Y$ and $Y'$ modulo $p^m$, and its Tate dual side $T$. Fix $c \in C$ and $c' \in C'$.

### Orders give safe pairs

**Lemma (Orders give safe pairs).** Let $\kappa, l \in \mathbb{N}$ and let $i$ be a letter. Let $\nu$ be a point of $T$ at $i^{(-l)}$ over $p^\kappa$ times the constant of $1$, with orders $o_\nu$ and any depth, and let $o_\nu(a, \cdot)$ decrease in the jump for every $a$. Let $w \in K_i(o_w)$ for $S$ and $y \in K_i(o_y)$ for $S'$. Suppose that for every level $a$ and all jumps $u$ of $S$ and $u'$ of $S'$ at $i^{(-a)}$,
$$0 < \mathrm{sh}_l(0, o_\nu)(a, -u-u'-1) + o_w(a, u) + o_y(a, u').$$
Then $(\delta w, y)$ and $(w, \delta y)$ are safe with exponent $\kappa$, where $\delta = z\tau$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isSafe_of_orders` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Write $w = \iota(w_0)$ and $y = \iota(y_0)$. By [Frobenius moves points](/chapter/exponent-lattices/#side-points), $\varphi^l\nu$ lies at $i$ over $p^\kappa$ times the constant of $1$, with orders $\mathrm{sh}_l(0, o_\nu)$. Let $\omega = \langle w_0, y_0\rangle$ in the tensor lattice $Y \otimes Y'$. Orders add under the pairing ([orders add](/chapter/exponent-lattices/#hodge-expansions)). The jumps $v$ of the tensor lattice that can occur are $v \leq u + u'$. As $\mathrm{sh}_l(0, o_\nu)$ decreases in the jump, the hypothesis gives that $\omega$ has the orders
$$(a, v) \mapsto 1 - \mathrm{sh}_l(0, o_\nu)(a, -v-1).$$
Now pair $\varphi^l\nu$ with $\omega$ by the extension form of $T$, and call the result $\xi$. It lies in the Tate lattice $\mathcal{O}(1)$, whose only jump is $-1$. On the jump $-1$ the orders of $\xi$ are at least $\mathrm{sh}_l(0, o_\nu)(a, u) + 1 - \mathrm{sh}_l(0, o_\nu)(a, -v-1)$ with $u \leq -v - 1$, so at least $1$. These are the standard orders of level $0$ of $\mathcal{O}(1)$. By the frame theorem for $\mathcal{O}(1)$, $\tau\xi$ is integral. As $z \in W(\mathfrak{m}^\flat)$, the reduction of $z\tau\xi$ modulo $p^m$ is small. The constant of $1$ acts on $Y$ as the projector to the letter $i$, and $w$ lies at $i$. So the image of $\xi$ modulo $p^m$ is $p^\kappa\langle \mathrm{fst}\,w, \mathrm{fst}\,y\rangle$. Hence $\delta p^\kappa\langle \mathrm{fst}\,w, \mathrm{fst}\,y\rangle$ is small. Both claims say this. $\square$

**Corollary.** Let $\nu$, $o_\nu$ be as in the lemma. If $w \in K_i(o_w)$ for $S$, $y$ is a point of $S'$ at $i$ with depth $d_y$, and $0 < \mathrm{sh}_l(0, o_\nu)(a, -u-u'-1) + o_w(a,u) + d_y(a,u')$ at all jumps, then the move of the first side by $w$ with $y$ at rest is safe with exponent $\kappa$. The same holds for a move of the second side by $y \in K_i(o_y)$ with a point $x$ of $S$ of depth $d_x$ at rest.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_orders`, `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_orders` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Let $g \in \Gamma'$. By [moving points](/chapter/exponent-lattices/#side-points), $\delta^{-1}(gy - y) \in K_i(d_y)$. Apply the lemma to $w$ and $\delta^{-1}(gy - y)$ and take its second claim. The other case uses $\delta^{-1}(gx - x) \in K_i(d_x)$ and $gy \in K_i(o_y)$. $\square$

### The rule

The Tate dual side gives the point $\nu$ when $p^\kappa E^t$ kills $T$: by [a first point](/chapter/exponent-lattices/#side-points), there is a point of $T$ over $p^\kappa$ times the constant of $1$ with orders $\rho_{-t}$. Its shifted orders take a simple form. Define the *rule bound*
$$r_{l,t}(a, s) = \begin{cases} 1 & a < l,\\ t[a = l] - s & a \geq l.\end{cases}$$

**Lemma.** For all $l, t, a \in \mathbb{N}$ and $u, u' \in \mathbb{Z}$, $\mathrm{sh}_l(0, \rho_{-t})(a, -u-u'-1) + r_{l,t}(a, u+u') = 1$. The system $\rho_t(a, \cdot)$ decreases in the jump.

Lean: `New.Lift.KummerChart.PairingSide.ruleBound` (New/Congruences/Lifting/SidePoints.lean).

Lean: `New.Lift.KummerChart.PairingSide.shiftedOrders_raisedOrdersAtZero_add_ruleBound`, `New.Lift.KummerChart.PairingSide.antitone_raisedOrdersAtZero` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Let $s = u + u'$. For $a < l$ the two terms are $0$ and $1$. For $a \geq l$ the first term is $\rho_{-t}(a - l, -s-1) = s + 1 - t[a = l]$, and the second is $t[a=l] - s$. $\square$

**Theorem (The rule).** Let $p^\kappa E^t$ kill $T$ at $i^{(-l)}$.

1. If $y \in K_i(o)$ for $S$, $x'$ is a point of $S'$ at $i$ with depth $d'$, and $r_{l,t}(a, u + u') \leq o(a, u) + d'(a, u')$ at all jumps $u$ of $S$ and $u'$ of $S'$ at $i^{(-a)}$, then the move of the first side by $y$ with $x'$ at rest is safe with exponent $\kappa$.
2. If $y' \in K_i(o')$ for $S'$, $x$ is a point of $S$ at $i$ with depth $d$, and $r_{l,t}(a, u' + u) \leq o'(a, u') + d(a, u)$ at all jumps, then the move of the second side by $y'$ with $x$ at rest is safe with exponent $\kappa$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_killsCokernel`, `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_killsCokernel` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Take the point $\nu$ of $T$ at $i^{(-l)}$ with orders $\rho_{-t}$. By the lemma, $\mathrm{sh}_l(0,\rho_{-t})(a, -u-u'-1) = 1 - r_{l,t}(a, u+u')$. Add the hypothesis: the sum of the three orders is at least $1$. The corollary applies. $\square$

So the rule for $l$ asks: below the level $l$, the move and the rest add up to $1$; at the level $l$ they add up to $t - u - u'$; above it, to $-u - u'$.

### Standard points and stops

**Definition.** Let $t, \eta, l, h_0 \in \mathbb{N}$.

1. The *standard depth* is $\sigma_{t,\eta,l}(a, u) = -u + t[a = 0] + \eta[a < l]$.
2. The *plain depth* is $\pi_{t,\eta,l,h_0}(a, u) = \sigma_{t,\eta,l}(a,u) + h_0[a = l]$.
3. The *stop orders* are $\varsigma_{\eta,l}(a, u) = \max(c^{\mathrm{std}}_l(a, u), -u - \eta[a < l])$, that is, $\max(0, -u-\eta)$ below $l$ and $-u$ from $l$ on.
4. The *standard points* at $i$ are $\mathrm{Std}_i(c, e, t, \eta, l) = \mathrm{Pts}_i(c, e, \rho_{-\eta}, \sigma_{t,\eta,l})$.
5. The *stops* at $i$ are $\mathrm{Stop}_i(c, e, \eta, l) = \mathrm{Pts}_i(c, e, \varsigma_{\eta,l}, \varsigma_{\eta,l})$.
6. $x$ *lies over* $p^ec$ at $i$ if $x$ is in the part of the letter $i$ and $\mathrm{pr}(x) = p^e$ times the constant of $c$ at $i$.

Lean: `New.Lift.KummerChart.PairingSide.standardDepth`, `New.Lift.KummerChart.PairingSide.plainDepth`, `New.Lift.KummerChart.PairingSide.stopOrders`, `New.Lift.KummerChart.PairingSide.standardPoints`, `New.Lift.KummerChart.PairingSide.stopPoints`, `New.Lift.KummerChart.PairingSide.LiesOver` (New/Congruences/Lifting/SidePoints.lean).

A standard point has a pole of order at most $\eta$ at $E$. A point with orders $\varsigma_{\eta,l}$ is a stop whatever its depth, because $\Gamma'$ keeps $L_i(o)$.

**Lemma (Two inequalities).** Let $0 < l_0$ and $0 < l$. At all $a$, $u$, $v$:

1. $r_{l,t_0}(a, u+v) \leq \min(\varsigma_{\eta,l}, \mathrm{sh}_l(0, \rho_{-\eta}))(a, u) + \mathrm{sh}_l(1, \sigma_{t_0,\eta,l_0})(a, v)$;
2. $r_{0,t}(a, u+v) \leq \min(\rho_{-\eta}, \varsigma_{\eta,l})(a, u) + \sigma_{t,\eta,l}(a, v)$.

Lean: `New.Lift.KummerChart.PairingSide.ruleBound_le_inf_add_shiftedOrders`, `New.Lift.KummerChart.PairingSide.ruleBound_zero_le_inf_add_standardDepth` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* (1) For $a < l$: the minimum is $0$, as $\varsigma \geq 0$ there, and the second term is $1$. For $a = l$: the minimum is $-u - \eta$, and the second term is $\sigma_{t_0,\eta,l_0}(0, v) = -v + t_0 + \eta$, as $0 < l_0$; the sum is $t_0 - u - v$. For $a > l$: the sum is at least $-u - v$. (2) For $a = 0$: the minimum is $-u - \eta$ and the depth is $-v + t + \eta$, as $0 < l$; the sum is $t - u - v$. For $0 < a < l$: the minimum is at least $-u - \eta$ and the depth is $-v + \eta$. For $a \geq l$: both terms are $-u$ and $-v$. $\square$

### Moves at a cut

**Theorem (Moves at a cut).** Let $0 < l$ and $0 < l_0$. Let $p^\kappa E^t$ kill $T$ at $i$ and $p^\kappa E^{t_0}$ kill $T$ at $i^{(-l)}$. Let $x \in \mathrm{Std}_i(c, e, t, \eta, l)$, $x' \in \mathrm{Std}_i(c', e', t, \eta, l)$, $x_0 \in \mathrm{Std}_{i^{(-l)}}(c, e, t_0, \eta, l_0)$ and $x_0' \in \mathrm{Std}_{i^{(-l)}}(c', e', t_0, \eta, l_0)$. Assume one of:

- (first side leads) there is a stop $q \in \mathrm{Stop}_i(c, e, \eta, l)$ such that the move of the second side by $\varphi^lx_0' - x'$ with $q$ at rest is safe with exponent $\kappa$;
- (second side leads) there is a stop $q' \in \mathrm{Stop}_i(c', e', \eta, l)$ such that the move of the first side by $\varphi^lx_0 - x$ with $q'$ at rest is safe with exponent $\kappa$.

Then there are $w$ over $p^ec$ at $i$ and $w'$ over $p^{e'}c'$ at $i$ such that a safe path with exponent $\kappa$ leads from $(\varphi^lx_0, \varphi^lx_0')$ through $(w, w')$ to $(x, x')$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.exists_isSafePath_of_stop` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* By Frobenius moves points, $\varphi^lx_0$ and $\varphi^lx_0'$ are points at $i$ with orders $\mathrm{sh}_l(0, \rho_{-\eta})$ and depth $\mathrm{sh}_l(1, \sigma_{t_0,\eta,l_0})$. Two points over the same constant differ by a vector over $0$ whose orders are the minimum of theirs. Let the first side lead, and take $w = q$, $w' = x'$. The four moves are:

1. the first side by $\varphi^lx_0 - q$ with $\varphi^lx_0'$ at rest. The orders of the move are $\min(\varsigma_{\eta,l}, \mathrm{sh}_l(0, \rho_{-\eta}))$. Use the rule for $l$ with the killer at $i^{(-l)}$ and inequality (1);
2. the second side by $\varphi^lx_0' - x'$ with $q$ at rest. This is the hypothesis;
3. the first side by $q - x$ with $x'$ at rest. The orders are $\min(\rho_{-\eta}, \varsigma_{\eta,l})$, the depth of $x'$ is $\sigma_{t,\eta,l}$. Use the rule for $0$ with the killer at $i$ and inequality (2);
4. the second side by $x' - x' = 0$. A zero move is safe.

If the second side leads, take $w = \varphi^lx_0$ and $w' = q'$. The first move is $0$, and the other three are the mirror images of the moves above. $\square$

**Lemma (The cocycle moves).** Let $0 < l$, let $p^\kappa E^t$ kill $T$ at $i^{(-d)}$, and let $x$, $x'$ be standard points at $i^{(-d)}$ with the parameters $t, \eta, l$. Then for every $g \in \Gamma'$ the move of the second side by $g\varphi^dx' - \varphi^dx'$ with $\varphi^dx$ at rest is safe with exponent $\kappa$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_cocycle` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* The depth of $\varphi^dx'$ is $\mathrm{sh}_d(1, \sigma_{t,\eta,l})$, so the move lies in $K_i$ of this system; so does the depth of $\varphi^dx$. Use the rule for $d$. Below $d$ the sum is $2 \geq 1$. At $d$ it is $-u-u' + 2t + 2\eta \geq t - u - u'$. Above $d$ it is at least $-u-u'$. $\square$

### The walk

**Lemma (Letter by letter).** Let $y_i, w_i, x_i$ lie over $p^ec$ at $i$, and $y'_i, w'_i, x'_i$ over $p^{e'}c'$ at $i$, for every letter $i$. Let $\varphi\sum_ix_i = \sum_iy_i$ and $\varphi\sum_ix'_i = \sum_iy'_i$. Assume that for all $i$ and $g \in \Gamma'$ the move of the second side by $gx'_i - x'_i$ with $x_i$ at rest is safe with exponent $\kappa$, and that a safe path with exponent $\kappa$ leads from $(y_i, y'_i)$ through $(w_i, w'_i)$ to $(x_i, x'_i)$. Then $(c, c')$ is a scaled cup coboundary with exponent $N$ for every $N \geq e + e' + \kappa$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_isSafePath`, `New.Lift.KummerChart.PairingSide.isSafeMoveFst_sum`, `New.Lift.KummerChart.PairingSide.isSafeMoveSnd_sum` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* The parts of different letters are orthogonal under the pairing, and $\Gamma'$ keeps each part. So a sum over the letters of safe moves is a safe move of the sums. The letter projectors add up to $1$, so $\sum_ix_i$ lies over $p^e(1 \otimes c)$, and the same holds for the other sums. Apply the pairing lemma to $\sum_ix_i$, $\sum_iw_i$, $\sum_ix'_i$, $\sum_iw'_i$, with $e_1 = e$, $e_2 = e'$, $e_3 = \kappa$. $\square$

**Theorem (The walk).** Let some letters be *cuts*. Let $l(i) > 0$ be the least $a > 0$ such that $i^{(-a)}$ is a cut, for every letter $i$. Let $t$ be a function on the letters. Assume, at every cut $i$:

1. $p^\kappa E^{t(i)}$ kills $T$ at $i$;
2. $x_i \in \mathrm{Std}_i(c, e, t(i), \eta, l(i))$ and $x'_i \in \mathrm{Std}_i(c', e', t(i), \eta, l(i))$;
3. one side leads at $i$, as in the theorem on moves at a cut, with $x_0 = x_{i^{(-l(i))}}$ and $x_0' = x'_{i^{(-l(i))}}$.

Then $(c, c')$ is a scaled cup coboundary with exponent $N$ for every $N \geq e + e' + \kappa$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_stops`, `New.Lift.KummerChart.PairingSide.eq_ite_add_one_of_isLeast_cut`, `New.Lift.KummerChart.PairingSide.isSafePath_refl` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Let $d(i) = 0$ if $i$ is a cut and $d(i) = l(i)$ if not. Then $i^{(-d(i))}$ is a cut for every $i$. The least-cut property gives $l(i) = d(i^{(-1)}) + 1$. Put $z_i = \varphi^{d(i)}x_{i^{(-d(i))}}$ and $y_i = \varphi^{l(i)}x_{i^{(-l(i))}}$. The Frobenius of letters is a bijection, and $(i^{(-1)})^{(-a)} = i^{(-(a+1))}$, so
$$\varphi\sum_iz_i = \sum_i\varphi^{d(i^{(-1)})+1}x_{i^{(-l(i))}} = \sum_iy_i,$$
and the same for the primed points. At a cut $i$, $z_i = x_i$, and the theorem on moves at a cut gives $w_i$, $w'_i$ and a safe path from $(y_i, y'_i)$ to $(z_i, z'_i)$. Off the cuts, $z_i = y_i$, and the constant path is safe, as its moves are $0$. The cocycle moves are safe by the last lemma with $d = d(i)$. All the vectors lie over the right constants. The lemma letter by letter finishes. $\square$

**Remark (Formalization).** The vectors $w_i$, $w'_i$ are taken by `choose` from the existence statement at each letter. Only their existence enters the pairing lemma. The hypothesis on $l$ is `IsLeast` of the set $\{a : 0 < a,\ i^{(-a)} \text{ is a cut}\}$. It forces every Frobenius orbit of letters to contain a cut. With no cut at all the hypothesis fails, so the theorem says nothing in that case.

**Corollary (Cuts at all letters).** If at every letter $p^\kappa E^t$ kills $T$, $x_i \in \mathrm{Std}_i(c, e, t, \eta, 1)$, $x'_i \in \mathrm{Std}_i(c', e', t, \eta, 1)$, and one side leads with $l = 1$, then $(c, c')$ is a scaled cup coboundary with exponent $N$ for every $N \geq e + e' + \kappa$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_stops_at_all_letters` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* Every letter is a cut, so $l(i) = 1$ for all $i$, and $t$ is constant. $\square$

### Plain cuts

The stop is easy to find when one side is *down*, with all jumps at most $\eta$ at the $l$ letters up to $i$, and the other is *up*, with all jumps at least $-\eta$ there.

**Lemma.** Let $0 < l$, let the jumps of $S$ at $i^{(-a)}$ be at most $\eta$ for $a < l$, and let $x \in \mathrm{Std}_i(c, e, t, \eta, l)$. Then $x \in \mathrm{Stop}_i(c, e, \eta, l)$.

Lean: `New.Lift.KummerChart.PairingSide.mem_stopPoints_of_down`, `New.Lift.KummerChart.PairingSide.mem_stopPoints_of_le` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* By the improvement lemma, $x$ has the orders $\mathrm{imp}(\rho_{-\eta}, \sigma_{t,\eta,l})$. Below $l$ the depth is $\sigma = -u + \eta + t[a=0] \geq 0$, since $u \leq \eta$. So the improved order is $\sigma$ where $\rho_{-\eta} > 0$, and $\min(\sigma, 0) = 0$ elsewhere. In both cases it is at least $\max(0, -u-\eta)$. From $l$ on, the improved order is $-u$. $\square$

**Theorem (Plain cuts).** Let $0 < l$ and let $p^\kappa E^t$ kill $T$ at $i$. Let the jumps of $S$ at $i^{(-a)}$, $a < l$, be at most $\eta$, and those of $S'$ at least $-\eta$. Let $x \in \mathrm{Pts}_i(c, e, \rho_{-\eta}, \pi_{t,\eta,l,\eta_0})$, $x' \in \mathrm{Pts}_i(c', e', \rho_{-\eta}, d')$ and $x_0' \in \mathrm{Pts}_{i^{(-l)}}(c', e', \rho_{-\eta_0}, d_0')$, with any $d'$, $d_0'$. Then $x$ is a stop of the first side, and the move of the second side by $\varphi^lx_0' - x'$ with $x$ at rest is safe with exponent $\kappa$. The same holds with the sides exchanged.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveSnd`, `New.Lift.KummerChart.PairingSide.SidePairing.exists_mem_stopPoints_isSafeMoveFst`, `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveSnd_of_up`, `New.Lift.KummerChart.PairingSide.SidePairing.isSafeMoveFst_of_neg_le_jumps`, `New.Lift.KummerChart.PairingSide.ruleBound_zero_le_inf_add_plainDepth` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* As $\pi \geq \sigma$, $x$ is a standard point, and by the lemma it is a stop. The move $\varphi^lx_0' - x'$ has the orders $\min(\rho_{-\eta}, \mathrm{sh}_l(0, \rho_{-\eta_0}))$. Use the rule for $0$ with the killer at $i$. At $a = 0$: the order is $-u' - \eta$, as $u' \geq -\eta$, the depth is $-u + t + \eta$, and the sum is $t - u - u'$. At $0 < a < l$: the order is $\min(0, -u') \geq -u' - \eta$ and the depth is $-u + \eta$. At $a = l$: the order is $-u' - \eta_0$ and the depth is $-u + \eta_0$. Above $l$: $-u'$ and $-u$. $\square$

The windows decide which side is down.

**Lemma (Windows).** Say that $U$ *fits the windows* $(\eta, \varepsilon, b, W)$ if each $u \in U$ lies in $[-\eta, \eta]$ or in $\varepsilon[b, b + W]$, for a sign $\varepsilon$. If the jumps of $S$ at $i$ fit the windows and $\varepsilon = -1$ or $b + W \leq \eta$, then they are at most $\eta$. If $\varepsilon = 1$ or $b + W \leq \eta$, then they are at least $-\eta$.

Lean: `New.Lift.FitsWindows` (New/Congruences/Lifting/SidePoints.lean).

Lean: `New.Lift.KummerChart.PairingSide.jump_le_of_fitsWindows`, `New.Lift.KummerChart.PairingSide.neg_le_jump_of_fitsWindows` (New/Congruences/Lifting/SafeMoves.lean).

*Proof.* A negative far window is below $0$, a positive one is above $0$, and if $b + W \leq \eta$ the far window lies in $[-\eta, \eta]$. $\square$

**Example (The model case).** In the model case of [the first section](/chapter/cup-products/#what-the-chapter-proves), every letter is a cut and $l = 1$. The jumps of $S$ and $S'$ lie in $\{-1, 0\}$, so with $\eta = 1$ each side is down and up. So the first side can always lead, with its own point as the stop. The jumps of $T$ are at most $0$, so $1$ kills $T$ ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)), and the exponent of the walk is $e + e'$, the costs of the points.
