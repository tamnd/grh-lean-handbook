---
title: Cuts and exponent bounds
lean:
  - New/Congruences/Lifting/CutExponentBounds.lean
decls:
  - New.Lift.KummerChart.Letter.IsNearestCut
  - New.Lift.KummerChart.Letter.HasSignBefore
  - New.Lift.KummerChart.Letter.IsLongGap
  - New.Lift.KummerChart.Letter.HasThinSuccessors
  - New.Lift.KummerChart.Letter.IsKillingCut
  - New.Lift.KummerChart.Letter.IsKillingCut.shift_eq_zero_or_lt
  - New.Lift.KummerChart.CutSizes
  - New.Lift.KummerChart.PairingSide.killsCokernel_zero_of_next_le
  - New.Lift.KummerChart.PairingSide.killsCokernel_of_isKillingCut
  - New.Lift.FitsWindows.le_add
  - New.Lift.KummerChart.PairingSide.SidePairing.jumps_le_of_fitsWindows
  - New.Lift.KummerChart.cutOrders
  - New.Lift.KummerChart.longGapDepth
  - New.Lift.KummerChart.Letter.windowSteps
  - New.Lift.KummerChart.CutSizes.sum_cost_windowSteps_le
  - New.Lift.KummerChart.PairingSide.pointsOver_cutOrders_nonempty
  - New.Lift.KummerChart.PairingSide.mem_pointsOver_plainDepth_of_cutOrders
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_sum_cost_le
  - New.Lift.KummerChart.PairingSide.pointsOver_longGapDepth_nonempty
  - New.Lift.KummerChart.PairingSide.ruleBound_le_inf_add_longGapDepth
  - New.Lift.KummerChart.PairingSide.exists_mem_pointsOver_ruleBound_le_of_isLongGap
  - New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_hasSignBefore
  - New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_isLongGap
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_cut_windows
  - New.Lift.KummerChart.Letter.hasThinSuccessors_stepBack_add
  - New.Lift.KummerChart.Letter.exists_hasThinSuccessors_stepBack
  - New.Lift.KummerChart.Letter.IsNearestCut.eq_zero_or_add_eq_of_hasThinSuccessors
  - New.Lift.KummerChart.Letter.hasSignBefore_or_isLongGap
  - New.Lift.KummerChart.cutSizes_zero_shift
  - New.Lift.KummerChart.IsUnramified.eight_mul_e_le_sq
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_sparse_thick
  - New.Lift.KummerChart.cutSizes_of_isUnramified
  - New.Lift.KummerChart.Letter.letterFrob_stepBack_succ
  - New.Lift.KummerChart.Letter.cut_stepBack_one_or_two
  - New.Lift.KummerChart.Letter.isLongGap_two_zero
  - New.Lift.KummerChart.Letter.IsNearestCut.hasSignBefore_or_isLongGap_of_two_sizes
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_any_pattern
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cuts and exponent bounds

This section chooses the cuts of the walk when the jumps lie in a low window $[-\eta, \eta]$ and a far window of width $V$ at distance $\beta_i$, with opposite signs on the two sides. It builds the points and the stops, and proves two exponent bounds.

Throughout, $\varepsilon$ is a sign on the letters, the jumps of $S$ at $i$ fit the windows $(\eta, -\varepsilon_i, \beta_i, V)$ and those of $S'$ fit $(\eta, \varepsilon_i, \beta_i, V)$ ([windows](/chapter/cup-products/#safe-moves-and-the-walk)), $\eta \geq 1$ and $V + 4\eta \leq W$. A *shift* $s$ on the letters is the pole order at $E$ allowed at a cut.

### Cuts, gaps and sizes

**Definition.** Let $i$ be a letter and $l \in \mathbb{N}$.

1. $i^{(-l)}$ is the *nearest cut* before $i$ if $0 < l$, $i^{(-l)}$ is a cut, and no $i^{(-a)}$ with $0 < a < l$ is a cut.
2. $i$ has the *sign* $\rho$ *before* it over $l$ letters if for all $a < l$, $\varepsilon(i^{(-a)}) = \rho$ or $\beta(i^{(-a)}) + V \leq \eta$.
3. $i$ has a *long gap* over $l$ letters with pivot $t$ and parameters $(J, s_0, \omega)$ if: the chart is unramified, $p \geq 5$; $s(i^{(-l)}) = 0$; $t + J + 1 = l$; $s_0 + \omega\sum_{a \leq J}p^a < \beta(i^{(-t)})$; for $a < l$, $a \neq t$, $\varepsilon(i^{(-a)}) \neq \varepsilon(i^{(-t)})$ or $\beta(i^{(-a)}) + V \leq \eta$; $\eta \leq \omega$; and $\beta(i^{(-a)}) + V \leq \omega$ for $t < a < l$.
4. $i$ has *thin successors* for a predicate $T$ if none of the $J$ letters $i^{p^t}$, $1 \leq t \leq J$, satisfies $T$.
5. $i$ is a *killing cut* if either $s(i) = 0$ and $\beta + W \leq G$ at the $J$ letters after $i$ (*thin*), or $s(i) < \beta(i)$, the chart is unramified, $p \geq 5$ and $s_0 \leq \kappa + s(i)$ (*unramified*).

Lean: `New.Lift.KummerChart.Letter.IsNearestCut`, `New.Lift.KummerChart.Letter.HasSignBefore`, `New.Lift.KummerChart.Letter.IsLongGap`, `New.Lift.KummerChart.Letter.HasThinSuccessors`, `New.Lift.KummerChart.Letter.IsKillingCut`, `New.Lift.KummerChart.Letter.IsKillingCut.shift_eq_zero_or_lt` (New/Congruences/Lifting/CutExponentBounds.lean).

At a killing cut, $s(i) = 0$ or $d = 0$.

**Definition (Cut sizes).** The *size conditions* for $(s, \beta, W, X, \delta, \kappa, b, n, J, s_0, G)$ are:

1. $n + \lfloor\log_p(2b)\rfloor + (J + 1 + d)W + dG \leq X$;
2. $12((J+1)X + \delta) < \kappa$;
3. $2eb \leq p^{J+1}\delta$ and $8e \leq p^{J+1}$;
4. $\beta_i + s_i + W \leq 2b$ for all $i$;
5. $G \leq (p-1)n$;
6. if $p \geq 5$, $\beta_i + W \leq (p-3)s_0$ for all $i$.

Lean: `New.Lift.KummerChart.CutSizes` (New/Congruences/Lifting/CutExponentBounds.lean).

Here $X$ is the cost of a level and $\delta$ that of the depth $2b$.

**Lemma (Killers at cuts).** Let the jumps of a side $R$ at each $i$ be at most $\beta_i + W$, and let the size conditions hold. Then at a killing cut $i$, $p^\kappa E^{s(i)}$ kills the cokernel of $R$ at $i$. The jumps of $S$, $S'$ and $T$ at $i$ are at most $\beta_i + W$.

Lean: `New.Lift.KummerChart.PairingSide.killsCokernel_zero_of_next_le`, `New.Lift.KummerChart.PairingSide.killsCokernel_of_isKillingCut`, `New.Lift.FitsWindows.le_add`, `New.Lift.KummerChart.PairingSide.SidePairing.jumps_le_of_fitsWindows` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Thin cut: the jumps are at most $2b$, and at most $G$ at the $J$ letters after $i$. The killer with weights ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)) gives $p^\kappa$ if $\kappa \geq 2JdG + (2J+4)G/(p-1) + 16eb/p^{J+1}$. By (1), (3) and (5) this is at most $(4J + 4)X + 8\delta < \kappa$. Unramified cut: by (6) the jumps are at most $(p-3)(\kappa + s(i))$, and the unramified killer applies. A jump $-u-u'-1$ of $T$ is at most $\beta_i + V + \eta$, as the far windows have opposite signs. $\square$

### Points at a cut

**Definition.** The *cut orders* are $\mathrm{cut}_{s,\eta,l} = \mathrm{imp}(\rho_{-s}, \sigma_{s,\eta,l+1})$. The *long gap depth* is $\lambda_{l,t,r}(a, u) = r$ if $a = t$, $1$ if $a < l$, $a \neq t$, and $-u$ if $a \geq l$. The *window steps* at $i$ are the pairs $(a, m)$ with $a < 2J+2$ and $m$ within $W + s(i)[a = 0]$ of $0$ or of $\mp\beta(i^{(-a)})$.

Lean: `New.Lift.KummerChart.cutOrders`, `New.Lift.KummerChart.longGapDepth`, `New.Lift.KummerChart.Letter.windowSteps` (New/Congruences/Lifting/CutExponentBounds.lean).

**Lemma (Cost of the windows).** Let the size conditions hold, $W \geq 4$, $s(i) + W \leq pn$, and $s(i) = 0$ or $d = 0$. Then $\kappa + 4\delta + \sum c_a(m) \leq 25\kappa$, the sum over the window steps.

Lean: `New.Lift.KummerChart.CutSizes.sum_cost_windowSteps_le` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* At a level $a$, the cost of two windows of half width $r + W \leq pn$ with centres at most $2b$ is at most $8n + 2\lfloor\log_p(2b)\rfloor + (4(r+W)+2)(d + 3a)$ ([costs](/chapter/exponent-lattices/#costs-and-depth-steps)). If $r > 0$ then $a = 0 = d$. So each level costs at most $30X$ by (1), and all levels at most $60(J+1)X < 5\kappa$. $\square$

**Theorem (Standard points at a cut).** Let the size conditions hold, $s(i) + W \leq pn$, let $i$ be a killing cut and $l \leq 2J + 1$. Then for every $c$ there is a point in $\mathrm{Pts}_i(c, 25\kappa, \mathrm{cut}_{s(i),\eta,l}, \sigma_{s(i),\eta,l+1})$. Each such point lies in $\mathrm{Pts}_i(c, e, \rho_{-\eta}, \pi_{s(i),\eta,l,\eta})$, and so is a standard point.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_cutOrders_nonempty`, `New.Lift.KummerChart.PairingSide.mem_pointsOver_plainDepth_of_cutOrders`, `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_sum_cost_le` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* The killer gives a point over $p^\kappa c$ with orders and depth $\rho_{-s(i)}$ ([side points](/chapter/exponent-lattices/#side-points)). Deepen it to $\sigma_{s(i),\eta,l+1}$. A needed step $(a, m)$ has $\rho_{-s(i)}(a, u) \leq m < \sigma(a, u)$ for a jump $u$, so $a \leq l$ and $m$ is within $s(i) + \eta$ of $-u$: a window step. By the cost lemma the point lies over $p^{25\kappa}c$, and the depth lemma improves the orders to $\mathrm{cut}$. For the second claim, no jump lies in $[-s(i), -\eta)$: if $s(i) > 0$, the far window starts beyond $s(i)$. So the improved order at $E$ is at least $-u - \eta$, and the depth $\sigma$ is at least $\pi$ since $\sigma_{s,\eta,l+1}$ has $\eta$ at the level $l$. $\square$

### Stops

**Theorem (Stop at a long gap).** Let $R$ fit the windows with signs $\sigma$, and $R'$ with signs $-\sigma$. Let the size conditions hold, $s(i) + W \leq pn$, $l \leq 2J+1$, let $i^{(-l)}$ be a killing cut, and let $i$ have a long gap with pivot $t$ and $\sigma(i^{(-t)}) = -1$. Let $\sigma(i^{(-a)}) \neq \sigma(i^{(-t)})$ or $\beta(i^{(-a)}) + V \leq \eta$ for $a < l$, $a \neq t$. Then $R$ has a point $q \in \mathrm{Pts}_i(c, 25\kappa, \varsigma_{\eta,l}, \lambda_{l,t,2b})$ such that for every jump $u$ of $R'$ at $i^{(-a)}$ and every $v$,
$$r_{l,0}(a, u+v) \leq \min\bigl(\mathrm{cut}_{s(i),\eta,l}, \mathrm{sh}_l(0, \mathrm{cut}_{0,\eta,l_0})\bigr)(a, u) + \lambda_{l,t,2b}(a, v).$$

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_longGapDepth_nonempty`, `New.Lift.KummerChart.PairingSide.ruleBound_le_inf_add_longGapDepth`, `New.Lift.KummerChart.PairingSide.exists_mem_pointsOver_ruleBound_le_of_isLongGap` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Let $N = s_0 + \omega\sum_{a\leq J}p^a$. By the unramified killer and (6), $E^{s_0}$ kills at the pivot; $p^\kappa$ kills at the cut $J+1$ steps before it. The jumps at the $J+1$ letters up to the pivot are at most $\omega$, as $\sigma = -1$ at the pivot. By (3), $2b \leq p^{J+1}\delta$. The long gap theorem ([the long gap](/chapter/cup-products/#the-long-gap)) with $g = \omega$, $s = s_0$ and $A = 2b > N$ gives a point at the pivot over $p^{\kappa+4\delta}c$ with depth $2b$ at $E$ and order $2b$ on the jumps $u < -N$. Move it to $i$ by $\varphi^t$, and raise the depth $0$ at the levels between $t$ and $l$ to $1$ by the window steps $(a, 0)$. The cost lemma gives $25\kappa$. At the pivot no jump lies in $[-N, -\eta)$, so the order is at least $\max(0, -u-\eta)$; at the other levels below $l$ the jumps are at least $-\eta$. For the inequality: at $a \geq l$ both sides are at least $-(u+v)$. Below $l$ the bound is $1$. At $a = t$ the depth is $2b$ and the jumps of $R'$ are less than $\eta + 2b$. At $a \neq t$ the jumps of $R'$ are at most $\eta$, the cut orders are at least $0$, and the depth is $1$. $\square$

**Theorem (Stops at a cut).** Let $i^{(-l)}$ be the cut before $i$, at distance $0 < l \leq 2J+1$. Let $x$, $x'$ at $i$ and $x_0$, $x_0'$ at $i^{(-l)}$ be points of the two sides.

1. (Plain.) If $i$ has the sign $\rho$ before it, $p^\kappa E^s$ kills $T$ at $i$, $x, x'$ lie in $\mathrm{Pts}_i(\cdot, e, \rho_{-\eta}, \pi_{s,\eta,l,\eta})$ and $x_0, x_0'$ have orders $\rho_{-\eta}$, then one side leads at $i$, with exponent $\kappa$.
2. (Long gap.) If $i$ has a long gap with pivot $t$, the hypotheses of the last theorem on sizes and cuts hold, $p^\kappa$ kills $T$ at $i^{(-l)}$, and $x, x'$ and $x_0, x_0'$ lie over $p^{25\kappa}c$, $p^{25\kappa}c'$ with the orders $\mathrm{cut}_{s(i),\eta,l}$ and $\mathrm{cut}_{0,\eta,l_0}$, then one side leads at $i$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_hasSignBefore`, `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_isLongGap` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* (1) If $\rho = 1$, $S$ is down and $S'$ up at the $l$ letters by the windows lemma, and the first side leads by the theorem on plain cuts. If $\rho = -1$, the second side leads. (2) The side whose far window at the pivot is negative leads. If $\varepsilon(i^{(-t)}) = 1$, this is $S$ with $\sigma = -\varepsilon$, and the last theorem gives the stop $q$. The move $\varphi^lx_0' - x'$ has orders $\min(\mathrm{cut}, \mathrm{sh}_l(0, \mathrm{cut}))$, and the rule for $l$ with the killer at $i^{(-l)}$ and the inequality make it safe. If $\varepsilon(i^{(-t)}) = -1$, exchange the sides. $\square$

### The scheme of cuts

**Theorem (The scheme).** Let the size conditions hold and $s(i) + W \leq pn$ for all $i$. Let every cut be a killing cut, and let every letter have a cut $l$ steps back for some $0 < l \leq 2J + 1$. Assume that whenever $i^{(-l)}$ is the nearest cut before $i$, there is $t$ such that $i$ has the sign $\varepsilon(i^{(-t)})$ before it over $l$ letters, or a long gap over $l$ letters with pivot $t$ and parameters $(J, s_0, \omega)$. Then for every $N \geq 51\kappa$ and all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $N$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_cut_windows` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Let $l(i) \leq 2J+1$ be the least $l > 0$ with $i^{(-l)}$ a cut. By the killers lemma, $p^\kappa E^{s(i)}$ kills $T$ at each cut. At each cut choose standard points $x_i$, $x'_i$ by the theorem on standard points, over $p^{25\kappa}c$ and $p^{25\kappa}c'$. At each cut one side leads, by the theorem on stops: at a plain cut by (1), and at a long gap by (2), since $s(i^{(-l)}) = 0$ there. The walk ([the walk](/chapter/cup-products/#safe-moves-and-the-walk)) gives the exponent $25\kappa + 25\kappa + \kappa = 51\kappa$. $\square$

### Sparse thick letters

Let $T$ be a predicate on the letters: the *thick* letters, or b-letters. Say that $T$ is *$J$-sparse* if there are no $i$ and $1 \leq s, t \leq J$ with $T(i)$, $T(i^{p^s})$ and $T(i^{p^{s+t}})$.

**Lemma (Thin cuts).** Let $T$ be $J$-sparse, and let the cuts be the letters with thin successors.

1. If $T(i^{(-r)})$ and $i^{(-r)}$ has no thin successors, then $i^{(-(r+J+1))}$ has thin successors.
2. Every letter has a cut $l$ steps back, $0 < l \leq 2J+1$.
3. If $i^{(-l)}$ is the nearest cut before $i$, $r < l$ and $T(i^{(-r)})$, then $r = 0$ or $r + J + 1 = l$.

Lean: `New.Lift.KummerChart.Letter.hasThinSuccessors_stepBack_add`, `New.Lift.KummerChart.Letter.exists_hasThinSuccessors_stepBack`, `New.Lift.KummerChart.Letter.IsNearestCut.eq_zero_or_add_eq_of_hasThinSuccessors` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* (1) A thick $j^{p^n}$, $j = i^{(-(r+J+1))}$, $1 \leq n \leq J$, the thick $i^{(-r)}$ and a thick letter $t \leq J$ steps after it contradict sparseness. (2) If $i^{(-(J+1))}$ has thin successors, take $l = J+1$. If not, some $i^{(-(J+1-n))}$ with $1 \leq n \leq J$ is thick. If it has thin successors, take $l = J+1-n$; if not, (1) gives $l = J+1-n+J+1 \leq 2J+1$. (3) If $0 < r$: the thick letter is $l - r$ steps after the cut, so $l - r > J$. If $r + J + 1 < l$, then $i^{(-r)}$ is not a cut and (1) makes $i^{(-(r+J+1))}$ a nearer cut. $\square$

**Lemma (Sign or long gap).** Let $\beta = b$ on the thick letters and $G$ on the others, with $G + V \leq \eta$. Let the thick letters $i^{(-r)}$, $r < l$, have $r = 0$ or $r + J + 1 = l$. Let either the chart be unramified, $p \geq 7$ and $10p^J\eta \leq b$, or $\varepsilon$ be constant. Then there is $t$ such that $i$ has the sign $\varepsilon(i^{(-t)})$ before it over $l$ letters, or a long gap over $l$ letters with pivot $t$, shift $0$ and parameters $(J, \lfloor(b+10\eta)/(p-3)\rfloor + 1, \eta)$.

Lean: `New.Lift.KummerChart.Letter.hasSignBefore_or_isLongGap` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* If the sign $\varepsilon(i)$ fails, some $t < l$ has $\varepsilon(i^{(-t)}) \neq \varepsilon(i)$ and a far window beyond $\eta$. So $\varepsilon$ is not constant, the chart is unramified, $i^{(-t)}$ is thick and $t \neq 0$, so $t + J + 1 = l$. The letters with $a \neq 0, t$ are thin. With $\sum_{a\leq J}p^a \leq 2p^J$ and $p - 3 \geq 4$, $\lfloor(b+10\eta)/4\rfloor + 1 + 2p^J\eta < b$ follows from $10p^J\eta \leq b$. $\square$

**Lemma.** Let $\beta_i \leq \max(b, W)$, $8e \leq p^{J+1}$, $2e(b+W) \leq p^{J+1}\delta$ and $4(J+1+d)W + \lfloor\log_p(2(b+W))\rfloor \leq X$. Then the size conditions hold with $s = 0$, $\kappa = 12((J+1)X+\delta)+1$, $b + W$ for $b$, $n = G = 2W$ and $s_0 = \lfloor(b+2W)/(p-3)\rfloor + 1$. On an unramified chart with $p \geq 3$, $8e \leq p^2$.

Lean: `New.Lift.KummerChart.cutSizes_zero_shift`, `New.Lift.KummerChart.IsUnramified.eight_mul_e_le_sq` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Direct checks; for (6), $\beta + W \leq b + 2W < (p-3)s_0$. $\square$

**Theorem (Sparse thick letters).** Let $S$, $S'$ be paired sides. At each letter $i$ let the jumps of $S$ fit $(\eta, -\varepsilon_i, \beta_i, V)$ and those of $S'$ fit $(\eta, \varepsilon_i, \beta_i, V)$, where $\beta_i = b$ if $T(i)$ and $\beta_i = G$ if not. Let $\eta \geq 1$, $G + V \leq \eta$, $J \geq 1$, and let $T$ be $J$-sparse. Assume that either the chart is unramified, $p \geq 7$ and $10p^J\eta \leq b$, or $\varepsilon$ is constant and $8e \leq p^{J+1}$. Let $2e(b + 5\eta) \leq p^{J+1}\delta$ and $20(J+1+d)\eta + \lfloor\log_p(2(b+5\eta))\rfloor \leq X$. Then for all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $10^3(\delta + (J+1)X)$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_sparse_thick` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Take $W = 5\eta$, so $V + 4\eta \leq W$, the shifts $0$, and the cuts the letters with thin successors. The last lemma gives the size conditions with $n = G = 10\eta$. Each cut is a thin killing cut, as $G + 5\eta \leq 10\eta$. The thin cuts lemma and the lemma on sign or long gap give the rest. The scheme gives the exponent $51\kappa \leq 10^3(\delta + (J+1)X)$. $\square$

### Any pattern of two sizes

**Lemma.** Let the chart be unramified, $p \geq 7$, $\beta \leq b$, $s \leq \lfloor b/p\rfloor - 7K$, $b < Kp^2$, $2G < Kp$ and $W \leq K$. Then the size conditions hold with $J = 1$, $X = 3K + \lfloor\log_p(2(b+W))\rfloor$, $\delta = 4K$, $\kappa = 12(2X + \delta) + 1$, $b + W$ for $b$, $n = K$, $s_0 = \lfloor b/p\rfloor + 12K$ and $G + W$ for $G$.

Lean: `New.Lift.KummerChart.cutSizes_of_isUnramified` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Here $d = 0$, $e = 1$. (3): $2(b+W) \leq 4Kp^2$. (5): $G + W < Kp/2 + K \leq (p-1)K$. (6): $b < p\lfloor b/p\rfloor + p$ and $3\lfloor b/p\rfloor + p \leq 4pK$. $\square$

**Lemma (Two sizes).** Let the chart be unramified, $p \geq 7$, $\beta = b$ on thick and $G$ on thin letters, $0 < G$, $b < Kp^2$, $V + 4\eta \leq W \leq K$. Let $s \leq \lfloor b/p\rfloor - 7K$, with $s(i) = 0$ when $i^p$ is thin. Let the cuts be the letters with $s < \beta$, and let the thick letters and the letters with a thin successor be cuts. Then:

1. one of $i^{(-1)}$, $i^{(-2)}$ is a cut;
2. if $i^{(-l)}$ is the nearest cut, $i$ has the sign $\varepsilon(i)$ before it over $l$ letters, or a long gap over $l$ letters with pivot $0$ and parameters $(1, \lfloor b/p\rfloor + 12K, G + W)$.

Lean: `New.Lift.KummerChart.Letter.letterFrob_stepBack_succ`, `New.Lift.KummerChart.Letter.cut_stepBack_one_or_two`, `New.Lift.KummerChart.Letter.isLongGap_two_zero`, `New.Lift.KummerChart.Letter.IsNearestCut.hasSignBefore_or_isLongGap_of_two_sizes` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* (1) If $i^{(-1)}$ is not a cut, it is thin, so $i^{(-2)}$ has a thin successor and is a cut. (2) The sign condition holds unless $l = 2$ and the signs differ. Then $i^{(-1)}$ is not a cut, so it is thin and $G \leq s(i^{(-1)}) \leq \lfloor b/p\rfloor - 7K$; $i$ is thick; and $s(i^{(-2)}) = 0$. The window at $i^{(-1)}$ ends at $G + V \leq G + W$, and $\lfloor b/p\rfloor + 12K + (G+W)(1+p) < b$ follows from $G + 7K \leq \lfloor b/p\rfloor$, $W \leq K$ and $b < Kp^2$. $\square$

**Theorem (Any pattern).** Let the chart be unramified and $p \geq 7$. Let the jumps of $S$ and $S'$ fit the windows as in the sparse theorem, with $\beta_i = b$ if $T(i)$ and $G$ if not, $0 < G \leq b$, $\eta \geq 1$ and $V + 4\eta \leq W$. If $b < Kp^2$, $2G < Kp$ and $W \leq K$, then for all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $10^4(K + \lfloor\log_p(2(b+W))\rfloor)$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_any_pattern` (New/Congruences/Lifting/CutExponentBounds.lean).

*Proof.* Take $J = 1$, $s(i) = \lfloor b/p\rfloor - 7K$ if $i^p$ is thick and $0$ if not, and let the cuts be the letters with $s < \beta$. The size lemma applies. Thick letters are cuts, as $s < b$, and so are letters with a thin successor, as $s = 0 < G$. A cut with a thick successor is an unramified killing cut, as $s_0 \leq \kappa + s(i)$; one with a thin successor is a thin killing cut. Also $s + W \leq pK$. The two sizes lemma gives the cuts and the stops, and the scheme gives $51\kappa \leq 10^4(K + \lfloor\log_p(2(b+W))\rfloor)$. $\square$

The exponent does not depend on the rank of the lattices.
