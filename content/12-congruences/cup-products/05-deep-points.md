---
title: Deep points
lean:
  - New/Congruences/Lifting/DeepPoints.lean
decls:
  - New.Lift.KummerChart.PairingSide.sum_cost_le_of_noMultipleNear
  - New.Lift.KummerChart.PairingSide.mem_twoWindows_union_iff
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_steps_level_zero
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_noMultipleNear
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_near_steps
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_gap
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_gap
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_fitsWindows
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_jumps_nonpos
  - New.Lift.KummerChart.PairingSide.pointsOver_stopOrders_nonempty
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_jumps_nonpos
  - New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_killsCokernel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Deep points

The walk of [the last section](/chapter/cup-products/#cuts-and-exponent-bounds) pays for depth at many levels. If every letter is a cut and all steps lie at the level $0$, the cost is much smaller. This section treats two such cases: no jump lies in $[-a, 0)$, or the chart is unramified and the jumps of $S'$ lie in $[-\eta, 0]$. In both cases the exponent does not grow with the far windows, if $p$ divides no nonzero integer near them.

Recall from [side points](/chapter/exponent-lattices/#side-points) that $\mathrm{NoMultipleNear}(p, n, b)$ means: $p$ divides no nonzero integer within $n$ of $0$, $b$ or $-b$. The two windows of radius $n$ at $c$ are $\mathrm{tw}(n, c) = [-n, n] \cup [c - n, c + n]$.

### Steps at the level zero

**Lemma (Cheap steps).** If $\mathrm{NoMultipleNear}(p, n, b)$, then $\sum c_0(y) \leq (8n + 4)d$, the sum over $y \in \mathrm{tw}(n, b) \cup \mathrm{tw}(n, -b)$. This set is the set of $y$ with $|y| \leq n$, $|y - b| \leq n$ or $|y + b| \leq n$.

Lean: `New.Lift.KummerChart.PairingSide.sum_cost_le_of_noMultipleNear`, `New.Lift.KummerChart.PairingSide.mem_twoWindows_union_iff` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* The set is a union of four intervals of $2n + 1$ integers, so it has at most $8n + 4$ elements. Each element is $0$ or prime to $p$, so $v_p(y) = 0$ and $c_0(y) = d$. $\square$

**Lemma (Deepening at the level zero).** Let $S$ have a point in $\mathrm{Pts}_i(c, \kappa, o_1, o)$. Let every step $y$ with $o(l, u) \leq y < o'(l, u)$, for a jump $u$ at $i^{(-l)}$, have $l = 0$ and lie in a set $Y$ with $\sum_{y \in Y}c_0(y) \leq C$. Then $\mathrm{Pts}_i(c, \kappa + C, \mathrm{imp}(o_1, o'), o')$ is nonempty. If $\mathrm{NoMultipleNear}(p, n, b)$ and $Y = \mathrm{tw}(n, b) \cup \mathrm{tw}(n, -b)$, then $C = (8n + 4)d$ will do. If also the chart is unramified, then $C = 0$, and any orders $o_1' \leq \mathrm{imp}(o_1, o')$ can be taken.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_steps_level_zero`, `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_noMultipleNear`, `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_near_steps` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* The depth lemma with costs ([costs and depth steps](/chapter/exponent-lattices/#costs-and-depth-steps)) raises the depth one step at a time, each step $(0, y)$ at the cost $c_0(y)$, and improves the orders. The cheap steps lemma bounds the sum. On an unramified chart $d = 0$. Lower orders give a larger set of points. $\square$

### A gap below zero

**Lemma.** Let $p^\kappa E^a$ kill the cokernel of $S$ at $i$, let no jump at $i$ lie in $[-a, 0)$, and let $Y \supseteq [-u - a, a + \eta - u)$ for every jump $u$ at $i$, with $\sum_{y\in Y}c_0(y) \leq C$. Then $S$ has a point in $\mathrm{Pts}_i(c, \kappa + C, \rho_0, \pi_{a,\eta,1,0})$: no pole, and depth $a + \eta - u$ at $E$ and $-u$ above.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_gap` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* The killer gives a point with orders and depth $\rho_{-a}$ ([side points](/chapter/exponent-lattices/#side-points)). The steps from $\rho_{-a}$ to $\pi_{a,\eta,1,0}$ are at the level $0$ and in $[-u-a, a+\eta-u)$. Deepen by the last lemma. The improved order at $E$ is the depth $a + \eta - u > 0$ where $-u - a > 0$, and $\min(a + \eta - u, 0)$ elsewhere. If $u \geq 0$, this is at least $-u$. If $u < 0$, then $u < -a$ by the gap, so $-u - a > 0$ and the order is $a + \eta - u \geq -u$. So the point has the orders $\rho_0$. $\square$

**Theorem (Gap below zero).** Let $p^\kappa E^a$ kill the cokernels of $S$, $S'$ and $T$ at every letter. Let the jumps of $S$ fit $(\eta, -\varepsilon_i, b_i, W)$ and those of $S'$ fit $(\eta, \varepsilon_i, b_i, W)$, and let no jump of $S$ or $S'$ lie in $[-a, 0)$. Let $Y_i \supseteq [-u - a, a + \eta - u)$ for every jump $u$ of $S$ or $S'$ at $i$, with $\sum_{y\in Y_i}c_0(y) \leq C$. Then for $H \geq 3\kappa + 2C$ and all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $H$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_gap` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* Make every letter a cut, with $l = 1$ and $t = a$. The lemma gives points $x_i$ of $S$ and $x'_i$ of $S'$ over $p^{\kappa+C}c$ and $p^{\kappa+C}c'$, with no pole and depth $\pi_{a,\eta,1,0}$. They have the orders $\rho_{-\eta}$ too, and lie in $\mathrm{Std}_i(\cdot, \kappa + C, a, \eta, 1)$. At each letter the side whose far window is negative has jumps at most $\eta$, and the other side has jumps at least $-\eta$. If $\varepsilon_i = 1$, $S$ is down and leads with $x_i$ as its stop, by the theorem on plain cuts ([plain cuts](/chapter/cup-products/#safe-moves-and-the-walk)) with $l = 1$ and $h_0 = 0$; if $\varepsilon_i = -1$, $S'$ leads. The corollary on cuts at all letters gives the exponent $(\kappa + C) + (\kappa + C) + \kappa$. $\square$

### Jumps of one side at most zero

**Lemma (Points on an unramified chart).** Let the chart be unramified and $\mathrm{NoMultipleNear}(p, n, \beta)$.

1. If $p^\kappa E^a$ kills the cokernel of $S$ at $i$, the jumps at $i$ fit $(\eta, \sigma, \beta, W)$, $a \leq t$ and $a + t + \eta + W \leq n$, then $\mathrm{Pts}_i(c, \kappa, \rho_{-t}, \pi_{a,t,1,0})$ is nonempty.
2. If all jumps of $S$ lie in $[-\eta, 0]$ and $a + t + \eta \leq n$, then $\mathrm{Pts}_i(c, 0, \rho_0, \pi_{a,t,1,0})$ is nonempty at every $i$.
3. In case 2, if $\eta \leq t$ and $x_0' \in \mathrm{Pts}_{i^{(-1)}}(c', 0, \rho_0, \pi_{a,t,1,0})$, then $\mathrm{Pts}_i(c', 0, \varsigma_{t,1}, \pi_{a,t,1,t})$ is nonempty.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_fitsWindows`, `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_jumps_nonpos`, `New.Lift.KummerChart.PairingSide.pointsOver_stopOrders_nonempty` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* (1) Start from the point of the killer, with $\rho_{-a}$. The steps are at $E$, in $[-u - a, a + t - u)$, and $u$ lies in $[-\eta, \eta]$ or within $W$ of $\pm\beta$, so the steps lie within $n$ of $0$ or $\pm\beta$. They are free. The improved orders are at least $\rho_{-t}$, as $a \leq t$. (2) The jumps are at most $0$, so $1$ kills the cokernel ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)), and the point of the killer has $\rho_0$. The steps lie in $[-u, a + t - u)$, within $n$ of $0$, and are free. The improved orders stay $\rho_0$. (3) Frobenius moves $x_0'$ to $i$ with depth $\mathrm{sh}_1(1, \pi_{a,t,1,0})$, which is $1$ at $E$ and $a + t - u$ at the level $1$, at least $t - u$. Raise the depth at $E$ from $1$ to $a + t - u$; the steps lie in $[1, a + t + \eta]$ and are free. The improved orders at $E$ are $\min(\cdot, 0) = 0$ or positive, so at least $\max(0, -u-t)$, and $-u$ above. $\square$

**Theorem (Jumps at most zero).** Let the chart be unramified. Let $p^\kappa E^a$ kill the cokernels of $S$ and $T$ at every letter, and let $\mathrm{NoMultipleNear}(p, 6(a + \eta + W), b_i)$ at every $i$. Let the jumps of $S$ fit $(\eta, -\varepsilon_i, b_i, W)$, and let the jumps of $S'$ lie in $[-\eta, 0]$. Then for $H \geq 2\kappa$ and all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $H$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_jumps_nonpos` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* Put $t = a + \eta$. Then $a + t + \eta + W \leq 6(t + W)$. Every letter is a cut with $l = 1$. Part (1) gives $x_i \in \mathrm{Std}_i(c, \kappa, a, t, 1)$ and part (2) gives $x'_i \in \mathrm{Std}_i(c', 0, a, t, 1)$, as no pole is a pole of order at most $t$. If $\varepsilon_i = 1$, the jumps of $S$ at $i$ are at most $\eta \leq t$ and those of $S'$ are at least $-t$, so $S$ leads with the stop $x_i$ by the theorem on plain cuts. If $\varepsilon_i = -1$, the jumps of $S$ are at least $-t$, and $S'$ is down. Part (3) gives a stop $q'$ of $S'$ at $i$ with depth $\pi_{a,t,1,t}$, and the plain cut theorem with the sides exchanged makes the move of $S$ by $\varphi x_{i^{(-1)}} - x_i$ safe with $q'$ at rest. The corollary on cuts at all letters gives the exponent $\kappa + 0 + \kappa$. $\square$

### The combined statement

**Theorem (Deep points).** Let $p^\kappa E^a$ kill the cokernels of $S$, $S'$ and $T$ at every letter. Let $n = 6(a + \eta + W)$ and $\mathrm{NoMultipleNear}(p, n, b_i)$ at every $i$. Let the jumps of $S$ fit $(\eta, -\varepsilon_i, b_i, W)$ and those of $S'$ fit $(\eta, \varepsilon_i, b_i, W)$. Assume that no jump of $S$ or $S'$ lies in $[-a, 0)$, or that the chart is unramified and the jumps of $S'$ lie in $[-\eta, 0]$. Then for
$$H \geq 3\bigl(\kappa + (8n + 4)d\bigr)$$
and all $c$, $c'$, $(c, c')$ is a scaled cup coboundary with exponent $H$.

Lean: `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_killsCokernel` (New/Congruences/Lifting/DeepPoints.lean).

*Proof.* In the first case take $Y_i = \mathrm{tw}(n, b_i) \cup \mathrm{tw}(n, -b_i)$. A jump $u$ lies within $\eta$ of $0$ or within $W$ of $\pm b_i$, so $[-u - a, a + \eta - u)$ lies within $a + \eta + W \leq n$ of $0$ or $\pm b_i$, inside $Y_i$. The cheap steps lemma gives $C = (8n + 4)d$, and the gap theorem applies with $3\kappa + 2C \leq H$. In the second case the last theorem applies, since $2\kappa \leq H$. $\square$

On an unramified chart $d = 0$, so the exponent is $3\kappa$ in the first case and $2\kappa$ in the second. It does not depend on the far windows $b_i$ or on the rank.
