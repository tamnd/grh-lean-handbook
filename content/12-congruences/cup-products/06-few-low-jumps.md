---
title: Few low jumps
lean:
  - New/Congruences/Lifting/FewLowJumps.lean
decls:
  - New.Lift.KummerChart.PairingSide.deepConstants
  - New.Lift.KummerChart.PairingSide.negativeWindowDepth
  - New.Lift.KummerChart.PairingSide.fewLowJumpsDepth
  - New.Lift.KummerChart.PairingSide.mem_locKisinPart_kerWithOrders_iff
  - New.Lift.KummerChart.PairingSide.mem_deepElements_iff_mem_range_and_invariantsMod
  - New.Lift.KummerChart.PairingSide.relLength_deepConstants_raiseOrder_le
  - New.Lift.KummerChart.PairingSide.natCast_dvd_frobE_zero_pow_sub_frobE
  - New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_zero_mem_deepElements
  - New.Lift.KummerChart.PairingSide.exists_sub_mem_deepElements_of_smul_sub_mem
  - New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_mem_deepElements_raiseOrder
  - New.Lift.KummerChart.PairingSide.exists_sum_smul_sub_mem_deepElements
  - New.Lift.KummerChart.PairingSide.relLength_deepConstants_le
  - New.Lift.KummerChart.PairingSide.relLength_deepConstants_le_sum_cost
  - New.Lift.KummerChart.PairingSide.sigma_Ico_raiseOrder
  - New.Lift.KummerChart.PairingSide.sum_cost_zero_eq_padicValNat_factorial
  - New.Lift.KummerChart.PairingSide.sum_cost_zero_le
  - New.Lift.KummerChart.PairingSide.sum_cost_zero_Ico_multiple_le
  - New.Lift.KummerChart.PairingSide.sum_cost_one_Ico_negativeWindowDepth_le
  - New.Lift.KummerChart.PairingSide.relLength_constantAt_deepConstants_le
  - New.Lift.KummerChart.PairingSide.pointsOver_raisedOrdersAtZero_nonempty
  - New.Lift.KummerChart.PairingSide.pointsOver_raisedOrdersAtZero_nonempty_of_fitsWindows
  - New.Lift.KummerChart.PairingSide.pow_smul_constantAt_mem_deepConstants
  - New.Lift.KummerChart.PairingSide.relLength_deepConstants_add_one_le
  - New.Lift.KummerChart.PairingSide.relLength_constantAt_range_deepConstants_le
  - New.Lift.KummerChart.PairingSide.relLength_deepConstants_negativeWindowDepth_le
  - New.Lift.KummerChart.PairingSide.tateDualSide_jump_near
  - New.Lift.KummerChart.PairingSide.tateDualSide_jump_le
  - New.Lift.KummerChart.PairingSide.improvedOrders_add_negativeWindowDepth_one_pos
  - New.Lift.KummerChart.PairingSide.isSafeMoveFst_of_negativeWindowDepth
  - New.Lift.KummerChart.PairingSide.relLength_iInf_comap_deepConstants_le
  - New.Lift.KummerChart.PairingSide.exists_relLength_le_and_isScaledCupCoboundary
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Few low jumps

The theorems so far lift every cocycle, at a price $p^H$. This section gives a different trade. On an unramified chart with $p \geq 5$, if the far windows are large and few jumps are low, the exponent is $0$ for all $d$ in a sublattice $V$ of the parameter lattice, and the colength of $V$ is bounded by the number of low jumps. The colength is the *relative length* of [Fitting ideals](/chapter/fitting-ideals/#discrete-valuation-rings-and-relative-lengths).

Throughout, the chart is unramified and $p \geq 5$. Fix $a, \eta, W$ and $b$, $\varepsilon$ on the letters, with at every letter $i$:

- (H1) $b_i + W + \eta \leq (p-3)a$ and $6(a + \eta + W) < b_i$;
- (H2) $\mathrm{NoMultipleNear}(p, 6(a + \eta + W), b_i)$;
- (H3) the jumps of $S$ at $i$ fit $(\eta, \varepsilon_i, b_i, W)$;
- (H4) $n_i$ and $r_i$ bound $f$ times the number of jumps of $S$ at $i$ in $[-\eta, \eta]$, and of all jumps, counted with multiplicity.

### Deep constants

**Definition.** For a letter $i$, $t \in \mathbb{Z}$ and an order system $o$, the *deep constants* $D_i(t, o)$ are the projections $\mathrm{pr}(x)$ of the points $x$ at $i$ with orders $\rho_t$ and depth $o$ that lie over a constant at $i$. The *negative window depth* is $\nu_{a,\eta,W,b}(0, u) = b + W + a + \eta$, $\nu(1, u) = W + 1 - u + 2a[|u| \leq \eta]$, and $\nu(l, u) = -u$ for $l \geq 2$. The *few low jumps depth* $\phi_i$ is $\rho_{2a+\eta}$ if $\varepsilon_i = 1$ and $\nu_{a,\eta,W,b_i}$ if $\varepsilon_i = -1$.

Lean: `New.Lift.KummerChart.PairingSide.deepConstants`, `New.Lift.KummerChart.PairingSide.negativeWindowDepth`, `New.Lift.KummerChart.PairingSide.fewLowJumpsDepth`, `New.Lift.KummerChart.PairingSide.mem_locKisinPart_kerWithOrders_iff`, `New.Lift.KummerChart.PairingSide.mem_deepElements_iff_mem_range_and_invariantsMod` (New/Congruences/Lifting/FewLowJumps.lean).

A point lies over $0$ with orders $o$ exactly if it lies in $K_i(o)$. So $D_i(t, o)$ is a $\mathbb{Z}_p$-module, and it shrinks when $o$ or $t$ grows.

### The length of one step

**Lemma (One step).** Let $o(l, v) \geq -v$ on the jumps, let $o(a', u) < o(a', v)$ for jumps $v < u$ at $i^{(-a')}$, and let no multiple of $p$ lie strictly between $o(0, v)$ and $o(0, v) + p^{a'}$. Let $o^+$ be $o$ with the value $o(a', u)$ raised by $1$. Then
$$\ell\bigl(D_i(0, o) / D_i(0, o^+)\bigr) \leq c_{a'}(o(a', u)) \cdot f \cdot m(u),$$
where $m(u)$ is the multiplicity of the jump $u$ at $i^{(-a')}$.

Lean: `New.Lift.KummerChart.PairingSide.relLength_deepConstants_raiseOrder_le`, `New.Lift.KummerChart.PairingSide.natCast_dvd_frobE_zero_pow_sub_frobE`, `New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_zero_mem_deepElements`, `New.Lift.KummerChart.PairingSide.exists_sub_mem_deepElements_of_smul_sub_mem`, `New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_mem_deepElements_raiseOrder`, `New.Lift.KummerChart.PairingSide.exists_sum_smul_sub_mem_deepElements` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* Let $C = c_{a'}(o(a', u))$. The step operator of [the depth lemma](/chapter/exponent-lattices/#invariance-and-the-depth-lemma) has cost $C$: it maps points of depth $o$ to points of depth $o^+$ over $p^C$ times the same constant. On an unramified chart $\varphi^{a'}E \equiv E^{p^{a'}}$ modulo $p$, and the condition on multiples of $p$ gives an operator of cost $0$ that raises the depth at the level $0$ from $o + 1$ to $o + p^{a'}$. With these, a point $x$ such that $px$ is a point of depth $o^+$ plus a vector over $0$ with orders $o$ can be replaced by $x - w$ of depth $o^+$, with $w$ over $0$: this is division by $p$. The obstruction to the step lies on the line $u$ at the level $a'$, which has rank $f\,m(u)$ over $\mathbb{Z}_p$. So among $f\,m(u) + 1$ points whose $p$-multiples are such sums, a combination with one coefficient $1$ is again such a sum. Hence the quotient needs at most $f\,m(u)$ generators, and $p^C$ kills it. Its length is at most $C f m(u)$. $\square$

**Theorem (One level).** Let $o(l, u) \geq -u$ on the jumps, let no multiple of $p$ lie strictly between $o(0, v)$ and $o(0, v) + p^{a'}$, let $o' \leq o$ at the levels $l \neq a'$, and let $o'(a', \cdot)$ decrease in the jump. If the costs $c_{a'}(y)$ of the steps $o(a', u) \leq y < o'(a', u)$ add up to at most $C_{\mathrm{all}}$, plus $C_{\mathrm{low}}$ when $|u| \leq \eta$, then
$$\ell\bigl(D_i(0, o) / D_i(0, o')\bigr) \leq C_{\mathrm{all}}\,r(i^{(-a')}) + C_{\mathrm{low}}\,n(i^{(-a')}).$$

Lean: `New.Lift.KummerChart.PairingSide.relLength_deepConstants_le`, `New.Lift.KummerChart.PairingSide.relLength_deepConstants_le_sum_cost`, `New.Lift.KummerChart.PairingSide.sigma_Ico_raiseOrder` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* Induct on the number of steps $(u, y)$ with $o(a', u) \leq y < o'(a', u)$. Raise first the step on the largest jump $u$ with $o(a', u) < o'(a', u)$; since $o'(a', \cdot)$ decreases in the jump, the order stays strictly decreasing in the jump, so the one step lemma applies. Raising $o(a', u)$ by $1$ removes exactly the step $(u, o(a', u))$. Lengths add in the chain of modules. Group the steps by jumps and multiply by $f\,m(u)$. $\square$

### The costs

**Lemma (Costs).** On an unramified chart:

1. the steps $0, \ldots, N$ at the level $0$ cost $v_p(N!)$, which is at most $m$ if $N \leq (p-1)m$;
2. for $u \in [-\eta, \eta]$ or $u \in -[\beta, \beta + W]$, with $\beta + W + \eta \leq (p-3)a$, $\mathrm{NoMultipleNear}(p, 6(a+\eta+W), \beta)$ and $\tau$ the least multiple of $p$ at least $\beta + W + a + \eta$, the steps $2a + \eta - u \leq y < \tau$ cost at most $a + 1$, and nothing if $|u| > \eta$;
3. if $6(a + \eta + W) < \beta$, $\mathrm{NoMultipleNear}$ as in 2, and $u$ fits the windows, the steps $-u \leq y < \nu(1, u)$ at the level $1$ cost at most $3(W+1)$, plus $6a$ if $|u| \leq \eta$.

Lean: `New.Lift.KummerChart.PairingSide.sum_cost_zero_eq_padicValNat_factorial`, `New.Lift.KummerChart.PairingSide.sum_cost_zero_le`, `New.Lift.KummerChart.PairingSide.sum_cost_zero_Ico_multiple_le`, `New.Lift.KummerChart.PairingSide.sum_cost_one_Ico_negativeWindowDepth_le` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* (1) $\sum_{y \leq N}v_p(y) = v_p(N!) = (N - s_p(N))/(p-1) \leq N/(p-1)$ by the Legendre formula. (2) For a far jump $-u \in [\beta, \beta + W]$, the steps lie within $a + \eta + W + p$ of $\beta$; those within $6(a+\eta+W)$ are prime to $p$, and the last ones up to $\tau$ are prime to $p$ too, as $\tau$ is the first multiple. For a low jump the steps run over at most $\beta + W + 2\eta + p$ integers, at most $(p-3)a + p + \eta$, and their valuations add up to at most $a + 1$. (3) There are $W + 1$ steps, plus $2a$ for low $u$, each of cost $v_p(y) + 3 = 3$, as $y$ is near $0$ or $\pm\beta$. $\square$

### Removing the pole and deepening

**Theorem (Colength at a letter).** Under (H1) to (H4), let $m = i^{(-1)}$. Then the constants at $i$ that lie in $D_i(0, \phi_i)$ have colength at most $(2a+1)n_i + 3(W+1)r_m + 6a\,n_m$ in the constants at $i$.

Lean: `New.Lift.KummerChart.PairingSide.relLength_constantAt_deepConstants_le`, `New.Lift.KummerChart.PairingSide.pointsOver_raisedOrdersAtZero_nonempty`, `New.Lift.KummerChart.PairingSide.pointsOver_raisedOrdersAtZero_nonempty_of_fitsWindows`, `New.Lift.KummerChart.PairingSide.pow_smul_constantAt_mem_deepConstants`, `New.Lift.KummerChart.PairingSide.relLength_deepConstants_add_one_le`, `New.Lift.KummerChart.PairingSide.relLength_constantAt_range_deepConstants_le`, `New.Lift.KummerChart.PairingSide.relLength_deepConstants_negativeWindowDepth_le` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* First, the depth $\rho_{2a+\eta}$ with a pole. The jumps are at most $b_i + W + \eta \leq (p-3)a$, so $p^sE^{a-s}$ kills the cokernel for every $s \leq a$ ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)). Deepen the point of the killer to $\rho_{2a+\eta}$; by (H2) the steps are free. So $p^s$ times every constant lies in $D_i(-(a-s), \rho_{2a+\eta})$. Second, remove the pole one order at a time. From $t$ to $t + 1$, with $t < 0$, only the lines of the jump $t$ change, and $p^a$ times every constant already lies in the next module, so the quotient has length at most $a\,f\,m(t)$. A jump $t \in [-a, 0)$ is low by (H1), so the total is at most $a\,n_i$. If $\varepsilon_i = 1$, this is the claim. Third, if $\varepsilon_i = -1$, raise the depth from $\rho_{2a+\eta}$ to $\nu$. At the level $0$, by the one level theorem and part 2 of the costs lemma, the length is at most $(a+1)n_i$; at the level $1$, by part 3, at most $3(W+1)r_m + 6a\,n_m$. Then $a\,n_i + (a+1)n_i = (2a+1)n_i$. $\square$

### The safe move and the theorem

**Lemma (Safe move at a negative window).** Let $\eta \geq 1$, let (H1) and (H2) hold, and let the jumps of $S$ and $T$ fit opposite windows $(\eta, \pm\varepsilon_j, b_j, W)$. Then the jumps of the Tate dual side are $0$ or lie near $0$ or $\pm b_i$, and are at most $(p-3)a$, so $E^a$ kills it. Let $x_0$, $x$ be points of $T$ over $c$ at $i^{(-1)}$ and $i$ with depth $\rho_{2a+\eta}$ and the improved orders $\mathrm{imp}(\rho_{-a}, \rho_{2a+\eta})$, and $x'$ a point of $S$ over $d$ at $i$ with depth $\nu_{a,\eta,W,b_i}$. Then the move of $T$ by $\varphi x_0 - x$ with $x'$ at rest is safe with exponent $0$.

Lean: `New.Lift.KummerChart.PairingSide.tateDualSide_jump_near`, `New.Lift.KummerChart.PairingSide.tateDualSide_jump_le`, `New.Lift.KummerChart.PairingSide.improvedOrders_add_negativeWindowDepth_one_pos`, `New.Lift.KummerChart.PairingSide.isSafeMoveFst_of_negativeWindowDepth` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* A jump of the dual side is $0$ or $-u-v-1$; with opposite windows, $u + v$ lies within $2\eta + W$ of $0$ or $\pm b_i$. Use the orders give safe pairs lemma with the point of the dual side from its killer, of improved orders $\mathrm{imp}(\rho_{-a}, \rho_a)$. At the level $0$ the depth of $x'$ is $b_i + W + a + \eta$, larger than any pole. At the level $1$, write $e_t(w) = t - w$ if $w < -a$ and $\min(t - w, 0)$ if not. The sum $e_a(-u-v-1) + \min(-u, e_{2a+\eta}(u)) + \nu(1, v)$ is positive: if both $u$, $v$ are low, $\nu$ has the extra $2a$; if one is far, the other window has the opposite sign and the far jump lies beyond $6(a+\eta+W)$, so one of the terms is large. At the levels $l \geq 2$ the sum is at least $1$ as in the rule. $\square$

**Theorem (Few low jumps).** Let the chart be unramified, $p \geq 5$, $\eta \geq 1$, and let (H1) to (H4) hold. Then the set $V$ of the $d$ in the parameter lattice of $S$ such that the constant of $d$ at $i$ lies in $D_i(0, \phi_i)$ for every letter $i$ is a submodule with
$$\ell(C_S / V) \leq 11\sum_i\bigl(n_i(a+1) + r_i(W+1)\bigr),$$
and for every side $T$ whose jumps fit $(\eta, -\varepsilon_i, b_i, W)$, every pairing of $T$ and $S$, every $c$ and every $d \in V$, $(c, d)$ is a scaled cup coboundary with exponent $0$.

Lean: `New.Lift.KummerChart.PairingSide.relLength_iInf_comap_deepConstants_le`, `New.Lift.KummerChart.PairingSide.exists_relLength_le_and_isScaledCupCoboundary` (New/Congruences/Lifting/FewLowJumps.lean).

*Proof.* The colength of an intersection of preimages is at most the sum of the colengths. Sum the bound of the colength theorem over $i$. As $i \mapsto i^{(-1)}$ permutes the letters, the sum is $\sum_i((8a+1)n_i + 3(W+1)r_i) \leq 11\sum_i(n_i(a+1) + r_i(W+1))$.

For the cup products, make every letter a cut with $l = 1$ and $t = a$. The side $S$ has points $x'_i$ over $d$ with no pole and depth $\phi_i$, which are standard points: at $E$ the depth is at least $a + \eta - u$ since $-u \leq b_i + W$. The side $T$ has points $x_i$ over $c$, by the first step of the last proof with $s = 0$, and no jump of $T$ lies in $[-a, -\eta)$, so they have a pole of order at most $\eta$ and are standard points. $E^a$ kills the dual side. If $\varepsilon_i = 1$, $T$ is down and $S$ up at $i$, and $T$ leads with the stop $x_i$ by the theorem on plain cuts. If $\varepsilon_i = -1$, $S$ is down, $x'_i$ is a stop, and the last lemma makes the move of $T$ safe. The corollary on cuts at all letters gives the exponent $0 + 0 + 0$. $\square$

The colength grows with the low jumps and the width $W$, but not with $b$. If no jump is low, $n = 0$ and the colength is at most $11(W+1)\sum_ir_i$.
