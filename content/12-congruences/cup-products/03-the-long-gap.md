---
title: The long gap
lean:
  - New/Congruences/Lifting/LongGap.lean
decls:
  - New.Lift.KummerChart.JumpLattice.shiftedStdOrders
  - New.Lift.KummerChart.JumpLattice.constantsModE
  - New.Lift.KummerChart.JumpLattice.mem_withOrders_of_add_E_smul_mem
  - New.Lift.KummerChart.JumpLattice.mem_withOrders_of_expansion_mem
  - New.Lift.KummerChart.exists_expansion_pow_E
  - New.Lift.KummerChart.JumpLattice.exists_taylor_expansion_of_mem_stdOrdersPart
  - New.Lift.KummerChart.JumpLattice.letterProj_mem_constantsModE
  - New.Lift.KummerChart.JumpLattice.exists_isMonicOfDegree_aeval_smul_mem
  - New.Lift.KummerChart.PairingSide.exists_wittMap_sub_smul_constantAt_mem_of_long_gap
  - New.Lift.KummerChart.PairingSide.projTrivial_coeff_sub_mem_withOrders
  - New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_long_gap
  - New.Lift.KummerChart.PairingSide.exists_lift_pow_smul_of_killsCokernel_stepBack
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The long gap

At a cut the walk needs a point with a large depth at the level $0$. A depth step at $p_0 = E$ costs $v_p(n) + d$, and many steps can cost much. This section gives a cheaper route on an unramified chart when the jumps before the cut are small for a long stretch. One expands a lift in powers of $E$ and takes one Taylor coefficient. The price is $p^{4\delta}$ for an expansion modulo $E^A$ with $A \leq p^l\delta$.

Throughout the section the chart is unramified: $E = z + p$ and $e = 1$. Let $L$ be a jump lattice, $i$ a letter and $l > 0$.

### Constants modulo $E^A$

**Definition.** For a function $o$ of the jump, the *shifted standard orders* are $c^{\mathrm{std}}_l[o](a, u) = c^{\mathrm{std}}_l(a, u) + o(u)[a = 0]$. A *constant modulo $E^A$* at $i$ is an element $\xi$ of the standard part of level $l$ at $i$ such that $g\xi - \xi \in L_i(c^{\mathrm{std}}_l[A])$ for all $g \in \Gamma'$. They form a $\mathbb{Z}_p$-module $\mathrm{Const}_{l,A}(i)$.

Lean: `New.Lift.KummerChart.JumpLattice.shiftedStdOrders`, `New.Lift.KummerChart.JumpLattice.constantsModE` (New/Congruences/Lifting/LongGap.lean).

Here $c^{\mathrm{std}}_l[A]$ means the constant function $A$. The value of a constant at $E$ is fixed by $\Gamma'$ modulo $\mathrm{Fil}^A$. Multiplication by an element of $W(\mathbb{F}_{p^f})$ keeps $\mathrm{Const}_{l,A}(i)$, and so do maps of lattice data.

**Lemma (Reading off a coefficient).** Let $0 < l$.

1. If $\xi \in \mathrm{Const}_{l,A}(i)$, $y \in L_i(c^{\mathrm{std}}_l)$ and $\xi + Ey \in L_i(c^{\mathrm{std}}_l[o])$, then $\xi \in L_i(c^{\mathrm{std}}_l[o^+])$, where $o^+(u) = 0$ if $o(u) \leq 0$ and $o^+(u) = A$ if $o(u) > 0$.
2. If $\xi_n \in \mathrm{Const}_{l,A}(i)$ for all $n$, $y \in L_i(c^{\mathrm{std}}_l)$, $o \leq A$, and $\sum_{n \leq N}E^n\xi_n + E^{N+1}y \in L_i(c^{\mathrm{std}}_l[o])$, then $\xi_N \in L_i(c^{\mathrm{std}}_l[o_N])$, where $o_N(u) = 0$ if $o(u) \leq N$ and $A$ if not.

Lean: `New.Lift.KummerChart.JumpLattice.mem_withOrders_of_add_E_smul_mem`, `New.Lift.KummerChart.JumpLattice.mem_withOrders_of_expansion_mem` (New/Congruences/Lifting/LongGap.lean).

*Proof.* (1) $Ey$ has the order $1$ more at the level $0$ ([twists by $p_a$](/chapter/exponent-lattices/#lattices-with-prescribed-orders)). So $\xi$ has the orders $c^{\mathrm{std}}_l[\min(1, o)]$. It is a constant modulo $E^A$, so it is deep for $c^{\mathrm{std}}_l[A]$, and the improvement lemma raises a positive order to $A$. (2) Induct on $N$. For $N = 0$ this is (1). For $N + 1$, if $o(u) > 0$ on a line, part (1) applied to $\xi_0$ and the rest shows that $\xi_0$ has order $A \geq o(u)$ at $E$ on this line. Subtract $\xi_0$, divide by $E$, and lower $o$ by $1$. The induction hypothesis gives the claim for $\xi_{N+1}$. $\square$

### Expansion in powers of $E$

**Lemma (Digits).** Every $s \in S = \Lambda[[z]]$ has digits $w_n \in \Lambda$ such that for every $N$, $s = \sum_{n < N}E^nw_n + E^Nt_N$ for some $t_N \in S$.

Lean: `New.Lift.KummerChart.exists_expansion_pow_E` (New/Congruences/Lifting/LongGap.lean).

*Proof.* As $e = 1$, the Weierstrass division by $E$ leaves a remainder in $\Lambda$: $r - w = Et$. Let $t^{(n)}$ be the $n$-th iterated quotient of $s$ and $w_n$ the remainder of $t^{(n)}$. Induct on $N$. $\square$

**Theorem (Taylor expansion).** Let $0 < l$, $3 \leq p^l$ and $A \leq p^l\delta$. Let $x$ be in the standard part of level $l$ at $i$. Then there are $\xi_n \in \mathrm{Const}_{l,A}(i)$ such that for every $N$,
$$p^{4\delta}x = \sum_{n < N}E^n\xi_n + E^Ny_N$$
with $y_N$ in the standard part of level $l$ at $i$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_taylor_expansion_of_mem_stdOrdersPart`, `New.Lift.KummerChart.JumpLattice.letterProj_mem_constantsModE` (New/Congruences/Lifting/LongGap.lean).

*Proof.* The frame theorem in its almost fixed form ([the frame theorem](/chapter/kisin-frames/#the-frame-theorem)) writes $p^{4\delta}x$ as $\sum_ar_av_a$ with $r_a \in S$ and $v_a$ whose form values lie in $\mathcal{K}_0$ and are fixed by $\Gamma'$ modulo $\mathrm{Fil}^A$. It needs $3 \leq p^l$ and $A \leq p^l\delta e$, and $e = 1$. Project to the letter $i$: $b_a = \mathrm{pr}_i(v_a)$ is a constant modulo $E^A$, and $p^{4\delta}x = \sum_ar_ab_a$ because $x$ lies at $i$. Expand each $r_a$ by the digits lemma, and put $\xi_n = \sum_aw_{a,n}b_a$ and $y_N = \sum_at_{a,N}b_a$. $\square$

**Remark (Formalization).** The digits and the quotients are taken by `choose` from the division with remainder, and the frame theorem gives the $r_a$ and $v_a$ as a finite family. The expansion is not unique, and the statements claim only existence.

### Clearing a pole

**Lemma.** Let $y \in L_i(\rho_{-s})$ and $g, l \in \mathbb{N}$. There is a monic $f \in \mathbb{Z}[X]$ of degree $s + g\sum_{j<l}p^j$ such that $f(E)y$ has the orders $(a, u) \mapsto g[a < l] - u$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_isMonicOfDegree_aeval_smul_mem` (New/Congruences/Lifting/LongGap.lean).

*Proof.* Take $f(E) = E^s\prod_{a<l}(\varphi^aE)^g$. As $E = z + p$, $\varphi^a(E) = (E - p)^{p^a} + p$, a monic polynomial in $E$ of degree $p^a$. The factor $E^s$ cancels the pole at the level $0$, and each $(\varphi^aE)^g$ raises the orders at the level $a$ by $g$. Induct on $l$. $\square$

### The long gap lemma

**Lemma (The coefficient).** Let $S$ be a side, $0 < l$, $3 \leq p^l$ and $A \leq p^l\delta$. Let $E^s$ kill the cokernel of $S$ at $i$, let the jumps of $S$ at $i^{(-a)}$ be at most $g$ for $a < l$, and let $N = s + g\sum_{a<l}p^a < A$. Then for each $c \in C$ there is $\xi \in \mathrm{Const}_{l,A}(i)$ of the extension lattice with the orders $c^{\mathrm{std}}_l[A\,[u < -N]]$, such that $\mathrm{pr}(\xi) - p^{4\delta}$ times the constant of $c$ lies in $L_i(c^{\mathrm{std}}_l[A])$ of the trivial lattice.

Lean: `New.Lift.KummerChart.PairingSide.exists_wittMap_sub_smul_constantAt_mem_of_long_gap`, `New.Lift.KummerChart.PairingSide.projTrivial_coeff_sub_mem_withOrders` (New/Congruences/Lifting/LongGap.lean).

*Proof.* The killer gives a point $y$ over $c$ with orders $\rho_{-s}$. The last lemma gives $f$, monic of degree $N$, with $f(E)y$ of orders $g[a<l] - u$. As $u \leq g$ below $l$, these orders are at least the standard ones, and at the level $0$ they are at least $\min(A, g - u)$. Expand $p^{4\delta}f(E)y = \sum_{n \leq N}E^n\xi_n + E^{N+1}y'$ by the Taylor theorem, and let $\xi = \xi_N$. If $u < -N$, then $g - u > N$, and part (2) of the reading lemma gives order $A$ at $E$. For the projection, let $\eta_n = \mathrm{pr}(\xi_n) - p^{4\delta}f_n$ times the constant, where $f_n$ is the $n$-th coefficient of $f$. The $\eta_n$ are constants modulo $E^A$ of the trivial lattice, and $\sum_{n\leq N}E^n\eta_n + E^{N+1}\mathrm{pr}(y') = 0$. Part (2), with $o = A$ and $N < A$, gives $\eta_N \in L_i(c^{\mathrm{std}}_l[A])$. As $f$ is monic, $f_N = 1$. $\square$

**Theorem (Long gap).** Let the chart be unramified, $3 \leq p^l$ and $A \leq p^l\delta$. Let $p^\kappa$ kill the cokernel of $S$ at $i^{(-l)}$ and $E^s$ kill it at $i$. Let the jumps of $S$ at $i^{(-a)}$ be at most $g$ for $a < l$, and let $N = s + g\sum_{a<l}p^a < A$. Then for each $c \in C$ there is a point
$$x \in \mathrm{Pts}_i\bigl(c, \kappa + 4\delta, c^{\mathrm{std}}_l[A\,[u < -N]], c^{\mathrm{std}}_l[A]\bigr).$$

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_long_gap`, `New.Lift.KummerChart.PairingSide.exists_lift_pow_smul_of_killsCokernel_stepBack` (New/Congruences/Lifting/LongGap.lean).

*Proof.* As $3 \leq p^l$, $l > 0$. Take $\xi$ from the lemma and let $w = \mathrm{pr}(\xi) - p^{4\delta}$ times the constant. Then $E^{-A}w$ has the standard orders of level $l$ at $i$. The map $\varphi^l$ carries the killer at $i^{(-l)}$ to a killer of level $l$ at $i$ ([constants and Frobenius](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)). So $p^\kappa E^{-A}w = \mathrm{pr}(x')$ for some $x'$ in the standard part of level $l$. Let
$$x = p^\kappa\xi - E^Ax'.$$
Its projection is $p^\kappa(w + p^{4\delta}\cdot\text{constant}) - p^\kappa w = p^{\kappa+4\delta}$ times the constant. Both terms have the orders $c^{\mathrm{std}}_l[A[u<-N]]$, since $E^Ax'$ has order $A$ at $E$ on every line. For the depth, $\xi$ is a constant modulo $E^A$, and $E^Ax'$ lies in $L_i(c^{\mathrm{std}}_l[A])$, which $\Gamma'$ keeps. $\square$

The point has order $A$ at $E$ on the very negative jumps, those below $-N$, and depth $A$ at $E$ everywhere, at the cost $\kappa + 4\delta$. A depth $A$ by steps would cost about $\sum_{n<A}v_p(n) \approx A/(p-1)$, which grows with $A$. Here the cost is $4\delta \approx 4A/p^l$.

**Example.** Let $f = 1$, $p = 5$, $l = 1$, $g = 2$ and $s = 3$. Then $N = 3 + 2 = 5$. Take $A = 10$ and $\delta = 2$, so $A \leq p\delta$. If $p^\kappa$ kills the cokernel at $i$ (here $i^{(-1)} = i$), the theorem gives a point over $p^{\kappa+8}c$ with depth $10$ at $E$, and order $10$ at $E$ on the jumps $u < -5$.
