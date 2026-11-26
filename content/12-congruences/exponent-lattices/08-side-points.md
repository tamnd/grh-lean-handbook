---
title: Side points
lean:
  - New/Congruences/Lifting/SidePoints.lean
decls: [New.Lift.raisedOrdersAtZero, New.Lift.KummerChart.PairingSide.inclKer, New.Lift.KummerChart.PairingSide.deepElements, New.Lift.KummerChart.PairingSide.kerWithOrders, New.Lift.KummerChart.PairingSide.IsOperatorOfCost, New.Lift.KummerChart.PairingSide.pointsOver, New.Lift.KummerChart.PairingSide.IsOperatorOfCost.mem_deepElements, New.Lift.KummerChart.PairingSide.IsOperatorOfCost.comp, New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_killsCokernel, New.Lift.KummerChart.PairingSide.depthOperator, New.Lift.KummerChart.PairingSide.depthOperator_mem_kerWithOrders, New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_mem_hodgeFil_succ, New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_and_mem_deepElements, New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_costs, New.Lift.KummerChart.PairingSide.zTauUnit_inv_smul_sub_mem_kerWithOrders, New.Lift.KummerChart.PairingSide.sub_mem_kerWithOrders_of_pointsOver, New.Lift.KummerChart.PairingSide.phi_pow_smul_mem_pointsOver]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Side points

The pairing lemma of [Section 6](/chapter/exponent-lattices/#pairing-sides-and-the-pairing-lemma) needs elements $x$, $w$ over $p^e$ times a constant. This section makes them. A cokernel killer gives a first point. Operators of a known cost then make it deeper. The Frobenius moves points between letters.

### Points and depth

**Definition.** Let $S$ be a side, $i$ a letter, $c \in C$, $e \in \mathbb{N}$, and $o$, $o'$ order systems.

1. $\iota$ is the inclusion of $Y$ into $Y \times C$.
2. $x \in N_{\mathrm{loc}}$ is *deep for $o$ at $i$* if $\mathrm{pr}(x)$ is a constant at $i$ and $x \in \mathrm{Inv}(L_i(o))$, that is, $gx - x \in L_i(o)$ for all $g \in \Gamma'$.
3. $K_i(o)$ is the set of the $x \in L_i(o)$ with $\mathrm{pr}(x) = 0$.
4. An additive map $A : N_{\mathrm{loc}} \to N_{\mathrm{loc}}$ is an *operator of cost $e$* if $Ax - p^ex \in N_{\mathrm{loc}} \cap K_i(o)$ for every letter $i$, every $o$ and every $x$ deep for $o$ at $i$.
5. The *points over $c$* with exponent $e$, orders $o$ and depth $o'$ are the $x \in N_{\mathrm{loc}}$ with $\mathrm{pr}(x) = p^e$ times the constant of $c$ at $i$, $x \in L_i(o)$, and $x \in \mathrm{Inv}(L_i(o'))$.
6. $\rho_t$ is the order system $\rho_t(a, u) = -u$ for $a \geq 1$ and $\rho_t(0, u) = t - u$.

Lean: `New.Lift.KummerChart.PairingSide.inclKer`, `New.Lift.KummerChart.PairingSide.deepElements`, `New.Lift.KummerChart.PairingSide.kerWithOrders`, `New.Lift.KummerChart.PairingSide.IsOperatorOfCost`, `New.Lift.KummerChart.PairingSide.pointsOver`, `New.Lift.raisedOrdersAtZero` (New/Congruences/Lifting/SidePoints.lean).

By [Section 4](/chapter/exponent-lattices/#invariance-and-the-depth-lemma), depth $o'$ means: each value $v_a(\mu, x)$ at a form of type $u$ lies in $K'$ modulo $\mathrm{Fil}^{o'(a,u)}$.

**Lemma.** (1) An operator of cost $e$ keeps depth: if $x$ is deep for $o$, so is $Ax$. (2) If $B$ has cost $e'$ and $A$ has cost $e$, then $B \circ A$ has cost $e' + e$.

Lean: `New.Lift.KummerChart.PairingSide.IsOperatorOfCost.mem_deepElements`, `New.Lift.KummerChart.PairingSide.IsOperatorOfCost.comp` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* (1) $Ax = p^ex + (Ax - p^ex)$. The first term is deep. The second lies in $K_i(o)$, and an element $y \in L_i(o)$ has $gy - y \in L_i(o)$, so it is deep, and it lies over $0$. (2) By (1), $Ax$ is deep for $o$. Then
$$BAx - p^{e'+e}x = (BAx - p^{e'}Ax) + p^{e'}(Ax - p^ex),$$
and both terms lie in $N_{\mathrm{loc}} \cap K_i(o)$. $\square$

### A first point

**Theorem (Points from a cokernel killer).** If $p^\kappa E^s$ kills the cokernel at $i$, then for every $c \in C$ there is a point over $c$ with exponent $\kappa$, orders $\rho_{-s}$ and depth $\rho_{-s}$.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_killsCokernel` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* The constant of $c$ is in the standard part of level $0$ of the trivial lattice ([Section 7](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)). By the lemma on lifts with $r = 0$, there is $x$ in the standard part of the extension with $\mathrm{pr}(x) = p^\kappa E^s$ times the constant. Let $x' = E^{-s}x$. It lies in $N_{\mathrm{loc}}$, as $E$ is inverted there. Its orders are $-u$ at levels $a \geq 1$ and $-u - s$ at level $0$, which is $\rho_{-s}$. Its projection is $p^\kappa$ times the constant. As $x' \in L_i(\rho_{-s})$, also $gx' - x' \in L_i(\rho_{-s})$, so the depth is $\rho_{-s}$. $\square$

### Operators of a cost

**Definition (Depth operator).** For $g \in \Gamma'$ and $\upsilon \in A_{\inf}$, the *depth operator* sends $x \in N_{\mathrm{loc}}$ to the retraction $r(\upsilon(gx - x)/\delta)$, where $\delta = z\tau$.

Lean: `New.Lift.KummerChart.PairingSide.depthOperator` (New/Congruences/Lifting/SidePoints.lean).

**Lemma.** If $x$ is deep for $o$ at $i$, the depth operator sends $x$ into $N_{\mathrm{loc}} \cap K_i(o)$.

Lean: `New.Lift.KummerChart.PairingSide.depthOperator_mem_kerWithOrders` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* Division by the unit $\delta$ keeps $L_i(o)$, by [Section 3](/chapter/exponent-lattices/#lattices-with-prescribed-orders), and so do $\upsilon$ and the retraction, by [Section 5](/chapter/exponent-lattices/#hodge-expansions). The element $g$ fixes the constant below $x$, so $gx - x$ lies over $0$, and the projection commutes with the retraction. $\square$

**Theorem (One step of depth).** For each level $a$ and $n \in \mathbb{Z}$ there is an operator $B$ of cost $c_a(n) = v_p(n) + d + 3a$ such that, for every $x \in N_{\mathrm{loc}}$ and every form $\mu$: if $v_a(\mu, gx - x) \in \mathrm{Fil}^n$ for all $g \in \Gamma'$, then $v_a(\mu, gBx - Bx) \in \mathrm{Fil}^{n+1}$ for all $g \in \Gamma'$.

Lean: `New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_mem_hodgeFil_succ` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* The one-step lemma of [Section 4](/chapter/exponent-lattices/#invariance-and-the-depth-lemma) gives $\gamma_1, \ldots, \gamma_m \in \Gamma'$ and $\upsilon$ such that the operator $D = p^{c_a(n)} + \upsilon\sum_l(\gamma_l - 1)/\delta$ takes a value that is constant modulo $\mathrm{Fil}^n$ to one that is constant modulo $\mathrm{Fil}^{n+1}$. Let $B = p^{c_a(n)} + \sum_l(\text{depth operator for }\gamma_l, \upsilon)$. By the lemma, $Bx - p^{c_a(n)}x$ lies in $N_{\mathrm{loc}} \cap K_i(o)$ for $x$ deep for $o$, so $B$ has cost $c_a(n)$. For the second claim, the value of $x$ is $\Gamma'$-invariant modulo $\mathrm{Fil}^n$, hence a constant of $K'$ modulo $\mathrm{Fil}^n$ by the almost-invariant lemma. So $v_a(\mu, Dx)$ is a constant $\kappa$ modulo $\mathrm{Fil}^{n+1}$. Now $Bx$ is the retraction of $Dx$, and the retraction keeps a value that is constant modulo $\mathrm{Fil}^{n+1}$ ([Section 3](/chapter/exponent-lattices/#lattices-with-prescribed-orders)). A value that is a constant modulo $\mathrm{Fil}^{n+1}$ has $g$-differences in $\mathrm{Fil}^{n+1}$. $\square$

**Theorem (Many steps).** Let $I$ be a finite set of pairs $(a, n)$. There is an operator $A$ of cost $\sum_{(a,n) \in I}c_a(n)$ with this property: if $x$ is deep for $o$ at $i$, and $I$ contains every $(a, n)$ with $o(a, u) \leq n < o'(a, u)$ for some jump $u$ at $i^{(-a)}$, then $Ax$ is deep for $o'$ at $i$.

Lean: `New.Lift.KummerChart.PairingSide.exists_isOperatorOfCost_and_mem_deepElements` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* Induct on $I$. For $I = \emptyset$ take the identity; then $o' \leq o$ on every jump, and $L_i(o) \subseteq L_i(o')$. Otherwise remove a pair $(a, n)$ with $n$ largest, and let $A$ be the operator for the rest. Let $o_{\mathrm{low}}$ equal $o'$, except that $o_{\mathrm{low}}(a, u) = n$ where $o'(a, u) = n + 1$. The rest of $I$ covers the passage from $o$ to $o_{\mathrm{low}}$: a missing pair could only be $(a, n)$, and then $(a, n+1)$ would lie in the rest, against the choice of $n$. So $Ax$ is deep for $o_{\mathrm{low}}$. Let $B$ be the operator of the last theorem for $(a, n)$. It keeps the depth $o_{\mathrm{low}}$, and it raises the lines with $o'(a,u) = n + 1$ from $n$ to $n + 1$. By the gap rule, depth $o'$ follows. Costs add by the composition rule. $\square$

**Corollary (Deeper points).** Let $x$ be a point over $c$ with exponent $e$, orders $o$ and depth $o'$. Let $I$ cover the passage from $o'$ to $o''$ as in the theorem, and let $e + \sum_I c_a(n) \leq e'$. Then there is a point over $c$ with exponent $e'$, orders $\mathrm{imp}(o, o'')$ and depth $o''$.

Lean: `New.Lift.KummerChart.PairingSide.pointsOver_nonempty_of_costs` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* Let $s$ be the slack and $y = p^sx$. Then $y$ is deep for $o$ and for $o'$. Apply the operator $A$ of the theorem. $Ay$ is deep for $o''$. As $y$ is deep for $o$ and $y \in L_i(o)$, $Ay - p^{\sum c}y \in L_i(o)$, so $Ay \in L_i(o)$. By the improvement lemma of [Section 4](/chapter/exponent-lattices/#invariance-and-the-depth-lemma), $Ay$ has the orders $\mathrm{imp}(o, o'')$. Its projection equals that of $p^{\sum c}y$, which is $p^{e'}$ times the constant. $\square$

### Moving points

**Lemma.** (1) If $x$ is a point over $c$ with orders $o_1$ and depth $o$, then $(gx - x)/\delta \in K_i(o)$ for $g \in \Gamma'$. (2) If $x$ and $w$ are points over $c$ with the same exponent and orders $o_1$ and $o_2$, then $w - x \in K_i(\min(o_1, o_2))$.

Lean: `New.Lift.KummerChart.PairingSide.zTauUnit_inv_smul_sub_mem_kerWithOrders`, `New.Lift.KummerChart.PairingSide.sub_mem_kerWithOrders_of_pointsOver` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* (1) Division by $\delta$ keeps $L_i(o)$, and $g$ fixes the constant. (2) Both lie in $L_i(\min(o_1, o_2))$, and they have the same projection. $\square$

**Proposition (Frobenius moves points).** If $w$ is a point at the letter $i^{(-l)}$ over $c$ with exponent $e$, orders $o$ and depth $o'$, then $\varphi^lw$ is a point at $i$ over $c$ with exponent $e$, orders $\mathrm{sh}_l(0, o)$ and depth $\mathrm{sh}_l(1, o')$.

Lean: `New.Lift.KummerChart.PairingSide.phi_pow_smul_mem_pointsOver` (New/Congruences/Lifting/SidePoints.lean).

*Proof.* $\varphi^l$ keeps $N_{\mathrm{loc}}$, moves the constant at $i^{(-l)}$ to the constant at $i$, and shifts the orders by [Section 5](/chapter/exponent-lattices/#hodge-expansions). For the depth, $g\varphi^lw - \varphi^lw = \varphi^l(\delta)\cdot\varphi^l((gw - w)/\delta)$. By (1) and the shift, the second factor has the orders $\mathrm{sh}_l(0, o')$. At a level $a < l$, $p_a$ divides $\varphi^l(\tau)$, so the image of $\varphi^l(\delta)$ at level $a$ lies in $\mathrm{Fil}^1$. This raises the order $0$ to $1$ at the levels below $l$. $\square$

**Example (The model case).** For the side with $Y = \mathbb{Z}_p(1)$, $C = \mathbb{Z}_p$ and the Kummer cocycle of a unit, the jumps are in $\{-1, 0\}$ and $e = 1$. With $\omega = 0$ and $p \geq 2$, the small-jumps theorem of [Section 7](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers) applies, and the first theorem gives a point over $c$ with exponent $0$ and orders $\rho_0$, the standard orders of level $0$.
