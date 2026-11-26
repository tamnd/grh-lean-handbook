---
title: Hodge expansions
lean:
  - New/Congruences/Lifting/HodgeExpansion.lean
decls: [New.Lift.KummerChart.JumpLattice.shiftedOrders, New.Lift.KummerChart.JumpLattice.apply_phi_pow_succ_smul_mem_hodgeFil_zero, New.Lift.KummerChart.JumpLattice.phi_pow_smul_mem_withOrders, New.Lift.KummerChart.JumpLattice.apply_mem_hodgeFil_of_forall_formsOfType, New.Lift.KummerChart.JumpLattice.coordRetract_mem_withOrders, New.Lift.KummerChart.JumpLattice.smul_mem_ainfLattice_of_frobE_smul_mem, New.Lift.KummerChart.JumpLattice.mem_saturateBy_powers_of_mem_withOrders, New.Lift.KummerChart.JumpLattice.mem_withOrders_stdOrders_iff, New.Lift.KummerChart.JumpLattice.mem_stdOrdersPart_iff, New.Lift.KummerChart.JumpLattice.prod_frobEUnit_zpow_smul_mem_kisinLoc_and_withOrders_iff, New.Lift.KummerChart.JumpLattice.letterProj_mem_stdOrdersPart, New.Lift.KummerChart.JumpLattice.frobEUnit_pow_smul_mem_frobKisinAinf_one, New.Lift.KummerChart.JumpLattice.wittPairing, New.Lift.KummerChart.JumpLattice.IsEquivariantPairing, New.Lift.KummerChart.JumpLattice.wittPairing_mem_kisinAinf, New.Lift.KummerChart.JumpLattice.wittPairing_mem_withOrders, New.Lift.KummerChart.JumpLattice.raiseOrder, New.Lift.KummerChart.JumpLattice.raiseOrdersAt, New.Lift.KummerChart.JumpLattice.exists_thetaBdR_sub_sum_smul_eq_zero, New.Lift.KummerChart.JumpLattice.exists_sub_sum_smul_mem_withOrders_raiseOrder, New.Lift.KummerChart.JumpLattice.exists_eq_one_and_sum_smul_eq_zero, New.Lift.KummerChart.JumpLattice.exists_sub_smul_one_eq_E_mul, New.Lift.KummerChart.JumpLattice.exists_sum_smul_mem_locKisinPart_sup]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hodge expansions

This section has three results. The lattice with the standard orders is the Frobenius twist $\varphi^l(M)$. Orders add under pairings. Among $fn + 1$ points one finds a primitive combination that gains one step. The source calls an order system an *exponent* system, and the family $a \mapsto o(a, u)$ the *line* $u$.

### Frobenius shifts orders

**Definition.** For $l \in \mathbb{N}$, $n \in \mathbb{Z}$ and an order system $c$, the *shifted orders* are $\mathrm{sh}_l(n, c)(a, u) = n$ for $a < l$ and $c(a - l, u)$ for $a \geq l$.

Lean: `New.Lift.KummerChart.JumpLattice.shiftedOrders` (New/Congruences/Lifting/HodgeExpansion.lean).

So the standard orders are $c_l^{\mathrm{std}} = \mathrm{sh}_l(0, -u)$, where $-u$ is the system $(a,u) \mapsto -u$.

**Lemma.** Let $\mu$ be a form, $x \in A_{\inf}N_{\mathrm{loc}}$ and $m \geq 0$. Then $\mu(\varphi^{m+1}x) \in \mathrm{Fil}^0$.

Lean: `New.Lift.KummerChart.JumpLattice.apply_phi_pow_succ_smul_mem_hodgeFil_zero` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* For $x \in M$ this is the definition of $M$. If $p_j x \in M$, then $\varphi^{m+1}(p_j x) = p_{m+1+j}\varphi^{m+1}x$, and $E = p_0$ does not divide $p_{m+1+j}$. So the image of $\varphi^{-0}(p_{m+1+j})$ in $B_{\mathrm{dR}}^+$ is a unit, and it cancels. $\square$

**Proposition (Frobenius shifts orders).** If $x \in L_{i^{(-l)}}(c)$, then $\varphi^l x \in L_i(\mathrm{sh}_l(0, c))$.

Lean: `New.Lift.KummerChart.JumpLattice.phi_pow_smul_mem_withOrders` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* $\varphi^l$ keeps $N_{\mathrm{loc}}$, so it keeps its span $A_{\inf}N_{\mathrm{loc}}$. It moves the part at $i^{(-l)}$ to the part at $i$. The value of $\varphi^l x$ at level $a$ is $\mu(\varphi^{l-a}x)$. If $l = a + m + 1$, this lies in $\mathrm{Fil}^0$ by the lemma. If $a = l + m$, it is the value of $x$ at level $m$, at the letter $(i^{(-l)})^{(-m)} = i^{(-a)}$, and it lies in $\mathrm{Fil}^{c(m,u)}$. $\square$

### Hodge bases

A form need not be of a type at a letter. A Hodge basis reduces all forms to forms of a type. Let $D$ be a $B_{\mathrm{dR}}$-linear map from functionals to $B_{\mathrm{dR}}$. It *shifts the filtration by $\kappa$* if $D\mu \in \mathrm{Fil}^{m+\kappa}$ whenever $\mu(1 \otimes L) \subseteq \mathrm{Fil}^m$. It *respects the Galois action* if $D\mu_2 = g\,D\mu_1$ whenever $\mu_2(1 \otimes gt) = g\,\mu_1(1 \otimes t)$ for all $t$.

**Lemma (Expansion in a Hodge basis).** Let $x$ lie in the span of $1 \otimes L$ over the fractions of $W(C^\flat)$, let $\mu$ be any $A_{\inf}$-linear functional and $n \in \mathbb{Z}$. Suppose $D\mu \cdot \nu(x) \in \mathrm{Fil}^n$ for every $\kappa$, every form $\nu$ of type $\kappa$ at $i$, and every $D$ that shifts the filtration by $\kappa$ and respects the Galois action. Then $\mu(x) \in \mathrm{Fil}^n$.

Lean: `New.Lift.KummerChart.JumpLattice.apply_mem_hodgeFil_of_forall_formsOfType` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* Take an invariant Hodge basis $P \cdot \mathrm{diag}(t^{\kappa_m})$ with $P$ invertible over $B_{\mathrm{dR}}^+$ ([Hodge-Tate jumps](/chapter/period-rings/)). Its dual forms $\nu_m$ are equivariant and of type $\kappa_m$, and $\mu(x) = \sum_m D_m\mu \cdot \nu_m(x)$, where $D_m$ pairs the values of $\mu$ with column $m$ of the basis. Column $m$ is divisible by $t^{\kappa_m}$, so $D_m$ shifts by $\kappa_m$. Each term lies in $\mathrm{Fil}^n$. $\square$

**Lemma.** If $y \in A_{\inf}N_{\mathrm{loc}}$ has orders $c$ at $i$, so does its retraction $r(y)$.

Lean: `New.Lift.KummerChart.JumpLattice.coordRetract_mem_withOrders` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* Write $y = \sum b_j w_j$ with $w_j \in N_{\mathrm{loc}}$, so $r(y) = \sum \lambda_0(b_j)w_j$. The values $v_a(\mu, w_j)$ lie in $\mathcal{K}_a$. A lemma of Volume 7 on sums $\sum \varphi^{-a}(f(b_j)) y_j$ with $y_j \in \mathcal{K}_a$ shows that if $\sum \varphi^{-a}(b_j)y_j \in \mathrm{Fil}^n$, then so is the sum with $\lambda_0(b_j)$. The letter part is kept, as $r$ is $S$-linear and $\Lambda \subseteq S$. $\square$

### The standard lattice

**Lemma.** Let $x \in L_i(c_l^{\mathrm{std}})$. (1) If $l \leq a$ and $r p_a x \in A_{\inf} \otimes L$ for some $r \in A_{\inf}$, then $rx \in A_{\inf} \otimes L$. (2) Some power of $\varphi^l(\tau)$ sends $x$ into $A_{\inf} \otimes L$.

Lean: `New.Lift.KummerChart.JumpLattice.smul_mem_ainfLattice_of_frobE_smul_mem`, `New.Lift.KummerChart.JumpLattice.mem_saturateBy_powers_of_mem_withOrders` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* (1) Take a $\mathbb{Z}_p$-basis $e_s$ of $L$. It is enough that $p_a$ divides each coordinate of $r p_a x$. Extend the coordinate functional to $\mu_s$. In a Hodge basis, a term of jump $\kappa$ is a coefficient of order at least $\kappa$ times a value of $x$ of order at least $-\kappa$, since $a \geq l$. So $\varphi^{-a}$ of the coordinate is $\varphi^{-a}(p_a r)$ times an element of $B_{\mathrm{dR}}^+$, which lies in $\mathrm{Fil}^1$. That is divisibility by $p_a$. (2) Induct on the number of factors $p_a$ that bring $x$ into $M$. With none, $x \in M$, the frame theorem gives $\tau^h x \in A_{\inf} \otimes L$, and $\tau \mid \varphi^l(\tau)$. For one more factor $p_a$: if $a \geq l$, use (1); if $a < l$, then $p_a$ divides $\varphi^l(\tau)$, and one more power of $\varphi^l(\tau)$ absorbs it. $\square$

**Theorem (Standard orders).** $x \in L_i(c_l^{\mathrm{std}})$ if and only if $x \in \varphi^l(M)$ and $x \in \mathcal{A}_i$. Hence $x$ is in the standard part $N_{\mathrm{loc}} \cap L_i(c_l^{\mathrm{std}})$ if and only if $x \in \varphi^l(M) \cap \mathcal{A}_i$ and all forms take values in $\mathcal{K}_0$ on $x$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_withOrders_stdOrders_iff`, `New.Lift.KummerChart.JumpLattice.mem_stdOrdersPart_iff` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* Write the element as $\varphi^l x$. The claim is: $\varphi^l x \in L_i(c_l^{\mathrm{std}})$ if and only if $x \in M \cap \mathcal{A}_{i^{(-l)}}$.

Forward. By (2) of the lemma, $\varphi^l(\tau)^n\varphi^l x \in A_{\inf} \otimes L$; apply $\varphi^{-l}$ to get $\tau^n x \in A_{\inf} \otimes L$. For the values, let $z = \varphi^{n+1}\varphi^l x$. By the proposition, $z$ has orders $\mathrm{sh}_{n+1}(0, c_l^{\mathrm{std}})$, so its orders at level $l$ are at least $0$ on every jump. For a form $\mu$, apply the expansion in a Hodge basis. Each coefficient $D\mu$ is fixed by $\Gamma'$, hence lies in $\mathrm{Fil}^0$. Each $\nu(\varphi^{-l} z)$ lies in $\mathrm{Fil}^0$ by the gap rule. So $\mu(\varphi^{n+1}x) \in \mathrm{Fil}^0$. The letter is clear.

Converse. Let $x \in M \cap \mathcal{A}_{i^{(-l)}}$. Then $\tau^n x \in A_{\inf} \otimes L$, and its values at a form of type $u$ lie in $\mathrm{Fil}^{-u}$. The element $\tau$ is prime to every $p_a$ (as $p_a \nmid \delta$), so the values of $x$ lie in $\mathrm{Fil}^{-u}$ too. So $x$ has the orders $-u$, and by the proposition $\varphi^l x$ has the orders $\mathrm{sh}_l(0, -u) = c_l^{\mathrm{std}}$. $\square$

**Corollary.** (1) For a product $F = \prod_{b \in s}p_b^{r_b}$, $Fx \in N_{\mathrm{loc}}$ with the orders $r_a$ at levels $a < l$ and $r_a - u$ at levels $a \geq l$ if and only if $x \in \mathcal{A}_i$ and $x$ lies in the $S$-span of $\varphi^l(N)$. (2) If $x \in \varphi^l(M)$ has values in $\mathcal{K}_0$, its projection to the letter $i$ is in the standard part at $i$. (3) If every jump at every letter is at most $n$, then $E^n M \subseteq \varphi(M)$.

Lean: `New.Lift.KummerChart.JumpLattice.prod_frobEUnit_zpow_smul_mem_kisinLoc_and_withOrders_iff`, `New.Lift.KummerChart.JumpLattice.letterProj_mem_stdOrdersPart`, `New.Lift.KummerChart.JumpLattice.frobEUnit_pow_smul_mem_frobKisinAinf_one` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* (1) Combine the theorem with the twists by $p_b$ and with the statement of Volume 7 that the points of $\varphi^l(M)$ with values in $\mathcal{K}_0$ are the $S$-span of $\varphi^l(N)$. (2) The projection is an average of powers of multiplication by $\omega(i)^{-1}\zeta$, and $\zeta$ keeps $\varphi^l(M)$. (3) Split $x \in M$ into letter parts. Each has the orders $-u$ at every level. Multiplication by $E^n$ raises the order at level $0$ to $n - u \geq 0$, which is the standard order at level $0$ for $l = 1$, and keeps the others. The theorem with $l = 1$ applies. $\square$

**Example (The model case).** For $L = \mathbb{Z}_p$ with jump $0$, $M = A_{\inf}$, and the theorem says that $r \otimes 1$ has order $0$ at every level if and only if $r \in \varphi^l(A_{\inf}) = A_{\inf}$. Part (3) with $n = 0$ is $M = \varphi(M)$.

### Orders add

For lattices $A$, $L$, $C$ and an $\mathcal{O}$-bilinear map $b : A \times L \to C$, let $b_W$ be its $W(C^\flat)$-bilinear extension. The map $b$ is *equivariant* if $b(gy, gx) = g\,b(y, x)$ for $g \in \Gamma$.

**Proposition (Orders add).** Let $b$ be equivariant. Then $b_W$ maps $M_A \times M_L$ into $M_C$. If $y \in A_i(c')$ and $x \in L_i(c)$, then $b_W(y, x) \in C_i(c'')$, provided $c''(a, v) \leq c(a, u') + c'(a, u)$ for all $a$ and all jumps $u$ of $A$, $u'$ of $L$ and $v$ of $C$ at $i^{(-a)}$ with $u + u' \leq v$.

Lean: `New.Lift.KummerChart.JumpLattice.wittPairing`, `New.Lift.KummerChart.JumpLattice.IsEquivariantPairing`, `New.Lift.KummerChart.JumpLattice.wittPairing_mem_kisinAinf`, `New.Lift.KummerChart.JumpLattice.wittPairing_mem_withOrders` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* Saturations pair into saturations, and the letter projection moves from the first argument to the value. For a form $\eta$ of type $v$ on $C$, expand the second argument in a Hodge basis of $L$. A coefficient map gives a form $\sigma$ on $A$. The value of $\eta$ on $b_W(y,x)$ is a sum of products $\sigma(y)\nu(x)$, with $\nu$ of type $\kappa$ on $L$ and $\sigma$ of type $v - \kappa$ on $A$. By the gap rule, $\nu(x)$ lies in $\mathrm{Fil}^{c(a,u')}$ for some jump $u' \leq \kappa$, and $\sigma(y)$ in $\mathrm{Fil}^{c'(a,u)}$ for some jump $u \leq v - \kappa$. Then $u + u' \leq v$, and the hypothesis applies. $\square$

### One step on one line

**Definition.** For an order system $o$, $\mathrm{raise}_{a,u}(o)$ raises the single value $o(a,u)$ by $1$, and $\mathrm{raise}_a(o)$ raises all values $o(a, v)$ at level $a$ by $1$.

Lean: `New.Lift.KummerChart.JumpLattice.raiseOrder`, `New.Lift.KummerChart.JumpLattice.raiseOrdersAt` (New/Congruences/Lifting/HodgeExpansion.lean).

**Lemma.** (1) Let $t$ be an $N \times r$ matrix over $B_{\mathrm{dR}}^+$. There are $d \leq r$ rows $s_1, \ldots, s_d$ and $A \in A_{\inf}^{N \times d}$ with $\theta(t_j - \sum_m A_{jm} t_{s_m}) = 0$ for every row $j$. (2) For $d \leq n$, any $fn + 1$ vectors in $W(\mathbb{F}_q)^d$ have a $\mathbb{Z}_p$-relation with one coefficient $1$. (3) If the chart is unramified, every $s \in S$ is $w + Ey$ with $w \in \Lambda$ and $y \in S$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_thetaBdR_sub_sum_smul_eq_zero`, `New.Lift.KummerChart.JumpLattice.exists_eq_one_and_sum_smul_eq_zero`, `New.Lift.KummerChart.JumpLattice.exists_sub_smul_one_eq_E_mul` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* (1) Let $U \subseteq \mathbb{C}_p^N$ be the column space of $\theta(t)$, of dimension $d \leq r$. Auerbach's lemma gives a basis of $U$ with entries of norm at most $1$ whose coordinates are the entries at $d$ rows $s_m$. Lift the entries to $A_{\inf}$ by the surjectivity of $\theta$. (2) $W(\mathbb{F}_q)^d$ has rank $df \leq nf < fn+1$, so the vectors are dependent. Divide a relation by a coefficient of least valuation. (3) With $e = 1$, $s$ is congruent modulo $p_0 = E$ to a constant of $\Lambda$, by the division of [Section 2](/chapter/exponent-lattices/#costs-and-depth-steps). $\square$

**Lemma.** Let $j = l^{(-b)}$ and suppose $o(b, u) < o(b, v)$ for every jump $v < u$ at $j$. Let $x_1, \ldots, x_N \in L_l(o)$. Then there are $d$ points $x_{s_m}$, with $d$ at most the multiplicity of $u$ at $j$, and $A_{km} \in A_{\inf}$ such that $x_k - \sum_m A_{km}x_{s_m} \in L_l(\mathrm{raise}_{b,u}(o))$ for every $k$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_sub_sum_smul_mem_withOrders_raiseOrder` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* Forms $\nu_1, \ldots, \nu_r$ of type $u$ span the forms of type $u$ modulo type $u - 1$, with $r$ at most the multiplicity ([jump lattices and Kisin modules](/chapter/kisin-frames/#jump-lattices-and-kisin-modules)). By the gap rule and the hypothesis, each value $v_b(\nu_m, x_k)$ is $t^{o(b,u)}$ times some $t_{km} \in B_{\mathrm{dR}}^+$. Apply (1) and take the coefficients $\varphi^b(A_{km})$. On $x' = x_k - \sum_m \varphi^b(A_{km})x_{s_m}$ the values at $\nu_m$ are $t^{o(b,u)}$ times an element of $\ker\theta$, so they lie in $\mathrm{Fil}^{o(b,u)+1}$. A form of type $u$ is $\sum \kappa_m\nu_m$ plus a form of type $u - 1$, and the gap rule bounds the last one by the orders of the jumps below $u$, which are at least $o(b,u)+1$. $\square$

**Theorem (One step gain).** Let the chart be unramified. Let $j = l^{(-b)}$, let the multiplicity of the jump $u$ at $j$ be at most $n$, and let $o(b,u) < o(b,v)$ for every jump $v < u$ at $j$. Let $x_1, \ldots, x_{fn+1} \in N_{\mathrm{loc}} \cap L_l(o)$. Then there are $c_k \in \mathbb{Z}_p$ with $c_{k_0} = 1$ for some $k_0$ such that $\sum_k c_k x_k$ lies in $N_{\mathrm{loc}}(L_l(\mathrm{raise}_0(o))) + N_{\mathrm{loc}}(L_l(\mathrm{raise}_{b,u}(o)))$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_sum_smul_mem_locKisinPart_sup` (New/Congruences/Lifting/HodgeExpansion.lean).

*Proof.* The last lemma gives $x_k - \sum_m A_{km}x_{s_m} \in L_l(\mathrm{raise}_{b,u}(o))$ with $d \leq n$. By (3), $\lambda_0(A_{km}) = w_{km} + Ey_{km}$ with $w_{km} \in \Lambda$. By (2) there are $c_k$ with $c_{k_0} = 1$ and $\sum_k c_k w_{km} = 0$ for every $m$. Apply the retraction $r$, which is the identity on $N_{\mathrm{loc}}$:

$$x_k - \sum_m w_{km}x_{s_m} = E\sum_m y_{km}x_{s_m} + r\Bigl(x_k - \sum_m A_{km}x_{s_m}\Bigr).$$

Multiply by $c_k$ and sum. The terms with $w$ cancel. The first term on the right lies in $N_{\mathrm{loc}}$ and has the orders $\mathrm{raise}_0(o)$, by the twist by $p_0 = E$. The second lies in $N_{\mathrm{loc}}$ and has the orders $\mathrm{raise}_{b,u}(o)$, by the lemma on the retraction. $\square$
