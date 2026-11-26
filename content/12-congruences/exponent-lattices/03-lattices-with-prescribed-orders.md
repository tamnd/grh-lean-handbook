---
title: Lattices with prescribed orders
lean:
  - New/Congruences/Lifting/ExponentLattices.lean
decls: [New.Lift.KummerChart.JumpLattice.withOrders, New.Lift.KummerChart.JumpLattice.stdOrdersPart, New.Lift.KummerChart.JumpLattice.mem_withOrders_iff, New.Lift.KummerChart.JumpLattice.mem_withOrders_of_mem_hodgeFil, New.Lift.KummerChart.JumpLattice.mem_withOrders_of_le, New.Lift.KummerChart.JumpLattice.valueAt_mem_hodgeFil_of_mem_ainfLattice, New.Lift.KummerChart.JumpLattice.Hom.wittMap_mem_withOrders, New.Lift.KummerChart.JumpLattice.mem_withOrders_of_smul, New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_withOrders_add, New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_withOrders_add_iff, New.Lift.KummerChart.JumpLattice.prod_frobEUnit_zpow_smul_mem_withOrders_add_iff, New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_kisinLoc_iff, New.Lift.KummerChart.JumpLattice.kisinLoc_induction, New.Lift.KummerChart.JumpLattice.smul_sub_mem_withOrders, New.Lift.KummerChart.JumpLattice.galMonoid_smul_mem_kisinLocAinf, New.Lift.KummerChart.JumpLattice.exists_zTau_smul_eq_smul_sub, New.Lift.KummerChart.JumpLattice.zTauUnit_inv_smul_sub_mem_kisinLocAinf, New.Lift.KummerChart.JumpLattice.zTauUnit_inv_smul_sub_mem_withOrders, New.Lift.KummerChart.JumpLattice.phi_pow_smul_mem_kisinLoc, New.Lift.KummerChart.JumpLattice.span_kisinLoc, New.Lift.KummerChart.JumpLattice.sum_map_smul_eq_zero_of_mem_kisinLoc, New.Lift.KummerChart.JumpLattice.valueAt_mem_valueField, New.Lift.KummerChart.JumpLattice.exists_coordRetract, New.Lift.KummerChart.JumpLattice.coordRetract, New.Lift.KummerChart.JumpLattice.coordRetract_smul, New.Lift.KummerChart.JumpLattice.coordRetract_of_mem_kisinLoc, New.Lift.KummerChart.JumpLattice.Hom.wittMap_coordRetract, New.Lift.KummerChart.JumpLattice.valueAt_mem_of_hodgeFil_le]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lattices with prescribed orders

Fix a jump lattice $L$ over the Kummer chart. Let $\mathcal{A} = W(C^\flat) \otimes L$ be its ambient module, $M$ its module of the frame theorem, $N_{\mathrm{loc}}$ the Kisin module with all $p_a$ inverted, and $A_{\inf}N_{\mathrm{loc}}$ the set of $x$ such that a product of the $p_a$ sends $x$ into $M$. For a letter $i$, $\mathcal{A}_i$ is the part of $\mathcal{A}$ at $i$. Write $v_a(\mu, x) = \mu(\varphi^{-a}x)$ for the value at $p_a$.

**Definition (Orders).** Let $i$ be a letter and $c : \mathbb{N} \times \mathbb{Z} \to \mathbb{Z}$. The module $L_i(c)$ is the set of $x \in A_{\inf}N_{\mathrm{loc}} \cap \mathcal{A}_i$ such that $v_a(\mu, x) \in \mathrm{Fil}^{c(a,u)}$ for every $a \geq 0$, every jump $u \in J_{i^{(-a)}}$ and every form $\mu$ of type $u$ at $i^{(-a)}$. Such an $x$ has *orders $c$ at $i$*. The *standard orders* at level $l$ are $c_l^{\mathrm{std}}(a, u) = 0$ for $a < l$ and $-u$ for $a \geq l$. The set $N_{\mathrm{loc}} \cap L_i(c_l^{\mathrm{std}})$ is the *standard part*.

Lean: `New.Lift.KummerChart.JumpLattice.withOrders`, `New.Lift.KummerChart.JumpLattice.stdOrdersPart` (New/Congruences/Lifting/ExponentLattices.lean). The unfolding is `New.Lift.KummerChart.JumpLattice.mem_withOrders_iff`.

$L_i(c)$ is an $A_{\inf}$-submodule, since the image of $A_{\inf}$ lies in $\mathrm{Fil}^0$. The condition is only on jumps $u$. A form whose type is not a jump is handled by the gap rule below.

**Lemma (Raising and lowering).** (1) Let $x \in L_i(c)$, and suppose $v_a(\mu, x) \in \mathrm{Fil}^{c'(a,u)}$ for all jumps $u$ with $c(a,u) < c'(a,u)$ and all forms $\mu$ of type $u$. Then $x \in L_i(c')$. (2) If $c' \leq c$ on the jumps, then $L_i(c) \subseteq L_i(c')$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_withOrders_of_mem_hodgeFil`, `New.Lift.KummerChart.JumpLattice.mem_withOrders_of_le` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* (1) Where $c' \leq c$, the filtration is decreasing, so $\mathrm{Fil}^{c} \subseteq \mathrm{Fil}^{c'}$. Elsewhere the hypothesis applies. (2) is (1) with no place where $c < c'$. $\square$

**Lemma.** Let $x \in A_{\inf} \otimes L$ lie in $\mathcal{A}_i$, and let $\mu$ be of type $u$ at $i^{(-a)}$. Then $v_a(\mu, x) \in \mathrm{Fil}^{-u}$.

Lean: `New.Lift.KummerChart.JumpLattice.valueAt_mem_hodgeFil_of_mem_ainfLattice` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* $\varphi^{-a}x$ lies in $A_{\inf} \otimes L$ and in the part at $i^{(-a)}$, so it equals its projection to that letter. The type condition says that $\mu$ sends the projection of each $1 \otimes t$ into $\mathrm{Fil}^{-u}$. This extends to the $A_{\inf}$-span. $\square$

### The gap rule

**Lemma (The gap rule).** Let $x \in L_i(c)$, $j = i^{(-a)}$, $\mu$ a form of type $u$ at $j$, and $W$ a $B_{\mathrm{dR}}^+$-submodule of $B_{\mathrm{dR}}$. Suppose that $\mathrm{Fil}^{c(a,v)} \subseteq W$ for every jump $v \in J_j$ with $v \leq u$. Then $v_a(\mu, x) \in W$.

Lean: `New.Lift.KummerChart.JumpLattice.valueAt_mem_of_hodgeFil_le` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Suppose $v_a(\mu, x) \notin W$. First, $\mu$ is of type $v$ for every $v \leq u$. This holds for $v = u$. Let it hold for $v$. If $v$ is a jump, then $v_a(\mu,x) \in \mathrm{Fil}^{c(a,v)} \subseteq W$, which is false. So $v \notin J_j$, and by the corollary on forms of a type ([jump lattices and Kisin modules](/chapter/kisin-frames/#jump-lattices-and-kisin-modules)) $\mu$ is of type $v - 1$.

Some $r \neq 0$ in $A_{\inf}$ sends $x$ into $A_{\inf} \otimes L$, since elements of $A_{\inf}N_{\mathrm{loc}}$ have this property. By the last lemma applied with every type $v \leq u$, $v_a(\mu, rx) \in \mathrm{Fil}^m$ for every $m$. An element of $B_{\mathrm{dR}}^+$ divisible by every power of $t$ is $0$. So $\varphi^{-a}(r) v_a(\mu, x) = 0$. As $\varphi^{-a}(r) \neq 0$ in the field $B_{\mathrm{dR}}$, $v_a(\mu, x) = 0 \in W$. This contradicts the hypothesis. $\square$

So a value at a form whose type falls in a gap between jumps is controlled by the order at the next jump below.

### Maps, saturation and twists

**Lemma (Functoriality).** Let $F : L \to L'$ be a map of jump lattices with $J'_j \subseteq J_j$ for every letter $j$. Then $1 \otimes F$ maps $L_i(c)$ into $L'_i(c)$.

Lean: `New.Lift.KummerChart.JumpLattice.Hom.wittMap_mem_withOrders` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* $1 \otimes F$ keeps $A_{\inf}N_{\mathrm{loc}}$ and commutes with the projections to the letters. For a form $\mu$ of type $u$ on $L'$, the composite $\mu \circ (1 \otimes F)$ is a form of type $u$ on $L$, and $u$ is a jump of $L$ when it is a jump of $L'$. $\square$

**Lemma (Saturation).** Let $r \in A_{\inf}$ be divisible by no $p_a$, let $x \in A_{\inf}N_{\mathrm{loc}}$, and let $rx \in L_i(c)$. Then $x \in L_i(c)$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_withOrders_of_smul` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* $r \neq 0$, so $x$ lies in $\mathcal{A}_i$. The value of $rx$ is $\varphi^{-a}(r)v_a(\mu,x)$. Since $p_a \nmid r$, $\varphi^{-a}(r)$ is not in $\mathrm{Fil}^1$, so it is a unit of $B_{\mathrm{dR}}^+$. Multiplication by it does not change the order. $\square$

**Lemma (Twists by $p_b$).** Let $x \in \mathcal{A}$, $b \geq 0$ and $m \in \mathbb{Z}$. Then $p_b^m x$ has the orders $c(a,u) + [a = b]m$ at $i$ if and only if $x$ has the orders $c$ at $i$. The same holds for a finite product $\prod_{b \in s} p_b^{r_b}$, with the orders raised by $r_a$ for $a \in s$. Also $p_b^m x \in N_{\mathrm{loc}}$ if and only if $x \in N_{\mathrm{loc}}$.

Lean: `New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_withOrders_add_iff`, `New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_withOrders_add`, `New.Lift.KummerChart.JumpLattice.prod_frobEUnit_zpow_smul_mem_withOrders_add_iff`, `New.Lift.KummerChart.JumpLattice.frobEUnit_zpow_smul_mem_kisinLoc_iff` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* The module $A_{\inf}N_{\mathrm{loc}}$ is a saturation by the $p_b$, so $p_b$ and $p_b^{-1}$ keep it. The value of $p_b^m x$ at $p_a$ is $\varphi^{-a}(p_b)^m v_a(\mu,x)$. For $a = b$, $\varphi^{-b}(p_b)$ has order exactly $1$, by the lemma on values in $B_{\mathrm{dR}}$ of [Kisin frames](/chapter/kisin-frames/#jump-lattices-and-kisin-modules). For $a \neq b$, $p_a \nmid p_b$ and the order does not change. Apply this with $-m$ for the converse, and induct on $s$ for products. The values of forms on $p_b^{\pm 1}x$ lie in the value field $\mathcal{K}_0$ when those on $x$ do, since the image of $p_b$ lies in it. $\square$

### The Galois action

**Lemma (Induction on $N_{\mathrm{loc}}$).** A property that holds on the Kisin module $N$ and passes from $p_a y$ to $y$ for $y \in N_{\mathrm{loc}}$ holds on $N_{\mathrm{loc}}$.

Lean: `New.Lift.KummerChart.JumpLattice.kisinLoc_induction` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Each $x \in N_{\mathrm{loc}}$ has a product of the $p_a$ that sends it into $M$; induct on the number of factors. $\square$

**Lemma.** For $g \in \Gamma'$, $g$ keeps $A_{\inf}N_{\mathrm{loc}}$, and $g$ keeps $L_i(c)$; so $gx - x \in L_i(c)$ for $x \in L_i(c)$.

Lean: `New.Lift.KummerChart.JumpLattice.galMonoid_smul_mem_kisinLocAinf`, `New.Lift.KummerChart.JumpLattice.smul_sub_mem_withOrders` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* $g$ keeps $M$, and $g p_a$ is associated to $p_a$. The forms are equivariant and $g$ keeps each $\mathrm{Fil}^n$, so $v_a(\mu, gx) = g\,v_a(\mu, x)$. $\square$

**Lemma.** Let $x \in N$ and $g \in \Gamma'$. Then $gx - x = \delta y$ for some $y \in M$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_zTau_smul_eq_smul_sub` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Divisibility by $\delta$ in $M$ is tested with crystalline forms, by the criteria of [the frame theorem](/chapter/kisin-frames/#the-frame-theorem). For a crystalline form $\mu$, $E^n\mu(x)$ lies in the ring $S_B$ for some $n$. Every element $\gamma \in \Gamma'$ moves an element of $S_B$ by a multiple of $\delta$. So $E^{2n}(\mu(gx) - \mu(x)) = E^{2n}(\gamma\mu(x) - \mu(x))$ lies in $\delta$ times the span, and the factor $E^{2n}$ cancels. $\square$

**Proposition (Triviality modulo $\delta$).** Let $x \in N_{\mathrm{loc}}$ and $g \in \Gamma'$. Then $\delta^{-1}(gx - x) \in A_{\inf}N_{\mathrm{loc}}$. If also $gx - x \in L_i(c)$, then $\delta^{-1}(gx - x) \in L_i(c)$.

Lean: `New.Lift.KummerChart.JumpLattice.zTauUnit_inv_smul_sub_mem_kisinLocAinf`, `New.Lift.KummerChart.JumpLattice.zTauUnit_inv_smul_sub_mem_withOrders` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Use the induction on $N_{\mathrm{loc}}$. On $N$ the last lemma applies. For the step, write $g p_a - p_a = \delta E r$. Then

$$\delta^{-1}\bigl(g(p_a y) - p_a y\bigr) = p_a\,\delta^{-1}(gy - y) + E r\, gy.$$

The last term lies in $A_{\inf}N_{\mathrm{loc}}$. So the left side lies in it if and only if $p_a \delta^{-1}(gy - y)$ does, and $p_a$ cancels there. For the second claim, no $p_a$ divides $\delta$, and saturation applies to $\delta \cdot \delta^{-1}(gx - x)$. $\square$

The source calls the first claim "a form of the known triviality of the Galois action on Kisin modules modulo the variable".

### Frobenius and the retraction

**Lemma.** (1) $\varphi^l$ keeps $N_{\mathrm{loc}}$. (2) The $A_{\inf}$-span of $N_{\mathrm{loc}}$ is $A_{\inf}N_{\mathrm{loc}}$. (3) Let $f : A_{\inf} \to S$ be $S$-linear, $v_j \in N_{\mathrm{loc}}$ and $b_j \in A_{\inf}$ finitely many, with $\sum b_j v_j = 0$. Then $\sum f(b_j) v_j = 0$. (4) For $x \in N_{\mathrm{loc}}$ and a form $\mu$, $v_a(\mu, x) \in \mathcal{K}_a$.

Lean: `New.Lift.KummerChart.JumpLattice.phi_pow_smul_mem_kisinLoc`, `New.Lift.KummerChart.JumpLattice.span_kisinLoc`, `New.Lift.KummerChart.JumpLattice.sum_map_smul_eq_zero_of_mem_kisinLoc`, `New.Lift.KummerChart.JumpLattice.valueAt_mem_valueField` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* (1) $E^h\varphi$ keeps $N$ by the frame theorem, with $h$ the jump bound, and $\varphi(p_a y) = p_{a+1}\varphi(y)$; the factors $E$ and $p_{a+1}$ cancel in $N_{\mathrm{loc}}$. (2) $M$ is spanned by $N$ (frame theorem), and $p_a^{-1}$ keeps $N_{\mathrm{loc}}$. (3) Clear the $p_a$ by a common product and apply the same statement of the frame theorem for points with values in $\mathcal{K}_0$. (4) Some $\rho \neq 0$ gives a relation $\rho x = \sum \varphi^a(t_l)\varphi^a(v_l)$ with $v_l \in N_{\mathrm{loc}}$. A coordinate $f$ with $f(\rho) \neq 0$ turns it into a relation over $S$, which one solves for $v_a(\mu,x)$ in $\mathcal{K}_a$. $\square$

The chart has a chosen topological $S$-basis of $A_{\inf}$. Its coordinate $\lambda_0 : A_{\inf} \to S$ at the basis element $1$ is $S$-linear and is the identity on $S$.

**Proposition (The retraction).** There is an $S$-linear map $r : A_{\inf}N_{\mathrm{loc}} \to N_{\mathrm{loc}}$ with $r(bx) = \lambda_0(b)x$ for $b \in A_{\inf}$ and $x \in N_{\mathrm{loc}}$. The source fixes one such map. It is the identity on $N_{\mathrm{loc}}$, and it commutes with $1 \otimes F$ for every map $F$ of jump lattices.

Lean: `New.Lift.KummerChart.JumpLattice.exists_coordRetract`, `New.Lift.KummerChart.JumpLattice.coordRetract`, `New.Lift.KummerChart.JumpLattice.coordRetract_smul`, `New.Lift.KummerChart.JumpLattice.coordRetract_of_mem_kisinLoc`, `New.Lift.KummerChart.JumpLattice.Hom.wittMap_coordRetract` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Let $\pi : A_{\inf} \otimes_S N_{\mathrm{loc}} \to A_{\inf}N_{\mathrm{loc}}$ be $b \otimes x \mapsto bx$. It is onto by (2). Let $\ell(b \otimes x) = \lambda_0(b)x$. An element $\sum b_j \otimes v_j$ of the kernel of $\pi$ has $\sum b_j v_j = 0$, so $\ell$ of it is $0$ by (3) with $f = \lambda_0$. So $\ell$ factors through $\pi$. Since $\lambda_0(1) = 1$, $r(x) = x$ on $N_{\mathrm{loc}}$. For $F$, compute both sides on an expansion $y = \sum b_j v_j$ and on its image $\sum b_j F(v_j)$. $\square$

**Remark (Formalization).** The retraction is `coordRetract := L.exists_coordRetract.choose`. Only the property $r(bx) = \lambda_0(b)x$ is used, and it determines $r$ on all of $A_{\inf}N_{\mathrm{loc}}$, since this module is spanned by products $bx$. So the choice does not matter. The map depends on the chosen basis of $A_{\inf}$ over $S$ through $\lambda_0$.
