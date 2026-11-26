---
title: Invariance and the depth lemma
lean:
  - New/Congruences/Lifting/ExponentLattices.lean
decls: [New.Lift.KummerChart.JumpLattice.locKisinPart, New.Lift.KummerChart.JumpLattice.invariantsMod, New.Lift.KummerChart.JumpLattice.cost_le_of_isUnramified, New.Lift.KummerChart.JumpLattice.improvedOrders, New.Lift.KummerChart.JumpLattice.exists_const_sub_mem_hodgeFil_of_smul_sub_mem, New.Lift.KummerChart.JumpLattice.galMonoid_smul_localFieldOf, New.Lift.KummerChart.JumpLattice.mem_invariantsMod_withOrders_iff, New.Lift.KummerChart.JumpLattice.mem_withOrders_improvedOrders, New.Lift.KummerChart.JumpLattice.smul_sub_mem_hodgeFil_one_of_mem_valueField, New.Lift.KummerChart.JumpLattice.smul_sub_phiInvToBdR_mul_mem_hodgeFil_succ, New.Lift.KummerChart.JumpLattice.depthStepOperator, New.Lift.KummerChart.JumpLattice.depthStepOperator_singleton, New.Lift.KummerChart.JumpLattice.exists_valueAt_depthStepOperator_sub_smul_mem, New.Lift.KummerChart.JumpLattice.exists_valueAt_sub_mem_hodgeFil_succ]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Invariance and the depth lemma

The orders of the last section bound the values of an element from below. The *depth* of an element says more: its value is a constant of the fixed field $K' = \bar{\mathbb{Q}}_p^{\Gamma'}$ up to a high step of the filtration. This section shows that depth is invariance under $\Gamma'$ modulo a lattice with orders, and it proves the depth lemma.

**Definition (Invariants modulo $Q$).** For an $A_{\inf}$-submodule $Q$ of $\mathcal{A}$, $\mathrm{Inv}(Q)$ is the $\mathbb{Z}_p$-module of the $x \in \mathcal{A}$ with $gx - x \in Q$ for every $g \in \Gamma'$. The $\mathbb{Z}_p$-module $N_{\mathrm{loc}}(Q)$ is the set of elements of $N_{\mathrm{loc}}$ that lie in $Q$.

Lean: `New.Lift.KummerChart.JumpLattice.invariantsMod`, `New.Lift.KummerChart.JumpLattice.locKisinPart` (New/Congruences/Lifting/ExponentLattices.lean).

**Remark (Formalization).** `invariantsMod Q` is the intersection over $g$ of the preimages of $Q$ under $g - 1$, rewritten with `.copy` so that membership unfolds to the condition above. The file also declares `instance : Module ℤ_[p] L.kisinLoc := inferInstance` before `locKisinPart`. It adds no new structure; it fixes the path by which Lean finds the $\mathbb{Z}_p$-module structure on $N_{\mathrm{loc}}$.

**Lemma.** (1) If $y \in B_{\mathrm{dR}}$ and $gy - y \in \mathrm{Fil}^n$ for every $g \in \Gamma'$, then $y - c \in \mathrm{Fil}^n$ for some $c \in K'$. (2) Every $g \in \Gamma'$ fixes the image of $K'$ in $B_{\mathrm{dR}}$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_const_sub_mem_hodgeFil_of_smul_sub_mem`, `New.Lift.KummerChart.JumpLattice.galMonoid_smul_localFieldOf` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* (1) is the statement on almost invariant elements of $B_{\mathrm{dR}}$ in [period rings](/chapter/period-rings/) (`New.Period.BdR.exists_sub_mem_of_smul_sub_mem`), applied to the subgroup $\Gamma'$. (2) The embedding of $\bar{\mathbb{Q}}_p$ in $B_{\mathrm{dR}}$ is equivariant, and $\Gamma'$ fixes $K'$. $\square$

**Proposition (Depth is invariance).** Let $x \in A_{\inf}N_{\mathrm{loc}} \cap \mathcal{A}_i$ and $o : \mathbb{N} \times \mathbb{Z} \to \mathbb{Z}$. Then $x \in \mathrm{Inv}(L_i(o))$ if and only if for every $a$, every jump $u \in J_{i^{(-a)}}$ and every form $\mu$ of type $u$ at $i^{(-a)}$ there is $c \in K'$ with $v_a(\mu, x) - c \in \mathrm{Fil}^{o(a,u)}$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_invariantsMod_withOrders_iff` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* The element $gx - x$ lies in $A_{\inf}N_{\mathrm{loc}}$ and in $\mathcal{A}_i$, by the last section. Its value is $g\,v_a(\mu,x) - v_a(\mu,x)$. If $gx - x \in L_i(o)$ for all $g$, then these differences lie in $\mathrm{Fil}^{o(a,u)}$, and part (1) of the lemma gives $c$. Conversely, if $v_a(\mu, x) - c \in \mathrm{Fil}^{o(a,u)}$, then $g(v - c) - (v - c) = gv - v$ by part (2), and it lies in $\mathrm{Fil}^{o(a,u)}$, as $g$ keeps the filtration. $\square$

The element $x$ has *depth $o$ at $i$* when the conditions hold.

### Improved orders

**Definition.** For $lo, hi : \mathbb{N} \times \mathbb{Z} \to \mathbb{Z}$, the *improved orders* are $\mathrm{imp}(lo, hi)(a,u) = \min\bigl(hi(a,u),\ \text{if } lo(a,u) > 0 \text{ then } hi(a,u) \text{ else } 0\bigr)$.

Lean: `New.Lift.KummerChart.JumpLattice.improvedOrders` (New/Congruences/Lifting/ExponentLattices.lean).

So the improved order is $hi$ where $lo > 0$, and $\min(hi, 0)$ elsewhere.

**Proposition (Invariance improves orders).** Let $x \in L_i(lo) \cap \mathrm{Inv}(L_i(hi))$. Then $x \in L_i(\mathrm{imp}(lo, hi))$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_withOrders_improvedOrders` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Fix $a$, $u$ and $\mu$, and let $v = v_a(\mu,x)$. By the proposition, $v - y \in \mathrm{Fil}^{hi}$ for a constant $y \in K'$. Also $v \in \mathrm{Fil}^{lo}$. So $y = v - (v - y) \in \mathrm{Fil}^{\min(lo, hi)}$. A nonzero element of $\bar{\mathbb{Q}}_p$ lies in $\mathrm{Fil}^0$ and not in $\mathrm{Fil}^1$. So if $\mathrm{imp}(lo,hi)(a,u) > 0$, then $\min(lo,hi) > 0$ and $y = 0$. In all cases $y \in \mathrm{Fil}^{\mathrm{imp}(lo,hi)(a,u)}$. Since $\mathrm{imp} \leq hi$, $v - y$ also lies there, and so does $v$. $\square$

**Example.** Let $lo = 1$ and $hi = 5$ at some $(a, u)$. An element with order $1$ whose value is a constant modulo $\mathrm{Fil}^5$ has order $5$: the constant must be $0$. With $lo = 0$, the constant may be nonzero, and the order stays $\min(5, 0) = 0$.

### The first-order action

**Lemma.** Let $t \in \Gamma'$ act trivially on $S$ modulo $p_a$, and let $y \in \mathcal{K}_a \cap \mathrm{Fil}^0$. Then $ty - y \in \mathrm{Fil}^1$. If also $t p_a = \omega p_a$ for a unit $\omega$ and $y \in \mathcal{K}_a \cap \mathrm{Fil}^n$, then $ty - \varphi^{-a}(\omega^n) y \in \mathrm{Fil}^{n+1}$.

Lean: `New.Lift.KummerChart.JumpLattice.smul_sub_mem_hodgeFil_one_of_mem_valueField`, `New.Lift.KummerChart.JumpLattice.smul_sub_phiInvToBdR_mul_mem_hodgeFil_succ` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* The first claim is the case of one element of a lemma of Volume 7: if $p_a$ divides $g(\sum_l t_l s) - \sum_l t_l s$ for all $s \in S$, then $g(\sum_l t_l y) - \sum_l t_l y \in \mathrm{Fil}^1$ for $y \in \mathcal{K}_a \cap \mathrm{Fil}^0$ (`New.Lift.KummerChart.smul_sub_mem_hodgeFil_of_valueField`, [Kisin frames](/chapter/kisin-frames/)). Here take one element $1$ and $g = t$. For the second claim let $\pi = \varphi^{-a}(p_a)$, of order $1$, and $w = \pi^{-n}y \in \mathcal{K}_a \cap \mathrm{Fil}^0$. Then $tw - w \in \mathrm{Fil}^1$. Also $t\pi = \varphi^{-a}(\omega)\pi$, so $t(\pi^n) = \varphi^{-a}(\omega^n)\pi^n$. Then $t(\pi^n)(tw - w) = ty - \varphi^{-a}(\omega^n)y$, and the left side is in $\mathrm{Fil}^{n}\mathrm{Fil}^1 = \mathrm{Fil}^{n+1}$. $\square$

So, to first order, $t$ acts on the values of depth $n$ by the scalar $\varphi^{-a}(\omega^n)$.

### The depth lemma

**Definition (Depth operator).** For $e \in \mathbb{N}$, $\upsilon \in A_{\inf}$ and $t_0, \ldots, t_{m-1} \in \Gamma'$, the operator on $\mathcal{A}$ is

$$D_{e,\upsilon,t}(x) = p^e x + \sum_{l < m} \upsilon\,\delta^{-1}(t_l x - x).$$

For one element it is $p^e x + \upsilon\delta^{-1}(tx - x)$.

Lean: `New.Lift.KummerChart.JumpLattice.depthStepOperator`, `New.Lift.KummerChart.JumpLattice.depthStepOperator_singleton` (New/Congruences/Lifting/ExponentLattices.lean).

**Lemma (One step).** Let $n \neq 0$. There are $t \in \Gamma'$ and $\upsilon \in A_{\inf}$ with this property. For $x \in N_{\mathrm{loc}}$, a form $\mu$ and $c \in K'$ with $v_a(\mu,x) - c \in \mathrm{Fil}^n$, the value $v_a(\mu, D_{c_a(n),\upsilon,t}(x)) - p^{c_a(n)}c$ lies in $\mathrm{Fil}^{n+1}$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_valueAt_depthStepOperator_sub_smul_mem` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* Take a depth step $(t, \omega, \upsilon_0, X)$ for $n$ at $p_a$ by [Section 2](/chapter/exponent-lattices/#costs-and-depth-steps), and put $\upsilon = -\upsilon_0$. Write $e = c_a(n)$, $y = v_a(\mu,x) - c$ and $w = \delta^{-1}(tx - x)$. The constant $c$ lies in $\mathcal{K}_a$, and $v_a(\mu, x)$ lies in it by the last section, so $y \in \mathcal{K}_a \cap \mathrm{Fil}^n$. The lemma on the first-order action gives $ty - \varphi^{-a}(\omega^n)y \in \mathrm{Fil}^{n+1}$.

Let $\delta_a = \varphi^{-a}(\delta)$ and $X_a = \varphi^{-a}(X)$. Since $t$ fixes $c$, $\delta_a v_a(\mu,w) = v_a(\mu, tx - x) = ty - y$. Since $\delta X = \omega^n - 1$, $\delta_a X_a = \varphi^{-a}(\omega^n) - 1$. So

$$\delta_a\bigl(v_a(\mu,w) - X_a y\bigr) = ty - \varphi^{-a}(\omega^n)y \in \mathrm{Fil}^{n+1}.$$

$p_a$ does not divide $\delta$, so $\delta_a$ is a unit of $B_{\mathrm{dR}}^+$, and $v_a(\mu,w) - X_a y \in \mathrm{Fil}^{n+1}$. Now

$$v_a(\mu, p^e x - \upsilon_0 w) - p^e c = -\Bigl(\varphi^{-a}(\upsilon_0)\bigl(v_a(\mu,w) - X_a y\bigr) + y\,\varphi^{-a}(\upsilon_0 X - p^e)\Bigr).$$

The first term lies in $\mathrm{Fil}^0 \cdot \mathrm{Fil}^{n+1}$. In the second, $p_a \mid \upsilon_0 X - p^e$, so $\varphi^{-a}(\upsilon_0 X - p^e) \in \mathrm{Fil}^1$, and $y \in \mathrm{Fil}^n$. $\square$

**Theorem (The depth lemma).** Let $a \geq 0$ and $n \in \mathbb{Z}$. There are $m$, $t_0, \ldots, t_{m-1} \in \Gamma'$ and $\upsilon \in A_{\inf}$ with this property. For $x \in N_{\mathrm{loc}}$ and a form $\mu$, if $v_a(\mu, x)$ is a constant of $K'$ modulo $\mathrm{Fil}^n$, then $v_a(\mu, D_{c_a(n),\upsilon,t}(x))$ is a constant of $K'$ modulo $\mathrm{Fil}^{n+1}$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_valueAt_sub_mem_hodgeFil_succ` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* For $n \neq 0$, take $m = 1$ and the one step lemma; the new constant is $p^{c_a(n)}c$. For $n = 0$, take the $m = p^{c_a(0)}$ elements $t_l$ of the averaging step of Section 2, and $\upsilon = \delta$. Then

$$D_{c_a(0),\delta,t}(x) = p^{c_a(0)}x + \sum_{l < m}(t_l x - x) = \sum_{l<m} t_l x,$$

since there are $p^{c_a(0)}$ terms. Its value is $\sum_l t_l v$ with $v = v_a(\mu,x)$. As $v$ is a constant modulo $\mathrm{Fil}^0$, $v \in \mathrm{Fil}^0$, and $v \in \mathcal{K}_a$. The averaging step and the Volume 7 lemma quoted above give $g(\sum_l t_l v) - \sum_l t_l v \in \mathrm{Fil}^1$ for every $g \in \Gamma'$. By the lemma on almost invariant elements, $\sum_l t_l v$ is a constant modulo $\mathrm{Fil}^1$. $\square$

The operator depends on $a$ and $n$, not on $x$ or $\mu$. It raises the depth for all forms at once.

**Lemma.** For an unramified chart and $n$ with $n = 0$ or $p \nmid n$, $c_a(n) \leq 3a$.

Lean: `New.Lift.KummerChart.JumpLattice.cost_le_of_isUnramified` (New/Congruences/Lifting/ExponentLattices.lean).

*Proof.* $v_p(n) = 0$ in both cases, and $d = 0$ for an unramified chart. $\square$

In the model case ($a = 0$, unramified), the depth lemma costs nothing for $p \nmid n$: the operator keeps the constant $c$ and raises the depth by one.
