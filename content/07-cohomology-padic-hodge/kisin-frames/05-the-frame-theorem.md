---
title: The frame theorem
lean:
  - Lib/PadicHodge/Kisin/FrameTheorem.lean
decls:
  - New.Lift.KummerChart.JumpLattice.exists_functional_extend
  - New.Lift.KummerChart.JumpLattice.FrameProperties
  - New.Lift.KummerChart.JumpLattice.frame_theorem
  - New.Lift.KummerChart.JumpLattice.free_kisinModule
  - New.Lift.KummerChart.JumpLattice.saturateBy_tau_span_kisinModule
  - New.Lift.KummerChart.JumpLattice.valueFieldPoints_frobKisinAinf_eq_span
  - New.Lift.KummerChart.JumpLattice.mem_kisinAinf_iff_crysForms
  - New.Lift.KummerChart.JumpLattice.mem_kisinModule_iff_crysForms
  - New.Lift.KummerChart.JumpLattice.pow_smul_gal_sub_mem_span_of_dvd
  - New.Lift.KummerChart.JumpLattice.smul_mem_kisinAinf
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The frame theorem

This section states the main theorem of `Lib/PadicHodge/Kisin`. It joins the two previous sections. The frame of [the period matrix](/decl/New.Lift.Chart.IsPeriodMatrix.exists_frame/) is a set of matrices. The modules $M$ and $N$ of a jump lattice are defined by forms. The frame theorem says that the columns of $\tau^{-a}Q$ are a basis of $N$ over $S$ and of $M$ over $A_{\inf}$, and it lists nine properties that follow.

Throughout, $k$ is a Kummer chart for $\Gamma$ with subgroup $\Gamma'$, ring $S$, element $E$ and exponent $e$. Let $L$ be a jump lattice over $k$ with coefficients $\mathcal{O}$, let $M$ and $N$ be its modules, and let $a$ be its jump bound.

### Forms exist

A first lemma makes forms plentiful.

**Lemma.** Every $\mathbb{Z}_p$-linear map $f : L \to B_{\mathrm{dR}}$ is the restriction of an $A_{\inf}$-linear map $\mu : W(C^\flat) \otimes L \to B_{\mathrm{dR}}$, in the sense that $\mu(1 \otimes t) = f(t)$ for all $t \in L$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_functional_extend` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* The source outlines the proof as follows. The ring $B_{\mathrm{dR}} \otimes_{A_{\inf}} W(C^\flat)$ is not zero, since $A_{\inf}$ maps injectively into the domains $B_{\mathrm{dR}}$ and $W(C^\flat)$. So over the field $B_{\mathrm{dR}}$ there is a linear map $\Psi$ on this ring, with values in the maps $L \to B_{\mathrm{dR}}$, that sends the non-zero vector $1$ to $f$. The restriction of $\Psi$ to $W(C^\flat)$ is $A_{\inf}$-linear and defines $\mu$. $\square$

The lemma gives a map $\mu$ with the values of $f$. It does not say that $\mu$ is a form, that is, that $\mu$ is $\Gamma'$-equivariant. The source tests equivariance separately, with `New.Lift.KummerChart.JumpLattice.equivariant_iff_basisValues`.

### The nine properties

**Definition (Frame properties).** The lattice $L$ has the *frame properties* if the following nine statements hold.

1. (a) Let $f : A_{\inf} \to S$ be $S$-linear. If vectors $v_i$ of $W(C^\flat) \otimes L$ lie in the $\mathcal{K}_0$-points of the fraction span of $A_{\inf} \otimes L$, and $\sum_i c_i v_i = 0$ with $c_i \in A_{\inf}$, then $\sum_i f(c_i) v_i = 0$.
2. (b) Let $l, A, \delta \geq 0$ with $3e \leq p^l$ and $eA \leq p^l \delta$. Let $x$ be a $\mathcal{K}_0$-point of $\varphi^l(M)$. Then $p^{4\delta} x$ is in the $S$-span of the $\mathcal{K}_0$-points $y$ of $\varphi^l(M)$ with $g\,\mu(y) - \mu(y) \in \mathrm{Fil}^A$ for every form $\mu$ and every $g \in \Gamma'$.
3. (c) $M$ is the $A_{\inf}$-span of $N$.
4. (d) For every crystalline form $\mu$ and every $y \in N$, $E^a \mu(y)$ is the image of an element of $S_B$.
5. (e) Let $d \in A_{\inf}$ be such that $d \mid E^m r$ in $B^+$ implies $d \mid r$ in $A_{\inf}$, for all $m$ and $r$. Let $x \in M$ and $n \geq 0$. If $E^n \mu(x)$ is a $B^+$-multiple of $d$ for every crystalline form $\mu$, then $x \in dM$.
6. (f) $\tau^a M \subseteq A_{\inf} \otimes L$.
7. (g) $\tau^a (A_{\inf} \otimes L) \subseteq M$.
8. (h) $E_0^a \varphi(N) \subseteq N$, where $E_0$ is the image of $E$ as a unit of $W(C^\flat)$.
9. (i) There are vectors $v_1, \ldots, v_d$, with $d$ the $\mathbb{Z}_p$-rank of $L$, such that the $S$-span of the $v_i$ is $N$, the $A_{\inf}$-span is $M$, and the $v_i$ are linearly independent over $A_{\inf}$.

Lean: `New.Lift.KummerChart.JumpLattice.FrameProperties` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

Here a $\mathcal{K}_0$-point of an $A_{\inf}$-module $P$ is an $x \in P$ with $\mu(x) \in \mathcal{K}_0$ for every form $\mu$ (`valueFieldPoints`). The fraction span of $A_{\inf} \otimes L$ is the set of $x$ that some non-zero-divisor of $A_{\inf}$ moves into $A_{\inf} \otimes L$ (`fracSpan`). The element $E$ is not divisible by $p$ in $A_{\inf}$, so it is a unit in $W(C^\flat)$, and $E_0$ is that unit (`New.Lift.KummerChart.frobEUnit`).

**Theorem (Frame theorem).** Every jump lattice over a Kummer chart has the frame properties.

Lean: `New.Lift.KummerChart.JumpLattice.frame_theorem` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* The source reads every property off a *frame* of $L$, a private structure `Frame`. A frame consists of an invertible $M_0$ over $B_{\max}$ with invariant columns, the period matrix $U = (E\tau)^a M_0$ of height $2a$ given by `New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf` for the jumps in $[-a, a]$, the matrices $Q$, $Q'$, $Z$, $Y$, $B$ of `New.Lift.Chart.IsPeriodMatrix.exists_frame`, and vectors $n_i$ with $\tau^a n_i$ the vector of $A_{\inf} \otimes L$ whose coordinates are the column $i$ of $Q$. The vectors $n_i$ exist because $\tau$ is not divisible by $p$, so it is a unit in $W(C^\flat)$. The source shows that the $n_i$ span $M$ over $A_{\inf}$ and that the $\varphi^l(n_i)$ span the $\mathcal{K}_0$-points of $\varphi^l(M)$ over $S$. The other properties are computations in these coordinates. Property (b) uses the radius lemma `New.Lift.Chart.radius_lemma` of [Period rings and crystalline representations](/chapter/period-rings/), which is Dwork's trick in the form of Kisin, Crystalline representations and F-crystals, Lemma 1.2.6, as the source cites it. $\square$

**Remark (Formalization).** The frame theorem gives part of Kisin's theorem. Its docstring says that it shows $E^a\varphi(N) \subseteq N$ but not the finite-height inclusion $E^n N \subseteq S\varphi(N)$. In Kisin's theory both inclusions hold for a module of finite $E$-height. Only the first is proved here. No equivalence of categories is stated. The theorem uses only the existence of a frame, through `obtain ⟨F⟩ : Nonempty (Frame L)`. The structure `Frame` is private, so no user of the theorem sees the choice of $Q$.

**Remark (Formalization).** Property (h) is a statement in $W(C^\flat) \otimes L$, where $E_0$ is a unit. It says that $\varphi(N) \subseteq E_0^{-a} N$. The exponent is the jump bound $a$, the least $a$ such that all jumps of $L$ over $\Gamma'$ lie in $[-a, a]$ (`New.Lift.KummerChart.JumpLattice.jumpBound`). It is not the width of the interval of jumps. A lattice with jumps in $[0, h]$ has $a \leq h$. In the frame, $Q$ has height $2a$: $QQ' = \tau^{2a}$ and $UZ = E^{2a}Q$.

### Consequences

The source states each of the nine properties again as a separate lemma, for example `New.Lift.KummerChart.JumpLattice.kisinAinf_eq_span_kisinModule`. The next consequences are new statements.

**Corollary.** The Kisin module $N$ is free over $S$.

Lean: `New.Lift.KummerChart.JumpLattice.free_kisinModule` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* The family $v$ of property (i) is linearly independent over $A_{\inf}$, so over $S$. It spans $N$ over $S$. $\square$

**Corollary.** After $\tau$ is inverted, the $A_{\inf}$-span of $N$ and $A_{\inf} \otimes L$ agree: $\mathrm{Sat}_\tau(A_{\inf} N) = \mathrm{Sat}_\tau(A_{\inf} \otimes L)$.

Lean: `New.Lift.KummerChart.JumpLattice.saturateBy_tau_span_kisinModule` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

The docstring compares this with Bhatt, Morrow and Scholze, Integral $p$-adic Hodge theory, Lemma 4.26: the comparison over $A_{\inf}[1/\mu]$ for Breuil-Kisin-Fargues modules, before the Frobenius twist. It follows from (c), (f) and (g).

**Corollary.** For every $l \geq 0$, the $\mathcal{K}_0$-points of $\varphi^l(M)$ are the $S$-span of $\varphi^l(N)$.

Lean: `New.Lift.KummerChart.JumpLattice.valueFieldPoints_frobKisinAinf_eq_span` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

### Criteria by crystalline forms

The modules $M$ and $N$ are defined by all forms. The next two theorems test membership by crystalline forms only. They are the form in which `New/Congruences/Lifting` uses the theory.

**Theorem.** Let $x \in W(C^\flat) \otimes L$. Then $x \in M$ if and only if two conditions hold: some power of $\tau$ moves $x$ into $A_{\inf} \otimes L$, and there is $n$ such that for every crystalline form $\mu$, $E^n \mu(x)$ is the image of an element of $B^+$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_kisinAinf_iff_crysForms` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* Forward: expand $x$ in the family $v$ of property (i) and use property (d) on each $v_i$, with $n = a$. Backward: some $\tau^N x$ lies in $M$, by the previous corollary on saturations and property (c). The crystalline forms and property (e) with $d = \tau^N$ show that $\tau^N x$ is divisible by $\tau^N$ in $M$. As $W(C^\flat) \otimes L$ has no $A_{\inf}$-torsion, $x \in M$. $\square$

**Theorem.** Let $x \in W(C^\flat) \otimes L$. Then $x \in N$ if and only if some power of $\tau$ moves $x$ into $A_{\inf} \otimes L$, and there is $n$ such that for every crystalline form $\mu$, $E^n \mu(x)$ is the image of an element of $S_B$.

Lean: `New.Lift.KummerChart.JumpLattice.mem_kisinModule_iff_crysForms` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* Forward: property (d). Backward: by the previous theorem $x \in M$, so $x = \sum u_i v_i$ with $u_i \in A_{\inf}$. Replace each $u_i$ by its coordinate $\lambda_0(u_i) \in S$. This changes $x$ by a vector on which every crystalline form vanishes (`apply_sum_sub_coord₀_smul_eq_zero_of_mem_crysForms`). That vector is $0$ by property (e) with $d = 0$. So $x$ is in the $S$-span of the $v_i$, which is $N$. $\square$

The next lemma is used with these criteria to bound the Galois action on the values of forms.

**Lemma.** Let $g \in G_p$ and $d \in B^+$ be such that $d$ divides $g y - y$ for every $y \in S_B$. Let $x \in B_{\mathrm{dR}}$ with $E^m x$ the image of an element of $S_B$. Then $E^{2m}(g x - x)$ is a $B^+$-multiple of $d$.

Lean: `New.Lift.KummerChart.JumpLattice.pow_smul_gal_sub_mem_span_of_dvd` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* Put $F = E^m$ and $E^m x = s$. Since $gE$ is associated to $E$, $F = (gF)w$ for a unit $w$. Write $gF - F = dr$ and $gs - s = dt$. Then $F^2(gx - x) = w\,(F(gs - s) - (gF - F)s) = w\,(Ft - rs)\,d$. $\square$

### Stability under the Galois group

**Proposition.** Let $g \in \Gamma$ with $g\Gamma' g^{-1} \subseteq \Gamma'$. Then $g$, acting diagonally on $W(C^\flat) \otimes L$, maps $M$ into $M$.

Lean: `New.Lift.KummerChart.JumpLattice.smul_mem_kisinAinf` (Lib/PadicHodge/Kisin/FrameTheorem.lean).

*Proof.* Let $\tau^N x \in A_{\inf} \otimes L$. Then $g(\tau^N) \cdot gx \in A_{\inf} \otimes L$, and $g(\tau^N)$ divides $\tau^N$, since $g\tau$ is associated to $\tau$. So $gx \in \mathrm{Sat}_\tau(A_{\inf} \otimes L)$. For a form $\mu$, the conjugate $\mu \circ g$ (`conjForm`) is again a form, because $g$ normalizes $\Gamma'$ (`conjForm_mem_forms`). Since $g$ commutes with $\varphi$, the condition $\mu(\varphi^{n+1}gx) \in B_{\mathrm{dR}}^+$ follows from the condition on $x$ for the conjugate form. $\square$

If $\Gamma' = \Gamma$, as in the Kummer chart of `New.Lift.exists_kummerChart`, then every $g \in \Gamma$ satisfies the hypothesis, and $M$ is stable under $\Gamma$.

**Example (The trivial lattice).** Let $L = \mathbb{Z}_p$ with the trivial action, so $a = 0$. Properties (f) and (g) give $M = A_{\inf} \otimes L$. Property (i) gives one vector $v_1$ with $N = S v_1$ and $M = A_{\inf} v_1$. So $v_1 = u \otimes 1$ for a unit $u$ of $A_{\inf}$. Property (h) with $a = 0$ says $\varphi(N) \subseteq N$. Classically the Kisin module of the trivial representation is $\mathfrak{S}$ with its Frobenius. The source gives the analogue up to the unit $u$. It does not compute $u$.
