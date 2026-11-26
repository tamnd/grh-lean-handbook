---
title: Constant terms and surviving orbits
lean:
  - Lib/Weil/Periods/ConstantTerm.lean
  - Lib/Weil/Periods/BesselIntegral.lean
  - Lib/Weil/Periods/Grading.lean
decls:
  - New.Grading.constTerm
  - New.Grading.hasSum_constTerm
  - New.Grading.constTerm_eq_homBicharacter_mul
  - New.Grading.constTerm_mul
  - New.Grading.Survives
  - New.Grading.AgreesWithStringMap
  - New.Grading.hasDegreeGe_zero_mul_stringMap_mul_sub
  - New.Grading.agreesWithStringMap_mul_iff
  - New.Grading.hasDegreeGe_of_survives
  - New.Grading.exists_agreesWithStringMap
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Constant terms and surviving orbits

The theta function on $\operatorname{Hom}(V, V')$ is a sum over rational maps $w \colon V \to V'$. This section groups the terms of the sum by the part of $w$ of negative degree. The sum of each group is a constant term, and the constant terms add up to the theta function ([Theorem](/decl/New.Grading.hasSum_constTerm/)). Then the section asks which groups survive integration against an equivariant function $W$ on $[R]$. It proves that a surviving rational map can be moved, by a rational point of $U(V')$, to a map that agrees with $T$ in negative degree, and that the moved map then equals $T$ up to degree $\geq 0$. These are the algebraic inputs of the unfolding in Section 5.

Throughout, $Y$ grades $V$ with a string of length $s$, and $Y'$ grades $V'$ with a string of length $s'$. From the definition of $\operatorname{Survives}$ on, $s' = s - 1$. Maps $w \colon V \to V'$ are written as matrices in rational coordinates, with rows indexed by the basis of $V'$ and columns by the basis of $V$. The map $T$ is the string map of [Definition](/decl/New.Grading.stringMap/).

### The constant term

Let $d$ be a weight on the basis of $V'$. The degree of the entry $(b, a)$ of a map is $d(b) - \operatorname{grade}(a)$. A map has degree $\geq k$ if its entries of degree $< k$ vanish. For an adelic matrix $v$ of the shape of $\operatorname{Hom}(V, V')$, write $v_{+}$ for the matrix that keeps the entries of $v$ of positive degree and puts $0$ in the other entries.

Recall that the source writes $f(x)$ for the theta function $\theta(\varrho(x) f)$ of $f \in \mathcal{S}(\operatorname{Hom}(V, V'))$, as in [the Weil representation from a vacuum](/chapter/weil-representation/). Here $\varrho(w)$ is the Heisenberg operator of $w$.

**Definition (Constant term).** For $f \in \mathcal{S}(\operatorname{Hom}(V, V'))$ and an adelic map $w$, the constant term of $f$ at $w$ along the maps of positive degree is

$$\mathrm{CT}_d(f)(w) = \int_{\mathbb{A}^{\iota' \times \iota} / E^{\iota' \times \iota}} (\varrho(w) f)(v_{+})\, dv,$$

the mean of the continuous periodic function $v \mapsto (\varrho(w) f)(v_+)$ over the compact quotient. The point $v_+$ is read in the adelic coordinates of $\operatorname{Hom}(V, V')$.

Lean: `New.Grading.constTerm`, with `New.Grading.mapDegree` and `New.Grading.nonnegMaps` (Lib/Weil/Periods/ConstantTerm.lean, Lib/Weil/Periods/Grading.lean).

The rational maps of degree $\geq 0$ form a group $\Lambda_d$ under addition. The classes of rational maps modulo $\Lambda_d$ form a countable set.

**Theorem (Fourier expansion in constant terms).** Let $d$ be odd under the string reversal of $Y'$: $d(\sigma b) = -d(b)$ for every basis index $b$ of $V'$, where $\sigma$ exchanges the string vectors $e'_i$ and $e'_{s'-1-i}$ and fixes $X'$. Choose a representative $w_x$ of each class $x$ of rational maps modulo $\Lambda_d$. Then:

1. the sum $\sum_x \mathrm{CT}_d(f)(w_x)$ converges absolutely to $f(0) = \theta(f)$;
2. there is a constant $M \geq 0$ such that $\sum_x |\mathrm{CT}_d(f)(w_x)| \leq M \|f\|$ for every $f$.

Lean: `New.Grading.hasSum_constTerm`, which joins `New.Grading.hasSum_constTerm_out` and `New.Grading.exists_tsum_enorm_constTerm_le` (Lib/Weil/Periods/ConstantTerm.lean).

*Proof.* Since $d$ is odd under $\sigma$, the basis vectors of $\operatorname{Hom}(V, V')$ of positive degree span an isotropic subspace, and those of negative degree span a dual one. So they give a splitting of $\operatorname{Hom}(V, V')$ in the sense of the mixed models of [the Weil representation from a vacuum](/chapter/weil-representation/), with frame $k$ the maps of positive degree. In this mixed model, the theta functional is a sum of the theta values of the slices over the rational points of the dual frame, and the sum of the norms of the slices is at most a constant times $\|f\|$. The source identifies the rational points of the dual frame with the classes modulo $\Lambda_d$, and the theta value of the slice at a class with the constant term at any representative. The bound in (2) is the norm of the theta functional times the bound on the slices. $\square$

The value $\mathrm{CT}_d(f)(w)$ depends only on the class of $w$, when $w$ is rational and $d$ is odd (Lean: `New.Grading.constTerm_congr_rat`). For adelic maps the dependence on $w$ is by a phase. Let $\beta$ be the Heisenberg bicharacter of $\operatorname{Hom}(V, V')$. In rational coordinates

$$\beta(x, y) = \psi\Big(\tfrac{\jmath}{2} \operatorname{tr}(y^\dagger x)\Big),$$

where $y^\dagger \colon V' \to V$ is the adjoint of $y$ for the two hermitian forms.

**Proposition (Change of the point).** Let $d$ be odd under the string reversal of $Y'$. If $w - w'$ has degree $\geq 1$, then $\mathrm{CT}_d(f)(w') = \beta(w, w')\, \mathrm{CT}_d(f)(w)$.

Lean: `New.Grading.constTerm_eq_homBicharacter_mul` (Lib/Weil/Periods/ConstantTerm.lean).

*Proof.* Write the constant term as the theta value of the zero term of $\varrho(w) f$ in the mixed model of the proof above. Since $w - w'$ has positive degree, it lies in the frame $k$. Translation by an element of $k$ does not change the zero term, up to the phase of the Heisenberg group law. That phase is $\beta(w, w')$. $\square$

**Proposition (Substitution law).** Let $d$ be odd under the string reversal of $Y'$. Let $\gamma \in G$ and $\delta \in G'$ satisfy one of:

1. $\gamma \in R(E)$, and $\delta$ is rational and its matrix does not lower the weights $d$;
2. $\gamma \in U$, and $\delta - 1$ raises the weights $d$ by at least $1$.

Then, for all $g \in G$, $h \in G'$ and every adelic map $w$,

$$\mathrm{CT}_d\big(\omega(\gamma g, \delta h) f\big)(w) = \mathrm{CT}_d\big(\omega(g, h) f\big)(\delta^{-1} w \gamma).$$

Here $\omega$ is the Weil action of $G \times G'$ on $\mathcal{S}(\operatorname{Hom}(V, V'))$, twisted by the characters $\alpha$ of the Weil data.

Lean: `New.Grading.constTerm_mul`, which joins `New.Grading.constTerm_mul_of_mem_ratBessel` and `New.Grading.constTerm_mul_of_mem_unipotent` (Lib/Weil/Periods/ConstantTerm.lean).

*Proof.* The Weil action of $(\gamma, \delta)$ moves the Heisenberg operator of $w$ to that of $\delta w \gamma^{-1}$. In both cases the substitution $w \mapsto \delta^{-1} w \gamma$ keeps the frame $k$ of maps of positive degree. In case (1) it is a rational substitution, and the theta functional is invariant under it. In case (2) both $\gamma$ and $\delta$ have determinant $1$, so no character of the determinant enters, and the substitution fixes the zero term. $\square$

### Which classes survive

Fix now $s' = s - 1$ and an equivariant $W$ on $R$. The unfolding integrates $W(r)$ times a constant term at $w$ over $[R]$. For $u \in U$ with $u - 1$ of degree $\geq 2$ and $w(u - 1)$ of degree $\geq 1$, the change $r \mapsto u r$ multiplies $W$ by $\psi_U(u)$ and the constant term by a phase $\beta(wu, w)^{\pm 1}$. So the integral is $0$ unless the two factors cancel. Now $\beta(T u, T) = \psi\big(\tfrac{\jmath}{2}\operatorname{tr}(T^\dagger T u)\big)$, and $T^\dagger T = \mathfrak{e}$ by [Proposition](/decl/New.Grading.formAdjoint_stringMap_mul_stringMap/). So $\beta(Tu, T) = \psi_U(u)$, and the condition for a nonzero integral is that the phase of $w$ is that of $T$.

**Definition (Survival).** Let $D$ be a weight on the basis of $V'$. A map $w \colon V \to V'$ survives the unipotent twists for $D$ if, for every $u \in U$ such that $u - 1$ has degree $\geq 2$ and $w(u - 1)$ has degree $\geq 1$ for the weights $D$ on the target,

$$\beta(T u, T) = \beta(w u, w).$$

Lean: `New.Grading.Survives` (Lib/Weil/Periods/BesselIntegral.lean).

The source uses $D = 0$ and $D = \operatorname{grade}'$, the weights of $Y'$.

The key computation turns survival into an equality of Gram data. If $w$ survives for $D$, then the vectors $T^\dagger T v$ and $w^\dagger w v$ have the same coordinate $k$, for every $k$ and every adelic $v$ that is supported in grades $\geq \max(1, \operatorname{grade}(k) + 2)$ and satisfies two side conditions on $w$ (Lean: `New.Grading.formAdjoint_mul_self_mulVec_apply_eq_of_survives`). The proof tests survival against the Eichler transformation of $v$ and a multiple $t$ of the basis vector dual to $k$.

### Moving a survivor to $T$

**Definition (Agreement with $T$).** A map $w \colon V \to V'$ agrees with $T$ if $w_{b a} = T_{b a}$ for every basis vector $e_a$ of $V$ of positive grade and every basis vector $e'_b$ of $V'$ with $\operatorname{grade}'(b) < \operatorname{grade}(a)$.

Lean: `New.Grading.AgreesWithStringMap` (Lib/Weil/Periods/Grading.lean).

So $w$ agrees with $T$ if, on each vector of positive grade $k$, the map $w$ equals $T$ modulo the vectors of grade $\geq k$ of $V'$. Since $T$ lowers grades by exactly $1$ on its support, this fixes the leading part of $w$ on the positive grades.

**Lemma (The double coset of $T$).** For $g \in R$ and $\delta \in R'$, the map $\delta T g - T$ has degree $\geq 0$.

Lean: `New.Grading.hasDegreeGe_zero_mul_stringMap_mul_sub`, with `New.Grading.hasDegreeGe_neg_one_stringMap` and `New.Grading.hasDegreeGe_zero_of_mem_besselGroup` (Lib/Weil/Periods/Grading.lean).

*Proof.* Write $\delta T g - T = (\delta - 1) T g + T(g - 1)$. The matrices of $g$ and $\delta$ do not lower grades. The map $T$ lowers grades by at most $1$, and it links only string vectors. An entry of $g - 1$ or $\delta - 1$ between string vectors raises grades by at least $1$, since the entries of grade $\leq$ that of the column are those of $1$. So each term has degree $\geq -1 + 1 = 0$. $\square$

**Proposition (The stabiliser of agreement).** Let $w$ agree with $T$, let $\gamma \in R$, and let $\delta \in G'$. Then $\delta w \gamma$ agrees with $T$ if and only if $\delta \in R'$.

Lean: `New.Grading.agreesWithStringMap_mul_iff` (Lib/Weil/Periods/BesselIntegral.lean).

*Proof.* If $\delta \in R'$, write $\delta w \gamma - T = \delta (w - T) \gamma + (\delta T \gamma - T)$. The first term vanishes on the entries in question, because $\delta$ and $\gamma$ do not lower grades and $w - T$ vanishes there. The second has degree $\geq 0$ by the lemma. So $\delta w \gamma$ agrees with $T$. Conversely, suppose that $\delta w\gamma$ agrees with $T$. The map $w\gamma$ also agrees with $T$, by the first part with $\delta = 1$. One proves that the entry $(b, k)$ of $\delta - 1$ vanishes for each string index $k$ of grade $\geq 0$ and each $b$ of grade $\leq$ that of $k$, by downward induction on the grade of $k$. For such $k$ there is a basis index $a$ of $V$ of grade $\operatorname{grade}'(k) + 1$ with $T_{k a}$ a unit, and column $a$ of $w\gamma$ is that of $T$ in the grades $\leq \operatorname{grade}'(k)$ (Lean: `New.Grading.exists_gradeOf_succ_isUnit_stringMap`). The entry $(b, a)$ of $(\delta - 1) w \gamma$ is $0$, since both $\delta w \gamma$ and $w \gamma$ agree with $T$ there. By the induction hypothesis it is also $(\delta - 1)_{b k} T_{k a}$. So $(\delta - 1)_{bk} = 0$. $\square$

**Theorem (Survivors that agree are $T$ up to degree $0$).** Let $w$ agree with $T$, and let $w$ survive the unipotent twists for the weights $\operatorname{grade}'$ of $Y'$. Then $w - T$ has degree $\geq 0$: its entry $(b, a)$ vanishes whenever $\operatorname{grade}'(b) < \operatorname{grade}(a)$.

Lean: `New.Grading.hasDegreeGe_of_survives` (Lib/Weil/Periods/BesselIntegral.lean).

*Proof.* By induction on the grade of $b$, one shows that $w_{ba} = T_{ba}$ whenever $\operatorname{grade}'(b) < \operatorname{grade}(a)$. If $\operatorname{grade}(a) > 0$, this is the agreement. So let $\operatorname{grade}(a) \leq 0$. Then $\operatorname{grade}'(b) < 0$, and the dual index $\sigma b$ has positive grade. Choose $i$ of grade $\operatorname{grade}'(\sigma b) + 1$ with $T_{\sigma b, i}$ a unit, as in the previous proof. Apply the key computation to $v = e_i$ and the coordinate dual to $a$. It gives that the entry $(\sigma a, \sigma b)$ of $T^\dagger$ equals that of $w^\dagger$, after one uses the induction hypothesis on the other entries and cancels the unit $T_{\sigma b, i}$. The entries of $w^\dagger$ are the entries of $w$ at the dual indices, times nonzero factors of the Gram matrices. So $w_{ba} = T_{ba}$. $\square$

**Theorem (Witt's theorem for survivors).** Let $w$ be a rational map $V \to V'$ that survives the unipotent twists for $D = 0$. Then there is a rational point $\delta \in G'(E)$ such that $\delta w$ agrees with $T$.

Lean: `New.Grading.exists_agreesWithStringMap`, with `New.Space.witt` (Lib/Weil/Periods/BesselIntegral.lean, Lib/Adelic/Unitary/RationalPoints.lean).

*Proof.* Let $A$ be the set of basis vectors of $V$ of positive grade. The key computation with $D = 0$ gives that the Gram matrices of $w$ and of $T$ on $A$ are equal: $\langle w e_a, w e_{a'} \rangle' = \langle T e_a, T e_{a'} \rangle'$ for $a, a' \in A$. Both $w$ and $T$ are injective on the span of $A$. For $T$ this is clear. For $w$, a vector $u$ in the kernel with a last nonzero coordinate $a$ gives, at the next string index $k$, the equation $(\mathfrak{e} u)_k = (w^\dagger w u)_k = 0$. But $(\mathfrak{e} u)_k$ is a nonzero factor of the shift times $u_a \neq 0$. By Witt's theorem for the hermitian space $V'$ over $E$, there is $g \in U(V')(E)$ with $g w = T$ on the span of $A$. Then $\delta = g$ works, since $g w$ and $T$ have the same columns on $A$. $\square$

Together, the three results describe the surviving orbits. A rational survivor $w$ can be moved by $G'(E)$ to a map that agrees with $T$. The moved map is unique up to $R'(E)$ on the left and $R(E)$ on the right. If it also survives for the weights of $Y'$, it is $T$ modulo maps of degree $\geq 0$.

**Remark (Formalization).** Survival is defined by the equality of the phases at $T$ and at $w$, not by a Gram condition on $w$. The Gram condition is a consequence, through the key computation. The class sums of Section 5 use representatives that the source chooses with `Quotient.out`. The set of classes whose chosen representative agrees with $T$ does not depend on the choice when $d \leq \max(\operatorname{grade}', 0)$ (Lean: `New.Grading.agreesWithStringMap_congr_rat`). The source applies the Fourier expansion with $d = 0$ and $d = \operatorname{grade}'$, which are both odd. The constant $M$ in the bound of the Fourier expansion is not explicit, and it is allowed to be large. It enters only through the integrability arguments of Section 5.
