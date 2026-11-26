---
title: Theta functions on complex tori
lean:
  - Lib/Shimura/ComplexTheta/AppellHumbertData.lean
decls:
  - New.FinComplexSpace
  - New.RealComplexForm
  - New.RealComplexForm.thetaSpace
  - New.RealComplexForm.riemannForm
  - New.IsAppellHumbert
  - New.IsPosRiemann
  - New.RealComplexForm.thetaShift
  - New.RealComplexForm.dualLattice
  - New.IsAppellHumbert.thetaShift_thetaShift
  - New.IsAppellHumbert.thetaShift_comm
  - New.IsAppellHumbert.thetaShift_mem
  - New.IsAppellHumbert.le_dualLattice
  - New.IsAppellHumbert.eq_exp_of_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta functions on complex tori

A complex torus $V/L$ of dimension $d \geq 1$ has no nonconstant holomorphic functions, since such a function is bounded and so constant by Liouville's theorem. So the projective geometry of $V/L$ is carried by sections of line bundles. On the torus these sections are entire functions on $V$ that change by a fixed factor under translation by $L$. Such functions are theta functions. This section defines them in the form of the source, gives the conditions of Appell and Humbert on the factor, and proves the first properties. All the results of this section are elementary. The deep results come in [Section 3](/chapter/complex-abelian-varieties/).

### The model case

Let $V = \mathbb{C}$, let $\tau$ be a complex number with $y = \operatorname{Im}\tau > 0$, and let $L = \mathbb{Z} + \tau\mathbb{Z}$. The Jacobi theta function
$$\vartheta(z) = \sum_{n \in \mathbb{Z}} \exp(\pi i n^2\tau + 2\pi i n z)$$
converges normally on compact sets, because $|\exp(\pi i n^2 \tau)| = \exp(-\pi n^2 y)$. A shift $n \mapsto n + 1$ of the summation index gives
$$\vartheta(z + 1) = \vartheta(z), \qquad \vartheta(z + \tau) = \exp(-\pi i \tau - 2\pi i z)\,\vartheta(z).$$
We want to write the two factors in one form $\chi(l)\exp(B(l, z) + B(l, l)/2)$ for $l \in L$. Put
$$B(u, v) = \frac{\pi}{y}(\bar u - u)\,v = -\frac{2\pi i}{y}\operatorname{Im}(u)\,v.$$
Then $B(1, z) = 0$ and $B(\tau, z) = -2\pi i z$, so $B(\tau, \tau)/2 = -\pi i \tau$. So the rule for $\vartheta$ is $\vartheta(z + l) = \chi(l)\exp(B(l, z) + B(l, l)/2)\,\vartheta(z)$ with $\chi(1) = \chi(\tau) = 1$. For a general lattice vector the factor is not multiplicative in $l$. The rule for $l + m$ follows from the rules for $l$ and $m$ only if $\chi$ corrects a sign. With $\chi(a + b\tau) = (-1)^{ab}$ the rule holds for all $l \in L$. The reader can check this at $l = 1 + \tau$ by a direct computation, or deduce it from the semicharacter condition below. The form $B$ is real-linear in its first argument and complex-linear in its second. This is the type of form that the source uses.

### Forms, lattices and theta functions

**Definition (Finite-dimensional complex space).** A *finite-dimensional complex space* is a normed complex vector space of finite dimension.

Lean: `New.FinComplexSpace` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

**Definition (Real-complex form).** A *real-complex form* on $V$ is a continuous map $B \colon V \times V \to \mathbb{C}$ that is real-linear in the first argument and complex-linear in the second.

Lean: `New.RealComplexForm` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

A subgroup $L$ of $V$ is a *full-rank lattice* if it is discrete and spans $V$ over $\mathbb{R}$. The source writes this as the class abbreviation `IsFullRankLattice L`, which joins `DiscreteTopology L` and `IsZLattice ℝ L` of Mathlib.

The source tags a form with a lattice by the type `New.ThetaTori.LatticeForm L`, which is the type of real-complex forms. The tag imposes no condition. It lets the dual lattice and the space of theta functions read $L$ from the type of $B$.

**Definition (Theta functions).** Let $L$ be a subgroup of $V$, let $B$ be a real-complex form and let $\chi \colon V \to \mathbb{C}$ be a function. The space of *theta functions of type $(B, \chi)$* is the complex vector space of entire functions $f \colon V \to \mathbb{C}$ with
$$f(z + l) = \chi(l)\exp\bigl(B(l, z) + B(l, l)/2\bigr) f(z) \qquad (l \in L,\ z \in V).$$

Lean: `New.RealComplexForm.thetaSpace` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

**Remark.** The multiplier $\chi$ is a function on all of $V$, but only its values on $L$ enter. Two multipliers that agree on $L$ give the same space. The definition asks for nothing on $L$: it is not required to be a full-rank lattice. For a subgroup that is not a lattice the space can be $0$ or infinite-dimensional, and the results that count dimensions take a full-rank lattice as a hypothesis.

**Definition (Riemann form).** The *Riemann form* of $B$ is the real bilinear form
$$E(u, v) = \frac{1}{2\pi}\operatorname{Im}\bigl(B(u, v) - B(v, u)\bigr).$$
It is alternating. We write $\mathbf{e}(t) = \exp(2\pi i t)$ for real $t$.

Lean: `New.RealComplexForm.riemannForm` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

In the model case, $B(u, v) - B(v, u) = (\pi/y)(\bar u v - \bar v u) = (2\pi i/y)\operatorname{Im}(\bar u v)$, so $E(u, v) = \operatorname{Im}(\bar u v)/y$. On the lattice, $E(a + b\tau, c + d\tau) = ad - bc$. This is the standard symplectic form of the basis $1, \tau$.

**Definition (Appell-Humbert data).** Let $L$ be a subgroup of $V$, $B$ a real-complex form with Riemann form $E$, and $\chi \colon V \to \mathbb{C}$. The pair $(B, \chi)$ is *Appell-Humbert data* for $L$ if:

1. $\operatorname{Re} B(u, v) = \operatorname{Re} B(v, u)$ for all $u, v \in V$;
2. $|\chi(l)| = 1$ for $l \in L$;
3. $\chi(l + m) = \chi(l)\chi(m)\exp\bigl(\pi i E(m, l)\bigr)$ for $l, m \in L$.

Lean: `New.IsAppellHumbert` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

Condition 3 is the condition that makes the factor $\chi(l)\exp(B(l, z) + B(l, l)/2)$ a cocycle. Expand $f(z + l + m)$ in two ways, once as $(z + m) + l$ and once directly. The exponents differ by $B(m, l) - B(l, m)$, and condition 1 makes this difference purely imaginary, equal to $2\pi i E(m, l)$. The factor $\exp(\pi i E(m, l))$ in condition 3 absorbs half of it. In the model case $E(c + d\tau, a + b\tau) = cb - da$, and $(-1)^{(a + c)(b + d)} = (-1)^{ab}(-1)^{cd}(-1)^{ad + bc}$ with $(-1)^{ad + bc} = \exp(\pi i(cb - da))$. So $\chi(a + b\tau) = (-1)^{ab}$ satisfies condition 3.

**Definition (Positive Riemann form).** The Riemann form of $B$ is *positive* if $E(u, iu) > 0$ for every $u \neq 0$ in $V$.

Lean: `New.IsPosRiemann` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

In the model case, $E(u, iu) = \operatorname{Im}(\bar u \cdot iu)/y = |u|^2/y > 0$.

### The textbook form

Birkenhake and Lange, *Complex Abelian Varieties*, Chapter 2, Section 2.2, state the theorem of Appell and Humbert as follows. A line bundle on $V/L$ is given by a pair $(H, \chi)$, where $H$ is a hermitian form on $V$ whose imaginary part $E_{BL} = \operatorname{Im} H$ is integral on $L$, and $\chi \colon L \to U(1)$ is a semicharacter: $\chi(l + m) = \chi(l)\chi(m)\exp(\pi i E_{BL}(l, m))$. The factor of automorphy of the line bundle $L(H, \chi)$ is
$$a_L(l, z) = \chi(l)\exp\bigl(\pi H(z, l) + \tfrac{\pi}{2}H(l, l)\bigr),$$
with $H$ complex-linear in the first argument. The theta functions for $L(H, \chi)$ are the entire $f$ with $f(z + l) = a_L(l, z) f(z)$. Mumford, *Abelian Varieties*, Sections 1 and 2, gives the same theory with a different sign convention.

The source form contains this as the case $B(u, v) = \pi \overline{H(u, v)} = \pi H(v, u)$. Then $B(l, z) = \pi H(z, l)$ and the two factors agree. The Riemann forms are related by $E(u, v) = E_{BL}(v, u)$, so the semicharacter conditions agree, and $E(u, iu) = E_{BL}(iu, u) = H(u, u)$, so positivity of $E$ in the source is positive definiteness of $H$.

**Remark (Formalization).** The source does not ask $B$ to be hermitian, and it does not split a line bundle into $H$ and a trivial factor. A real-complex form $B$ with symmetric real part is always $B = \pi\overline{H} + S$, with $H$ hermitian and $S$ complex-bilinear and symmetric. The proof is short. The part $S(u, v) = \frac{1}{2}(B(u, v) - iB(iu, v))$ that is complex-linear in $u$ is symmetric; this is the lemma `New.IsAppellHumbert.linearPart_symm` of `Lib/Shimura/ComplexTheta/DimensionFormula.lean`. The rest $A = B - S$ is conjugate-linear in $u$ and complex-linear in $v$, with $\operatorname{Re} A$ symmetric. Then $\operatorname{Re} A(u, iv) = -\operatorname{Im} A(u, v)$ and $\operatorname{Re} A(iv, u) = \operatorname{Im} A(v, u)$, so $\operatorname{Im} A$ is antisymmetric and $A$ is hermitian in the sense $A(u, v) = \overline{A(v, u)}$. The symmetric part $S$ changes theta functions only by the factor $\exp(S(z, z)/2)$: if $f$ has type $(B, \chi)$, then $\exp(-S(z, z)/2) f(z)$ has type $(B - S, \chi)$. In the model case $H(u, v) = u\bar v/y$ and $S(u, v) = -\pi uv/y$. The source keeps $S$. The form that the proof of the Appell-Humbert theorem in [Section 6](/chapter/complex-abelian-varieties/) produces comes from a factor of automorphy, and it has no reason to be hermitian. No argument of the source needs the hermitian part alone.

### Twisted translations

The group $V$ acts on functions by translation, but translation does not preserve a space of theta functions. The right operator multiplies by the inverse of the factor of automorphy.

**Definition (Twisted translation).** For $a \in V$ the *twisted translation* $T_a$ is the complex-linear map on all functions $V \to \mathbb{C}$ given by
$$(T_a f)(z) = \exp\bigl(-(B(a, z) + B(a, a)/2)\bigr) f(z + a).$$

Lean: `New.RealComplexForm.thetaShift` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

So $f$ is a theta function of type $(B, \chi)$ if and only if $f$ is entire and $T_l f = \chi(l) f$ for all $l \in L$. The second half of this statement is the lemma `New.thetaShift_of_mem`.

**Proposition.** Let $(B, \chi)$ be Appell-Humbert data for $L$, with Riemann form $E$. For all $u, v \in V$ and every function $f \colon V \to \mathbb{C}$,
$$T_u T_v f = \exp\bigl(\pi i E(u, v)\bigr)\, T_{u + v} f.$$

Lean: `New.IsAppellHumbert.thetaShift_thetaShift` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

*Proof.* Both sides are $f(z + u + v)$ times an exponential. The exponent on the left is $-(B(u, z) + B(u, u)/2) - (B(v, z + u) + B(v, v)/2)$. The exponent of $T_{u + v}$ is $-(B(u + v, z) + B(u + v, u + v)/2)$. The difference is $(B(u, v) - B(v, u))/2$. By condition 1 the real part of $B(u, v) - B(v, u)$ is zero, so the difference is $\pi i E(u, v)$. $\square$

**Corollary.** Under the same hypotheses, $T_u T_v f = \mathbf{e}\bigl(E(u, v)\bigr)\, T_v T_u f$ for all $u, v \in V$ and all $f$.

Lean: `New.IsAppellHumbert.thetaShift_comm` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

*Proof.* Apply the proposition to both sides and use $E(v, u) = -E(u, v)$. $\square$

So the operators $T_a$ do not commute. Together with the scalars they form a Heisenberg group, a central extension of $V$ by $\mathbb{C}^\times$ with commutator $\mathbf{e}(E(u, v))$. This is the complex form of the theta group of Mumford, *Abelian Varieties*, Section 23.

**Proposition.** Let $(B, \chi)$ be Appell-Humbert data for $L$, let $f$ be a theta function of type $(B, \chi)$, and let $a \in V$. Then $T_a f$ is a theta function of type $(B, \chi_a)$, where $\chi_a(l) = \chi(l)\,\mathbf{e}\bigl(E(l, a)\bigr)$.

Lean: `New.IsAppellHumbert.thetaShift_mem` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

*Proof.* $T_a f$ is entire. For $l \in L$, compute $(T_a f)(z + l)$ with the rule for $f$ at the point $z + a$. The exponents differ from those of $\chi(l)\exp(B(l, z) + B(l, l)/2)(T_a f)(z)$ by $B(l, a) - B(a, l) = 2\pi i E(l, a)$. $\square$

### The dual lattice

**Definition (Dual lattice).** The *dual lattice* of $L$ for $B$ is
$$L^\perp = \{ v \in V : E(v, l) \in \mathbb{Z} \text{ for all } l \in L \}.$$

Lean: `New.RealComplexForm.dualLattice` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

The name is that of the source. If $E$ is nondegenerate and $L$ is a full-rank lattice, $L^\perp$ is again a full-rank lattice. In the textbooks $L^\perp$ is written $\Lambda(L)$, and the finite group $K(L) = L^\perp/L$ is the kernel of the map $V/L \to \operatorname{Pic}^0(V/L)$ that sends $x$ to $t_x^*L \otimes L^{-1}$ (Birkenhake and Lange, Chapter 2; Mumford, Section 8).

For $a \in L^\perp$ the character $\mathbf{e}(E(l, a))$ of the last proposition is $1$ on $L$. So $T_a$ maps theta functions of type $(B, \chi)$ to theta functions of the same type. This is the lemma `New.IsAppellHumbert.thetaShift_mem_of_mem_dualLattice`, and the restriction of $T_a$ to the space of theta functions is `New.IsAppellHumbert.thetaShiftEnd`. For $l \in L$ the operator $T_l$ is the scalar $\chi(l)$ on this space. So the theta group of the pair $(B, \chi)$ acts on the space of theta functions through a central extension of $L^\perp/L$ by $\mathbb{C}^\times$.

**Proposition.** If $(B, \chi)$ is Appell-Humbert data for $L$, then $L \subseteq L^\perp$: the Riemann form is integral on $L$.

Lean: `New.IsAppellHumbert.le_dualLattice` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

*Proof.* Let $l, m \in L$. Condition 3 gives $\chi(l + m) = \chi(l)\chi(m)\exp(\pi i E(m, l))$ and $\chi(m + l) = \chi(m)\chi(l)\exp(\pi i E(l, m))$. The left sides are equal and $\chi(l)\chi(m) \neq 0$ by condition 2. So $\exp(\pi i E(m, l)) = \exp(\pi i E(l, m))$. As $E$ is alternating, $\exp(2\pi i E(l, m)) = 1$, and $E(l, m) \in \mathbb{Z}$. $\square$

In the model case, write $v = s + t\tau$ with real $s, t$. Then $E(v, 1) = -t$ and $E(v, \tau) = s$. So $L^\perp = L$. If $B$ is replaced by $nB$, then $E$ is replaced by $nE$, and $L^\perp = \frac{1}{n}L$, with $[L^\perp : L] = n^2$.

### Theta functions without zeros

The last result of the section says that a theta function without zeros is trivial. It is the analytic core of the statement that a line bundle with a nowhere vanishing section is trivial.

**Proposition.** Let $L$ be a full-rank lattice in $V$, let $(B, \chi)$ be Appell-Humbert data for $L$, and let $f$ be a theta function of type $(B, \chi)$ with $f(z) \neq 0$ for all $z \in V$. Then:

1. the Riemann form of $B$ is zero;
2. $\chi(l) = 1$ for all $l \in L$;
3. $f(z) = \exp\bigl(B(z, z)/2\bigr) f(0)$ for all $z \in V$.

Lean: `New.IsAppellHumbert.eq_exp_of_ne_zero` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

The proposition does not assume that $E$ is positive. It uses only that $L$ is a full-rank lattice.

*Proof.* The function $u \mapsto |(T_u f)(0)| = |\exp(-B(u, u)/2) f(u)|$ is continuous, and a shift of $u$ by $l \in L$ multiplies $T_u f$ by a number of absolute value $1$. So it factors through the compact torus $V/L$, and it is bounded (`New.IsAppellHumbert.isCompact_range_norm_thetaShift`).

Fix $u \in V$ with $E(u, iu) \leq 0$, and put $g(s) = \exp(-s^2 B(u, u)/2) f(su)$ for $s \in \mathbb{C}$. Write $s = x + iy$. A computation with condition 1 gives
$$\operatorname{Re}\bigl(s^2 B(u, u)\bigr) - \operatorname{Re} B(su, su) = -2\pi y^2 E(u, iu) \geq 0.$$
So $|g(s)| \leq |(T_{su} f)(0)|$, and $g$ is a bounded entire function. By Liouville's theorem $g$ is constant, and $f(su) = \exp(s^2 B(u, u)/2) f(0)$. This is `New.IsAppellHumbert.apply_smul_of_nonpos`.

If $E(u, iu) \geq 0$, apply the same argument to $1/f$. It is a theta function of type $(-B, \chi^{-1})$, and $(-B, \chi^{-1})$ is Appell-Humbert data (`New.IsAppellHumbert.neg`), with Riemann form $-E$. So for every $u$ and $s$ one has $f(su) = \exp(s^2 B(u, u)/2) f(0)$. At $s = 1$ this is part 3.

For part 1, compare the two expressions for $|f(iu)|$: from the point $iu$ with $s = 1$, and from the point $u$ with $s = i$. They give $\operatorname{Re} B(u, u) = \operatorname{Im} B(iu, u)$ for all $u$. Polarization at $u + iv$, together with condition 1, gives $\operatorname{Im} B(u, v) = \operatorname{Im} B(v, u)$, which is $E = 0$. For part 2, put $z = 0$ in the rule for $f$ at $l \in L$ and use part 3 at $z = l$: $\exp(B(l, l)/2)f(0) = \chi(l)\exp(B(l, l)/2)f(0)$, and $f(0) \neq 0$. $\square$

In the model case the proposition says that $\vartheta$ must have a zero, since $E \neq 0$. Indeed $\vartheta$ vanishes at $z = (1 + \tau)/2$, and this is its only zero modulo $L$.
