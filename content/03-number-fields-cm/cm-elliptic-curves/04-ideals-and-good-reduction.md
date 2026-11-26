---
title: Ideals, the class number and good reduction
lean:
  - Lib/CM/GoodReduction.lean
  - Lib/CM/FiniteLattices.lean
  - Lib/CM/ChowlaSelberg.lean
decls:
  - New.QuadField.scaledIdeal
  - New.QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal
  - New.CMLattice.exists_latticeModule_eq_scaledIdeal
  - New.QuadField.area_eq_of_eq_scaledIdeal
  - New.CMLattice.pow_four_eq_one_of_mul_mem_iff
  - New.CMLattice.finite_range_latticeModule
  - New.QuadField.classGroup_sq_bijective
  - PeriodPair.scaledDisc
  - PeriodPair.IsOrderTwo.scaledDisc_sum_prod
  - PeriodPair.IsOrderTwo.scaledDisc_mul_of_isogeny
  - New.norm_le_one_of_cycle
  - New.CMLattice.exists_class_scaledDisc_mul
  - New.CMLattice.norm_scaledDisc_le_one
  - New.CMLattice.prod_scaledDisc_t
  - New.CMLattice.norm_disc_eq_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ideals, the class number and good reduction

From here on $d$ is a prime with $d \equiv 7 \pmod 8$ and $K = \mathbb{Q}(\sqrt{-d})$, with the class group $\mathrm{Cl}_K$ and the class number $h$. This section connects the CM lattices of [Section 3](/decl/New.CMLattice/) with the fractional ideals of $K$, and proves the one arithmetic fact about the curve $y^2 + a_1xy = x^3 + x$ that the Chowla-Selberg formula needs: its discriminant $a_1^4 - 64$ is a unit at every $p$-adic place ([Theorem](/decl/New.CMLattice.norm_disc_eq_one/)). The proof is elementary. It uses only the three points of order $2$, the $2$-isogenies between the lattices of the classes, and the ultrametric inequality. The section also proves that $h$ is odd.

### Lattices and ideals

Classically, a lattice $\Lambda$ with $\mathcal{O}_K\Lambda \subseteq \Lambda$ is a multiple $u\mathfrak{a}$ of a fractional ideal $\mathfrak{a}$ of $K$, and the class of $\mathfrak{a}$ is determined by $\Lambda$ (Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1). The source proves this in the following form.

**Definition (Scaled ideals).** For $u \in \mathbb{C}^\times$ and a nonzero fractional ideal $\mathfrak{a}$ of $K$, $u\mathfrak{a} \subset \mathbb{C}$ is the $\mathcal{O}_K$-submodule $\{u y : y \in \mathfrak{a}\}$. The map $(u, \mathfrak{a}) \mapsto u\mathfrak{a}$ is a homomorphism of monoids into the $\mathcal{O}_K$-submodules of $\mathbb{C}$ under multiplication.

Lean: `New.QuadField.scaledIdeal` (Lib/CM/GoodReduction.lean), with `New.QuadField.mem_scaledIdeal`. The lattice of a CM lattice $C$ as an $\mathcal{O}_K$-module is `New.CMLattice.latticeModule`.

**Theorem (CM lattices and ideals).** Let $d$ be a prime with $d \equiv 7 \pmod 8$.

1. For every nonzero fractional ideal $\mathfrak{c}$ there are a CM lattice $C$ and $u \in \mathbb{C}^\times$ with $\Lambda_C = u\mathfrak{c}$.
2. For every CM lattice $C$ there are $u \in \mathbb{C}^\times$ and a nonzero fractional ideal $\mathfrak{a}$ with $\Lambda_C = u\mathfrak{a}$.
3. If $\Lambda_C = u\mathfrak{a}$, then the area of $\Lambda_C$ is $|u|^2\, N\mathfrak{a}\, \sqrt d/2$.

Lean: `New.QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal`, `New.CMLattice.exists_latticeModule_eq_scaledIdeal`, `New.QuadField.area_eq_of_eq_scaledIdeal` (Lib/CM/GoodReduction.lean).

*Proof.* (1) The ideal $\mathfrak{c}$ is a lattice $L$ in $\mathbb{C}$. Multiplication by $\omega/2$ does not map $L$ into $L$: if it did, then $\omega/2$ and $\omega/2 + 1$ would both be endomorphisms of $L$, with degrees $|\omega|^2/4 = N$ and $|\omega + 2|^2/4 = N'$ in $\mathbb{N}$, and $4N' = 4N + 6$ is impossible modulo $4$. The same holds for $\bar\omega/2$. Two proper subgroups do not cover $L$, so there is $l \in L$ with $\omega l/2 \notin L$ and $\bar\omega l/2 \notin L$. Put $t = l/2$. Then $t$ satisfies conditions 1 and 5 of [the definition](/decl/New.CMLattice/). The number $\wp''(t) = 2(3\wp(t)^2 - g_2/4)$ is not $0$, since $\wp(t)$ is a simple root of $4x^3 - g_2x - g_3$. Replace $L$ by $cL$ and $t$ by $ct$, where $c^4 = \wp''(t)/2$. Then $\wp''(ct) = 2$ for $cL$. Choose $a_1$ with $a_1^2 = 12\wp(ct)$. (2) Write $\omega\omega_2 = m\omega_1 + n\omega_2$ with $m, n \in \mathbb{Z}$. Then $\Lambda = \omega_1(\mathbb{Z} + \mathbb{Z}\, m/(\omega - n))$, and the second factor is the fractional ideal spanned by $1$ and $m/(\omega - n)$. (3) The ring of integers has the $\mathbb{Z}$-basis $1, \omega$, with area $\operatorname{Im}\omega = \sqrt d/2$. An ideal $\mathfrak{a}$ has index $N\mathfrak{a}$ in $\mathcal{O}_K$ when integral, and multiplication by $u$ scales areas by $|u|^2$. $\square$

**Lemma (Fourth roots of unity).** If $c \ne 0$ and $c\Lambda_C = \Lambda_D$ for CM lattices $C$ and $D$, then $c^4 = 1$. So if $\Lambda_C$ and $\Lambda_D$ are multiples of ideals in the same class, then $\Lambda_C = c\Lambda_D$ with $c^4 = 1$, and the set of the lattices $\Lambda_C$ of CM lattices for $d$ is finite, with at most $4h$ elements.

Lean: `New.CMLattice.pow_four_eq_one_of_mul_mem_iff`, `New.CMLattice.finite_range_latticeModule` (Lib/CM/FiniteLattices.lean).

*Proof.* The map $x \mapsto cx$ takes $t_C$ to a point of order $2$ of $\Lambda_D$. It is not in the kernel of $\omega$ or $\bar\omega$, so it is $t_D$ modulo $\Lambda_D$ (`New.CMLattice.mul_t_sub_t_mem`). The sum $\wp''(t) = 6\sum_{l}(l - t)^{-4}$ scales by $c^{-4}$, and it is $2$ for both lattices. $\square$

**Remark (Formalization).** The source does not prove that the class of $\mathfrak{a}$ in (2) depends only on $C$. It works instead with the predicate $C$ *is in the class* $\mathcal{C}$ (`New.CMLattice.IsInClass`): some multiple of an ideal in $\mathcal{C}$ is $\Lambda_C$. A family of CM lattices $D : \mathrm{Cl}_K \to \text{CMLattice}$ with $D_{\mathcal{C}}$ in the class $\mathcal{C}$ exists, and it can contain any given CM lattice (`New.CMLattice.exists_forall_isInClass`). The lemma above makes the family unique up to fourth roots of unity.

### The class number is odd

**Theorem (Odd class number).** Let $d$ be a prime with $d \equiv 7 \pmod 8$. The map $\mathcal{C} \mapsto \mathcal{C}^2$ on $\mathrm{Cl}_K$ is bijective. So $h$ is odd.

Lean: `New.QuadField.classGroup_sq_bijective` (Lib/CM/ChowlaSelberg.lean).

Classically this is the case of Gauss's genus theory with one ramified prime: the $2$-rank of $\mathrm{Cl}_K$ is the number of ramified primes minus $1$, which is $0$. The source proves it directly.

*Proof.* The group is finite, so it suffices that the kernel of squaring is trivial. Let $I$ be an integral ideal with $I^2 = (\alpha)$, and put $n = NI$. Then $\alpha\bar\alpha = n^2$. Put $J = (\bar\alpha + n)I$. Then
$$J^2 = (\bar\alpha + n)^2(\alpha) = \bigl(n(\alpha + n)(\bar\alpha + n)\bigr),$$
since $(\bar\alpha + n)^2\alpha = n^2\bar\alpha + 2n^3 + n^2\alpha = n(\alpha + n)(\bar\alpha + n)$. So $J^2$ is generated by a rational integer, and $J^2 = (NJ)$. Write $NJ = s^2r$ with $r$ squarefree. Then $(r) = (J/s)^2$ is the square of an ideal. For a prime $p \mid r$, the ideal $(p)$ is then a square, so $p$ is ramified, and $p = d$ (`New.QuadField.eq_d_of_span_eq_sq`, from the different of $K$). So $r = 1$ or $r = d$, and $J = (s)$ or $J = (s\sqrt{-d})$. In both cases $J$ is principal, so $I$ is principal. $\square$

The odd class number is used in [Section 7](/decl/New.CMLattice.chowla_selberg/): every class $\mathcal{C}$ is a square $\mathcal{B}^2$, and this gives ideals $\mathfrak{c}_{\mathcal{C}}$ in the classes with product $(1)$.

### The discriminants at the points of order two

Let $u$ be a point of order $2$ of a lattice $L$. If $L$ is replaced by $cL$ with $c^4 = \wp''(u)/2$, then $\wp''(cu) = 2$, and the discriminant of $cL$ is $144\wp_{cL}(cu)^2 - 64$, by [the discriminant](/decl/New.CMLattice.disc_eq/). In terms of $L$ this is the following number.

**Definition (Scaled discriminant).** For a lattice $L$ and $u \in \mathbb{C}$,
$$s_L(u) = \frac{288\, \wp(u)^2}{\wp''(u)} - 64.$$

Lean: `PeriodPair.scaledDisc` (Lib/CM/GoodReduction.lean).

For a CM lattice, $\wp''(t) = 2$ and $a_1^2 = 12\wp(t)$, so $s(t) = a_1^4 - 64$ (`New.CMLattice.scaledDisc_t`). The value of $s_L$ at a point $u \notin L$ with $2u \notin L$ is a junk value of no use. The lemmas below state the hypothesis that $u$ has order $2$ (`PeriodPair.IsOrderTwo`: $u \notin L$ and $u + u \in L$).

**Lemma (The three points of order two).** Let $u_1, u_2, u_3$ be points of order $2$ of $L$ with $u_1 + u_2 + u_3 \in L$, and $e_i = \wp(u_i)$. Then
$$s(u_1) = \frac{-16(e_2 - e_3)^2}{(e_3 - e_1)(e_1 - e_2)},$$
and
$$s(u_1) + s(u_2) + s(u_3) = -48, \qquad s(u_1)\, s(u_2)\, s(u_3) = -2^{12}.$$

Lean: `PeriodPair.IsOrderTwo.scaledDisc_sum_prod` (Lib/CM/GoodReduction.lean), with `PeriodPair.IsOrderTwo.scaledDisc_eq`.

*Proof.* The $e_i$ are the three distinct roots of $4x^3 - g_2x - g_3$, so $e_1 + e_2 + e_3 = 0$, and $\wp''(u_1) = 6e_1^2 - g_2/2 = 2(e_1 - e_2)(e_1 - e_3)$. Then $288e_1^2/\wp''(u_1) - 64$ simplifies to the formula for $s(u_1)$. Put $\delta_1 = e_2 - e_3$, $\delta_2 = e_3 - e_1$, $\delta_3 = e_1 - e_2$. Then $s(u_i) = -16\delta_i^2/(\delta_j\delta_k)$, and $\delta_1 + \delta_2 + \delta_3 = 0$. The sum is $-16(\delta_1^3 + \delta_2^3 + \delta_3^3)/(\delta_1\delta_2\delta_3) = -48$, and the product is $(-16)^3 = -2^{12}$. $\square$

**Lemma (Two-isogeny).** Let $u_1, u_2, u_3$ be as above, let $L'$ be a lattice and $c \ne 0$ with $cx \in L'$ if and only if $x \in L$ or $x + u_1 \in L$. So $L' = c(L + \mathbb{Z}u_1)$. Then
$$s_L(u_1)\, s_{L'}(cu_2) = 2^{12}.$$

Lean: `PeriodPair.IsOrderTwo.scaledDisc_mul_of_isogeny` (Lib/CM/GoodReduction.lean).

*Proof.* Sum over the two cosets of $L$ in $c^{-1}L'$. This gives $\wp''_{L'}(cy) = c^{-4}(\wp''_L(y + u_1) + \wp''_L(y))$ and $g_2(L') = c^{-4}(g_2(L) + 10\wp''_L(u_1))$, (`PeriodPair.deriv_derivWeierstrassP_of_two_cosets`, `PeriodPair.g₂_eq_of_two_cosets`). At $y = u_2$, the points $u_2$ and $u_2 + u_1 \equiv u_3$ appear. The factors $c$ cancel in $s_{L'}(cu_2)$, and the identity becomes a rational identity in $e_1, e_2, e_3$ with $e_1 + e_2 + e_3 = 0$. $\square$

### Good reduction

For a CM lattice $C$ and $b \in \{\omega, \bar\omega\}$, the three points of order $2$ are $bt$, $(1 - b)t$ and $t$, with sum $2t \in \Lambda$ (`New.CMLattice.scaledDisc_sum_prod`). The lattice $\Lambda + \mathbb{Z}\,bt$ is $\Lambda$ times the inverse of a prime above $2$ (`New.CMLattice.halfIdeal`). So the $2$-isogeny moves the class of the lattice by a fixed class $\mathfrak{g}$.

**Lemma (A cycle in the class group).** Let $b = \omega$ or $b = \bar\omega$. There is a class $\mathfrak{g} \in \mathrm{Cl}_K$ such that for all CM lattices $C$ in the class $\mathcal{C}$ and $D$ in the class $\mathfrak{g}\mathcal{C}$,
$$s_C(bt_C)\, s_D((1 - b)t_D) = 2^{12}, \qquad s_D(bt_D)\, s_D(t_D) = -s_C(bt_C).$$

Lean: `New.CMLattice.exists_class_scaledDisc_mul` (Lib/CM/GoodReduction.lean), with `New.CMLattice.scaledDisc_two_isogeny`.

*Proof.* Take $D' = c(\Lambda_C + \mathbb{Z}\,bt_C)$ with the scaling that makes it a CM lattice, and $\mathfrak{g}$ the class of the inverse of the prime above $2$ that does not contain $b$ (`New.CMLattice.halfIdeal`, `New.CMLattice.mul_mem_iff_of_halfIdeal`). By the lemma on fourth roots of unity, $\Lambda_D = c'\Lambda_{D'}$ with $c'^4 = 1$, and $s$ does not change under this scaling. The first identity is [the two-isogeny lemma](/decl/PeriodPair.IsOrderTwo.scaledDisc_mul_of_isogeny/). The product of the three values of $s_D$ is $-2^{12}$. Divide it by the first identity to get the second. $\square$

The next lemma is the $p$-adic heart of the argument. It uses only the ultrametric inequality: if $|a + b| \le 1$ and $|ab| > 1$, then $|a| = |b|$, so $|a|^2 = |ab|$.

**Lemma (Cycle lemma).** Let $p$ be a prime, $G$ a finite group, $g \in G$, and $s, s', s_0 : G \to \mathbb{C}_p$ such that for all $c \in G$,
$$|s(c) + s'(c) + s_0(c)| \le 1, \qquad |s(c)\, s'(gc)| \le 1, \qquad s(gc)\, s_0(gc) = -s(c).$$
Then $|s(c)| \le 1$ for all $c$.

Lean: `New.norm_le_one_of_cycle` (Lib/CM/GoodReduction.lean).

*Proof.* Suppose $|s(c)| > 1$. Then $|s'(gc)| < 1$ by the second condition. So $|s(gc) + s_0(gc)| \le 1$ by the first condition at $gc$, and $|s(gc)s_0(gc)| = |s(c)| > 1$ by the third. By the ultrametric remark, $|s(gc)|^2 = |s(c)|$, and $|s(gc)| > 1$. By induction, $|s(g^ic)|^{2^i} = |s(c)|$ for all $i$. At $i$ equal to the order $n$ of $g$, this says $|s(c)|^{2^n} = |s(c)|$, which is false for $|s(c)| > 1$. $\square$

**Theorem (Good reduction).** Let $p$ be a prime, $d$ a prime with $d \equiv 7 \pmod 8$, $C$ a CM lattice for $d$, and $\iota : \mathbb{C} \to \mathbb{C}_p$ a ring homomorphism. Then
$$|\iota(a_1)^4 - 64|_p = 1.$$

Lean: `New.CMLattice.norm_disc_eq_one` (Lib/CM/GoodReduction.lean), with `New.CMLattice.norm_scaledDisc_le_one` and `New.CMLattice.prod_scaledDisc_t`.

*Proof.* Take a family $D_{\mathcal{C}}$, one CM lattice in each class, that contains $C$. First, $|\iota\, s_{D_{\mathcal{C}}}(bt)| \le 1$ for $b \in \{\omega, \bar\omega\}$ and all $\mathcal{C}$. This is [the cycle lemma](/decl/New.norm_le_one_of_cycle/) for the group $\mathrm{Cl}_K$, the class $\mathfrak{g}$ of [the cycle in the class group](/decl/New.CMLattice.exists_class_scaledDisc_mul/), and $s(\mathcal{C}) = \iota s_{D_{\mathcal{C}}}(bt)$, $s'(\mathcal{C}) = \iota s_{D_{\mathcal{C}}}((1 - b)t)$, $s_0(\mathcal{C}) = \iota s_{D_{\mathcal{C}}}(t)$. The three conditions are the sum $-48$, the product $2^{12}$ and the second identity of the cycle, and $|\iota(n)| \le 1$ for $n \in \mathbb{Z}$. Second, $s(t) = -48 - s(\omega t) - s(\bar\omega t)$, so $|\iota s_{D_{\mathcal{C}}}(t)| \le 1$. Third, multiply $s_D(\omega t_D)s_D(t_D) = -s_C(\omega t_C)$ over all $\mathcal{C}$, with $D = D_{\mathfrak{g}\mathcal{C}}$. The products of the $s(\omega t)$ cancel, since they are not $0$, and
$$\prod_{\mathcal{C}} s_{D_{\mathcal{C}}}(t) = (-1)^h.$$
So the numbers $|\iota s_{D_{\mathcal{C}}}(t)|$ are at most $1$ and have the product $1$. Each is $1$. For $\mathcal{C}$ with $D_{\mathcal{C}} = C$ this is $|\iota(a_1^4 - 64)| = 1$. $\square$

**Example (d = 7).** For $d = 7$ the class number is $1$, and the family is one CM lattice $C$. The identity $\prod s(t) = (-1)^h$ gives $s(t) = -1$, so $a_1^4 = 63$ and $\Delta = -1$. The other two values satisfy $s(\omega t) + s(\bar\omega t) = -47$ and $s(\omega t)s(\bar\omega t) = 2^{12}$, so they are $(-47 \pm 45\sqrt{-7})/2$, of norm $2^{12}$. They are not units at $2$, and the cubic $y^2 + 63^{1/4}xy = x^3 + x$ is the only one of the three scaled cubics with unit discriminant. Its $j$-invariant is $(63 - 48)^3/(63 - 64) = -3375$, the $j$-invariant of the curves with CM by $\mathbb{Z}[(1 + \sqrt{-7})/2]$. For comparison, the curve 49a1 of Cremona's tables, $y^2 + xy = x^3 - x^2 - 2x - 1$, has the same $j$-invariant and the discriminant $-7^3$. The two curves are isomorphic over a finite extension of $\mathbb{Q}$, since $j \ne 0, 1728$. The source model has the discriminant $-1$, a unit at every prime.

Classically, $j(E)$ is an algebraic integer for a CM curve (Silverman, *Advanced Topics*, Chapter II, §6), so $E$ has potential good reduction everywhere (Silverman, *The Arithmetic of Elliptic Curves*, Chapter VII, Proposition 5.5). The theorem above is an explicit form of this for the source model. If $a_1$ is integral and $a_1^4 - 64$ is a unit at all primes of the number field $K(a_1)$, then the model $y^2 + a_1xy = x^3 + x$ has good reduction everywhere over $K(a_1)$. The integrality of $a_1$ is in [Section 5](/decl/New.CMLattice.norm_a₁_le_one/). The docstring of the file relates the theorem to the unit property of Siegel units (Ramachandra, Robert), and the file cites Kubert and Lang, *Modular Units*, and Birch, *Weber's class invariants* (Mathematika 16, 1969).

**Remark (Formalization).** The source states good reduction for every ring homomorphism $\iota : \mathbb{C} \to \mathbb{C}_p$. It does not prove that $a_1$ is algebraic. A ring homomorphism $\mathbb{C} \to \mathbb{C}_p$ exists by the axiom of choice, and it can send a transcendental number to any transcendental element of $\mathbb{C}_p$, for example one of norm $p$. So a statement for all $\iota$ that a number $x$ has norm $1$ can hold only for algebraic $x$. The source uses the theorem only in this form, with the class `New.PadicPlace` of Section 5 or an explicit $\iota$, and it does not derive the algebraicity. No step of the proof uses the reduction of the curve modulo a prime.
