---
title: The finite places and the cocycle as a Gauss sum
lean:
  - Lib/Weil/Construction/WeilData.lean
  - Lib/Weil/Construction/FiniteMultiplier.lean
  - Lib/Weil/Construction/FiniteCocycle.lean
decls:
  - New.WeilData
  - New.stdLattice.finVac
  - New.integral_selfDualAddChar_stdLattice
  - New.stdLattice.isVacuum_finVac
  - New.glMultiplier
  - New.latticeMeasure_inter_eq_glMultiplier
  - New.glMultiplier_mul_diagGL_mul
  - New.finMultiplier
  - New.upsilon_mul_finMultiplier
  - New.stdLattice.exists_gauss_sum_finProjAction
  - New.eq_one_of_apply_apply_eq_neg
  - New.stdLattice.mem_cocycleRadical
  - New.finAction
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The finite places and the cocycle as a Gauss sum

This section builds the Weil representation of the finite adelic unitary group. The space is the space of vectors of finite adeles, and the vacuum is a twisted indicator function of the standard lattice. The multiplier is a character of the determinant of a lattice index. The cocycle of [Section 3](/chapter/weil-representation/#weil-operators-and-their-cocycle) becomes a Gauss sum over a finite module, and the section proves that it equals $1$. At a split place the terms of the sum are all $1$. At an inert place a congruence modulo $4$ fixes the sign. The result is the finite factor of the adelic Weil representation of Section 6.

Throughout, $E$ is a CM field with maximal totally real subfield $E^+$, $\mathbb{A}_{E,f}$ is the ring of finite adeles of $E$, and $\hat{\mathcal{O}} = \prod_w \mathcal{O}_w$ is the ring of integral finite adeles. The bar is complex conjugation on $E$ and on its adeles. For a finite set $\iota$ and vectors $x, y \in \mathbb{A}_{E,f}^\iota$ we write $x^* y = \sum_i \bar{x}_i y_i$. The group $G_f$ is the finite adelic unitary group of [Volume 4](/decl/New.Gf/): the matrices $g \in \mathrm{GL}_\iota(\mathbb{A}_{E,f})$ with $g^* g = 1$. The group $K_f \subset G_f$ is the stabilizer of the lattice $\hat{\mathcal{O}}^\iota$, the [standard level](/decl/New.stdLevel/). The character $\psi_f$ is the standard additive character of $\mathbb{A}_{E,f}$.

### Weil data

The construction needs some arithmetic data on $E$. The source collects them in one structure.

**Definition (Weil data).** Weil data on $E$ consist of the following.

1. The field $E$ contains a primitive root of unity of order $5040$, as in [Volume 4](/decl/New.HasPrimitiveRoot5040/).
2. A splitting character $\upsilon$: a unitary Hecke character of $E$ with $\upsilon(\bar{x}) = \upsilon(x)^{-1}$, and with $\upsilon(x) = \prod_\tau x_\tau / |x_\tau|$ over the infinite places $\tau$ when the finite part of the idele $x$ is a unit of $\hat{\mathcal{O}}$.
3. An element $\jmath \in E$ with $\bar{\jmath} = -\jmath$ and $\operatorname{Im} \Phi_\tau(\jmath) > 0$ for each embedding $\Phi_\tau$ of the CM type.
4. A finite idele $\alpha$ such that, at every finite place $w$, the valuation of $(\jmath \alpha \bar{\alpha})_w$ is $\exp$ of the multiplicity of $w$ in the different of $E$.
5. The element $c_0 = (1 - \jmath^{-1})/2$ is an algebraic integer.
6. At every finite place $w$ with $\bar{w} = w$, the character $\upsilon$ is $-1$ at the chosen uniformizer of $w$.

Lean: `New.WeilData`, `New.SplittingChar`, `New.WeilData.traceOne` (Lib/Weil/Construction/WeilData.lean).

Since $\bar{\jmath} = -\jmath$, we have $c_0 + \bar{c}_0 = 1$. Condition (4) says that $\jmath\alpha\bar{\alpha}$ generates the inverse different locally. So for the character
$$\psi_0(z) = \psi_f(\jmath \alpha \bar{\alpha} z)$$
of $\mathbb{A}_{E,f}$, the ring $\hat{\mathcal{O}}$ is its own dual for the pairing $(z, u) \mapsto \psi_0(z u)$. This is the self-duality that the construction uses.

**Remark (Formalization).** The Weil data are a class, so the statements of this section and of the rest of the volume do not show them. The source gives one instance, `New.Parameters.instWeilDataE`, for the field $E$ of the main argument. There $\jmath = -1/\sqrt{-d}$, and the splitting character is picked with `.some` from a proof that one exists. The findings record it as open whether a statement of the main argument depends on this pick (F-043). Condition (6) uses a uniformizer that the source fixes at each place.

### The lattice vacuum

The Heisenberg datum at the finite places lives on $W_f = \mathbb{A}_{E,f}^\iota$. Its bicharacter is
$$\beta(x, y) = \psi_0\big(\tfrac{1}{2} y^* x\big).$$
It satisfies $\beta(x, x) = 1$. The reason is that $c_0 + \bar{c}_0 = 1$, so $\tfrac12 x^* x = t + \bar{t}$ with $t = c_0 \tfrac12 x^* x$, and $\psi_0$ is trivial on elements of this form. The measure is the Haar measure $\mu_f$ on $W_f$ that gives $\hat{\mathcal{O}}^\iota$ mass $1$.

**Definition (The lattice vacuum).** Let $L = \hat{\mathcal{O}}^\iota$. The finite vacuum is
$$e_f(x) = \begin{cases} \psi_0\big(c_0 \cdot \tfrac12 \cdot x^* x\big) & \text{if } x \in L, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.stdLattice.finVac`, `New.stdLattice.finHeisenberg`, `New.stdLattice.semichar`, `New.stdLattice.semichar_eq_ψf`, `New.stdLattice`, `New.latticeMeasure`, `New.latticeMeasure_stdLattice` (Lib/Weil/Construction/FiniteMultiplier.lean).

In terms of $\psi_f$ alone, $e_f(x) = \psi_f(-\tfrac14 y^* y)$ with $y = \alpha x$, for $x \in L$. On the lattice, $e_f(x)^2 = 1$, so $e_f$ takes the values $0$ and $\pm 1$. For $y \in L$ and any $x$,
$$e_f(x)\, e_f(y)\, \beta(x, y) = e_f(x + y).$$

**Lemma (Self-duality of the lattice).** For every $x \in W_f$,
$$\int_L \psi_0(x^* y)\, d\mu_f(y) = \begin{cases} 1 & \text{if } x \in L, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.integral_selfDualAddChar_stdLattice`, `New.stdLattice.mem_stdLattice_iff_selfDualAddChar` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* First, $x \in L$ if and only if $\psi_0(y^* x) = 1$ for every $y \in L$. One direction is the triviality of $\psi_0$ on $\hat{\mathcal{O}}$. For the other, test with $y$ a multiple of a basis vector and use that $\hat{\mathcal{O}}$ is its own dual for $\psi_0$. So the character $y \mapsto \psi_0(x^* y)$ is trivial on the compact open group $L$ exactly when $x \in L$. The orthogonality of characters on $L$ gives the integral, since $L$ has mass $1$. $\square$

**Theorem (The lattice vacuum).** The function $e_f$ is a vacuum for the Heisenberg datum $(W_f, \beta)$ and the measure $\mu_f$.

Lean: `New.stdLattice.isVacuum_finVac`, `New.stdLattice.finVac_add` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* The function $e_f$ is continuous, since $L$ is open and closed. It has compact support, so it is integrable. It is even, $e_f(0) = 1$, and it is real, since its values are $0$ and $\pm 1$. It remains to prove the vacuum identity of [Section 2](/decl/New.Heisenberg.IsVacuum/),
$$\int_{W_f} e_f(z)\, e_f(x - y - z)\, \beta(z, y)\, \beta(z + y, x)\, d\mu_f(z) = e_f(y)\, e_f(x).$$
The integrand vanishes for $z \notin L$. For $z \in L$, expand $e_f(x - y - z)$ with the addition rule above, and use $e_f(z)^2 = 1$ and $\beta(z, x)^2 = \psi_0(x^* z)$. The integrand becomes $e_f(x - y)\beta(x, y)^{-1}\psi_0(x^* z)$. By [the self-duality of the lattice](/decl/New.integral_selfDualAddChar_stdLattice/), the integral is $e_f(x - y)\beta(x,y)^{-1}$ if $x \in L$ and $0$ otherwise. If $x \in L$, the addition rule for $-y$ and $x$ gives $e_f(y) e_f(x)$. If $x \notin L$, the right side is $0$ too. $\square$

### The multiplier

Let $g \in \mathrm{GL}_\iota(\mathbb{A}_{E,f})$. An invertible matrix $u$ saturates $g$ if $u$ and $g u$ are integral and $u^{-1} = l + m g$ for integral matrices $l$ and $m$. Then $u L = L \cap g^{-1} L$. Saturating matrices exist by the theory of elementary divisors over $\hat{\mathcal{O}}$, and the source picks one, $u_g$. Let
$$\chi_f(x) = \upsilon(x)\, |x|^{-1/2}$$
on the finite ideles, extended by $1$ at the infinite places. By condition (2) of the Weil data, $\chi_f(x)$ depends only on the valuations of $x$ at the finite places.

**Definition (The multiplier on $\mathrm{GL}_\iota$).** For $g \in \mathrm{GL}_\iota(\mathbb{A}_{E,f})$, let $\Delta_f(g) = \chi_f(\det u_g)$.

Lean: `New.glMultiplier`, `New.saturatingElem`, `New.IsSaturating`, `New.chiFin`, `New.chiAdelic` (Lib/Weil/Construction/FiniteMultiplier.lean).

**Remark (Formalization).** The matrix $u_g$ is a choice: the source takes it with `.some` from a proof of existence. The value $\Delta_f(g)$ does not depend on the choice, since two saturating matrices of $g$ have determinants with the same valuations at every place, and $\chi_f$ sees only valuations. The source proves this as a lemma, `New.IsSaturating.glMultiplier_eq`. The value is never $0$, because $\chi_f$ takes values in $\mathbb{C}^\times$.

**Proposition (The multiplier as a volume).** For $g \in \mathrm{GL}_\iota(\mathbb{A}_{E,f})$,
$$\mu_f\{x \in L : g x \in L\} = |\Delta_f(g)|^{-2}.$$
Equivalently, $|\Delta_f(g)|^2$ is the index of $L \cap g^{-1}L$ in $L$.

Lean: `New.latticeMeasure_inter_eq_glMultiplier`, `New.norm_glMultiplier_sq` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* The set is $u_g L$, and its volume is $|\det u_g|$. Since $\upsilon$ is unitary, $|\chi_f(\det u_g)|^2 = |\det u_g|^{-1}$. $\square$

**Theorem (The multiplier in elementary divisors).** Let $k, k' \in \mathrm{GL}_\iota(\hat{\mathcal{O}})$ and let $d_i$ be finite ideles for $i \in \iota$. Then
$$\Delta_f\big(k \operatorname{diag}(d) k'\big) = \prod_{i \in \iota} \chi_f\big(\operatorname{den}(d_i)\big),$$
where $\operatorname{den}(x)$ is the idele equal to $1$ where $x$ is integral and to $x^{-1}$ elsewhere.

Lean: `New.glMultiplier_mul_diagGL_mul`, `New.glMultiplier_mul_of_mem`, `New.glMultiplier_inv` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* Multiplication by integral invertible matrices on both sides does not change $\Delta_f$, since it moves a saturating matrix to a saturating matrix with a unit determinant. For a diagonal matrix, the diagonal matrix of the denominators saturates it. $\square$

**Definition (The multiplier on $G_f$).** For $g \in G_f$, the multiplier $\Delta_f(g)$ is the multiplier of $g$ as an element of $\mathrm{GL}_\iota(\mathbb{A}_{E,f})$.

Lean: `New.finMultiplier`, `New.finMultiplier_inv`, `New.finMultiplier_eq_one_of_mem`, `New.finMultiplier_ne_zero`, `New.norm_finMultiplier_sq` (Lib/Weil/Construction/FiniteMultiplier.lean).

For $g \in G_f$ we have $g^{-1} = g^*$, and this gives $\Delta_f(g^{-1}) = \overline{\Delta_f(g)}$. The multiplier is $1$ on $K_f$, it is never $0$, and $|\Delta_f(g)|^2$ is the index of $L \cap g^{-1}L$ in $L$.

**Proposition (The phase of the multiplier).** For $g \in G_f$,
$$\upsilon(\det g)\, \Delta_f(g) = \overline{\Delta_f(g)},$$
where $\det g$ is read as an idele with component $1$ at the infinite places.

Lean: `New.upsilon_mul_finMultiplier`, `New.finMultiplier_eq_of_supportedOn` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* Both sides equal $\Delta_f(g^{-1})$. The left side is $\chi_f(\det g)\Delta_f(g)$, and $|\det g| = 1$ since $\det g$ is unitary. $\square$

The source also gives a formula at a set $S$ of places disjoint from its conjugate: if $g \in G_f$ is $1$ outside $S \cup \bar{S}$ and $a$ is the matrix equal to $g$ at $S$ and to $1$ elsewhere, then $\Delta_f(g) = |\Delta_f(a)|^2\, \overline{\chi_f(\det a)}$.

### The cocycle as a Gauss sum

The group $G_f$ acts on $W_f$ by matrices. It preserves $\beta$, since $(g y)^*(g x) = y^* x$. It preserves $\mu_f$, since $|\det g| = 1$. The multiplier $\Delta_f$ is continuous, since it is invariant under right translation by the open subgroup $K_f$. So with the cocycle
$$c(g, s) = \Delta_f(g)\Delta_f(s)\Delta_f((g s)^{-1}) \int_{W_f}\int_{W_f} e_f(s x)\, e_f(g s y)\, \beta(x, y)\, e_f(x + y)\, d\mu_f(y)\, d\mu_f(x)$$
we get a [multiplier action](/decl/New.Heisenberg.MultiplierAction/) of $G_f$ on the lattice vacuum. The task is to show $c = 1$.

The integrand is supported on the compact module
$$M = \{(x, y) : x + y \in L,\ s x \in L,\ g s y \in L\},$$
and on $M$ it equals $\psi_0(\bar{c}_0\, y^* x)$. It is constant on the cosets of $M \cap (L \times L)$. So the double integral is a finite sum.

**Theorem (The cocycle as a Gauss sum).** Let $g, s \in G_f$. There are a finite $\hat{\mathcal{O}}$-module $Q$ and a function $\gamma \colon Q \to \mathbb{A}_{E,f}$ with the following properties.

1. $c(g, s)\, \Delta_f(s^{-1})\, \Delta_f(g s) = \Big(\sum_{q \in Q} \psi_0(\gamma(q))\Big)\, \Delta_f(g)$.
2. For all $t \in \hat{\mathcal{O}}$ and $q \in Q$, $\psi_0(\gamma(t q)) = \psi_0(\bar{t}\, t\, \gamma(q))$.
3. For all $t \in \hat{\mathcal{O}}$ such that the matrix $t s^{-1}$ is integral, $t q = 0$ for every $q \in Q$.

Lean: `New.stdLattice.exists_gauss_sum_finProjAction`, `New.stdLattice.finProjAction`, `New.stdLattice.cocycleIntegrand_eq`, `New.stdLattice.measureReal_prod_inter_cocycleSubmodule` (Lib/Weil/Construction/FiniteCocycle.lean).

*Proof.* Take $Q = M / (M \cap (L \times L))$ and $\gamma(q) = \bar{c}_0\, y^* x$ for a representative $(x, y)$ of $q$. The quotient is finite, since $M$ is compact and $L \times L$ is open. The double integral is the volume of $M \cap (L \times L)$ times the sum over $Q$. By [the multiplier as a volume](/decl/New.latticeMeasure_inter_eq_glMultiplier/), that volume is $|\Delta_f(s)|^{-2} |\Delta_f(g s)|^{-2}$. With $|\Delta_f(h)|^2 = \Delta_f(h^{-1})\Delta_f(h)$, the factors cancel and give (1). Property (2) holds since $\gamma$ is sesquilinear in the representative. For (3), if $(x, y) \in M$ then $t x = (t s^{-1})(s x) \in L$ and $t(x + y) \in L$, so $t(x, y) \in L \times L$. $\square$

When $s \in K_f$, the matrix $s^{-1}$ is integral, so (3) with $t = 1$ gives $Q = 0$. The sum is $1$, and since $\Delta_f(g s) = \Delta_f(g)$ and $\Delta_f(s^{-1}) = 1$, we get $c(g, s) = 1$. The cocycle also has absolute value $1$ for all $g$ and $s$: by [the cocycle relation](/decl/New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp/), $c(g,s)$ is the scalar $\omega((g s)^{-1})\omega(g)\omega(s)$, and each operator is an isometry, so it keeps the vacuum a unit vector.

Lean: `New.stdLattice.finProjAction_cocycle_eq_one_of_mem`, `New.stdLattice.norm_cocycle_eq_one` (Lib/Weil/Construction/FiniteCocycle.lean).

### A sign from a congruence modulo 4

At an inert place, the sum is real and has absolute value a power of $r$, but its sign is not clear.

**Lemma (A sign from a real sum of roots of unity).** Let $X$ be a finite abelian group without $2$-torsion, and let $f \colon X \to X$ be a map with $f(f(x)) = -x$ for every $x$. Let $F \colon X \to \mathbb{C}$ with $F(f(x)) = F(x)$ for every $x$, with values that are roots of unity, with $F(0) = 1$, and with a real sum. Let $r$ be an integer with $r \equiv 1 \pmod 4$, let $a, b \ge 0$, and let $c \in \mathbb{C}$ with $|c| = 1$ and
$$c\, r^a = \Big(\sum_{x \in X} F(x)\Big)\, r^b.$$
Then $c = 1$.

Lean: `New.eq_one_of_apply_apply_eq_neg` (Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* Conjugate the equation. The sum is real and $\bar{c} = c^{-1}$, so $c^{-1} = c$ and $c = \pm 1$. Suppose $c = -1$. Off $0$, the orbits of $f$ have four points, since $f^2(x) = -x \ne x$ for $x \ne 0$. The function $F$ is constant on each orbit, so $\sum_{x \ne 0} F(x) = 4z$ for an algebraic integer $z$. The equation becomes $4 z r^b = -(r^a + r^b)$. So $z r^b$ is a rational algebraic integer, hence an integer, and $4$ divides $r^a + r^b$. But $r^a + r^b \equiv 2 \pmod 4$. $\square$

### The finite cocycle is trivial

**Theorem (The finite cocycle is trivial).** For all $g, s \in G_f$, $c(g, s) = 1$. In the source, this is the statement that every $s \in G_f$ lies in the [radical of the cocycle](/decl/New.Heisenberg.IsVacuum.cocycleRadical/).

Lean: `New.stdLattice.mem_cocycleRadical`, `New.stdLattice.eq_one_of_gauss_sum_of_inert`, `New.stdLattice.exists_finMultiplier_eq_neg_pow`, `New.stdLattice.finMultiplier_div_nonneg_of_isSplit` (Lib/Weil/Construction/FiniteCocycle.lean), `New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert` (Lib/General/NumberTheory/FrobeniusOrbits.lean).

*Proof.* The elements $s$ with $c(g, s) = 1$ for all $g$ form a subgroup, by [the radical of the cocycle](/decl/New.Heisenberg.IsVacuum.cocycleRadical/). It contains $K_f$, as shown above. A subgroup of $G_f$ that contains $K_f$ and, for each finite place $w$, the elements that are $1$ outside $\{w, \bar w\}$, is all of $G_f$. So let $s$ be $1$ outside $\{w, \bar{w}\}$.

Write $g = a b$, with $a$ supported on $\{w, \bar{w}\}$ and $b$ equal to $1$ there. Then $\Delta_f(x b) = \Delta_f(x)\Delta_f(b)$ for $x$ supported on $\{w, \bar w\}$, and $b$ commutes with $s$. The factor $\Delta_f(b)$ cancels in the Gauss sum identity, which becomes
$$c(g, s)\, \Delta_f(s^{-1})\, \Delta_f(a s) = \Big(\sum_{q \in Q} \psi_0(\gamma(q))\Big)\, \Delta_f(a).$$
Let $t \in \hat{\mathcal{O}}$ be the idempotent that is $0$ at $\bar{w}$ and $1$ elsewhere.

*Split place*, $\bar{w} \ne w$. First reduce to the case where $s^{-1}$ is integral at $w$. Take a matrix $u$ that saturates $s^{-1}$ at $w$, and let $h \in G_f$ be the element with component $u^{-1}$ at $w$, the inverse conjugate transpose at $\bar{w}$, and $1$ elsewhere. Then $h^{-1}$ and $(h s)^{-1} = s^{-1}u$ are integral at $w$, so the case gives $h$ and $h s$ in the subgroup, and hence $s$. Now $t s^{-1}$ is integral at every place, so $t$ kills $Q$. The element $1 - t$ acts on $Q$ as the identity, and $\overline{(1 - t)}(1 - t) = 0$, because the first factor lives at $w$ and the second at $\bar w$. Property (2) gives $\psi_0(\gamma(q)) = \psi_0(0) = 1$ for every $q$. So
$$c(g, s) = |Q| \cdot \frac{\Delta_f(a)}{\Delta_f(a s)\, \Delta_f(s^{-1})}.$$
The formula at $S = \{w\}$ shows that the quotient on the right is a nonnegative real number: its phases are values of $\overline{\chi_f}$ at determinants, and they cancel. So $c(g, s) \ge 0$, and $|c(g, s)| = 1$ gives $c(g, s) = 1$.

*Inert place*, $\bar{w} = w$. By the root of unity of order $5040$, the residue field of $w$ has $q_w = r^2$ elements with $r \equiv 3 \pmod 4$. An element $x$ supported on $w$ has $\Delta_f(x) = (\upsilon(\varpi_w) \sqrt{q_w})^n$ for some $n \ge 0$, where $\varpi_w$ is the uniformizer. By condition (6) of the Weil data, this is $(-r)^n$. So the identity reads $c\,(-r)^{k} = (\sum_q \psi_0(\gamma(q)))\,(-r)^m$ for some $k$ and $m$. Apply [the sign lemma](/decl/New.eq_one_of_apply_apply_eq_neg/) with $X = Q$, the integer $-r \equiv 1 \pmod 4$, and $F(q) = \psi_0(\gamma(q))$. Its hypotheses hold for these reasons.

1. The values of $\psi_0$ are roots of unity, and $F(0) = 1$ by property (2) with $t = 0$.
2. The sum is real. A unit of $\hat{\mathcal{O}}$ with norm $\bar{t}t = -1$ permutes $Q$, and by property (2) it conjugates the terms.
3. The group $Q$ has no $2$-torsion. The element $t$ kills $Q$, and $t - 2$ is a unit of $\hat{\mathcal{O}}$, since $q_w$ is odd.
4. The field contains an element $i$ with $i^2 = -1$ and $\bar{\imath} i = 1$. The map $f(q) = i q$ satisfies $f(f(q)) = -q$, and by property (2) it preserves $F$.

So $c(g, s) = 1$. $\square$

**Definition (The finite Weil action).** The finite Weil action is the multiplier action of $G_f$ on $(W_f, \beta, \mu_f, e_f)$ with multiplier $\Delta_f$ and cocycle $1$.

Lean: `New.finAction` (Lib/Weil/Construction/FiniteCocycle.lean).

By [the Weil representation of an action](/decl/New.Heisenberg.IsVacuum.weilRep/), it gives a continuous unitary representation of $G_f$ on the lattice model. Section 6 takes its tensor product with the real representation of Section 4.

**Remark (Formalization).** The classical construction fixes the scalars of the Weil representation over a unitary group with a splitting character, as in Kudla's work on the splitting of metaplectic covers. The source does not use a metaplectic cover or the Weil index. It gives the explicit multiplier $\Delta_f$ and proves that the cocycle is $1$ for the lattice vacuum and this normalization. The inert case uses the root of unity of order $5040$ and condition (6). The theorem is a special case of the general splitting, for this normalization only.
