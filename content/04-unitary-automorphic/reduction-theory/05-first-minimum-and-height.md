---
title: The first minimum and the height
lean:
  - Lib/Adelic/Reduction/FirstMinimumShortBases.lean
decls:
  - New.weak_transference
  - New.weak_transference_covering_radius
  - New.span_norm_le_eq_top_of_covering
  - New.Space.archCoords
  - New.Space.firstMinimum
  - New.Space.height
  - New.Space.IsModerate
  - New.Space.IsRapid
  - New.Space.finite_latticeBall
  - New.Space.firstMinimum_pos
  - New.Space.form_eq_zero_of_norm_mul_lt_one
  - New.Space.eq_zero_of_isotropic_of_definite
  - New.Space.firstMinimum_move_eq_one
  - New.Space.firstMinimum_le_norm_of_inner_int
  - New.Space.exists_norm_sub_archCoords_le
  - New.Space.shortBasisConst
  - New.Space.exists_short_basis
  - New.Space.exists_short_basis_stdSpace
  - New.Rows.inf_le_firstMinimum_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The first minimum and the height

A point $g$ of $G$ moves a space $V = (J, x)$ to the space $(J, xg)$, and so it moves the base lattice. When $g$ goes to infinity in $\Gamma_V \backslash G$, the moved lattice gets a very short vector. Mahler's criterion says that this is the only way to go to infinity. This section measures it. It defines the first minimum of a space and the height of a point, proves that short lattice vectors are orthogonal, shows that a definite space has height $1$ everywhere, and proves that every lattice has a basis of vectors whose length is at most a constant over the first minimum.

### A model case

Take $\mathrm{SL}_2(\mathbb{Z}) \backslash \mathfrak{H}$. A point $z = u + iy$ of the upper half plane gives the lattice $L_z = y^{-1/2}(\mathbb{Z} + \mathbb{Z} z)$ in $\mathbb{C}$, of covolume $1$. For $z$ in the standard fundamental domain, $|cz + d| \ge 1$ for all integers $(c, d) \ne (0, 0)$, and equality holds for $(c, d) = (0, 1)$ (Serre, *A Course in Arithmetic*, Chapter VII, §1.2). So the shortest nonzero vector of $L_z$ has length $y^{-1/2}$. The point goes to the cusp exactly when $y \to \infty$, that is, when the shortest vector of $L_z$ goes to $0$. If we cut the shortest length off at $1$ and invert it, we get $\max(1, y^{1/2})$. This is the height of this section, in the model case.

### The textbook form

Let $\Lambda$ be a lattice in a Euclidean space of dimension $m$, and let $\Lambda^* = \{y : \langle y, x \rangle \in \mathbb{Z} \text{ for all } x \in \Lambda\}$ be its dual. Let $\lambda_1$ be the length of a shortest nonzero vector, and let $\mu(\Lambda)$ be the covering radius, the least $r$ such that every point lies within $r$ of $\Lambda$. A *transference theorem* bounds $\mu(\Lambda) \lambda_1(\Lambda^*)$ and $\lambda_1(\Lambda)\lambda_1(\Lambda^*)$ by functions of $m$ alone. Banaszczyk proved $\mu(\Lambda) \lambda_1(\Lambda^*) \le m/2$ (W. Banaszczyk, *New bounds in some transference theorems in the geometry of numbers*, Math. Ann. 296 (1993)). Earlier bounds with polynomials in $m$ are due to Lagarias, Lenstra and Schnorr (Combinatorica 10 (1990)).

### Weak transference

The source proves a weak transference theorem with elementary means. It does not assume that $\Lambda$ is discrete.

**Theorem (Weak transference).** Let $\Lambda$ be an additive subgroup of a Euclidean space $W$ of dimension $m \ge 1$. Let $\rho > 0$ and assume that every nonzero $y \in W$ with $\langle y, x \rangle \in \mathbb{Z}$ for all $x \in \Lambda$ has $\|y\| \ge \rho$. Then:

1. there is $b \in \Lambda$ with $b \ne 0$ and $\|b\| < 2m/\rho$;
2. for every $u \in W$ there is $x \in \Lambda$ with $\|u - x\| \le m^2/\rho$.

The second statement also holds for $m = 0$.

Lean: `New.weak_transference`, `New.weak_transference_covering_radius` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* For (1), assume that every nonzero $b \in \Lambda$ has $\|b\| \ge R = 2m/\rho$. Then $\Lambda$ is discrete. It also spans $W$: the orthogonal complement of its span lies in the dual of $\Lambda$, which is discrete by the hypothesis, and a discrete vector subspace is zero. So $\Lambda$ is a lattice with a basis $b_1, \dots, b_m$, and the dual basis spans $\Lambda^*$. Minkowski's bound (Section 4) in the form $(R/\sqrt{m})^m \le \operatorname{covol}(\Lambda)$ holds for a lattice whose nonzero vectors have length at least $R$. It holds for $\Lambda$ with $R$, and for $\Lambda^*$ with $\rho$. The covolumes of $\Lambda$ and $\Lambda^*$ have product $1$. Multiply the two bounds:
$$\Big(\frac{\rho}{\sqrt{m}} \cdot \frac{2m}{\rho \sqrt{m}}\Big)^m = 2^m \le 1.$$
This is false for $m \ge 1$.

For (2), use induction on $m$. For $m = 0$ take $x = 0$. For $m \ge 1$, part (1) gives $b \in \Lambda$, $b \ne 0$, $\|b\| < 2m/\rho$. Let $P$ be the orthogonal projection to the hyperplane $b^\perp$, and let $\Lambda' = P(\Lambda)$. A vector of $b^\perp$ that pairs integrally with $\Lambda'$ also pairs integrally with $\Lambda$, because $\langle y, Px \rangle = \langle y, x \rangle$ for $y \perp b$. So $\Lambda'$ satisfies the hypothesis with the same $\rho$ in dimension $m - 1$. By induction there is $x \in \Lambda$ with $\|Pu - Px\| \le (m-1)^2/\rho$. So $u - x - tb$ has this length for some real $t$. Round $t$ to the nearest integer $k$. Then
$$\|u - (x + kb)\| \le \frac{(m-1)^2}{\rho} + \frac{1}{2} \cdot \frac{2m}{\rho} \le \frac{m^2}{\rho}. \qquad \square$$

**Lemma (Short vectors of a dense set span).** Let $S$ be a subset of a finite dimensional Euclidean space $W$, and let $r > 0$. If every $u \in W$ lies within $r$ of a point of $S$, then the points of $S$ of length at most $3r$ span $W$ over $\mathbb{R}$.

Lean: `New.span_norm_le_eq_top_of_covering` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* Let $y \ne 0$ be orthogonal to all such points, and put $u = 2r y/\|y\|$. Some $x \in S$ has $\|u - x\| \le r$. Then $\|x\| \le 3r$, and $\langle x, u \rangle = \|u\|^2 + \langle x - u, u \rangle \ge 4r^2 - 2r^2 > 0$. So $x$ is not orthogonal to $y$, a contradiction. $\square$

**Remark (Formalization).** The constant in (2) is $m^2$, where Banaszczyk has $m/2$. The constant enters the argument only through the short basis constant below, and no step needs the sharp form. The hypothesis is on the dual alone, and $\Lambda$ is an arbitrary subgroup. Part (1) is the step of the induction.

### The first minimum and the height

Let $V = (J, x)$ be a space. For $\xi \in E^n$, the vector $x^{-1}\xi$ has a component in $\mathbb{C}^n$ at each infinite place $w$. Put these together into one vector $\mathrm{a}(\xi)$ in the Euclidean space $\mathbb{C}^{f \times n}$, which has real dimension $m = 2fn$. Its norm is the *length* of $\xi$:
$$\|\xi\|_V^2 = \sum_{w} \sum_{i} |(x_w^{-1} \xi)_i|^2.$$
The map $\xi \mapsto \mathrm{a}(\xi)$ is additive and $\mathbb{Q}$-linear.

Lean: `New.Space.archCoords` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

**Definition (First minimum).** The first minimum of $V$ is
$$\lambda(V) = \min\Big(1, \inf\{\|\xi\|_V : \xi \in L_V, \ \xi \ne 0\}\Big),$$
where $L_V = E^n \cap x_f \hat{\mathcal{O}}_E^n$ is the base lattice.

Lean: `New.Space.firstMinimum` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

**Definition (Height).** The height of $g \in G$ for $V$ is $\operatorname{ht}_V(g) = \lambda(V g)^{-1}$, where $Vg = (J, xg)$ is the moved space.

Lean: `New.Space.height` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

**Definition (Moderate growth, rapid decay).** A function $F : G \to \mathbb{C}$ has *moderate growth* if there are a real $C$ and a natural number $B$ with $|F(g)| \le C \operatorname{ht}_V(g)^B$ for all $g$. It has *rapid decay* if for every natural number $B$ there is a real $C$ with $|F(g)| \operatorname{ht}_V(g)^B \le C$ for all $g$.

Lean: `New.Space.IsModerate`, `New.Space.IsRapid` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

In the model case, the Hermite constant shows that $\lambda_1(L_z)^2 \le 2/\sqrt{3}$, so the shortest length can exceed $1$ by a little. The cut at $1$ removes this. It makes $\lambda(V) \le 1$ and $\operatorname{ht}_V \ge 1$ for every space, so that powers of the height are increasing in the exponent.

**Proposition (Discreteness and positivity).** For every real $r$, only finitely many $\xi \in L_V$ have $\|\xi\|_V \le r$. So $\lambda(V) > 0$, and the height is a finite real number $\ge 1$.

Lean: `New.Space.finite_latticeBall`, `New.Space.firstMinimum_pos` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* If $\xi \in L_V$ has length at most $r$, then $x^{-1}\xi$ lies in the compact box of adelic vectors whose infinite components have norm at most $r$ and whose finite components lie in $\hat{\mathcal{O}}_E$. The rational vectors $E^n$ are discrete in $\mathbb{A}_E^n$, so the preimage of a compact set is finite. For positivity, the nonzero lengths at most $1$ form a finite set of positive numbers, and the least of these and $1$ is a positive lower bound for $\lambda(V)$. $\square$

**Remark (Formalization).** The first minimum is the infimum of the lengths with the number $1$ added. This set is not empty and is bounded below, so there is no junk value. The height would be the junk value $0$ if the minimum were $0$, and the positivity above excludes this. The constants $C$ in the growth conditions are real numbers. The inequalities force $C \ge 0$.

### Short vectors are orthogonal

The form takes integral values on the lattice. This is the only arithmetic input of the section.

**Lemma (Orthogonality of short vectors).** Let $a, b \in L_V$ with $\|a\|_V \|b\|_V < 1$. Then $a^* J b = 0$.

Lean: `New.Space.form_eq_zero_of_norm_mul_lt_one` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* At the finite places, $x_f^{-1} a$ and $x_f^{-1} b$ are integral and $x_f^* J x_f = 1$. So $a^* J b$ is an algebraic integer. At an infinite place $w$, its image is $\sum_i s_i \overline{\alpha_i} \beta_i$, where $\alpha$ and $\beta$ are the components of $x_w^{-1} a$ and $x_w^{-1} b$. By Cauchy and Schwarz its absolute value is at most the product of the lengths at $w$, which is at most $\|a\|_V \|b\|_V < 1$. An algebraic integer of $E$ whose absolute values at all infinite places are less than $1$ has a norm in $\mathbb{Z}$ of absolute value less than $1$, so it is $0$. $\square$

For a definite space every nonzero vector has nonzero norm, so the lemma with $a = b$ forbids short vectors.

**Proposition (Definite spaces have height one).** Assume that all signs $s_i$ are equal. If $\xi \in E^n$ has $\xi^* J \xi = 0$, then $\xi = 0$. Every nonzero vector of $L_V$ has length at least $1$. So $\lambda(Vg) = 1$ and $\operatorname{ht}_V(g) = 1$ for every $g \in G$.

Lean: `New.Space.eq_zero_of_isotropic_of_definite`, `New.Space.firstMinimum_move_eq_one` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* At an infinite place, with $v = x_w^{-1}\xi$, the value is $\xi^* J \xi = v^* \varepsilon_s v = \pm \|v\|^2$. So $v = 0$, and $\xi = x_w v = 0$. If $\xi \in L_V$ is nonzero and $\|\xi\|_V < 1$, then $\|\xi\|_V^2 < 1$, so the lemma gives $\xi^* J \xi = 0$ and $\xi = 0$, a contradiction. So $\lambda(V) \ge 1$. The cutoff gives $\lambda(V) \le 1$. The moved space $Vg$ has the same signs, so the same holds for it. $\square$

This proposition is the reason that the quotient by a definite unitary group is compact, in [Section 6](/chapter/reduction-theory/#finite-volume-and-the-finiteness-of-classes).

### Short bases

The image of $L_V$ under $\mathrm{a}$ is a subgroup of a real space of dimension $2fn$. To apply weak transference one needs a lower bound on the dual. The form gives it. Let $d$ be a nonzero element of the different $\mathfrak{D}$ of $E$. The inverse different is the dual of $\mathcal{O}_E$ for the trace form, and $x_f^* J x_f = 1$ makes $L_V$ unimodular for $J$ at every finite place.

**Lemma (The dual of a scaled lattice).** Let $0 \ne d \in \mathfrak{D}$. Let $y$ be a nonzero vector of $\mathbb{C}^{f \times n}$ such that $\langle y, \mathrm{a}((2/d)\xi) \rangle \in \mathbb{Z}$ for all $\xi \in L_V$, for the real inner product. Then $\|y\| \ge \lambda(V)$.

Lean: `New.Space.firstMinimum_le_norm_of_inner_int` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* The pairing $\langle y, \mathrm{a}((2/d)\xi)\rangle$ is a sum over the infinite places of twice the real part of a hermitian product. Every vector of $E^n$ has a multiple in $L_V$, so the pairing is rational on $E^n$. Hence there is $\alpha \in E^n$ with $J\alpha$ equal at the infinite places to the vector that represents $y$, scaled by $\bar d^{-1}$. Then the pairing equals $\operatorname{Tr}_{E/\mathbb{Q}}(\xi^* J \alpha)$, and $\|y\| = \|d \alpha\|_V$. The trace is in $\mathbb{Z}$ for all $\xi \in L_V$. Since $L_V$ is unimodular and $d$ lies in the different, this puts $d\alpha$ in $L_V$. It is nonzero because $y \ne 0$. So $\|y\| = \|d\alpha\|_V \ge \lambda(V)$. $\square$

**Corollary (Covering radius).** Let $0 \ne d \in \mathfrak{D}$. For every $u \in \mathbb{C}^{f \times n}$ there is $a \in L_V$ with
$$\|u - \mathrm{a}((2/d) a)\| \le \frac{(2fn)^2}{\lambda(V)}.$$

Lean: `New.Space.exists_norm_sub_archCoords_le` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* Apply part (2) of weak transference to $\Lambda = \mathrm{a}((2/d) L_V)$, with $\rho = \lambda(V) > 0$ from the lemma and $m = 2fn$. $\square$

**Theorem (Short bases).** Let $N \ne 0$ be a natural number in $\mathfrak{D}$. Put $C(N) = 6N(fn)^2$. There is $Y \in \mathrm{GL}_n(E)$ whose columns all lie in $L_V$ and have length at most $C(N)/\lambda(V)$.

Lean: `New.Space.shortBasisConst`, `New.Space.exists_short_basis` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* If $n$ is empty there is nothing to prove. Put $r = (2fn)^2/\lambda(V)$. By the corollary with $d = N$, the set $S = \{(2/N)\mathrm{a}(a) : a \in L_V\}$ comes within $r$ of every point. By the lemma on dense sets, the points of $S$ of length at most $3r$ span $\mathbb{C}^{f \times n}$ over $\mathbb{R}$. A point $(2/N)\mathrm{a}(a)$ of length at most $3r$ has $\|a\|_V \le 3rN/2 = C(N)/\lambda(V)$. A set of vectors of $E^n$ whose images under $\mathrm{a}$ span over $\mathbb{R}$ spans $E^n$ over $E$: a linear form on $E^n$ that vanishes on the set extends at one place to a real linear form that vanishes on the span. So the short lattice vectors contain a basis of $E^n$, and its vectors are the columns of $Y$. $\square$

For a definite space the bound is $C(N)$ for every point. The source records this for the standard space $I_n$, in coordinates.

**Corollary (Short bases for $I_n$).** Let $N \ne 0$ be a natural number in $\mathfrak{D}$ and let $g \in G_f$. There is $Y \in \mathrm{GL}_n(E)$ such that $g^{-1} Y$ has all entries in $\hat{\mathcal{O}}_E$ and $|\varphi(Y_{ij})| \le 6N(fn)^2$ for every embedding $\varphi : E \to \mathbb{C}$ and all $i, j$.

Lean: `New.Space.exists_short_basis_stdSpace` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* Apply the theorem to $I_n$ moved by $(1, g)$. Its first minimum is $1$ by the proposition on definite spaces. An entry $|\varphi(Y_{ij})|$ is one coordinate of the column $j$ at the place of $\varphi$, so it is at most the length of the column. $\square$

**Remark (Formalization).** The theorem needs a natural number $N \ne 0$ in the different. Such a number exists: the absolute norm of the different is a nonzero natural number, and it lies in the different. The constant $C(N)$ depends on $E$ only through $f$ and $N$. With $N$ the norm of the different, $N = |d_E|$, so the bound is polynomial in $|d_E|$ and $fn$. The columns of $Y$ form a basis of $E^n$ inside $L_V$. The source does not prove that they form an $\mathcal{O}_E$-basis of $L_V$, and the argument does not need this.

### Orthogonal sums

**Proposition (First minimum of a sum).** Let $V$ and $W$ be spaces with signs $s$ and $s'$, let $g$ and $h$ be points of their groups, and let $V \oplus W$ be the orthogonal sum, moved by the block diagonal point $(g, h)$. Then
$$\min\big(\lambda(Vg), \lambda(Wh)\big) \le \lambda\big((V \oplus W)(g, h)\big).$$

Lean: `New.Rows.inf_le_firstMinimum_sum` (Lib/Adelic/Reduction/FirstMinimumShortBases.lean).

*Proof.* A vector $\xi$ of the base lattice of the sum has components $\xi'$ and $\xi''$ in the base lattices of $Vg$ and $Wh$, and $\|\xi\|^2 = \|\xi'\|^2 + \|\xi''\|^2$. If $\xi \ne 0$, one component is nonzero and not longer than $\xi$. The cutoff at $1$ is the same on both sides. $\square$

So the height of a block diagonal point is at most the larger of the two heights.

### Where the argument uses this section

The short bases for $I_n$ bound the lattice vectors in the class count and the size estimate of [Theorem A: the plan](/chapter/theorem-a-plan/), and in the comparison operator of [Theorem C: the plan](/chapter/theorem-c-plan/). There the short bases also give $\lambda(S)\lambda(T)/(C(N)|n'||n|) \le \lambda(\operatorname{Hom}(S, T))$ for two spaces of ranks $|n|$ and $|n'|$, which bounds the theta kernel. Rapid decay and moderate growth are the conditions on the functions of the seesaw stages of Theorem A and of the exchange steps and diagonal turns of Theorem C.

**Remark (Formalization).** The bound for $\operatorname{Hom}(S, T)$ is `New.Rows.firstMinimum_mul_le_hom` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean). Weak transference is not used by name in New. It enters only through `New.Space.exists_short_basis`. The comparison of heights on sets $\Gamma g \Xi$ with $\Xi$ compact is `New.Space.exists_height_le_mul` (Lib/Adelic/AutomorphicForms/Basic.lean).
