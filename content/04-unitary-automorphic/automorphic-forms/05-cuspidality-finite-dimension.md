---
title: Cuspidality and finite dimension
lean:
  - Lib/Adelic/AutomorphicForms/UnipotentRadical.lean
  - Lib/Adelic/AutomorphicForms/Cuspidality.lean
  - Lib/Adelic/AutomorphicForms/RealConvolution.lean
  - Lib/Adelic/Reduction/FirstMinimumShortBases.lean
  - Lib/Adelic/Reduction/DefiniteClassSums.lean
decls:
  - New.IsCuspKernel.integral_mul_eq_zero
  - New.Space.IsCuspidal
  - New.Space.IsForm.isCuspidal
  - New.cuspConst
  - New.one_le_cuspConst
  - New.Space.RadicalCovered
  - New.Space.CuspFrame
  - New.Space.exists_cuspFrame
  - New.Space.IsCuspidal.norm_le_of_firstMinimum_lt
  - New.Space.IsForm.norm_le_of_firstMinimum_lt
  - New.Space.exists_norm_le_of_radicalCovered
  - New.Space.exists_cuspFrame_of_height
  - New.Space.exists_norm_mul_height_pow_le
  - New.Space.IsForm.mem_rapidFunctions
  - New.eventually_norm_realConv_sub_le
  - New.Space.finite_levelSpace
  - New.Space.isForm_realConv
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cuspidality and finite dimension

This section proves the two facts about forms of type $e$ that the classical theory gets from Harish-Chandra's theorem (Section 2). For a cusp kernel $e$, every form of type $e$ is cuspidal and decays rapidly, and the forms of type $e$ and of a fixed level make up a space of finite dimension. The source proves both from the kernel alone, with no differential equation, and with explicit constants in the cusp estimate.

Throughout, $V = (J, x)$ is a hermitian space over $E$ with signs $s$, $\Gamma_V$ is its group of rational points, $e$ is a cusp kernel of order $B$ on $G_\infty$ (Section 4), and $n$ is the rank. For a point $g \in G$, the space $V \cdot g$ is $V$ moved to the point $xg$, as in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). Its lattice is the lattice of $V$ read in the frame at $g$.

### The idea

On the upper half plane, a cusp form $f$ of weight $k$ satisfies $|f(x + iy)| \ll y^{-A}$ for every $A$ as $y \to \infty$. The usual proof uses the Fourier expansion. A second proof does not use the expansion. For $y$ large, the horocycle $\{x + iy : 0 \le x \le h\}$ has hyperbolic length $h/y$, which is small. The constant term is the mean of $f$ over it, and is $0$. So each value of $f$ on it is within a small oscillation of $0$. Repeat the estimate and the bound improves by a fixed factor each time.

The source follows the second proof. The horocycle becomes the quotient $(\Gamma_V \cap N_A) \backslash N_A$ for the unipotent radical $N_A$ of a rational isotropic subspace $A$. A point is high in a cusp if the lattice at that point has a short vector, so the first minimum measures the depth. The kernel gives the oscillation bound through its moments.

### Constant terms of a cusp kernel

The local fact behind cuspidality is a theorem of Harish-Chandra on the real group: the $K$-finite matrix coefficients of a discrete series have constant term $0$ along every proper parabolic subgroup. The source proves the case it needs.

For a matrix $A_w$ over $\mathbb{C}$ at an infinite place $w$, let the *dilations by $c$ along $A_w$* be the $r \in U(\operatorname{diag} s)$ that act as the scalar $c$ on the columns of $A_w$ and satisfy $v^* \operatorname{diag}(s)\, r u = v^* \operatorname{diag}(s)\, u$ for all $u$, $v$ orthogonal to these columns. The dilations by $1$ make up the unipotent radical of the stabilizer of the column span.

**Theorem (Vanishing constant terms).** Let $n$ be nonempty. For each infinite place $w$, let $A_w$ be a nonzero complex $n \times n$ matrix with $A_w^* \operatorname{diag}(s) A_w = 0$. Let $\Psi$ be a bounded continuous function on $G_\infty$ with $\Psi(rx) = \Psi(x)$ for all $x$ and for every $r$ whose component $r_w$ is a dilation by $1$ along $A_w$ at every $w$. Then $\int_{G_\infty} e(x)\, \Psi(yx)\, dx = 0$ for every $y \in G_\infty$.

Lean: `New.IsCuspKernel.integral_mul_eq_zero` (Lib/Adelic/AutomorphicForms/UnipotentRadical.lean).

*Proof idea.* Fix one place $w_0$ and let $H(x) = \log \|x_{w_0}^{-1} A_{w_0}\|$. A dilation by $c$ moves $H$ by $-\log |c|$. A real point $z$ moves $H$ by at most $\|z\|^{B+1}$, where $\|z\|$ is the product of the operator norms. Every neighbourhood of $1$ holds, in each conjugate, a dilation by $1 + \delta$ with $\delta > 0$. A general lemma on minimal idempotent kernels with an integrable moment, in [discrete series](/chapter/discrete-series/), turns these three facts into the vanishing. $\square$

### Cuspidal functions

**Definition (Cuspidal function, source form).** A function $F$ on $G$ is *cuspidal* for $V$ if (i) $F$ is continuous, (ii) $F$ is left $\Gamma_V$-invariant, and (iii) for every $g \in G$ and every nonzero matrix $X$ over $E$ with $X^* J X = 0$, the integral of $F(gv)$ over $v$ in $(\Gamma \cap N) \backslash N$ is $0$. Here $N$ is the adelic unipotent radical of the span of the columns of $X$ in the moved space $V \cdot g$, and $\Gamma$ is the group of rational points of $V \cdot g$.

Lean: `New.Space.IsCuspidal` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

Condition (iii) is the classical condition of Section 2 for the maximal parabolic subgroup that stabilizes the span $A$ of the columns of $X$: the substitution $v = g^{-1} u g$ turns the integral of $F(ug)$ over $(\Gamma_V \cap N_A) \backslash N_A$ into the integral in (iii). Section 2 explains why the maximal parabolic subgroups are enough.

**Remark (Formalization).** The integral in (iii) is a Bochner integral against the quotient measure of Haar measure by $\Gamma \cap N$. A Bochner integral of a function that is not integrable is $0$, so (iii) would be empty for such a function. Here the quotient $(\Gamma \cap N) \backslash N$ is compact (`New.Space.isCocompact_radical`), so the quotient measure is finite, and a bounded continuous $F$ is integrable. The normalization of the Haar measure does not matter, since (iii) only says that the integral is $0$.

**Theorem (Forms are cuspidal).** A form of type $e$ for $V$ is cuspidal.

Lean: `New.Space.IsForm.isCuspidal` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Conditions (i) and (ii) are part of the definition of a form. For (iii), fix $g$ and $X$. Then $X \neq 0$, so $n$ is nonempty. The function $\Psi(v) = F(gv)$ is bounded, continuous, fixed by $R(e)$, and left invariant under the rational points of the radical. Integrate $F(gv) = \int e(x) F(gv(x,1))\,dx$ over the compact quotient and change the order of the integrals ($e$ is integrable and $F$ is bounded). The inner integral is $0$ by the theorem on vanishing constant terms, read place by place in the adelic coordinates of $X$. $\square$

### The cusp estimate

The next result makes the idea above exact. It needs a constant that depends only on $E$, $n$ and one integer.

**Definition (Cusp constant).** Let $f$ be the number of infinite places of $E$, let $\operatorname{rd}_E$ be the root discriminant of $E$, and let $N$ be a natural number. The *cusp constant* is
$$\kappa(E, n, N) = 8 f n \operatorname{rd}_E + 48 n^6 f^2 N + 1.$$
It is at least $1$.

Lean: `New.cuspConst`, `New.one_le_cuspConst` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

The cusp at a point is built from a short basis of the lattice. A *cusp frame of size $\delta$* for a space $W$ is a nonzero isotropic subspace $A$ of $W$, spanned by the columns of a matrix $X$, together with a matrix $Y$ whose columns span $A^\perp$, such that the columns of $X$ and $Y$ are lattice vectors of lengths at most $a$ and $b$, with $a \le b$ and $ab \le \delta$. For a subgroup $K'$ of $G_f$, the radical of $A$ in $W \cdot g$ is *covered at size $\delta$ by $K'$* if every $u$ in that radical is $\gamma^{-1}(z, k)$ for a rational point $\gamma$ of the radical, a real point $z$ with $\operatorname{dist}(z, 1) \le \delta$, and $k \in K'$. In terms of $V$: $N_A g \subseteq (\Gamma_V \cap N_A)\, g\, Z_\delta K'$, where $Z_\delta$ is the real ball of radius $\delta$ about $1$.

Lean: `New.Space.CuspFrame`, `New.Space.RadicalCovered` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

Write $K(M)$ for the principal level of an integer $M$ ([adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/)), and $\lambda(W)$ for the first minimum of the lattice of $W$, cut off at $1$ ([reduction theory](/chapter/reduction-theory/)).

**Theorem (A cusp at a short vector).** Let $W$ be a space. Let $N \neq 0$ be a natural number that lies in the different of $E$, let $M \neq 0$, and let $0 < \delta \le 1$. If $\lambda(W) < (\delta / (M \kappa^2))^n$ with $\kappa = \kappa(E, n, N)$, then $W$ has a cusp frame of size $\delta$ whose radical is covered at size $\delta$ by $K(M)$.

Lean: `New.Space.exists_cuspFrame` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof idea.* Take a short nonzero lattice vector $\xi$ and a Minkowski basis of the lattice, sorted by length. By Minkowski's second theorem the product of the lengths is at most $\kappa^n$; this uses $8 f n \operatorname{rd}_E \le \kappa$. The longest basis vector has length at least $1/\|\xi\|$, so the other lengths have a small product. Pairing the lengths from both ends gives a gap, and the vectors below the gap span a nonzero isotropic subspace $A$ with the bounds $a$ and $b$ above. A point of the radical is then moved close to $1$ by a rational element of the radical, built from the explicit matrix $1 + 2(T - T^* - T^*JT)J$. The integer $N$ in the different is used to make this element integral, and the factor $M$ makes the finite part of the remainder lie in $K(M)$. $\square$

**Theorem (Cusp estimate).** Let $F$ be cuspidal for $V$ of level $K(M)$ with $M \neq 0$. Let $N \neq 0$ be a natural number in the different of $E$, and let $0 < \delta \le 1$. Let $g \in G$ with $\lambda(V \cdot g) < (\delta / (M \kappa^2))^n$, where $\kappa = \kappa(E, n, N)$. If $|F(g(x,1)) - F(g)| \le C$ for every $x \in G_\infty$ with $\operatorname{dist}(x, 1) \le \delta$, then $|F(g)| \le C$. The same holds for a form of type $e$ in place of a cuspidal function.

Lean: `New.Space.IsCuspidal.norm_le_of_firstMinimum_lt`, `New.Space.IsForm.norm_le_of_firstMinimum_lt` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Take the cusp frame of the last theorem at $V \cdot g$, with subspace $A$ and radical $N$. Since $F$ is cuspidal, $F(g)$ is the mean over the compact quotient of $F(g) - F(gv)$, $v \in N$. By the covering, $gv = \gamma' g (z, k)$ with $\gamma'$ rational, $\operatorname{dist}(z, 1) \le \delta$ and $k \in K(M)$. So $F(gv) = F(g(z,1))$, by the invariance under $\Gamma_V$ and the level. Each value of $F(g) - F(gv)$ is then at most $C$ in absolute value, and so is the mean. For a form of type $e$, apply the first part with the theorem that forms are cuspidal. $\square$

The argument uses the explicit constant: the threshold $(m^{-2} / (M \kappa^2))^n$ appears in [deep level Poincaré series](/chapter/deep-level-poincare/), with $m$ large.

### Rapid decay

The cusp estimate turns into decay by iteration: the oscillation of a function fixed by $e$ is small, and each step gives a factor $\delta$.

**Theorem (Decay in a cusp).** Let $n$ be nonempty and $j \ge 0$. There is $\delta_0 > 0$ with the following property. Let $K'$ be a level, $W$ a space, $g \in G$, $\delta \ge 0$, and $X \neq 0$ a matrix with $X^* J_W X = 0$ whose radical in $W \cdot g$ is covered at size $\delta$ by $K'$. Let $f$ be a continuous function on $G$ with $|f| \le T$, $R(e) f = f$, of level $K'$, and left invariant under the rational points of the radical of $X$ in $W$. Then $|f(g)| \le (\delta / \delta_0)^j\, T$.

Lean: `New.Space.exists_norm_le_of_radicalCovered` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

**Theorem (Depth and height).** Let $n$ be nonempty and $K'$ an open subgroup of $G_f$. There is $\kappa' > 0$ such that for every space $V$ and every $g \in G$ there is $\delta > 0$ with $\delta^n \operatorname{ht}_V(g) = \kappa'$, and, if $\delta \le 1$, a cusp frame of size $\delta$ at $V \cdot g$ whose radical is covered at size $\delta$ by $K'$.

Lean: `New.Space.exists_cuspFrame_of_height` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

Here $\operatorname{ht}_V(g) = \lambda(V \cdot g)^{-1}$ is the height.

**Theorem (Uniform rapid decay).** Let $K$ be an open subgroup of $G_f$ and $A \ge 0$ an integer. There is $R$ such that for every form $F$ of type $e$ for $V$ of level $K$ and every $c$ with $|F| \le c$ on $G$,
$$|F(g)|\, \operatorname{ht}_V(g)^A \le c R \quad \text{for all } g \in G.$$

Lean: `New.Space.exists_norm_mul_height_pow_le` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* If $n$ is empty, the lattice has no nonzero vector, so the height is $1$ and $R = 1$ works. Otherwise let $K' = K \cap K_0$, a level. Take $\kappa'$ from the theorem on depth and height, and $\delta_0$ from the theorem on decay with $j = nA$. Fix $g$ and the $\delta$ of the theorem on depth and height. If $\delta \le 1$, the theorem on decay gives $|F(g)| \le (\delta / \delta_0)^{nA} c$, and $\delta^{nA} = (\kappa' / \operatorname{ht}_V(g))^A$. If $\delta > 1$, then $\operatorname{ht}_V(g) < \kappa'$ and $|F(g)| \le c$. In both cases $R = (\kappa' / \min(\delta_0, 1)^n)^A$ works. $\square$

The constant $R$ does not depend on $F$, and the proof of finite dimension needs this.

**Corollary.** A form of type $e$ decays rapidly: for every $A$ there is $C$ with $|F(g)|\, \operatorname{ht}_V(g)^A \le C$ for all $g$.

Lean: `New.Space.IsForm.mem_rapidFunctions` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* A form has some open level $K$ and some bound $c$. Apply the last theorem. $\square$

### Finite dimension

**Lemma (Uniform continuity of averages).** Let $\alpha$ be integrable on $G_\infty$, $K$ an open subgroup of $G_f$, and $\varepsilon > 0$. Then there is a neighbourhood $U$ of $1$ in $G$ with the following property. Let $z \in U$ with real part $z_\infty$, let $F$ be bounded, measurable and of level $K$, let $g \in G$, and let $C$ be a real number with $|F(g(x, 1))| \le C$ for all $x \in G_\infty$ with $\alpha(z_\infty^{-1} x) \neq \alpha(x)$. Then $|R(\alpha)F(gz) - R(\alpha)F(g)| \le \varepsilon |C|$.

Lean: `New.eventually_norm_realConv_sub_le` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* Near $1$ the finite part of $z$ lies in $K$ and drops out. The real part $u$ changes $R(\alpha)F(g)$ by $\int (\alpha(u^{-1}x) - \alpha(x)) F(g(x,1))\,dx$, which is at most $|C| \int |\alpha(u^{-1}x) - \alpha(x)|\,dx$. Translation is continuous in $L^1(G_\infty)$, so this is at most $\varepsilon |C|$ for $u$ near $1$. $\square$

**Theorem (Finite dimension).** Let $K$ be an open subgroup of $G_f$. The forms of type $e$ for $V$ that have level $K$ make up a complex vector space of finite dimension.

Lean: `New.Space.finite_levelSpace` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Take $R$ from the theorem on uniform rapid decay with $A = 1$. By Mahler's criterion ([reduction theory](/chapter/reduction-theory/)) there is a compact set $C \subseteq G$ such that every $g$ with $\operatorname{ht}_V(g) \le 2R$ has $\gamma g \in C$ for some $\gamma \in \Gamma_V$. Take the neighbourhood $U$ of the lemma, for $\alpha = e$ and $\varepsilon = 1/2$, and let $U^\circ$ be its interior. The compact set $C$ is covered by finitely many translates $a U^\circ$, $a \in t$.

We claim that a form $F$ of type $e$ and level $K$ with $F(a^{-1}) = 0$ for all $a \in t$ is $0$. Let $M \ge 0$ be a bound for $|F|$. We show that $M/2$ is also a bound. Suppose $|F(g)| > M/2$ for some $g$. The theorem on uniform rapid decay gives $|F(g)|\,\operatorname{ht}_V(g) \le MR$, so $\operatorname{ht}_V(g) < 2R$. Take $\gamma \in \Gamma_V$ with $\gamma g \in C$, and $a \in t$ with $\gamma g \in a U^\circ$. Then $\gamma g = a^{-1}\,(a \gamma g)$ with $a\gamma g \in U$. The lemma, with the bound $M$, gives
$$|R(e)F(\gamma g) - R(e)F(a^{-1})| \le M/2.$$
Now $R(e)F = F$, $F(\gamma g) = F(g)$, and $F(a^{-1}) = 0$. So $|F(g)| \le M/2$, a contradiction. Hence $M/2$ is a bound. Repeat: $M/2^k$ is a bound for every $k$, so $F = 0$.

By the claim, the linear map $F \mapsto (F(a^{-1}))_{a \in t}$ from the level space to $\mathbb{C}^t$ is injective. So the level space has finite dimension, at most $|t|$. $\square$

**Remark (Formalization).** The compact set of Mahler's criterion and the finite cover $t$ come from existence statements inside the proof, so the bound $|t|$ is not explicit. The argument never needs an explicit bound on the dimension of a space of forms on an indefinite group. The dimensions that it counts are those of algebraic forms on definite groups, where Section 6 gives an exact formula. The theorem holds for every open subgroup $K$, not only for levels $K \subseteq K_0$, since the decay theorem first passes to $K \cap K_0$.

### Projection of automorphic functions

The finite dimension gives a way to project functions that are not bounded.

**Theorem (Projection).** Let $F$ be automorphic for $V$ (continuous, left $\Gamma_V$-invariant, of some open level), and suppose that $x \mapsto e(x)\, F(g(x, 1))$ is integrable on $G_\infty$ for every $g \in G$. Then $R(e)F$ is a form of type $e$.

Lean: `New.Space.isForm_realConv` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Let $K$ be an open level of $F$. For $t$ real, let $F_t$ be $F$ where $|F| \le t$ and $0$ elsewhere. Then $F_t$ is bounded, measurable, left $\Gamma_V$-invariant and of level $K$. So $R(e)F_t$ is a form of type $e$ of level $K$, by the proposition on making forms in Section 4. As $t \to \infty$, $R(e)F_t(g) \to R(e)F(g)$ for every $g$, by dominated convergence with the integrable bound $|e(x) F(g(x,1))|$. The forms of type $e$ and level $K$ make up a space of finite dimension, by the last theorem. A subspace of finite dimension of the functions on $G$ is closed for pointwise convergence. So $R(e)F$ lies in it. $\square$

**Remark (Formalization).** The integral $R(e)F(g)$ is a Bochner integral, which would be $0$ where the integrand is not integrable. The hypothesis of integrability at every $g$ excludes this.

### Where the argument uses these objects

The finite dimension theorem is used three times. In [the objects of the upper bound](/chapter/upper-bound-objects/) it is used for the rows of the lift. In [grids, paths and turns](/chapter/grids-paths-turns/) it is used for the first columns of a grid and for the first path. The cusp estimate for forms, with its constant $\kappa(E, n, N)$, is used in [deep level Poincaré series](/chapter/deep-level-poincare/) to show that auxiliary forms of deep level are small high in the cusps. The rapid decay of forms is used in [seesaw squares](/chapter/seesaw-squares/) and in [the comparison operator](/chapter/comparison-operator-1/). The theorem that forms are cuspidal and the projection theorem are not used outside this chapter.
