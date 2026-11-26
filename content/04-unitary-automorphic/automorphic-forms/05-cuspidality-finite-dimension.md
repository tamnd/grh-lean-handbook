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

For a cusp kernel $e$, every form of type $e$ is cuspidal and decays rapidly, and the forms of type $e$ and fixed level make up a space of finite dimension. The classical theory gets these facts from Harish-Chandra's theorem (Section 2). The source proves them from the kernel alone, with explicit constants in the cusp estimate.

Throughout, $V = (J, x)$ is a hermitian space over $E$ with signs $s$, $\Gamma_V$ is its group of rational points, $e$ is a cusp kernel of order $B$ on $G_\infty$ (Section 4), and $n$ is the rank. $V \cdot g$ is $V$ moved to $xg$, as in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

### The idea

On the upper half plane, for $y$ large the horocycle $\{x + iy : 0 \le x \le h\}$ of a cusp form $f$ is short, and the mean of $f$ over it is the constant term $0$. So each value of $f$ on it is within a small oscillation of $0$, and repetition gives $|f(x + iy)| \ll y^{-A}$ with no Fourier expansion. The source follows this proof, with $(\Gamma_V \cap N_A) \backslash N_A$ for a rational isotropic subspace $A$ in place of the horocycle. A point is high in a cusp if its lattice has a short vector.

### Constant terms of a cusp kernel

Harish-Chandra showed that the $K$-finite matrix coefficients of a discrete series have constant term $0$ along every proper parabolic subgroup. The source proves the case it needs. For a complex matrix $A_w$ at an infinite place $w$, the *dilations by $c$ along $A_w$* are the $r \in U(\operatorname{diag} s)$ that act as $c$ on the columns of $A_w$ and satisfy $v^* \operatorname{diag}(s)\, r u = v^* \operatorname{diag}(s)\, u$ for all $u$, $v$ orthogonal to these columns.

**Theorem (Vanishing constant terms).** Let $n$ be nonempty. For each infinite place $w$, let $A_w$ be a nonzero complex $n \times n$ matrix with $A_w^* \operatorname{diag}(s) A_w = 0$. Let $\Psi$ be a bounded continuous function on $G_\infty$ with $\Psi(rx) = \Psi(x)$ for all $x$ and for every $r$ whose component $r_w$ is a dilation by $1$ along $A_w$ at every $w$. Then $\int_{G_\infty} e(x)\, \Psi(yx)\, dx = 0$ for every $y \in G_\infty$.

Lean: `New.IsCuspKernel.integral_mul_eq_zero` (Lib/Adelic/AutomorphicForms/UnipotentRadical.lean).

*Proof idea.* With $H(x) = \log \|x_{w_0}^{-1} A_{w_0}\|$ at one place $w_0$, a dilation by $c$ moves $H$ by $-\log |c|$, and a real point $z$ moves $H$ by at most $\|z\|^{B+1}$. A lemma on minimal idempotent kernels with an integrable moment, in [discrete series](/chapter/discrete-series/), turns these facts into the vanishing. $\square$

### Cuspidal functions

**Definition (Cuspidal function, source form).** A function $F$ on $G$ is *cuspidal* for $V$ if (i) $F$ is continuous, (ii) $F$ is left $\Gamma_V$-invariant, and (iii) for every $g \in G$ and every nonzero matrix $X$ over $E$ with $X^* J X = 0$, the integral of $F(gv)$ over $v$ in $(\Gamma \cap N) \backslash N$ is $0$. Here $N$ is the adelic unipotent radical of the span of the columns of $X$ in $V \cdot g$, and $\Gamma$ is the group of rational points of $V \cdot g$.

Lean: `New.Space.IsCuspidal` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

With $v = g^{-1} u g$, condition (iii) is the classical condition of Section 2 for the maximal parabolic subgroup of the column span of $X$.

**Remark (Formalization).** The integral in (iii) is a Bochner integral, which is $0$ for a function that is not integrable. Here $(\Gamma \cap N) \backslash N$ is compact (`New.Space.isCocompact_radical`), so a bounded continuous $F$ is integrable, and (iii) has content. The normalization of the Haar measure does not matter.

**Theorem (Forms are cuspidal).** A form of type $e$ for $V$ is cuspidal.

Lean: `New.Space.IsForm.isCuspidal` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* For (iii), $X \neq 0$, so $n$ is nonempty. Integrate $F(gv) = \int e(x) F(gv(x,1))\,dx$ over the compact quotient and change the order of the integrals ($e$ is integrable and $F$ is bounded). The inner integral is $0$ by the theorem on vanishing constant terms, read place by place in the adelic coordinates of $X$. $\square$

### The cusp estimate

**Definition (Cusp constant).** Let $f$ be the number of infinite places of $E$, let $\operatorname{rd}_E$ be the root discriminant of $E$, and let $N$ be a natural number. Then
$$\kappa(E, n, N) = 8 f n \operatorname{rd}_E + 48 n^6 f^2 N + 1.$$
It is at least $1$.

Lean: `New.cuspConst`, `New.one_le_cuspConst` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

A *cusp frame of size $\delta$* for a space $W$ is a nonzero isotropic subspace $A$ of $W$, spanned by the columns of a matrix $X$, with a matrix $Y$ whose columns span $A^\perp$, such that the columns of $X$ and $Y$ are lattice vectors of lengths at most $a$ and $b$, with $a \le b$ and $ab \le \delta$. For a subgroup $K'$ of $G_f$, the radical of $A$ in $W \cdot g$ is *covered at size $\delta$ by $K'$* if every $u$ in it is $\gamma^{-1}(z, k)$ for a rational point $\gamma$ of the radical, a real point $z$ with $\operatorname{dist}(z, 1) \le \delta$, and $k \in K'$.

Lean: `New.Space.CuspFrame`, `New.Space.RadicalCovered` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

$K(M)$ is the principal level of $M$ ([adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/)), and $\lambda(W)$ is the first minimum of the lattice of $W$, cut off at $1$ ([reduction theory](/chapter/reduction-theory/)).

**Theorem (A cusp at a short vector).** Let $W$ be a space. Let $N \neq 0$ be a natural number that lies in the different of $E$, let $M \neq 0$, and let $0 < \delta \le 1$. If $\lambda(W) < (\delta / (M \kappa^2))^n$ with $\kappa = \kappa(E, n, N)$, then $W$ has a cusp frame of size $\delta$ whose radical is covered at size $\delta$ by $K(M)$.

Lean: `New.Space.exists_cuspFrame` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof idea.* Minkowski's second theorem bounds the product of the lengths of a reduced basis by $\kappa^n$. A short vector forces a gap in the lengths, and the vectors below the gap span the isotropic subspace. A rational element of the radical built from $1 + 2(T - T^* - T^*JT)J$ moves a point close to $1$; $N$ makes it integral, and $M$ puts the remainder in $K(M)$. $\square$

**Theorem (Cusp estimate).** Let $F$ be cuspidal for $V$ of level $K(M)$ with $M \neq 0$. Let $N \neq 0$ be a natural number in the different of $E$, and let $0 < \delta \le 1$. Let $g \in G$ with $\lambda(V \cdot g) < (\delta / (M \kappa^2))^n$, where $\kappa = \kappa(E, n, N)$. If $|F(g(x,1)) - F(g)| \le C$ for every $x \in G_\infty$ with $\operatorname{dist}(x, 1) \le \delta$, then $|F(g)| \le C$. The same holds for a form of type $e$ in place of a cuspidal function.

Lean: `New.Space.IsCuspidal.norm_le_of_firstMinimum_lt`, `New.Space.IsForm.norm_le_of_firstMinimum_lt` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* With the cusp frame of the last theorem, $F(g)$ is the mean of $F(g) - F(gv)$ over the quotient, since $F$ is cuspidal. By the covering, $F(gv) = F(g(z,1))$ with $\operatorname{dist}(z, 1) \le \delta$, so each term is at most $C$. For a form, use that forms are cuspidal. $\square$

### Rapid decay

**Theorem (Decay in a cusp).** Let $n$ be nonempty and $j \ge 0$. There is $\delta_0 > 0$ with the following property. Let $K'$ be a level, $W$ a space, $g \in G$, $\delta \ge 0$, and $X \neq 0$ a matrix with $X^* J_W X = 0$ whose radical in $W \cdot g$ is covered at size $\delta$ by $K'$. Let $f$ be a continuous function on $G$ with $|f| \le T$, $R(e) f = f$, of level $K'$, and left invariant under the rational points of the radical of $X$ in $W$. Then $|f(g)| \le (\delta / \delta_0)^j\, T$.

Lean: `New.Space.exists_norm_le_of_radicalCovered` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

**Theorem (Depth and height).** Let $n$ be nonempty and $K'$ an open subgroup of $G_f$. There is $\kappa' > 0$ such that for every space $V$ and every $g \in G$ there is $\delta > 0$ with $\delta^n \operatorname{ht}_V(g) = \kappa'$, and, if $\delta \le 1$, a cusp frame of size $\delta$ at $V \cdot g$ whose radical is covered at size $\delta$ by $K'$.

Lean: `New.Space.exists_cuspFrame_of_height` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

Here the height is $\operatorname{ht}_V(g) = \lambda(V \cdot g)^{-1}$.

**Theorem (Uniform rapid decay).** Let $K$ be an open subgroup of $G_f$ and $A \ge 0$ an integer. There is $R$ such that for every form $F$ of type $e$ for $V$ of level $K$ and every $c$ with $|F| \le c$ on $G$,
$$|F(g)|\, \operatorname{ht}_V(g)^A \le c R \quad \text{for all } g \in G.$$

Lean: `New.Space.exists_norm_mul_height_pow_le` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Combine the last two theorems at the level $K \cap K_0$ with $j = nA$, since $\delta^{nA} = (\kappa' / \operatorname{ht}_V(g))^A$. Then $R = (\kappa' / \min(\delta_0, 1)^n)^A$ works. $\square$

**Corollary.** A form of type $e$ decays rapidly: for every $A$ there is $C$ with $|F(g)|\, \operatorname{ht}_V(g)^A \le C$ for all $g$.

Lean: `New.Space.IsForm.mem_rapidFunctions` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

### Finite dimension

**Lemma (Uniform continuity of averages).** Let $\alpha$ be integrable on $G_\infty$, $K$ an open subgroup of $G_f$, and $\varepsilon > 0$. Then there is a neighbourhood $U$ of $1$ in $G$ with the following property. Let $z \in U$ with real part $z_\infty$, let $F$ be bounded, measurable and of level $K$, let $g \in G$, and let $C$ be a real number with $|F(g(x, 1))| \le C$ for all $x \in G_\infty$ with $\alpha(z_\infty^{-1} x) \neq \alpha(x)$. Then $|R(\alpha)F(gz) - R(\alpha)F(g)| \le \varepsilon |C|$.

Lean: `New.eventually_norm_realConv_sub_le` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

**Theorem (Finite dimension).** Let $K$ be an open subgroup of $G_f$. The forms of type $e$ for $V$ that have level $K$ make up a complex vector space of finite dimension.

Lean: `New.Space.finite_levelSpace` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Take $R$ from uniform rapid decay with $A = 1$. By Mahler's criterion ([reduction theory](/chapter/reduction-theory/)) there is a compact $C \subseteq G$ such that every $g$ with $\operatorname{ht}_V(g) \le 2R$ has $\gamma g \in C$ for some $\gamma \in \Gamma_V$. Take $U$ from the lemma for $\alpha = e$ and $\varepsilon = 1/2$, and cover $C$ by finitely many translates $a U^\circ$, $a \in t$.

Let $F$ have level $K$, $F(a^{-1}) = 0$ for $a \in t$, and $|F| \le M$. If $|F(g)| > M/2$, then $\operatorname{ht}_V(g) < 2R$, so $\gamma g \in a^{-1} U$ for some $\gamma$, $a$, and the lemma gives $|F(g)| = |R(e)F(\gamma g) - R(e)F(a^{-1})| \le M/2$. So $M/2$ is a bound, and by repetition $F = 0$. Thus $F \mapsto (F(a^{-1}))_{a \in t}$ is injective, and the dimension is at most $|t|$. $\square$

**Remark (Formalization).** The cover $t$ comes from existence statements, so $|t|$ is not explicit. The argument needs explicit dimensions only on definite groups, where Section 6 gives an exact formula. The theorem holds for every open subgroup $K$, not only for levels $K \subseteq K_0$.

### Projection of automorphic functions

**Theorem (Projection).** Let $F$ be automorphic for $V$ (continuous, left $\Gamma_V$-invariant, of some open level), and suppose that $x \mapsto e(x)\, F(g(x, 1))$ is integrable on $G_\infty$ for every $g \in G$. Then $R(e)F$ is a form of type $e$.

Lean: `New.Space.isForm_realConv` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

*Proof.* Truncate $F$ at height $t$. By Section 4, $R(e)F_t$ is a form of level $K$, and $R(e)F_t \to R(e)F$ pointwise by dominated convergence. A subspace of finite dimension of the functions on $G$ is closed for pointwise convergence, so $R(e)F$ lies in it. $\square$

**Remark (Formalization).** $R(e)F(g)$ is a Bochner integral, so it would be $0$ where the integrand is not integrable. The hypothesis excludes this.

### Where the argument uses these objects

Finite dimension is used in [the objects of the upper bound](/chapter/upper-bound-objects/) and in [grids, paths and turns](/chapter/grids-paths-turns/). The cusp estimate, with threshold $(m^{-2} / (M \kappa^2))^n$, is used in [deep level Poincaré series](/chapter/deep-level-poincare/). Rapid decay is used in [seesaw squares](/chapter/seesaw-squares/) and in [the comparison operator](/chapter/comparison-operator-1/). Cuspidality and projection are not used outside this chapter.
