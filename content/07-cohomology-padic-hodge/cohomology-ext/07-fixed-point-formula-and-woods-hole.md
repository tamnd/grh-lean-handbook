---
title: The fixed point formula and the Woods Hole formula
lean:
  - Lib/Cohomology/Hodge/FixedPointFormula.lean
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Cohomology/PointClass/LinearIndependence.lean
  - Lib/PadicComparison/HodgeTate/Map.lean
  - Lib/Cohomology/WoodsHole.lean
decls:
  - New.Variety.ConstIfCoincident
  - New.Variety.IsCoincidenceSet
  - New.Variety.exists_isCoincidenceSet
  - New.Variety.HasJacobianRatio
  - New.Variety.IsTangentPoly
  - New.Variety.IsTangentPoly.hasJacobianRatio_eval_div
  - New.Variety.IsTangentPoly.constIfCoincident
  - New.Variety.scaledGraph
  - New.Variety.exists_diagonal_local_terms
  - New.Variety.hodgeTateMap
  - New.Variety.linearIndepOn_hodgeTateMap_pointClass
  - New.Variety.IsNullFamily
  - Polynomial.exists_dual_eval_mul_eq_coeff_mul
  - New.Variety.sum_mul_hodgeTateMap_scaledGraph_eq_zero
  - New.Variety.ellAdicCohom.woods_hole
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The fixed point formula and the Woods Hole formula

This section pulls the diagonal class of Section 6 back along a twisted graph. The result is a sum of point classes over the coincidences, with Jacobian ratios as multiplicities. It then states the Woods Hole formula of the source, the vanishing half of the holomorphic Lefschetz formula, and computes a model case.

### The classical statement

Let $M$ be a compact complex manifold and $f : M \to M$ a holomorphic map whose fixed points are simple, that is, $\det(1 - df_x) \neq 0$ at each fixed point $x$. The holomorphic Lefschetz formula of Atiyah and Bott (M. F. Atiyah and R. Bott, A Lefschetz fixed point formula for elliptic complexes II, Ann. of Math. 88 (1968) 451-491) says that

$$\sum_q (-1)^q \operatorname{tr}\big(f^* \mid H^q(M, \mathcal{O}_M)\big) = \sum_{f(x) = x} \frac{1}{\det(1 - df_x)}.$$

In one standard form, the version for $h$-forms replaces $\mathcal{O}_M$ by $\Omega^h_M$. The local term at $x$ then has the numerator $\operatorname{tr}(\Lambda^h df_x)$. Up to the sign $(-1)^h$, this numerator is the coefficient of $z^h$ in $\det(1 - z\,df_x)$. The source uses that coefficient.

The source does not state this equality. It states only that the right side vanishes when the maps kill the relevant classes. The pair $(c, u)$ below plays the part of a correspondence, and $c = \mathrm{id}$ is the case of a single map $u$.

### Coincidences

Let $k$ be a field with dual numbers $k[\varepsilon]$, and let $W$ and $X$ be functors from $k$-algebras to sets. A coincidence of $u, c : W \to X$ is a point $x \in W(A)$ with $c(x) = u(x)$.

**Definition 7.1 (Reduced coincidence).** A point $x \in W(k[\varepsilon])$ satisfies the condition if $c(x) = u(x)$ implies that $x$ is the image of its base point under $k \to k[\varepsilon]$.

Lean: `New.Variety.ConstIfCoincident` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

This is the algebraic form of the condition that the fixed points are simple.

**Definition 7.2 (Coincidence set).** A finite set $s$ of $k$-points of $W$ is a coincidence set of $u$ and $c$ if three conditions hold. First, every $k[\varepsilon]$-valued point satisfies Definition 7.1. Second, every $w \in s$ is a coincidence. Third, for every $k$-algebra $K$ that is a field, every coincidence $x \in W(K)$ is the image of some $w \in s$.

Lean: `New.Variety.IsCoincidenceSet` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

**Lemma 7.3.** Let $k$ be algebraically closed and let $X$ be separated. Suppose that every $k[\varepsilon]$-valued coincidence of $u$ and $c$ is constant, and that finitely many charts of $W$ with $d$ étale coordinates contain all field-valued coincidences. Then a coincidence set exists.

Lean: `New.Variety.exists_isCoincidenceSet` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

*Proof sketch.* Since $X$ is separated, the coincidences in each chart are cut out by an ideal $J_i$ of the chart ring. The chart ring is of finite type, so it is Noetherian and $J_i$ has finitely many minimal primes. By the Nullstellensatz each minimal prime has a $k$-point. Since the coincidences have no nonzero tangent vectors, each component is that one point. $\square$

### Jacobian ratios and tangent polynomials

Let $E \to k$ be a map of fields. Let $X$ be a functor on $E$-algebras with an atlas of dimension $d$, and let $u, c$ map $W$ to $X$ read on $k$-algebras.

**Definition 7.4 (Jacobian ratio).** Let $t, n \in k$ and let $w$ be a $k$-point of $W$. Then $n$ is the Jacobian ratio of $u$ and $c$ at $w$ for $t$ if the following holds for every chart $A$ of $X$ that contains $c(w)$. There is a $d \times d$ matrix $N$ with $\det N = n$ such that, for all tangent vectors $v$ at $w$ in the coordinates of $A$,

$$t\,du(v) - dc(v) = N\big(du(v) - dc(v)\big).$$

Lean: `New.Variety.HasJacobianRatio` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

**Definition 7.5 (Tangent polynomial).** Let $y \in W(k)$ and let $P$ be a polynomial over $k$. Then $P$ is a tangent polynomial of rank $d$ of $c$ and $u$ at $y$ if there are a finitely generated $k$-module $T$ of rank $d$, a point $v \in W(k \oplus T^*)$ and an endomorphism $B$ of $T$ with these properties. Each $x \in T$ gives a tangent vector $f(x) \in W(k[\varepsilon])$ by evaluation at $x$. The point $v$ lies over $y$. The map $x \mapsto c(f(x))$ is injective. For all $x$, $u(f(x)) = c(f(Bx))$. For all $t \in k$, $P(t) = P(0)\det(1 - tB)$.

Lean: `New.Variety.IsTangentPoly` (Lib/Cohomology/Etale/Basic.lean).

**Lemma 7.6.** Suppose that every field-valued point of $W$ lies in a chart with $d$ coordinates. Let $P$ be a tangent polynomial of $c$ and $u$ at $w$ with $P(1) \neq 0$. Then for every $t \in k$, the Jacobian ratio of $u$ and $c$ at $w$ for $t$ is $P(t)/P(1)$. Every $k[\varepsilon]$-valued coincidence above $w$ is constant.

Lean: `New.Variety.IsTangentPoly.hasJacobianRatio_eval_div` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

Lean: `New.Variety.IsTangentPoly.constIfCoincident` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

*Proof sketch.* From $P(1) \neq 0$ we get $P(0) \neq 0$ and $\det(1 - B) \neq 0$. So $S = 1 - B$ is invertible. On the tangent space, $du - dc = dc \circ (B - 1)$ and $t\,du - dc = dc \circ (tB - 1)$. So $t\,du - dc = N(du - dc)$ with $N$ conjugate to $(1 - tB)S^{-1}$, and $\det N = \det(1 - tB)/\det(1 - B) = P(t)/P(1)$. A tangent vector $x$ with $u(f(x)) = c(f(x))$ has $c(f(Bx)) = c(f(x))$, so $Bx = x$ by injectivity, and $x = 0$ since $1 - B$ is injective. $\square$

### The twisted graph and the local terms

From here $k$ has characteristic $0$. For $t \in k$, let $s_t$ be the map $(a, m) \mapsto (a, tm)$ on a square-zero extension $B \oplus M$.

**Definition 7.7 (Twisted graph).** For $u, c : W \to X$ and $t \in k$, the twisted graph is the map $w \mapsto (u(s_t w), c(w))$ from $W(B \oplus M)$ to $X(B \oplus M) \times X(B \oplus M)$.

Lean: `New.Variety.scaledGraph` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

The parameter $t$ scales the derivative of $u$ and nothing else.

**Theorem 7.8 (Fixed point formula).** Let $X$ have an atlas of dimension $d$. Then there is a class $\delta \in \operatorname{Hdg}^d(X \times X)$ with this property. Let $E$ be a field of characteristic $0$ over $k$ and let $W$ be a separated functor on $E$-algebras whose field-valued points lie in charts of dimension $d$. Let $u, c : W \to X$, let $s$ be a coincidence set of $u$ and $c$, let $t \in E$, and let $n(w)$ be the Jacobian ratio at $w$ for $t$, for each $w \in s$. Then two statements hold.

1. Some class relative to the complement of $s$ is a point sum with multiplicities $n$.
2. The pull-back of $\delta$, read over $E$, along the twisted graph is $\sum_{w \in s} n(w)\,[w]$, where $[w]$ is the point class of $w$.

Lean: `New.Variety.exists_diagonal_local_terms` (Lib/Cohomology/Hodge/FixedPointFormula.lean).

*Proof sketch.* Take the diagonal class of Section 6 and forget its supports. Its pull-back along the twisted graph has support in $s$. So it is enough to find its multiplicity at each $w \in s$, by the result of Section 6 that a class with support in $s$ is the sum of its local point classes. Near $w$, the differences of the coordinates of $u \circ s_t$ and $c$ cut out $w$. The transformation law for Grothendieck symbols then gives the multiplicity as the determinant that relates these differences to the coordinate differences at $t = 1$. That determinant is $n(w)$. $\square$

With Lemma 7.6, the multiplicity at a simple coincidence is $P(t)/P(1)$, so the coefficient of $t^h$ is $\operatorname{coeff}_h(P)/P(1)$. For $c = \mathrm{id}$ this is the coefficient of $t^h$ in $\det(1 - t\,du)/\det(1 - du)$. These are the local terms of the Woods Hole formula, in the form that the source uses.

**Remark (Formalization).** The class $\delta$ comes from an existential statement, and any choice works below. A multiplicity $n(w)$ can be $0$. For example, $P(t)/P(1)$ is $0$ when $t \neq 0$ and $t^{-1}$ is an eigenvalue of $B$. Then $w$ gives no term in statement 2, and the formula still holds. Lemma 7.6 needs $P(1) \neq 0$ because the source divides by $P(1)$, and division by $0$ in Lean gives $0$. The hypothesis excludes this junk value.

### The Hodge-Tate map

To tell point classes apart, the source uses the Hodge-Tate map of Volume 7, chapter 5 (/chapter/comparison-theorems/).

**Definition 7.9 (Hodge-Tate map).** For each weight $h$, the Hodge-Tate map $\lambda_h$ is a $k$-linear map from $\operatorname{Hdg}^q(N)$ to a group of pairs $\mathrm{PairH}(N)$. That group is the total cohomology on pairs $(S, M)$ with coefficients $S[1/p]$.

Lean: `New.Variety.hodgeTateMap` (Lib/PadicComparison/HodgeTate/Map.lean).

**Theorem 7.10 (Point classes stay independent).** Let $k$ be algebraically closed with an embedding into $\overline{\mathbb{Q}}_p$. Let $Y$ be a scheme over a ring $R$ with a projective embedding, and let the $k$-points of $Y$ have an atlas of dimension $d$. Then $\lambda_d$ is injective on the span of the point classes of $k$-points: the images of distinct point classes are linearly independent over $k$.

Lean: `New.Variety.linearIndepOn_hodgeTateMap_pointClass` (Lib/Cohomology/PointClass/LinearIndependence.lean).

The register of findings (/chapter/register-of-findings/, "Citations and docstrings", F-108) records that a summary of the source describes this result as a statement about degrees of zero-cycles. The Lean statement is only the linear independence above.

### The Woods Hole formula

**Definition 7.11 (Null family).** Let $u_i : W \to Z$ be maps and $a \in k^{(I)}$ a family of scalars, almost all zero. The family is null in weight $h$ for rank $d$ if the following holds for every $c : W \to Z$. Let $S$ be the set of pairs $(i, y)$ with $a_i \neq 0$, $y \in W(k)$ and $c(y) = u_i(y)$. Suppose each $(i, y) \in S$ has a tangent polynomial $P_{(i,y)}$ of rank $d$ of $c$ and $u_i$ at $y$ with $P_{(i,y)}(1) \neq 0$. Then $S$ is finite and

$$\sum_{(i, y) \in S} a_i \, \frac{\operatorname{coeff}_h(P_{(i,y)})}{P_{(i,y)}(1)} = 0.$$

Lean: `New.Variety.IsNullFamily` (Lib/Cohomology/Etale/Basic.lean).

**Theorem 7.12 (Woods Hole formula, vanishing half).** Let $R$ be a subalgebra of a field $E$ of characteristic $0$, and let $E \to k$ with $k$ algebraically closed and embedded in $\overline{\mathbb{Q}}_p$. Let $Y$ be proper over $R$, and let $W$ over $R$ have a projective embedding. Let the $E$-points of $Y$ and the $k$-points of $W$ have atlases of dimension $d$. Let $u_i : W \to Y$ be maps and $b_i \in k$, almost all zero. Assume that $h > d$, or that the following holds over $k$ for every class $x \in \operatorname{Hdg}^q(Y)$ over $E$ with $q \le d$:

$$\sum_i b_i \, \lambda_h\big(u_i^* x\big) = 0.$$

Then the family $(u_i, b_i)$ is null in weight $h$ for rank $d$.

Lean: `New.Variety.ellAdicCohom.woods_hole` (Lib/Cohomology/WoodsHole.lean).

The proof uses two auxiliary results.

**Lemma 7.13.** Let $k$ be an infinite field and $h \ge 0$. There is a linear form $L$ on the functions $k \to k$ such that $L(t \mapsto Q(t)\,a) = \operatorname{coeff}_h(Q)\,a$ for every polynomial $Q$ and every $a \in k$.

Lean: `Polynomial.exists_dual_eval_mul_eq_coeff_mul` (Lib/Cohomology/WoodsHole.lean).

**Lemma 7.14.** Assume the atlas of $Y$ and the hypothesis on $u_i$, $b_i$ and $h$ of Theorem 7.12. Let $c : W \to Y$, let $\varphi$ be a linear form on $\mathrm{PairH}(W)$, and let $L$ be as in Lemma 7.13. For a class $z \in \operatorname{Hdg}^d(Y \times Y)$, let $\Phi_{t,i}\, z$ be the pull-back of $z$, read over $k$, along the twisted graph of $(u_i, c)$ for $t$. Then

$$\sum_i b_i \, L\Big(t \mapsto \varphi\big(\lambda_d(\Phi_{t,i}\, z)\big)\Big) = 0.$$

Lean: `New.Variety.sum_mul_hodgeTateMap_scaledGraph_eq_zero` (Lib/Cohomology/WoodsHole.lean).

*Proof sketch of Theorem 7.12.* Fix $c$ and tangent polynomials $P$ as in Definition 7.11. Let $\delta$ be the class of Theorem 7.8. By Theorem 7.10 there is a linear form $\varphi$ with $\varphi(\lambda_d [w]) = 1$ for every point class $[w]$. Let $L$ be the form of Lemma 7.13.

By Lemma 7.6, each coincidence of $u_i$ and $c$ is reduced and has Jacobian ratio $P(t)/P(1)$. By Lemma 7.3, the coincidences of $u_i$ and $c$ form a finite coincidence set $s_i$, and $S$ is the union of the sets $\{i\} \times s_i$. So $S$ is finite. By Theorem 7.8,

$$\Phi_{t,i}\,\delta = \sum_{w \in s_i} \frac{P_{(i,w)}(t)}{P_{(i,w)}(1)}\,[w].$$

Apply $\varphi \circ \lambda_d$, which gives $1$ on each $[w]$, and then $L$, which takes the coefficient of $t^h$. The $i$-th term becomes $\sum_{w \in s_i} \operatorname{coeff}_h(P_{(i,w)})/P_{(i,w)}(1)$. The weighted sum over $i$ is the sum of Definition 7.11. Lemma 7.14 with $z = \delta$ says that it is zero.

For Lemma 7.14, the Künneth formula of Section 6 writes $z$ as a sum of cross products $x \times y$. On a cross product, the pull-back along the twisted graph is the cup product of $s_t^* u_i^* x$ and $c^* y$ on the diagonal of $W$. The map $\lambda_d$ splits this cup product into terms of weights $j$ and $d - j$, and the scaling $s_t$ multiplies the term of weight $j$ by $t^j$. So $L$ keeps only the term with $j = h$. If $h > d$, no such term exists. If $h \le d$, that term contains $\sum_i b_i \lambda_h(u_i^* x)$, which is zero by hypothesis. $\square$

### A model case on the projective line

Let $W = Y = \mathbb{P}^1$ over a field of characteristic $0$, with $d = 1$. Let $c = \mathrm{id}$ and let $u(z) = az$ with $a \neq 0, 1$. The coincidences are the fixed points $0$ and $\infty$. At $0$ the derivative is $a$, so $B = a$ and $P(t) = 1 - ta$. At $\infty$, in the coordinate $1/z$, the derivative is $a^{-1}$, so $P(t) = 1 - ta^{-1}$. Both satisfy $P(1) \neq 0$.

For $h = 0$ the sum of the local terms is

$$\frac{1}{1 - a} + \frac{1}{1 - a^{-1}} = \frac{1}{1 - a} - \frac{a}{1 - a} = 1.$$

This is the classical value: the left side of the Atiyah-Bott formula is the trace on $H^0(\mathbb{P}^1, \mathcal{O}) = k$, which is $1$, since $H^1(\mathbb{P}^1, \mathcal{O}) = 0$.

For $h = 1$ the coefficients of $t$ are $-a$ and $-a^{-1}$, and the sum is

$$\frac{-a}{1 - a} + \frac{-a^{-1}}{1 - a^{-1}} = \frac{-a}{1 - a} + \frac{1}{1 - a} = 1.$$

Classically, the formula for $1$-forms has the value $-\operatorname{tr}(u^* \mid H^1(\mathbb{P}^1, \Omega^1)) = -1$. The sign $(-1)^h$ of the numerator accounts for the difference.

For the single map $u$ with $b = 1$, the family is not null in weights $0$ and $1$, so by Theorem 7.12 its hypothesis must fail there. A null family needs several maps whose pull-backs cancel. Volume 8 applies the formula to correspondences on Shimura varieties.

**Remark (Formalization).** Several points of the Lean statement need care.

1. Only the vanishing half is stated, and no trace is computed.
2. For $h > d$ the hypothesis is vacuous. The conclusion is then trivial, since each local term has $\operatorname{coeff}_h(P) = 0$ (Exercise 4).
3. Definition 7.11 is an implication. If some coincidence has no tangent polynomial with $P(1) \neq 0$, for example a coincidence that is not simple, then the condition holds for that $c$ without content.
4. The theorem lives in the namespace `ellAdicCohom`, but the statement and the proof use only Hodge cohomology and the Hodge-Tate map. The register records this as F-112 (/chapter/register-of-findings/, "Citations and docstrings").
5. The field $k$ must be algebraically closed and embedded in $\overline{\mathbb{Q}}_p$, through the instance `[EmbeddedInQpBar p k]`. The prime $p$ is implicit, and it enters through the Hodge-Tate map. The field $E$ has characteristic $0$. The instance `[IsProper Y.hom]` is a hypothesis, and the proof does not refer to it by name.
