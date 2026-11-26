---
title: Hodge cohomology
lean:
  - Lib/General/Geometry/EtaleCharts.lean
  - Lib/Cohomology/Hodge/Site.lean
  - Lib/Cohomology/Hodge/GrothendieckSymbol.lean
  - Lib/Cohomology/Hodge/Kunneth.lean
  - Lib/Cohomology/Hodge/DiagonalClass.lean
decls:
  - New.Variety.HodgeTest
  - New.Variety.HodgeTest.sqZeroExt
  - New.Variety.hodgeCoeff
  - New.Variety.HodgeH
  - New.Variety.HodgeH.scale
  - New.Variety.HodgeH.baseChange
  - New.Variety.EtaleChart
  - New.Variety.EtaleChart.exists_univPoint
  - New.Variety.HasAtlas
  - New.Variety.symbolClass
  - New.Variety.hodge_excision
  - New.Variety.IsPointSum
  - New.Variety.pointClass
  - New.Variety.IsPointSum.map_eq_pointClass
  - New.Variety.IsPointSum.map_eq_sum_pointClass
  - New.Variety.kunneth
  - New.Variety.exists_diagonal_class
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hodge cohomology

The Woods Hole formula of Section 7 is a statement in Hodge cohomology, not in $\ell$-adic cohomology. This section builds Hodge cohomology with the method of Section 2. The test objects are now pairs of an algebra and a free module, and the coefficient is the exterior algebra. Throughout, $k$ is a field. From the Künneth formula on, $k$ has characteristic $0$.

### Pairs and the coefficient

**Definition (Hodge test).** A Hodge test over $k$ is a pair $(A, A^\iota)$ of a commutative $k$-algebra $A$ and a free module on a finite ordered set $\iota$. A morphism $(A, A^\iota) \to (B, B^\kappa)$ is a $k$-algebra map $f : A \to B$ with an $f$-semilinear map $A^\iota \to B^\kappa$.

Lean: `New.Variety.HodgeTest` (Lib/General/Geometry/EtaleCharts.lean).

Write $(A, M)$ for a Hodge test, with $M = A^\iota$. Two functors on Hodge tests carry the theory.

**Definition (Square-zero extension).** The functor $(A, M) \mapsto A \oplus M$ sends a Hodge test to the square-zero extension of $A$ by $M$, as a $k$-algebra.

Lean: `New.Variety.HodgeTest.sqZeroExt` (Lib/Cohomology/Hodge/Site.lean).

**Definition (Hodge coefficient).** The coefficient of Hodge cohomology is the functor $(A, M) \mapsto \bigwedge_A M$, the exterior algebra, with values in abelian groups.

Lean: `New.Variety.hodgeCoeff` (Lib/Cohomology/Hodge/Site.lean).

A $k$-point of $A \oplus M$ over a point of $A$ is a tangent vector with values in $M$. So a functor $N$ on $k$-algebras, read as $(A, M) \mapsto N(A \oplus M)$, sees the tangent spaces of $N$.

**Definition (Hodge cohomology).** Let $N$ be a functor from $k$-algebras to abelian groups. Its Hodge cohomology in degree $q$ is $\operatorname{Hdg}^q(N) = \operatorname{Ext}^q(N \circ \mathrm{sqZeroExt}, \bigwedge)$ in the category of functors from Hodge tests to abelian groups. For a space $X$ one takes $N = \mathbb{Z}[X]$. For a subfunctor $U \subseteq X$ one takes $N = \mathbb{Z}[X] / \mathbb{Z}[U]$, the relative chains of Section 2.

Lean: `New.Variety.HodgeH` (Lib/Cohomology/Hodge/Site.lean).

The group is a $k$-module, and pull-back along a map of spaces is $k$-linear. The degree $q$ is the Ext degree. The degree of forms is the grading of $\bigwedge M$, and $\operatorname{Hdg}^q$ contains all form degrees at once. The classical analogue is $\bigoplus_p H^q(X, \Omega^p_X)$ for a smooth variety $X$. The source does not compare the two.

Two operations act on Hodge cohomology. For $t \in k$, the scaling $\operatorname{scale}_t$ is induced by $(a, m) \mapsto (a, tm)$ on $A \oplus M$.

Lean: `New.Variety.HodgeH.scale` (Lib/Cohomology/Hodge/Site.lean).

For a $k$-algebra $E \to k$, base change sends the Hodge cohomology over $E$ of $N$ to the Hodge cohomology over $k$ of $N$ restricted to $k$-algebras. It restricts scalars on the tests and is the identity on $\bigwedge_A M$.

Lean: `New.Variety.HodgeH.baseChange` (Lib/Cohomology/Hodge/Site.lean).

### Charts and the universal point

The source works with spaces that are covered by étale charts.

**Definition (Étale chart).** Let $X$ be a functor from $k$-algebras to sets. A chart of dimension $d$ of $X$ is a $k$-algebra $R$ with $d$ elements $x_1, \dots, x_d$ that make $R$ étale over $k[T_1, \dots, T_d]$, and a point $y \in X(R)$, such that the map $h_R \to X$ given by $y$ is injective on $A$-points for every $A$ and has an open subfunctor as image.

Lean: `New.Variety.EtaleChart` (Lib/General/Geometry/EtaleCharts.lean).

**Definition (Atlas).** The space $X$ has an atlas of dimension $d$ if it is separated and there are finitely many charts of dimension $d$ whose images contain every point of $X$ with values in a field.

Lean: `New.Variety.HasAtlas` (Lib/General/Geometry/EtaleCharts.lean).

A smooth separated scheme of finite type over $k$, of pure dimension $d$, has such charts locally.

**Proposition (Universal point).** Let $R$ be the ring of a chart with coordinates $x_1, \dots, x_d$. There is a section $u : R \to R \oplus R^d$ of the projection such that $(R, R^d)$ represents the functor $(A, M) \mapsto \operatorname{Hom}_k(R, A \oplus M)$ through $u$. Concretely, $u$ lifts the identity of $R$ and sends $x_i$ to $(x_i, e_i)$.

Lean: `New.Variety.EtaleChart.exists_univPoint` (Lib/Cohomology/Hodge/Site.lean).

*Proof.* An étale map lifts uniquely along a square-zero extension. So a $k$-algebra map $s : R \to A \oplus M$ is determined by its composite with $A \oplus M \to A$ and by the $M$-parts of the $s(x_i)$. These data are exactly a morphism of Hodge tests $(R, R^d) \to (A, M)$. The same uniqueness defines $u$. $\square$

**Example (A chart).** Let $R$ be the ring of a chart of dimension $d$. By the proposition, the functor $\mathbb{Z}[h_R \circ \mathrm{sqZeroExt}]$ is $\mathbb{Z}[\operatorname{Hom}((R, R^d), -)]$. This is projective, by the Yoneda argument of Section 2. So $\operatorname{Hdg}^q(h_R) = 0$ for $q > 0$, and $\operatorname{Hdg}^0(h_R) = \bigwedge_R R^d$. In the classical picture, $\bigwedge_R R^d$ is the algebra of differential forms on $\operatorname{Spec} R$, with basis the products $dx_{i_1} \wedge \dots \wedge dx_{i_p}$. The scaling by $t$ corresponds to the endomorphism of $(R, R^d)$ that multiplies $R^d$ by $t$. So it acts on the forms of degree $p$ by $t^p$.

**Example (A point).** Take $R = k$ with no coordinates. A morphism of Hodge tests $(k, 0) \to (A, M)$ is the unique pair of the structure map and the zero map. So $(k, 0)$ is initial, and $\operatorname{Hdg}^0(h_k) = \bigwedge_k 0 = k$, with no higher groups. The scaling acts as the identity.

### The symbol $[dT/T]$

A class of a point needs a local model. The source uses Grothendieck's symbol on affine space relative to the complement of the origin. Let $\mathbb{A}^d$ be affine $d$-space as a functor, and let $\mathbb{A}^d \setminus 0$ be the subfunctor of vectors whose entries generate the unit ideal.

**Definition (Symbol).** The symbol $[dT/T] \in \operatorname{Hdg}^d(\mathbb{A}^d, \mathbb{A}^d \setminus 0)$ is the class of the cocycle $(v, l_1, \dots, l_d) \mapsto \det(l_1, \dots, l_d) \cdot dT_1 \wedge \dots \wedge dT_d$. Here $v$ is a point of $\mathbb{A}^d$ with values in $A \oplus M$ off the origin, and each $l_j \in A^d$ is a linear form with value $1$ on the $A$-part of $v$.

Lean: `New.Variety.symbolClass` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

A point of $\mathbb{A}^d \setminus 0$ has such witnesses $l$, since its entries generate the unit ideal. The source proves a transformation law: if $f = Mg$ for two tuples that cut out the same locus, the pull-backs $[df/f]$ and $[dg/g]$ differ by $\det M$, under conditions on the forms. In characteristic $0$ it also proves that the symbol in degree $d + 1$ restricts to the product of the symbols in degrees $d$ and $1$. The head of the file on the fixed point formula cites Hartshorne, *Residues and Duality* (1966), III.9, for the symbol.

**Theorem (Excision).** Let $u : X' \to X$ be injective on points with open image, and let every point of $X$ over a field outside the image lie in an open subfunctor contained in $U$. Then pull-back along $u$ is bijective from $\operatorname{Hdg}^q(X, U)$ to $\operatorname{Hdg}^q(X', u^{-1} U)$ for all $q$.

Lean: `New.Variety.hodge_excision` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

*Proof sketch.* The union of the image of $u$ and $U$ is Zariski locally everything. Hodge cohomology has Zariski descent: on a Hodge test, the relative chains of the locus where some $f_i$ is a unit have no cohomology when the $f_i$ generate the unit ideal. So the union is dense, and the excision of Section 2 applies. $\square$

### Classes of points

Let $s$ be a set of $k$-points of $X$ and $n : X(k) \to k$ a function. Write $X \setminus s$ for the subfunctor of points none of whose values in fields comes from $s$.

**Definition (Point sum).** A relative class $\xi \in \operatorname{Hdg}^d(X, U)$ has multiplicity $n(z)$ at each $z \in s$ if, for each $z \in s$, there are a chart of dimension $d$ that contains $z$ and $d$ functions $g$ on it that cut out $z$, such that the pull-back of $\xi$ to the chart is $n(z) \cdot [dg/g]$. Nothing is asked of $\xi$ away from $s$.

Lean: `New.Variety.IsPointSum` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

**Definition (Class of a point).** The class $[z] \in \operatorname{Hdg}^d(X)$ of a $k$-point $z$ is the image under $\operatorname{Hdg}^d(X, X \setminus \{z\}) \to \operatorname{Hdg}^d(X)$ of a class that has multiplicity $1$ at $z$.

Lean: `New.Variety.pointClass` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

**Proposition (Independence of the choice).** Let $X$ be separated. Every class with support $z$ and multiplicity $1$ at $z$ maps to $[z]$.

Lean: `New.Variety.IsPointSum.map_eq_pointClass` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

*Proof sketch.* Let $\xi$ and $\xi_0$ be two such classes, with charts $a$ and $b$. Take a chart $c$ inside the intersection of their images that contains $z$. On $c$ both classes are symbols of functions that cut out $z$. By the transformation law, the two symbols agree. Excision to $c$ is injective on classes with support $z$, so $\xi = \xi_0$. $\square$

**Theorem (Sum over points).** Let $X$ be separated and $s$ a finite set of $k$-points. If $\xi \in \operatorname{Hdg}^d(X, X \setminus s)$ has multiplicity $n(z)$ at each $z \in s$, then the image of $\xi$ in $\operatorname{Hdg}^d(X)$ is $\sum_{z \in s} n(z) [z]$.

Lean: `New.Variety.IsPointSum.map_eq_sum_pointClass` (Lib/Cohomology/Hodge/GrothendieckSymbol.lean).

*Proof sketch.* For one point this is the proposition, scaled by $n(z)$. For several points the proof is an induction on $s$, by Mayer-Vietoris: the complement of $s$ is the intersection of the complements of its points. $\square$

**Remark (Formalization).** (1) The definition of $[z]$ uses `Classical.epsilon (IsPointSum {z} 1)` ([GrothendieckSymbol.lean](lean:Lib/Cohomology/Hodge/GrothendieckSymbol.lean#L941)). If no class of multiplicity $1$ exists, the epsilon returns an arbitrary class, and $[z]$ is its image. This is a junk value, and the register lists it (F-051 in [Junk values](/chapter/register-of-findings/)). The proposition above shows that the choice does not matter when a class of multiplicity $1$ exists and $X$ is separated. If $X$ has an atlas of dimension $d$, the source proves that such a class exists for every $k$-point. For a $d$ that is not the dimension of the charts, $[z]$ may be junk. (2) The file has the line `seal H.map` with no `in` ([GrothendieckSymbol.lean](lean:Lib/Cohomology/Hodge/GrothendieckSymbol.lean#L802)). It acts to the end of the file and hides the definition of pull-back from `rfl` and `simp` there. The register lists this (F-020 in [Settings and instances](/chapter/register-of-findings/)). It changes how the proofs in the file are written, not what the statements say.

### The Künneth formula

From now on $k$ has characteristic $0$. The source needs only a weak form of the Künneth formula.

**Theorem (Künneth, spanning form).** Let $X$ have an atlas of dimension $d$. Then every class $z \in \operatorname{Hdg}^n(X \times X)$ is a finite sum of cross products $x \times y$ with $x \in \operatorname{Hdg}^a(X)$, $y \in \operatorname{Hdg}^b(X)$ and $b + a = n$. The cross product is the cup product for the multiplication of exterior algebras, pulled back along $\mathbb{Z}[X \times X] \to \mathbb{Z}[X] \otimes \mathbb{Z}[X]$.

Lean: `New.Variety.kunneth` (Lib/Cohomology/Hodge/Kunneth.lean).

*Proof sketch.* Replace $X$ by a subfunctor $V$ built from charts, which the atlas gives. It is Zariski locally all of $X$, so $V \times V$ is dense in $X \times X$ and restriction of classes to it is injective. The proof uses the Leray-Hirsch map of Section 5, with the products with a basis of the classes on $V$, and a dévissage in each factor in turn. At represented functors the Example on charts reduces the claim to forms: the forms on $R \otimes_k R'$ are spanned by products of forms on $R$ and on $R'$. Finally the classes on $V$ in the products are restrictions of classes on $X$. $\square$

The classical Künneth formula is an isomorphism $\bigoplus_{a+b=n} H^a(X, F) \otimes_k H^b(Y, G) \cong H^n(X \times_k Y, F \boxtimes G)$ for quasi-coherent sheaves on suitable schemes over a field. The source cites Stacks Project, Tag 0BEC, for it. The source proves only that the map is onto.

### The class of the diagonal

Let $\Delta \subseteq X \times X$ be the diagonal, and let $X \times X \setminus \Delta$ be the subfunctor of pairs whose values in every field are distinct.

**Theorem (Diagonal class).** Let $X$ have an atlas of dimension $d$. There is a class $\delta \in \operatorname{Hdg}^d(X \times X, X \times X \setminus \Delta)$ with the following property. Every point $z$ of $X$ with values in a field has a chart $a$ of $X$ with coordinates $x_1, \dots, x_d$ and an open subfunctor $O \ni (z, z)$ of $X \times X$ on which $\delta$ is the symbol $[d(x \otimes 1 - 1 \otimes x) / (x \otimes 1 - 1 \otimes x)]$ of the differences of the coordinates.

Lean: `New.Variety.exists_diagonal_class` (Lib/Cohomology/Hodge/DiagonalClass.lean).

*Proof sketch.* Each chart $a_i$ of the atlas gives a chart $V_i$ of $X \times X$ near the diagonal, on which the differences of the coordinates cut out $\Delta$. On each $V_i$ the symbol of these differences is a class relative to the complement of $\Delta$. On overlaps the symbols agree, by the transformation law. Below degree $d$ the relative groups along the diagonal vanish, since the differences form a regular sequence of length $d$ in the chart ring. So a Mayer-Vietoris argument glues the local symbols to a global class without obstruction. $\square$

The class $\delta$ is the analogue of the cycle class of the diagonal. The statement is existential: the source does not fix one $\delta$.

**Remark (Formalization).** The Künneth formula and the diagonal class both carry the instance `[CharZero k]`. The Künneth formula takes `[hX : HasAtlas d X]` as an instance, and the diagonal class takes `(hX : HasAtlas d X)` as an explicit argument. Neither result is an isomorphism with a classical group. The diagonal class is characterized only by its local form near the diagonal.
