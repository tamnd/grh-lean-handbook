---
title: Complex points and étale charts
lean:
  - Lib/General/Geometry/DenseComplexPoints.lean
  - Lib/General/Geometry/EtaleCharts.lean
  - Lib/General/Geometry/PointsOfProperSchemes.lean
decls:
  - New.IsDenseFamily
  - New.IsSeparatingFamily
  - New.exists_lift_of_dense_preimage
  - New.exists_reduced_closure
  - New.IsDenseFamily.surjective
  - New.IsSeparatingFamily.pointFn_ext
  - New.IsSeparatingFamily.hom_ext
  - New.IsSeparatingFamily.exists_map_of_coords
  - New.exists_valuative_arc_of_isDenseFamily
  - New.Variety.IsOpenSubfunctor
  - New.Variety.IsSeparatedFunctor
  - New.Variety.EtaleChart
  - New.Variety.EtaleChart.locus
  - New.Variety.etale_polyEval_iff
  - New.Variety.IsChartCovered
  - New.Variety.HasAtlas
  - New.Variety.IsClosedClass
  - New.Variety.IsCharting
  - New.Variety.IsClosedClass.freeAb_iSup_locus
  - New.Variety.HasAtlas.exists_isCharting
  - New.Variety.Comparison.isClosedClass
  - New.Variety.IsCharted
  - New.Variety.isSeparatedFunctor_algPointsOf
  - New.Variety.hasAtlas_algPointsOf
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Complex points and étale charts

This section treats two further uses of points. The first is a family of complex points that is dense in a reduced scheme. Functions and morphisms are then determined by their values on the family. The second is the functor of points of a scheme on algebras over a ring $k$, with étale charts and atlases. An atlas gives a charting subfunctor, and a charting subfunctor is the hypothesis `New.Variety.IsCharted` of the comparison theorems of this volume.

### Dense families of complex points

Classically, let $X$ be a scheme of finite type over $\mathbb{C}$. Its closed points are dense (Hartshorne, *Algebraic Geometry*, Chapter II, Exercise 3.14), and they are the points with values in $\mathbb{C}$. If $X$ is reduced, a regular function that vanishes at all closed points is zero, by the Nullstellensatz. Two morphisms from a reduced scheme to a separated scheme that agree on a dense open subset are equal (Hartshorne, Chapter II, Exercise 4.2).

The source works with an arbitrary scheme $X$ and an arbitrary family $\xi \colon Z \to \operatorname{Hom}(\operatorname{Spec} \mathbb{C}, X)$.

**Definition (Dense and separating families).** The family $\xi$ is *dense* if the images of the points $\xi_z$ form a dense subset of $X$. It is *separating* if it is dense and $X$ is reduced.

Lean: `New.IsDenseFamily`, `New.IsSeparatingFamily` (Lib/General/Geometry/DenseComplexPoints.lean).

**Theorem.** Let $i \colon Y \to Z$ be a closed immersion and $f \colon X \to Z$ with $X$ reduced. If $f^{-1}(i(Y))$ is dense in $X$, then $f$ factors through $i$.

Lean: `New.exists_lift_of_dense_preimage` (Lib/General/Geometry/DenseComplexPoints.lean).

*Proof.* The pull-back of the ideal sheaf of $i$ has closed support that contains a dense set. So its support is all of $X$, and the ideal maps to $0$ in the reduced scheme $X$. $\square$

**Theorem (Reduced closure).** Every family $\xi$ of complex points of $X$ factors as $\xi_z = i \circ e_z$ through a closed immersion $i \colon Y \to X$, with $e$ a separating family of $Y$.

Lean: `New.exists_reduced_closure` (Lib/General/Geometry/DenseComplexPoints.lean).

**Theorem.** Let $\xi$ be a dense family of $X$, and let $f \colon Y \to X$ be universally closed. If each $\xi_z$ lifts to a complex point of $Y$, then $f$ is surjective.

Lean: `New.IsDenseFamily.surjective` (Lib/General/Geometry/DenseComplexPoints.lean).

**Theorem.** Let $\xi$ be a separating family of $X$.

1. Two functions on points that are regular on an open $U$ and agree at all $\xi_z$ that land in $U$ agree at every point that lands in $U$.
2. Let $X$ and $G$ be schemes over $S$, with $G$ separated over $S$. Two morphisms $X \to G$ over $S$ that agree on all $\xi_z$ are equal.

Lean: `New.IsSeparatingFamily.pointFn_ext`, `New.IsSeparatingFamily.hom_ext` (Lib/General/Geometry/DenseComplexPoints.lean).

*Proof.* (1) On $U$ both functions come from sections $s$ and $s'$, by Section 2. If $s - s' \neq 0$, then, since $X$ is reduced, its basic open is not empty. Some $\xi_z$ lies in it, and there $s - s'$ is a unit. This contradicts the agreement at $\xi_z$. (2) The equalizer of the two morphisms is a closed subscheme, since $G$ is separated. Every $\xi_z$ factors through it, so it is surjective by the last theorem. A surjective closed immersion into a reduced scheme gives $f = g$. $\square$

The second statement is stronger than Hartshorne's exercise in one way: the set of agreement is a dense set of points, not a dense open set. It needs no finiteness hypothesis, because the density is a hypothesis on the family, and not a consequence of the Nullstellensatz.

**Theorem.** Let $e$ be a separating family of $X$ and $p$ a family of complex points of $G$, over the same points of $S$. Let $W$ be a linear system on $X$ and $M$ a projective embedding of $G$ over $S$, both with the finite index set $\iota$. If $e_z$ and $p_z$ have the same homogeneous coordinates for all $z$, then there is a morphism $d \colon X \to G$ over $S$ with $d \circ e_z = p_z$ and $d^* M = W$.

Lean: `New.IsSeparatingFamily.exists_map_of_coords` (Lib/General/Geometry/DenseComplexPoints.lean).

*Proof.* By Sections 4 and 5, $W$ is the pull-back of $\mathcal{O}(1)$ along a morphism $f \colon X \to \mathbb{P}^\iota \times S$, and $M$ is the pull-back along a closed immersion $j \colon G \to \mathbb{P}^\iota \times S$. The points $f \circ e_z = j \circ p_z$ lie in the image of $j$. They are dense in $X$, so $f$ factors through $j$ by the theorem on dense preimages. $\square$

This theorem lets the source build a morphism of algebraic varieties from an analytic statement: the coordinates of complex points agree. It is used in `Lib/Shimura/ArcExtension.lean` and `Lib/Shimura/ThetaModuli/FamilyFromPoints.lean`, for the moduli of Volume 8 ([complex abelian varieties](/chapter/complex-abelian-varieties/)).

**Theorem (Arcs).** Let $S$ be locally noetherian, with finitely many complex points $\eta_i$ whose images are dense. For each point $s$ of $S$ there are an index $i$, a valuation $v$ of $\mathbb{C}$ with values in $\mathbb{R}_{\ge 0}$, and a morphism $a \colon \operatorname{Spec} V \to S$ from the spectrum of its valuation ring that restricts to $\eta_i$ on $\operatorname{Spec} \mathbb{C}$ and sends the closed point to $s$.

Lean: `New.exists_valuative_arc_of_isDenseFamily` (Lib/General/Geometry/DenseComplexPoints.lean).

*Proof.* Some $\eta_i$ specializes to $s$, since the closure of the finitely many images is all of $S$. So $\eta_i$ gives a map from the local ring at $s$ to $\mathbb{C}$. The source claims that a valuation ring of $\mathbb{C}$ dominates the image of this map, with a valuation of rank one, and it constructs such a valuation ring through minimal primes over a principal ideal. $\square$

Classically, this is the existence of a valuation ring that dominates a local ring, as in the valuative criteria. The rank one condition is the extra content. It is needed because the valuations of the source take values in $\mathbb{R}_{\ge 0}$.

### Functors of points on algebras

For the cohomology of this volume, the source does not use a scheme as a locally ringed space. It uses its functor of points on commutative algebras over a ring $k$. For a scheme $W$ over $\operatorname{Spec} R$ and an $R$-algebra $k$, `New.Variety.algPointsOf k R W` is the functor $A \mapsto W(A)$ on commutative $k$-algebras. It takes values in `Type 1`. The next chapter ([cohomology and Ext](/chapter/cohomology-ext/)) defines cohomology as Ext groups of such functors.

**Definition (Open subfunctor).** A subfunctor $V \subseteq X$ is *open* if each point $x \in X(A)$ has an ideal $I \subseteq A$ such that, for each $\varphi \colon A \to B$, $\varphi(x) \in V(B)$ if and only if $\varphi(I) B = B$.

Lean: `New.Variety.IsOpenSubfunctor` (Lib/General/Geometry/EtaleCharts.lean).

**Definition (Separated functor).** $X$ is *separated* if for each pair $x, y \in X(A)$ there is an ideal $J \subseteq A$ such that $\varphi(x) = \varphi(y)$ if and only if $\varphi$ kills $J$.

Lean: `New.Variety.IsSeparatedFunctor` (Lib/General/Geometry/EtaleCharts.lean).

Classically, these say that $V \to X$ is an open immersion and that the diagonal of $X$ is a closed immersion, after base change to each affine scheme. For a scheme the ideals are those of the open set and of the closed diagonal.

**Definition (Étale chart).** A *chart* of dimension $d$ of $X$ is a $k$-algebra $R$ with elements $c_1, \dots, c_d$ that make $R$ étale over $k[T_1, \dots, T_d]$, and a point $y \in X(R)$ such that the map $\operatorname{Hom}(R, -) \to X$, $\varphi \mapsto \varphi(y)$, is injective on $A$-points for all $A$, with an open image. The image is the *locus* of the chart.

Lean: `New.Variety.EtaleChart`, `New.Variety.EtaleChart.locus` (Lib/General/Geometry/EtaleCharts.lean).

So a chart is an affine open subscheme with étale coordinates. Classically, a scheme smooth of relative dimension $d$ over $k$ is covered by such opens (EGA IV, Corollaire 17.11.4).

**Theorem.** Let $k$ be noetherian and $R$ of finite type over $k$. Elements $c_1, \dots, c_d$ of $R$ make $R$ étale over $k[T_1, \dots, T_d]$ if and only if, for every square-zero extension $B \to A$ of $k$-algebras, every map $R \to A$ and every lift of the values of the $c_j$ to $B$, there is a unique lift $R \to B$ with these values.

Lean: `New.Variety.etale_polyEval_iff` (Lib/General/Geometry/EtaleCharts.lean).

This is the infinitesimal lifting criterion of Grothendieck (EGA IV, Section 17), for maps of finite type over a noetherian ring.

**Definition (Atlas).** $X$ is *covered by charts* of dimension $d$ if each point of $X$ with values in a field lies in the locus of some chart. $X$ has an *atlas* of dimension $d$ if it is separated and finitely many charts of dimension $d$ contain all its field-valued points.

Lean: `New.Variety.IsChartCovered`, `New.Variety.HasAtlas` (Lib/General/Geometry/EtaleCharts.lean).

The condition on field-valued points is enough to cover $X$, because the loci are open: a point with values in a ring lies in the union of the loci after a Zariski cover of its spectrum.

**Theorem.** Let $W$ be proper over $\operatorname{Spec} R$, and let $k$ be an $R$-algebra. Then `algPointsOf k R W` is separated. If in addition $W \times_R k$ is smooth of relative dimension $d$ over $k$, it has an atlas of dimension $d$.

Lean: `New.Variety.isSeparatedFunctor_algPointsOf`, `New.Variety.hasAtlas_algPointsOf` (Lib/General/Geometry/PointsOfProperSchemes.lean).

*Proof.* Proper morphisms are separated, and the source shows that the diagonal locus is cut out by an ideal. For the atlas, a point of $W$ with values in a $k$-algebra is a point of the base change $W_k$. Each point of $W_k$ has an affine neighbourhood that is standard smooth of relative dimension $d$, and this neighbourhood is a chart. $W_k$ is quasi-compact, so finitely many charts suffice. $\square$

The atlas does not need $k$ noetherian. The next step does.

### Charting subfunctors

**Definition (Closed class).** A class $P$ of functors $D \to \mathrm{Ab}$ is *closed* if it contains every zero functor and, for every short exact sequence $0 \to N_1 \to N_2 \to N_3 \to 0$ with $N_1$ in $P$, $N_2$ is in $P$ if and only if $N_3$ is.

Lean: `New.Variety.IsClosedClass` (Lib/Cohomology/Etale/BijectiveComparisons.lean).

**Definition (Charting subfunctor).** A subfunctor $V$ of $X$ is *charting* if

1. it is locally everything: for each $y \in X(A)$ and maximal ideal $\mathfrak{m}$ of $A$, there is an $a \notin \mathfrak{m}$ such that $y$ maps into $V$ along every $A \to B$ that makes $a$ a unit;
2. the free abelian group functor $\mathbb{Z}[V]$ lies in every closed class $P$ that contains $\mathbb{Z}[\operatorname{Hom}(R, -)]$ for the ring $R$ of each chart of $X$, of any dimension, whose coordinates are all units.

Lean: `New.Variety.IsCharting` (Lib/General/Geometry/EtaleCharts.lean).

A chart whose coordinates are units is étale over the torus $\mathbb{G}_m^d = \operatorname{Spec} k[T_1^{\pm 1}, \dots, T_d^{\pm 1}]$. So the second condition says that $\mathbb{Z}[V]$ is in the smallest closed class that contains the pieces étale over tori.

**Theorem.** Let $k$ be noetherian, $X$ separated, and $u$ a finite family of charts with unit coordinates. If a closed class $P$ contains $\mathbb{Z}[\operatorname{Hom}(R, -)]$ for each chart with unit coordinates, then it contains $\mathbb{Z}[\bigcup_p \operatorname{locus}(u_p)]$.

Lean: `New.Variety.IsClosedClass.freeAb_iSup_locus` (Lib/General/Geometry/EtaleCharts.lean).

*Proof.* The intersection of two charts is a chart, since $X$ is separated. A chart inside a chart with unit coordinates has unit coordinates. The source then applies `New.Variety.IsClosedClass.freeAb_iSup` to the set of loci of charts inside some $u_p$. That lemma says: if a set of subfunctors is closed under intersection and $\mathbb{Z}[V]$ is in $P$ for each member $V$, then $\mathbb{Z}[\bigcup_i U_i]$ is in $P$ for each finite family of members. $\square$

**Theorem.** Let $k$ be noetherian and let $X$ have an atlas of dimension $d$. Then some subfunctor of $X$ is charting.

Lean: `New.Variety.HasAtlas.exists_isCharting` (Lib/General/Geometry/EtaleCharts.lean).

*Proof.* For each chart $a_i$ of the atlas and each set $S$ of coordinates, shift the coordinates in $S$ by $1$. The shifted coordinates are still étale, by the lifting criterion. Invert the product of the new coordinates. The result is a chart $u_{(i, S)}$ with unit coordinates. At a field point of $a_i$, shift exactly the coordinates that vanish there. Then the field point lies in $u_{(i, S)}$. So the finitely many $u_{(i, S)}$ cover the field-valued points. Their union is locally everything, and the last theorem gives the second condition. $\square$

The shift by $1$ is the classical trick: the coordinate $T$ and the coordinate $T + 1$ do not vanish together, so $\mathbb{A}^1 = \mathbb{G}_m \cup (\mathbb{G}_m - 1)$.

**Theorem.** For a comparison $c$ of cohomologies, the functors $N$ on $D$ for which $c$ induces bijections $\operatorname{Ext}^n(\psi^* N, F) \to \operatorname{Ext}^n(\psi'^* N, F')$ for all $n$ form a closed class.

Lean: `New.Variety.Comparison.isClosedClass` (Lib/General/Geometry/EtaleCharts.lean).

*Proof.* Precomposition with $\psi$ and $\psi'$ is exact. A short exact sequence gives long exact sequences of Ext groups, and the five lemma gives the claim. The source derives it from `New.Variety.Comparison.devissage`. $\square$

**Definition (Charted scheme).** A scheme $Y$ over $\operatorname{Spec} R$ is *charted* over the $R$-algebra $k$ if `algPointsOf k R Y` has a charting subfunctor.

Lean: `New.Variety.IsCharted` (Lib/General/Geometry/EtaleCharts.lean).

The use is the following. To prove that a comparison map of cohomologies is bijective for $Y$, a proof under `New.Variety.IsCharted` checks it for the pieces étale over tori, where it can be computed. The closed class of the last theorem then contains $\mathbb{Z}[V]$. Condition 1 compares $\mathbb{Z}[V]$ with $\mathbb{Z}[Y]$.

**Remark (Formalization).** Four points.

1. `New.Variety.IsCharting` is impredicative. Its second condition quantifies over all predicates $P$ on functors to abelian groups, a type in a higher universe. Lean allows this, because the result is a proposition. The definition says that $\mathbb{Z}[V]$ lies in the smallest closed class generated by the pieces étale over tori, without a construction of that class.
2. The class `New.Variety.IsCharted` is a hypothesis of the comparison theorems: `Lib/PadicComparison/CrystallineFrobenius.lean` (lines 627 and 717), `Lib/PadicComparison/HodgeTate/PeriodMap.lean` (lines 126 and 273), `Lib/PadicComparison/Primitive/ComparisonTheorem.lean` (lines 231 and 354) and `Lib/Shimura/CongruenceRelation/EichlerShimura.lean` (line 48).
3. It is discharged in `Lib/Shimura/Eigenspace.lean`, at lines 449, 508, 576 and 656, each time by the term `(hasAtlas_algPointsOf X.dimension).exists_isCharting`. The hypotheses come from the fields `proper` and `smooth` of the model in `Lib/Shimura/HeckeTower/Model.lean`.
4. `New.Variety.HasAtlas.exists_isCharting` needs $k$ noetherian, because the lifting criterion does. In `Lib/Shimura/Eigenspace.lean` the rings $k$ are named $R$ and $\Omega$.
