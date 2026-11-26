---
title: Projective space and linear systems
lean:
  - Lib/General/Geometry/ProjectiveSpace.lean
decls:
  - New.ProjSpace
  - New.ProjSpace.coordSection
  - New.ProjSpace.coordRatio
  - New.ProjSpace.hyperplaneBundle
  - New.ProjSpace.isAffineOpen_chart
  - New.ProjSpace.landsIn_chart_iff_isUnit
  - New.LineBundle.IsHomogeneousCoords
  - New.LineBundle.IsHomogeneousCoords.smul
  - New.LineBundle.IsLinearSystem
  - New.ProjSpace.isLinearSystem_hyperplaneBundle
  - New.LineBundle.IsLinearSystem.pull
  - New.LineBundle.IsLinearSystem.mul
  - New.ProjSpace.exists_isHomogeneousCoords
  - New.LineBundle.exists_hom_isHomogeneousCoords_of_cover
  - New.LineBundle.exists_landsIn_opens_iff_isUnit
  - New.LineBundle.picClass_eq_of_isHomogeneousCoords
  - New.LineBundle.exists_picClass_eq_pull_hyperplane
  - New.LineBundle.IsLinearSystem.exists_hom_projSpace
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Projective space and linear systems

This section defines projective space, the bundle $\mathcal{O}(1)$, and homogeneous coordinates of points. It then gives the source form of the classical theorem that maps to projective space are the same as line bundles with generating sections. All the statements are in `Lib/General/Geometry/ProjectiveSpace.lean`.

### The classical statement

Let $A$ be a ring and $X$ a scheme over $A$. A morphism $\varphi \colon X \to \mathbb{P}^n_A$ over $A$ gives the invertible sheaf $\varphi^* \mathcal{O}(1)$ and its global sections $s_i = \varphi^*(x_i)$, which generate it. Conversely, an invertible sheaf $\mathcal{L}$ with global sections $s_0, \dots, s_n$ that generate it comes from a unique morphism $\varphi$ with $\mathcal{L} \cong \varphi^* \mathcal{O}(1)$ and $s_i = \varphi^*(x_i)$ under this isomorphism (Hartshorne, *Algebraic Geometry*, Chapter II, Theorem 7.1). On points: an $R$-valued point of $\mathbb{P}^n$ is, locally on $\operatorname{Spec} R$, a vector $(v_0, \dots, v_n)$ with one unit entry, up to a unit scalar.

The source proves the converse direction in a form adapted to line bundles given by cocycles. It proves the first direction through the notion of a linear system.

### Projective space

**Definition (Projective space).** For a type $\iota$, the scheme $\mathbb{P}^\iota = \operatorname{Proj} \mathbb{Z}[X_i : i \in \iota]$, with the polynomial ring graded by total degree.

Lean: `New.ProjSpace` (Lib/General/Geometry/ProjectiveSpace.lean).

The scheme is over $\operatorname{Spec} \mathbb{Z}$. Projective space over a base $S$ is the product $\mathbb{P}^\iota \times S$. The set $\iota$ can be infinite in the definition. The theorems on maps and on properness need $\iota$ finite.

**Definition (Coordinates).** For $i, j \in \iota$, the section $X_j / X_i$ of $\mathcal{O}$ over the chart $D_+(X_i)$, and the function on points $x_{ij}$ that it defines by `New.PointFn.ofSection`. So $x_{ij}(A, t)$ is the pull-back of $X_j / X_i$ along $t$ if $t$ lands in $D_+(X_i)$, and $0$ otherwise.

Lean: `New.ProjSpace.coordSection`, `New.ProjSpace.coordRatio` (Lib/General/Geometry/ProjectiveSpace.lean).

**Definition (The bundle O(1)).** The line bundle on $\mathbb{P}^\iota$ with index set $\iota$, opens $D_+(X_i)$, and transition functions $g_{ij} = x_{ij}$.

Lean: `New.ProjSpace.hyperplaneBundle` (Lib/General/Geometry/ProjectiveSpace.lean).

Classically, $\mathcal{O}(1)$ has the frame $X_i$ on $D_+(X_i)$, and $X_i = (X_i / X_j) X_j$. So the classical transition function from chart $j$ to chart $i$ is $X_i / X_j$. In the convention of the source, a section satisfies $s_i = g_{ij} s_j$, and the sections $X_k$ of $\mathcal{O}(1)$ become the families $s_i = X_k / X_i$. Then $s_i = (X_j / X_i) s_j$, which gives $g_{ij} = X_j / X_i$. The two conventions agree.

**Theorem.** Each chart $D_+(X_i)$ is affine. A point $t$ that lands in $D_+(X_i)$ lands in $D_+(X_j)$ if and only if $x_{ij}(A, t)$ is a unit.

Lean: `New.ProjSpace.isAffineOpen_chart`, `New.ProjSpace.landsIn_chart_iff_isUnit` (Lib/General/Geometry/ProjectiveSpace.lean).

### Homogeneous coordinates

**Definition (Homogeneous coordinates).** Let $L = (U_i, g_{ij})$ be a line bundle on $X$ and $t \colon \operatorname{Spec} A \to X$ a point. A vector $v \in A^\iota$ is a vector of *homogeneous coordinates* of $t$ for $L$ if, for each $j$,

1. $t$ lands in $U_j$ if and only if $v_j$ is a unit, and
2. if $v_j$ is a unit, then $g_{jk}(A, t) = v_k\, v_j^{-1}$ for all $k$.

Lean: `New.LineBundle.IsHomogeneousCoords` (Lib/General/Geometry/ProjectiveSpace.lean).

The inverse in the second condition is `Ring.inverse`, which is $0$ on non-units. The condition only applies when $v_j$ is a unit, so the junk value does not enter.

**Theorem.** If $v$ is a vector of homogeneous coordinates of $t$ and $u \in A^\times$, then so is $u v$.

Lean: `New.LineBundle.IsHomogeneousCoords.smul` (Lib/General/Geometry/ProjectiveSpace.lean).

The converse holds when some $v_j$ is a unit: two vectors of homogeneous coordinates of one point are then proportional by a unit. This is the classical statement that a point of $\mathbb{P}^n$ is a vector up to scalars. The definition says less than the classical one in one way. If $A$ is not local, the point $t$ may lie in no single chart, and then no $v_j$ is a unit. Such a $t$ has no vector of homogeneous coordinates at all, since the first condition would make $t$ land in no chart. For a local ring $A$, every point has one, and one of its entries is nonzero (`New.LineBundle.IsHomogeneousCoords.exists_ne_zero`).

### Linear systems

**Definition (Linear system).** A line bundle $L = (U_i, g_{ij})$ is a *linear system* if

1. each $g_{ij}$ is regular on all of $U_i$, not only on $U_i \cap U_j$;
2. $g_{ij}(A, t) = 0$ at each point $t$ that does not land in $U_i$;
3. at each point $t$ of $U_i$, the vector $(g_{ij}(A, t))_{j \in \iota}$ is a vector of homogeneous coordinates of $t$ for $L$.

Lean: `New.LineBundle.IsLinearSystem` (Lib/General/Geometry/ProjectiveSpace.lean).

The model is $g_{ij} = s_j / s_i$ on the open $U_i$ where the section $s_i$ does not vanish, for a family of global sections $(s_j)$ with no common zero. In this model $g_{ij}$ is defined on all of $U_i$, it is a unit exactly on $U_i \cap U_j$, and $g_{jk} = g_{ik} / g_{ij}$. The three conditions say exactly this. A linear system is thus a line bundle with a chosen family of generating sections, and with the cover and the trivializations that the sections determine. The second condition fixes the junk values: the function $g_{ij}$ is $0$ off its chart, as `New.PointFn.ofSection` makes it. So the family $j \mapsto (g_{ij})_i$ is a global section of $L$ for each $j$ (`New.LineBundle.IsLinearSystem.isSection`). It is the $j$-th coordinate section.

**Theorem.** $\mathcal{O}(1)$ is a linear system on $\mathbb{P}^\iota$. Pull-backs and tensor products of linear systems are linear systems.

Lean: `New.ProjSpace.isLinearSystem_hyperplaneBundle`, `New.LineBundle.IsLinearSystem.pull`, `New.LineBundle.IsLinearSystem.mul` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* For $\mathcal{O}(1)$: the function $x_{ij}$ comes from a section over $D_+(X_i)$, so it is regular there. It is $0$ off the chart by the definition of `New.PointFn.ofSection`. At a point of $D_+(X_i)$, the units among the $x_{ij}(A, t)$ mark the charts that contain $t$, and the identity $x_{jk} = x_{ik} / x_{ij}$ is the cocycle condition. For pull-backs, the three conditions are conditions on points, and a point of $Y$ composed with $p$ is a point of $X$. For tensor products, the index of a chart is a pair, a product is a unit if and only if each factor is one, and the coordinates multiply factor by factor. $\square$

### Points of projective space

**Theorem.** Let $b \colon \operatorname{Spec} A \to S$ be a point, and let $v \in A^\iota$ have a unit entry $v_i$. Then there is a point $s$ of $\mathbb{P}^\iota \times S$ with $\operatorname{pr}_2 \circ s = b$ such that $v$ is a vector of homogeneous coordinates of $s$ for the pull-back of $\mathcal{O}(1)$.

Lean: `New.ProjSpace.exists_isHomogeneousCoords` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* The ring of sections over $D_+(X_i)$ is the degree $0$ part of the localization $\mathbb{Z}[X]_{X_i}$. The substitution $X_j \mapsto v_j$ sends $X_i$ to a unit, so it extends to the localization. Its restriction to the degree $0$ part sends $X_j / X_i$ to $v_j / v_i$. This ring map gives a point $x$ of the affine chart $D_+(X_i)$ with coordinates $v_j / v_i$. Pair $x$ with $b$, and scale by the unit $v_i$. $\square$

**Theorem (Gluing of points).** Let $\kappa$ be finite and let $(s_j)_{j \in \kappa}$ be sections of a line bundle $L = (U_i, g_{ij})$ on $X$. Let $C$ be a line bundle indexed by $\iota \times \kappa$, used only for its cover, with $C_{(i, j)} \subseteq U_i$ and $s_{j,i}$ a unit on $C_{(i,j)}$. Then there is a morphism $f \colon X \to \mathbb{P}^\kappa$ such that, at each point $t$ of $C_{(i, j)}$, the vector $(s_{k,i}(A, t))_{k \in \kappa}$ is a vector of homogeneous coordinates of $f \circ t$ for $\mathcal{O}(1)$.

Lean: `New.LineBundle.exists_hom_isHomogeneousCoords_of_cover` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* At each point $t$ of $C_{(i, j)}$ the vector $(s_{k,i}(A, t))_k$ has the unit entry $s_{j,i}(A, t)$. The last theorem gives a point $F(t)$ of projective space, and the proof picks one with `choose`. On overlaps, the vectors for two charts differ by the unit $g_{i i'}(A, t)$. The two points are equal because $\mathbb{P}^\kappa \times X$ is a projective embedding over $X$ (Section 5), so a point is determined by its homogeneous coordinates and its image in the base. So the family $F$ is compatible with base change, and `New.exists_hom_of_cover` from Section 2 glues it to a morphism. $\square$

The chosen points $F(t)$ do not appear in the statement. The morphism $f$ is unique by Section 2, so the choice has no effect on the result.

**Theorem.** Let $p \colon Y \to X$ be surjective, and let $(s_j)_{j \in \kappa}$ be sections of $L$ with no common zero at the field-valued points of $X$ that factor through $p$: for each $i$, each field $K$ and each $t \colon \operatorname{Spec} K \to Y$ with $p \circ t$ in $U_i$, some $s_{j,i}(K, p \circ t)$ is nonzero. Then the opens of $U_i$ where $s_{j,i}$ is a unit cover $X$. The cover is given as the cover of a line bundle indexed by $\iota \times \kappa$, with transition functions $1$.

Lean: `New.LineBundle.exists_landsIn_opens_iff_isUnit` (Lib/General/Geometry/ProjectiveSpace.lean).

The condition with $p$ lets a user test the condition of no common zero on a cover of $X$, for instance on geometric points. A trivial bundle is used here as a container for a cover. Its transition functions play no part.

**Theorem.** Let $(s_j)_{j \in \kappa}$ be sections of $L$, and let $N$ be a line bundle indexed by $\kappa$. Suppose that at each point $t$ of $U_i$ the vector $(s_{j,i}(A, t))_j$ is a vector of homogeneous coordinates of $t$ for $N$. Then $[L] = [N]$.

Lean: `New.LineBundle.picClass_eq_of_isHomogeneousCoords` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* The family $(s_{j,i})_{(i, j)}$ is a frame of $L \otimes N^{-1}$. It is a unit on $U_i \cap N_j$ by the first condition on homogeneous coordinates, and the section relation follows from the second condition. $\square$

**Theorem (Maps to projective space).** Let $\kappa$ be finite, let $p \colon Y \to X$ be surjective, and let $(s_j)_{j \in \kappa}$ be sections of $L$ with no common zero at the field-valued points that factor through $p$. Then there is $f \colon X \to \mathbb{P}^\kappa$ such that

1. $[L] = [f^* \mathcal{O}(1)]$, and
2. at each point $t$ of $U_i$, the vector $(s_{j,i}(A, t))_j$ is a vector of homogeneous coordinates of $t$ for $f^* \mathcal{O}(1)$.

Lean: `New.LineBundle.exists_picClass_eq_pull_hyperplane` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* The last three theorems in order. The cover comes from the condition of no common zero. The morphism comes from gluing on that cover. A check on the cover shows that the points of $U_i$ that $f$ sends to the chart $j$ are in $C_{(i, j)}$, which gives the second statement on all of $U_i$. The comparison of classes follows. $\square$

This is the converse half of Hartshorne, Chapter II, Theorem 7.1, in a weaker form. The source gives equality of classes in $\operatorname{Pic} X$, not an isomorphism $L \cong f^* \mathcal{O}(1)$ that sends $s_j$ to $f^* X_j$. The second statement replaces that part: it says that the sections are the coordinates of $f$. The source does not state uniqueness of $f$ here. It follows from the second statement and Section 5, since a morphism to $\mathbb{P}^\kappa$ is determined by the homogeneous coordinates of its points.

**Theorem.** Let $N$ be a linear system on $X$ with a finite index set $\kappa$, and let $s \colon X \to S$. Then there is $j \colon X \to \mathbb{P}^\kappa \times S$ with $\operatorname{pr}_2 \circ j = s$ and $j^* \operatorname{pr}_1^* \mathcal{O}(1) = N$, as an equality of line bundles: the covers and the transition functions are equal.

Lean: `New.LineBundle.IsLinearSystem.exists_hom_projSpace` (Lib/General/Geometry/ProjectiveSpace.lean).

*Proof.* Apply the last theorem with $p$ the identity to the coordinate sections $j \mapsto (g_{ij})_i$. They have no common zero, because $g_{ii} = 1$ on $U_i$. The map $f$ pulls $\mathcal{O}(1)$ back to a linear system with the same homogeneous coordinates as $N$ at every point. Two linear systems with this property are equal (`New.LineBundle.IsLinearSystem.ext_of_transition_eq_mul`). Pair $f$ with $s$. $\square$

The equality of line bundles is a strong statement. It holds because a linear system is a line bundle with its cover and trivializations fixed by the coordinates. So a linear system is the same as a morphism to projective space, and not only up to isomorphism.

**Example.** Take $X = \mathbb{P}^1 = \mathbb{P}^{\{0, 1\}}$ and the linear system $\mathcal{O}(1)$. The point $t$ with values in a ring $A$ given by the vector $(1, a)$ lands in $D_+(X_0)$. Its coordinates for chart $0$ are $x_{00} = 1$ and $x_{01} = a$. It lands in $D_+(X_1)$ if and only if $a$ is a unit, and then $x_{10} = a^{-1}$ and $x_{11} = 1$. The point with the vector $(1, 0)$ lands only in chart $0$. At this point $x_{10}(A, t) = 0$, by the junk convention, since the point is not in chart $1$. This value is consistent with the vector $(1, 0)$: the second condition on homogeneous coordinates applies only to charts that contain the point.

**Remark (Formalization).** The weak form of Theorem 7.1 is sufficient for the uses in the source. `Lib/Shimura/ThetaModuli/FamilyFromPoints.lean` and `Lib/Shimura/ArcExtension.lean` call `New.LineBundle.exists_picClass_eq_pull_hyperplane`. The first passes the identity as $p$, the second a composite of morphisms. The gluing step uses `choose` for the local points, but the glued morphism is unique, so no choice leaks into a statement. The whole section works with an arbitrary scheme $X$ and an arbitrary base $S$. It needs no noetherian or separatedness hypotheses, which is in line with Hartshorne's statement.
