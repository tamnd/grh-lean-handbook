---
title: Points and functions on points
lean:
  - Lib/General/Geometry/LineBundles.lean
decls:
  - New.specMap
  - New.LandsIn
  - New.PointFn
  - New.PointFn.IsRegularOn
  - New.PointFn.evalSection
  - New.PointFn.ofSection
  - New.PointFn.isRegularOn_ofSection
  - New.PointFn.ofSection_fromSpecStalk
  - New.PointFn.landsIn_basicOpen
  - New.PointFn.point_eq_of_ofSection_eq
  - New.hom_ext_of_isOpenCover
  - New.hom_ext_of_points
  - New.exists_hom_of_cover
  - New.PointFn.exists_ofSection_glue
  - New.PointFn.IsRegularOn.exists_ofSection
  - New.PointFn.IsRegularOn.pull
  - New.PointFn.IsRegularOn.ext_of_dominant_of_isOpenCover
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Points and functions on points

This section gives the basic language of the chapter. A scheme is seen through its points with values in rings. A function is a rule that gives a value at each such point. The section states when such a rule is regular, and it proves that a regular rule comes from a section of the structure sheaf. It then gives the gluing of morphisms from points and the descent of functions along a flat, surjective, quasi-compact morphism. Everything is in the first half of `Lib/General/Geometry/LineBundles.lean`.

### The classical picture

Let $X$ be a scheme. For a ring $A$, an $A$-valued point of $X$ is a morphism $t \colon \operatorname{Spec} A \to X$. The functor $A \mapsto X(A) = \operatorname{Hom}(\operatorname{Spec} A, X)$ determines $X$: a morphism of schemes $X \to Y$ is the same as a natural transformation $X(-) \to Y(-)$ of functors on rings. This is the Yoneda lemma together with the fact that every scheme has an open cover by affine schemes. Eisenbud and Harris, *The Geometry of Schemes*, Chapter VI, develop schemes from this point of view.

A global function on $X$ is a morphism $X \to \mathbb{A}^1_{\mathbb{Z}} = \operatorname{Spec} \mathbb{Z}[T]$. Indeed, for any scheme $X$ and ring $R$, morphisms $X \to \operatorname{Spec} R$ correspond to ring maps $R \to \Gamma(X, \mathcal{O}_X)$ (Hartshorne, *Algebraic Geometry*, Chapter II, Exercise 2.4), and a ring map $\mathbb{Z}[T] \to \Gamma(X, \mathcal{O}_X)$ is the choice of one element. So a section $s \in \Gamma(X, \mathcal{O}_X)$ gives, at each point $t \in X(A)$, the element $t^* s \in A$, and these elements satisfy $(\varphi^* t)^* s = \varphi(t^* s)$ for each ring map $\varphi \colon A \to B$. Conversely, such a compatible family of elements is a natural transformation $X(-) \to \mathbb{A}^1(-)$, so it comes from one section.

The source takes this picture as the definition. It does not use the restriction maps of the structure sheaf. It works with rules on points and with one condition of compatibility.

### Functions on points

All schemes in this chapter live in the universe $0$ of Lean, and all rings are objects of `CommRingCat` in that universe.

**Definition (Landing in an open).** A morphism $t \colon Y \to X$ *lands in* an open $U \subseteq X$ if $t^{-1}(U) = Y$.

Lean: `New.LandsIn` (Lib/General/Geometry/LineBundles.lean).

In Lean, `New.LandsIn t U` is `⊤ ≤ t ⁻¹ᵁ U`. For a point $t \colon \operatorname{Spec} A \to X$, it says that every prime of $A$ maps into $U$. If $A$ is local, it is enough that the closed point maps into $U$, by the lemma `New.landsIn_iff_mem`.

**Definition (Functions on points).** A *function on points* of $X$ is a rule $f$ that attaches to each ring $A$ and each point $t \colon \operatorname{Spec} A \to X$ an element $f(A, t) \in A$.

Lean: `New.PointFn` (Lib/General/Geometry/LineBundles.lean).

The Lean type is `∀ A : CommRingCat, (Spec A ⟶ X) → A`, of type `Type 1` because it quantifies over all rings. The docstring says it plainly: there is "no compatibility required". Functions on points form a commutative ring under pointwise operations. If $X$ is a scheme over $\operatorname{Spec} R$, they form an $R$-algebra: a scalar $r$ acts at $t$ through the image of $r$ in $A$.

**Definition (Spectrum of a ring map).** For a ring map $\varphi \colon R \to B$, the morphism $\operatorname{Spec}\varphi \colon \operatorname{Spec} B \to \operatorname{Spec} R$.

Lean: `New.specMap` (Lib/General/Geometry/LineBundles.lean).

The abbreviation takes a ring map of Lean types, not a morphism of `CommRingCat`. It appears in most statements of the chapter.

**Definition (Regular on an open).** A function on points $f$ is *regular on* $U$ if, for every ring map $\varphi \colon A \to B$ and every point $t \colon \operatorname{Spec} A \to X$ that lands in $U$,
$$f(B, t \circ \operatorname{Spec}\varphi) = \varphi(f(A, t)).$$

Lean: `New.PointFn.IsRegularOn` (Lib/General/Geometry/LineBundles.lean).

The condition says nothing about points that do not land in $U$. There $f$ may take any values.

**Remark (Formalization).** The definition of `New.PointFn` imposes no condition, so a function on points is far from a function on $X$. The rule with $f(A, t) = 1$ if $A$ is a field and $f(A, t) = 0$ otherwise is a function on points. It is not regular on any nonempty open $U$: for $x \in U$ with residue field $\kappa$, the map $\varphi \colon \kappa[\varepsilon]/(\varepsilon^2) \to \kappa$ and the point of $U$ over $\kappa[\varepsilon]/(\varepsilon^2)$ that factors through $\operatorname{Spec}\kappa$ give $1 \neq \varphi(0)$. Nothing in the type of $f$ says so. The plan of this book records this as finding F-062: "`PointFn X` is any rule on points with values in rings, with no compatibility." The source puts the compatibility into the predicate `IsRegularOn` and into the fields of the structures that use functions on points. A reader must check, for each statement, that the functions that occur carry the condition `IsRegularOn` on the right open. The structures of Section 3 always do. Values off the open are junk values. They never enter a conclusion, except where a statement asks that they be $0$.

### Sections as functions on points

**Definition (The function of a section).** Let $U \subseteq X$ be open and $s \in \Gamma(X, U)$. For a point $t$ that lands in $U$, let $\operatorname{ev}_t \colon \Gamma(X, U) \to A$ be the ring map $\Gamma(X,U) \to \Gamma(\operatorname{Spec} A, \operatorname{Spec} A) = A$ given by $t$. The function of $s$ is
$$\operatorname{ofSection}(s)(A, t) = \begin{cases} \operatorname{ev}_t(s) & \text{if } t \text{ lands in } U, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.PointFn.evalSection`, `New.PointFn.ofSection` (Lib/General/Geometry/LineBundles.lean).

The map `New.PointFn.ofSection` is a homomorphism of non-unital rings `Γ(X, U) →ₙ+* PointFn X`. It is not unital, since the function of $1$ is $0$ at the points that do not land in $U$. The value $0$ off $U$ is a junk value. It is chosen so that sums and products of sections give sums and products of functions.

**Theorem.** The function of a section over $U$ is regular on $U$.

Lean: `New.PointFn.isRegularOn_ofSection` (Lib/General/Geometry/LineBundles.lean).

*Proof.* For $t$ landing in $U$ and $\varphi \colon A \to B$, the point $t \circ \operatorname{Spec}\varphi$ lands in $U$, and $\operatorname{ev}_{t \circ \operatorname{Spec}\varphi} = \varphi \circ \operatorname{ev}_t$ by the naturality of the identification $\Gamma(\operatorname{Spec} A, \operatorname{Spec} A) = A$. $\square$

Three lemmas link the values of sections to the classical objects.

**Theorem.** Let $x \in U$ and $s \in \Gamma(X, U)$. The value of $s$ at the canonical point $\operatorname{Spec} \mathcal{O}_{X,x} \to X$ is the germ $s_x \in \mathcal{O}_{X,x}$.

Lean: `New.PointFn.ofSection_fromSpecStalk` (Lib/General/Geometry/LineBundles.lean).

**Theorem.** Let $t$ land in $U$ and $s \in \Gamma(X, U)$. Then $t$ lands in the basic open $D(s) \subseteq U$ if and only if $\operatorname{ofSection}(s)(A, t)$ is a unit of $A$.

Lean: `New.PointFn.landsIn_basicOpen` (Lib/General/Geometry/LineBundles.lean).

*Proof.* The preimage of $D(s)$ under $t$ is the basic open $D(a)$ of $\operatorname{Spec} A$, with $a = \operatorname{ev}_t(s)$. It is all of $\operatorname{Spec} A$ if and only if $a$ lies in no prime, that is, if and only if $a$ is a unit. $\square$

**Theorem.** Let $U$ be an affine open, and let $t, x \colon \operatorname{Spec} A \to X$ land in $U$. If every section over $U$ has the same value at $t$ and at $x$, then $t = x$.

Lean: `New.PointFn.point_eq_of_ofSection_eq` (Lib/General/Geometry/LineBundles.lean).

*Proof.* A point of the affine scheme $U$ is determined by the ring map $\Gamma(X, U) \to A$ that it defines. $\square$

### Gluing morphisms from points

The next three results are the functor of points in the form that the source uses.

**Theorem.** Let $(V_a)$ be an open cover of $Y$, and let $f, g \colon Y \to X$. If $t \circ f = t \circ g$ for each point $t \colon \operatorname{Spec} A \to Y$ that lands in some $V_a$, then $f = g$. In particular, two morphisms that agree on all ring-valued points are equal.

Lean: `New.hom_ext_of_isOpenCover`, `New.hom_ext_of_points` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Refine the cover by affine opens. The inclusions of these affine opens are points that land in the cover, and morphisms that agree on an open cover are equal. $\square$

**Theorem (Gluing from points).** Let $(V_a)$ be an open cover of $Y$. Suppose that for each $a$, each ring $A$ and each point $t \colon \operatorname{Spec} A \to Y$ that lands in $V_a$ there is a morphism $F_a(t) \colon \operatorname{Spec} A \to X$. Suppose that the morphisms are compatible: if $t$ lands in $V_a$, $\varphi \colon A \to B$ is a ring map and $t \circ \operatorname{Spec}\varphi$ lands in $V_b$, then
$$F_b(t \circ \operatorname{Spec}\varphi) = F_a(t) \circ \operatorname{Spec}\varphi.$$
Then there is a morphism $f \colon Y \to X$ with $t \circ f = F_a(t)$ for all such $a$ and $t$.

Lean: `New.exists_hom_of_cover` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Every morphism of affine schemes is $\operatorname{Spec}$ of a ring map, so the hypothesis holds for all morphisms $\operatorname{Spec} B \to \operatorname{Spec} A$. For two points $t$ and $s$ in $V_a$ and $V_b$, the two morphisms $F_a(t)$ and $F_b(s)$ agree on the fibre product of $t$ and $s$. This is tested on the points of the fibre product, where both sides are values of $F$ at one point. Now refine the cover by affine opens and glue the morphisms $F$ on the members of the refinement. The glued morphism has the stated values, as one checks on the pull-back of the cover along $t$. $\square$

The statement is an existence statement, with no uniqueness clause. Uniqueness follows from `New.hom_ext_of_isOpenCover`.

### Regular functions come from sections

The main result of this part says that a regular function is the function of a section, at the points of the open. The source proves it as the special case of a descent theorem.

**Theorem (Descent of functions).** Let $p \colon Y \to X$ be flat, surjective and quasi-compact, let $U \subseteq X$ be open and let $(V_a)$ be an open cover of $Y$. Let $f_a$ be functions on points of $Y$, with $f_a$ regular on $p^{-1}(U) \cap V_a$. Suppose that $f_a(A, t) = f_b(A, s)$ whenever $t \circ p = s \circ p$ lands in $U$, $t$ lands in $V_a$ and $s$ lands in $V_b$. Then there is a section $s \in \Gamma(X, U)$ with
$$\operatorname{ofSection}(s)(A, t \circ p) = f_a(A, t)$$
for every $a$ and every point $t$ of $Y$ that lands in $V_a$ with $t \circ p$ in $U$.

Lean: `New.PointFn.exists_ofSection_glue` (Lib/General/Geometry/LineBundles.lean).

*Proof.* A function is a morphism to the affine line $\mathbb{A} = \operatorname{Spec} \mathbb{Z}[T]$. A point $t$ in $p^{-1}(U) \cap V_a$ gives the ring map $\mathbb{Z}[T] \to A$ with $T \mapsto f_a(A, t)$, and so a morphism $\operatorname{Spec} A \to \mathbb{A}$. Regularity of $f_a$ and the hypothesis of agreement make these morphisms compatible in the sense of the gluing theorem. So they glue to a morphism $q \colon p^{-1}(U) \to \mathbb{A}$. By the hypothesis of agreement again, $q$ is constant on the fibres of $p^{-1}(U) \to U$: its two pull-backs to the fibre product $p^{-1}(U) \times_U p^{-1}(U)$ are equal. A flat, surjective, quasi-compact morphism is an effective epimorphism of schemes, so $q$ descends to a morphism $d \colon U \to \mathbb{A}$. The section $s = d^* T$ over $U$ has the stated values. $\square$

The textbook form is fpqc descent for the structure sheaf: for a faithfully flat ring map $A \to B$, the sequence $0 \to A \to B \rightrightarrows B \otimes_A B$ is exact. Grothendieck proves the descent of quasi-coherent modules and of morphisms along faithfully flat quasi-compact maps in SGA 1, Exposé VIII, Section 1. The proof of the source uses the effective epimorphisms of Mathlib, so it does not repeat the algebra.

**Theorem.** If $f$ is regular on $U$, there is a section $s \in \Gamma(X, U)$ with $\operatorname{ofSection}(s)(A, t) = f(A, t)$ at every point $t$ that lands in $U$.

Lean: `New.PointFn.IsRegularOn.exists_ofSection` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Apply the descent theorem to the identity of $X$ and to the cover of $X$ by the single open $X$. $\square$

The section is unique. Two sections with the same values at all points of $U$ have the same germs, by `New.PointFn.ofSection_fromSpecStalk`, so they are equal. In this sense the regular functions on $U$, taken up to their junk values off $U$, are the ring $\Gamma(X, U)$.

**Theorem.** Let $p \colon Y \to X$ and let $f$ be regular on $U$. Then the function $t \mapsto f(A, t \circ p)$ on points of $Y$ is regular on $p^{-1}(U)$. If $p$ is quasi-compact and scheme-theoretically dominant, two functions regular on $U$ agree at all points of $U$ if their pull-backs agree at the points of $p^{-1}(U) \cap V_a$ for an open cover $(V_a)$ of $Y$.

Lean: `New.PointFn.IsRegularOn.pull`, `New.PointFn.IsRegularOn.ext_of_dominant_of_isOpenCover` (Lib/General/Geometry/LineBundles.lean).

*Proof.* The first claim is direct. For the second, write the two functions as the functions of sections $s$ and $s'$. Their pull-backs to $p^{-1}(U)$ have the same germs at every point, since germs are values at the points $\operatorname{Spec} \mathcal{O}_{Y,y} \to Y$. So $p^* s = p^* s'$. Pull-back of sections along a quasi-compact scheme-theoretically dominant morphism is injective, so $s = s'$. $\square$

**Example.** Let $X = \operatorname{Spec} R$ and $U = X$. A point is a ring map $\psi \colon R \to A$. The function of $r \in R$ is $\psi \mapsto \psi(r)$. Let $f$ be regular on $X$, and let $e \colon \operatorname{Spec} R \to X$ be the identity, the point given by $\mathrm{id}_R$. The point given by $\psi$ is $e \circ \operatorname{Spec}\psi$. So regularity with $\varphi = \psi$ at the point $e$ gives $f(A, \psi) = \psi(f(R, e))$. So $f$ is the function of $r = f(R, e)$. This is the Yoneda lemma, and it is the proof of the theorem for affine $X$ without descent.

**Remark (Formalization).** The point of view of the source has two effects. First, restriction maps disappear. A function regular on $U$ is also regular on every smaller open, by `New.PointFn.IsRegularOn.mono`, with no restriction map. Products of functions regular on $U$ and on $V$ are regular on $U \cap V$, by `New.PointFn.IsRegularOn.mul`. Second, every statement must carry the open on which a function is regular, and the values off that open are junk values. The function of a section is $0$ off its open, by definition. A general function on points can take any value there. The chapter writes $f(A, t)$ for the value of $f$ at $t$, as in the source, and it says on which open a function is regular each time.
