---
title: Spaces, coefficients and Ext
lean:
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Cohomology/Etale/DenseSubfunctors.lean
  - Lib/Cohomology/Etale/BijectiveComparisons.lean
  - Lib/Cohomology/Etale/RelativeChains.lean
decls:
  - New.Variety.AbFunctor
  - New.Variety.freeAb
  - New.Variety.H
  - New.Variety.H.map
  - New.Variety.H.push
  - New.Variety.reprBy
  - New.Variety.pointMap
  - New.Variety.homReprEquiv
  - New.Variety.IsCohomEquiv
  - New.Variety.IsCohomDense
  - New.Variety.IsCohomDense.isCohomEquiv
  - New.Variety.mayer_vietoris_shortExact
  - New.Variety.IsCover
  - New.Variety.relFreeAb
  - New.Variety.relFreeAb.excision
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Spaces, coefficients and Ext

This section gives the definitions on which the whole chapter rests. They make sense over any small category $\mathcal{C}$. Section 3 takes for $\mathcal{C}$ the category of test rings. Section 6 takes for $\mathcal{C}$ a category of pairs of a ring and a module.

### Spaces and coefficients

A *space* over $\mathcal{C}$ is a functor $Y : \mathcal{C} \to \mathbf{Set}$. A *coefficient* is a functor $F : \mathcal{C} \to \mathbf{Ab}$. The source puts the values in the universe `Type 1`, so that the category of coefficients has enough room for its Ext groups. This choice of universe does not change any statement of this chapter.

**Definition (Coefficient functors).** For a category $\mathcal{C}$, the category $\operatorname{Fun}(\mathcal{C}, \mathbf{Ab})$ has the functors from $\mathcal{C}$ to abelian groups as objects and the natural transformations as maps. It is an abelian category, and kernels, cokernels and exactness are computed at each object.

Lean: `New.Variety.AbFunctor` (Lib/Cohomology/Etale/Basic.lean).

**Definition (Free abelian group of a space).** For a space $Y$, the functor $\mathbb{Z}[Y]$ sends $A$ to the free abelian group $\mathbb{Z}[Y(A)]$ on the set $Y(A)$, and a map $f$ to the map induced by $Y(f)$. A map $u : Y' \to Y$ of spaces gives a map $\mathbb{Z}[u] : \mathbb{Z}[Y'] \to \mathbb{Z}[Y]$.

Lean: `New.Variety.freeAb` (Lib/Cohomology/Etale/Basic.lean).

The functor $\mathbb{Z}[-]$ is left adjoint to the forgetful functor from coefficients to spaces. A map $\mathbb{Z}[Y] \to F$ is the same as a map of spaces $Y \to F$, where $F$ is read as a functor to sets.

### Cohomology

**Definition (Cohomology).** Let $N$ and $F$ be coefficient functors on $\mathcal{C}$ and let $n \geq 0$. The cohomology of $N$ with coefficients in $F$ in degree $n$ is
$$H^n(N, F) = \operatorname{Ext}^n_{\operatorname{Fun}(\mathcal{C}, \mathbf{Ab})}(N, F).$$
For a space $Y$, the cohomology of $Y$ is $H^n(Y, F) = H^n(\mathbb{Z}[Y], F)$.

Lean: `New.Variety.H` (Lib/Cohomology/Etale/Basic.lean).

The Ext group is the Ext of Mathlib for an abelian category. It is defined by maps in the derived category, and it agrees with the Yoneda Ext of classes of extensions (Weibel, Section 3.4). The category of coefficients is a Grothendieck abelian category, so the Ext groups exist. The source records this as an instance in [Basic.lean](lean:Lib/Cohomology/Etale/Basic.lean#L705).

**Definition (Pull-back and push-forward).** A map $\alpha : N' \to N$ of coefficient functors gives the pull-back $H^n(N, F) \to H^n(N', F)$, by composition with $\alpha$. A map $\beta : F \to F'$ gives the push-forward $H^n(N, F) \to H^n(N, F')$, by composition with $\beta$. Both maps are additive. For a map of spaces $u : Y' \to Y$, the pull-back along $\mathbb{Z}[u]$ is written $u^*$.

Lean: `New.Variety.H.map` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.H.push` (Lib/Cohomology/Etale/Basic.lean).

**Definition (Equivalence for a coefficient).** Let $F$ be a coefficient. A map $\alpha : N' \to N$ is an *equivalence for $F$* if the pull-back $H^n(N, F) \to H^n(N', F)$ is bijective for every $n \geq 0$.

Lean: `New.Variety.IsCohomEquiv` (Lib/Cohomology/Etale/Basic.lean).

Most theorems of this chapter have this form. They say that a map of spaces induces an equivalence for a given coefficient. The source does not speak of a derived category of sheaves or of the cohomology of a complex. It works with one Ext group at a time, and with long exact sequences of Ext groups.

### Points and the Yoneda lemma

**Definition (Represented space, point map).** For an object $A$ of $\mathcal{C}$, the space $h_A = \operatorname{Hom}(A, -)$ is the space *represented* by $A$. For a space $Y$ and a point $y \in Y(A)$, the *point map* $h_A \to Y$ sends $f : A \to B$ to $Y(f)(y)$.

Lean: `New.Variety.reprBy` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.pointMap` (Lib/Cohomology/Etale/Basic.lean).

By the Yoneda lemma, every map $h_A \to Y$ is the point map of exactly one point $y \in Y(A)$. With the adjunction of $\mathbb{Z}[-]$, this gives the additive Yoneda lemma.

**Lemma (Additive Yoneda lemma).** Let $A$ be an object of $\mathcal{C}$ and $F$ a coefficient. Then $\varphi \mapsto \varphi_A(\mathrm{id}_A)$ is an isomorphism of groups $\operatorname{Hom}(\mathbb{Z}[h_A], F) \cong F(A)$.

Lean: `New.Variety.homReprEquiv` (Lib/Cohomology/Etale/Basic.lean).

*Proof.* A map $\mathbb{Z}[h_A] \to F$ is a map of spaces $h_A \to F$ by the adjunction. Such a map is an element of $F(A)$ by the Yoneda lemma. The bijection respects sums, since sums of maps are computed at each object. $\square$

The source deduces that $\mathbb{Z}[h_A]$ is a projective object ([Basic.lean](lean:Lib/Cohomology/Etale/Basic.lean#L1120)). Let $e : E \to X$ be an epimorphism of coefficients and $\varphi : \mathbb{Z}[h_A] \to X$ a map. The map $e_A : E(A) \to X(A)$ is surjective, so the element $\varphi_A(\mathrm{id}_A)$ of $X(A)$ has a preimage $x$. The map $\mathbb{Z}[h_A] \to E$ that corresponds to $x$ lifts $\varphi$.

**Example (Cohomology of a represented space).** Let $A$ be an object of $\mathcal{C}$ and $F$ a coefficient. Then $H^0(h_A, F) \cong F(A)$ and $H^n(h_A, F) = 0$ for $n \geq 1$. The first claim is the additive Yoneda lemma, since $H^0$ is the group of maps. The second claim holds because $\operatorname{Ext}^n(P, -) = 0$ for $n \geq 1$ when $P$ is projective. The source does not state this as one theorem. It uses the two facts separately.

So a represented space is acyclic for every coefficient. In the language of sites, the represented spaces play the role of the affine objects, and every coefficient behaves as if it had no higher cohomology on them. This is the reason for the choice of test rings in Section 3. On a test ring, the coefficients $\mathbb{Z}/\ell$ ought to have no higher cohomology, and the definition forces this.

### Dense subfunctors

A *subfunctor* $U$ of a space $Y$ is a choice of subsets $U(A) \subseteq Y(A)$ that is stable under the maps $Y(f)$. For a map $p : E \to Y$ the preimage $p^{-1}U$ is a subfunctor of $E$.

**Definition (Dense subfunctor).** Let $F$ be a coefficient and $U$ a subfunctor of $Y$. Then $U$ is *dense for $F$* if for every object $A$ and every point $y \in Y(A)$, the inclusion of the preimage $y^{-1}U \subseteq h_A$ is an equivalence for $F$.

Lean: `New.Variety.IsCohomDense` (Lib/Cohomology/Etale/Basic.lean).

**Proposition (Dense subfunctors are equivalences).** If $U$ is dense in $Y$ for $F$, then the inclusion $U \to Y$ is an equivalence for $F$.

Lean: `New.Variety.IsCohomDense.isCohomEquiv` (Lib/Cohomology/Etale/DenseSubfunctors.lean).

The proof in the source tests the map on the fibres over the points of $Y$. Over a point $y \in Y(A)$ the fibre of $U \to Y$ is $y^{-1}U \to h_A$, which is an equivalence by hypothesis. The source proves the passage from fibres to the whole map by a descent along the point maps. The file also proves that density is stable under preimages, under finite intersections and under composition: if $V$ is dense in $Y$ and $U \cap V$ is dense in $V$, then $U$ is dense in $Y$ (`New.Variety.IsCohomDense.trans`).

The notion of density is the notion of a covering in this theory. A classical cover $\{U_i \to Y\}$ by open sets becomes the statement that the union of the $U_i$ is dense. The source never fixes a topology. Each theorem says which subfunctors are dense for which coefficient.

**Lemma (Mayer-Vietoris).** Let $U$ and $V$ be subfunctors of $Y$. The sequence
$$0 \to \mathbb{Z}[U \cap V] \to \mathbb{Z}[U] \oplus \mathbb{Z}[V] \to \mathbb{Z}[U \cup V] \to 0,$$
with maps $x \mapsto (x, -x)$ and $(x, y) \mapsto x + y$, is short exact.

Lean: `New.Variety.mayer_vietoris_shortExact` (Lib/Cohomology/Etale/DenseSubfunctors.lean).

*Proof.* At each object $A$, the square of the sets $U(A) \cap V(A)$, $U(A)$, $V(A)$ and $U(A) \cup V(A)$ is a push-out of sets with injective maps. The free abelian group functor sends it to a push-out of groups whose first map is injective. Such a push-out gives a short exact sequence of the stated form. $\square$

With the long exact sequence of Ext, the lemma gives the Mayer-Vietoris sequence of cohomology. If $U \cup V$ is dense in $Y$, the cohomology of $U \cup V$ is that of $Y$.

### Covers and Čech descent

**Definition (Cover).** A map $p : E \to Y$ is a *cover for $F$* if the inclusion of the image of $p$ into $Y$ is an equivalence for $F$.

Lean: `New.Variety.IsCover` (Lib/Cohomology/Etale/BijectiveComparisons.lean).

A map that is surjective at every object is a cover for every coefficient, because its image is all of $Y$ (`New.Variety.IsPointwiseSurjective.isCover`). The file proves a form of Čech descent. Let $E^{(m)}$ be the $(m+1)$-fold fibre power of $E$ over $Y$. If a natural comparison of cohomology theories is bijective on each $\mathbb{Z}[E^{(m)}]$, then it is bijective on $\mathbb{Z}[\operatorname{im} p]$ (`New.Variety.Devissage.allBijective_freeAb_range_of_cech`). The proof is an induction on the degree, by the four lemma at each step. Section 4 uses this descent for the proof of proper base change.

### Relative cohomology and excision

**Definition (Relative chains).** For a subfunctor $U$ of $Y$, the coefficient $\mathbb{Z}[Y, U]$ is the cokernel of $\mathbb{Z}[U] \to \mathbb{Z}[Y]$. The relative cohomology is $H^n(\mathbb{Z}[Y, U], F)$.

Lean: `New.Variety.relFreeAb` (Lib/Cohomology/Etale/Basic.lean).

The sequence $0 \to \mathbb{Z}[U] \to \mathbb{Z}[Y] \to \mathbb{Z}[Y, U] \to 0$ is short exact (`New.Variety.relFreeAb.shortExact`). So relative cohomology fits in the usual long exact sequence of a pair. Section 6 uses relative cohomology for classes with support: a class on $\mathbb{Z}[Y, U]$ is a class on $Y$ that vanishes on $U$.

**Proposition (Excision).** Let $u : V' \to V$ be a monomorphism of spaces, let $U$ be a subfunctor of $V$ and let $U' = u^{-1} U$. Assume that $u(V') \cup U$ is dense in $V$ for $F$. Then the map $\mathbb{Z}[V', U'] \to \mathbb{Z}[V, U]$ is an equivalence for $F$.

Lean: `New.Variety.relFreeAb.excision` (Lib/Cohomology/Etale/RelativeChains.lean).

*Proof.* The cokernel of the map is $\mathbb{Z}[V, u(V') \cup U]$, by the exact sequence of a triple. By density the inclusion of $u(V') \cup U$ into $V$ is an equivalence, so this cokernel has zero cohomology in every degree. A map whose cokernel has zero cohomology, and whose kernel is zero, is an equivalence, by the long exact sequence. $\square$

**Remark (Formalization).** About twenty lines in `Lib/Cohomology` set the option `backward.isDefEq.respectTransparency false` without `in`, so that it acts to the end of a section or a file (register row F-021, [Settings and instances](/chapter/register-of-findings/)). The option changes how Lean unifies terms. It does not change what a statement says. A reader who checks a lemma of this chapter in a plain session may have to set the same option. The file `BijectiveComparisons.lean` also makes the lemma `subsingleton_of_projective` a global instance at line 671 (row F-023). The lemma says that the Ext groups out of a projective object vanish in positive degree, which is true. As a global instance it acts in every file that imports this one. It is not checked whether a statement of `New` picks it up.
