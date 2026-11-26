---
title: Proper base change
lean:
  - Lib/Cohomology/ProperBaseChange/PlaceSpace.lean
  - Lib/Cohomology/ProperBaseChange/Theorem.lean
  - Lib/General/Geometry/PointsOfProperSchemes.lean
  - Lib/Cohomology/Etale/ProperFunctors.lean
decls:
  - New.Variety.IsProperOver
  - New.Variety.isProperOver_pointsToBase
  - New.Variety.IsProperOver.proper_base_change
  - New.Variety.IsProperOver.injective_map_residue
  - New.Variety.IsProperOver.isTestCohomEquiv_field_extension
  - New.Variety.IsProperOver.isOpen_zero_set_and_eq_zero
  - New.Variety.IsDetectedAtPoints
  - New.Variety.IdealFamily.isDetectedAtPoints_of_proper
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Proper base change

This section states the analogue of proper base change in the theory of Section 3, and its three consequences. The coefficients are $\mathbb{Z}/\ell$ throughout.

### The classical theorem

The classical theorem reads as follows. Let $f : X \to S$ be a proper morphism of schemes and $F$ a torsion sheaf on the étale site of $X$. For every geometric point $\bar{s}$ of $S$ and every $q \geq 0$, the map $(R^q f_* F)_{\bar{s}} \to H^q(X_{\bar{s}}, F|_{X_{\bar{s}}})$ is an isomorphism (SGA 4, Exposé XII, Théorème 5.1). In particular, if $S = \operatorname{Spec} A$ with $A$ strictly henselian local and $X_0$ is the closed fibre, then restriction $H^q(X, F) \to H^q(X_0, F|_{X_0})$ is an isomorphism.

The source does not state this theorem. It states an analogue for its own cohomology, with a different notion of properness and a narrower base.

### Proper functors

**Definition (Proper functor).** Let $Z$ be a space over rings with a map $s : Z \to h_D$. Then $Z$ is *proper over $D$* if two conditions hold.

1. (Closed diagonal.) For every ring $C$ and points $x, y \in Z(C)$ there is an ideal $I$ of $C$ such that, for every ring map $f : C \to C'$, the images $Z(f)(x)$ and $Z(f)(y)$ agree exactly when $f$ kills $I$.
2. (Valuative cover.) There are one ring $T$ and one point $a \in Z(T)$ with the following property. For every algebraically closed field $K$, every valuation subring $O$ of $K$ and every point $z \in Z(K)$ whose structure map sends $D$ into $O$, there is a ring map $u : T \to O$ such that the image of $a$ under $T \to O \subseteq K$ is $z$.

Lean: `New.Variety.IsProperOver` (Lib/Cohomology/ProperBaseChange/PlaceSpace.lean).

The first condition is the closed diagonal of a separated scheme. The second condition is the existence half of the valuative criterion, in a uniform form: one point $a$ over one ring $T$ serves all valuation rings at once. This uniform form also contains quasi-compactness. For a scheme, $T$ can be taken to be a product of the coordinate rings of a finite affine cover.

**Proposition (Proper schemes are proper functors).** Let $s : X \to \operatorname{Spec} R$ be a proper morphism of schemes. Then the functor of points of $X$, with its map to $h_R$, is proper over $R$.

Lean: `New.Variety.isProperOver_pointsToBase` (Lib/General/Geometry/PointsOfProperSchemes.lean).

The represented functor $h_R$ is proper over $R$ through the identity (`New.Variety.isProperOver_id_reprBy`), and every power $(\mathbb{P}^1)^\iota$ of the projective line is proper over $\mathbb{Z}$ (`New.Variety.isProperOver_projLinePow`). The second fact holds for an infinite index set $\iota$ too. For such $\iota$ the power is not a scheme of finite type. The definition of proper functor allows it, and Section 5 uses it.

### The theorem of the source

**Theorem (Proper base change).** Let $\ell$ be a prime and $A$ an absolutely integrally closed local domain in which of any two elements one divides the other. Assume that $\ell$ is a unit in $A$. Let $Y$ be a space over rings with a map $s : Y \to h_A$ that is proper over $A$. Let $Y_0 \subseteq Y$ be the closed fibre, the subfunctor of points whose structure map kills the maximal ideal of $A$. Then the inclusion $Y_0 \to Y$ is a $\mathbb{Z}/\ell$-equivalence: restriction $H^n(Y, \mathbb{Z}/\ell) \to H^n(Y_0, \mathbb{Z}/\ell)$ is bijective for every $n$.

Lean: `New.Variety.IsProperOver.proper_base_change` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

The ring $A$ is a valuation ring whose fraction field is algebraically closed. Its residue field is algebraically closed too. So $A$ is a strictly henselian local ring, and the theorem has the shape of the last sentence of the classical statement.

*Proof sketch.* The source proves the theorem in three steps.

First, it covers $Y$ by a space of places. Let $P$ be a ring that is absolutely flat with algebraically closed residue fields, and $\xi \in Y(P)$ a point. A place of $P$ is a prime $\mathfrak{q}$ of $P$ with a valuation ring of $\kappa(\mathfrak{q})$ over $A$. The valuative cover lifts $\xi$ to the product of the valuation rings of all places. The *space of places* of this lift is a form of the Riemann-Zariski space. It is again proper over $A$ (`New.Variety.ResiduePlace.isProperOver_placeSpace`). Its points over local rings come from single places.

Second, it proves the theorem for each space of places (`New.Variety.ResiduePlace.isTestCohomEquiv_closedFibre`). The space of places splits along the idempotents of $P$, and its cohomology is continuous in the sense of Section 3. So the claim reduces to the places that kill one maximal ideal $\mathfrak{q}$ of $P$, that is, to the valuation rings of a single algebraically closed field $\kappa(\mathfrak{q})$. Over such a field the source runs Zorn's lemma on the subrings $B$ of $\kappa(\mathfrak{q})$ for which the claim holds. If $B$ contains $x$ or $x^{-1}$ for every $x$, the space is acyclic over $B$ by a direct computation. Otherwise $B$ splits into two larger subrings by a Mayer-Vietoris sequence, and Kummer theory for $\mathbb{Z}/\ell$ controls the overlap. This is where the hypothesis that $\ell$ is a unit enters.

Third, it descends from a space of places to $Y$. The valuative cover gives one ring $P$, one point $\xi$ and one lift whose space of places has dense image in $Y$ for $\mathbb{Z}/\ell$. The fibre powers of this cover over $Y$ are again proper over $A$. The proof is an induction on the degree $r$, for all proper $Y$ at once. The Čech descent of Section 2 (`New.Variety.Comparison.bijectiveUpTo_of_cech_pred`) needs the claim for the cover in all degrees, which is the second step, and the claim for the fibre powers in lower degrees, which is the induction hypothesis. $\square$

The head of the file cites SGA 4, Exposé XII, 5.1, 5.4 and 5.5, the Stacks project, Tag 095S, and, for the reduction to spaces of places, Scholze, *Étale cohomology of diamonds* (2017), Theorem 19.2 and Lemma 19.4, after Huber, Math. Ann. 295 (1993).

**Remark (Formalization).** The source form differs from the classical form in four ways. (1) The base is a valuation ring of an algebraically closed field, not a general strictly henselian local ring. (2) The coefficient is the constant $\mathbb{Z}/\ell$ with $\ell$ invertible on the base. The classical theorem holds for every torsion sheaf and needs no condition on $\ell$. (3) The space $Y$ is any functor that is proper in the sense above. It need not be a scheme. (4) The cohomology is the Ext group of Section 3, not étale cohomology. The argument needs no more. The only uses of the theorem in the source are the three consequences below, and they are used for spaces built from schemes over such valuation rings, with $\ell$ invertible. Condition (3) is a gain: it allows the spaces of places and the infinite powers of $\mathbb{P}^1$, which are not schemes of finite type.

**Example (A represented space).** Let $A$ be as in the theorem and $Y = h_A$ with the identity map. The closed fibre $Y_0$ is the subfunctor of maps $A \to B$ that kill $\mathfrak{m}$, which is $h_\kappa$ for the residue field $\kappa$. The Example of Section 2 gives $H^0(h_A, \mathbb{Z}/\ell) = C(\operatorname{Spec} A, \mathbb{Z}/\ell)$ and $H^0(h_\kappa, \mathbb{Z}/\ell) = \mathbb{Z}/\ell$, with no higher groups. Since $A$ is local, $\operatorname{Spec} A$ is connected and the first group is also $\mathbb{Z}/\ell$. So the theorem holds in this case by a direct computation. The content of the theorem is that the same is true for every proper $Y$.

### Consequences

**Corollary (Restriction to the residue fibre is injective).** Let $W$ be proper over a ring $R$ in which $\ell$ is a unit. Let $A$ be as in the theorem, with a ring map $a : R \to A$, and let $\kappa$ be the residue field of $A$. Then pull-back along $W_\kappa \to W_A$ is injective on $H^n(-, \mathbb{Z}/\ell)$ for every $n$.

Lean: `New.Variety.IsProperOver.injective_map_residue` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

*Proof.* The base change $W_A$ is proper over $A$. The inclusion of its closed fibre $X_0$ factors through $W_\kappa \to W_A$. Restriction to $X_0$ is bijective by the theorem, so the first map in the factorisation is injective. $\square$

**Corollary (Invariance under extension of algebraically closed fields).** Let $W$ be proper over $R$, with $\ell$ a unit in $R$. Let $S \to T$ be a map of algebraically closed fields over $R$. Then the map $W_T \to W_S$ is a $\mathbb{Z}/\ell$-equivalence.

Lean: `New.Variety.IsProperOver.isTestCohomEquiv_field_extension` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

The proof writes $T$ as the filtered union of its finitely generated $S$-subalgebras $A_t$. By continuity, classes on $W_T$ and their vanishing come from the $W_{A_t}$. By the Nullstellensatz each $A_t$ has an $S$-point, which gives a section $W_S \to W_{A_t}$.

**Corollary (Open zero sets).** Let $W$ be proper over $R$, with $\ell$ a unit in $R$. Let $T$ be a test ring with a map $R \to T$, and let $x \in H^n(W_T, \mathbb{Z}/\ell)$. Let $z$ be the set of primes $\mathfrak{p}$ of $T$ such that $x$ restricts to zero on $W_{\kappa(\mathfrak{p})}$. Then $z$ is open in $\operatorname{Spec} T$, and if $z = \operatorname{Spec} T$ then $x = 0$.

Lean: `New.Variety.IsProperOver.isOpen_zero_set_and_eq_zero` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

These two properties together form the notion of detection at points. A coefficient $F$ on a category of tests over $A$ is *detected at points* if zero sets of classes are open, a class that vanishes at every prime is zero, and every map of fields among the tests is an equivalence for $F$.

**Definition (Detection at points).** For a functor $g$ from a category $\mathcal{D}$ to tests over $A$, a coefficient $F$ on $\mathcal{D}$ is *detected at points* if the two properties above hold for the groups $\operatorname{Ext}^n(\mathbb{Z}[\operatorname{Hom}(c, g(-))], F)$, for every test $c$ over $A$.

Lean: `New.Variety.IsDetectedAtPoints` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

**Theorem (Detection for proper spaces).** Let $A$ be an absolutely integrally closed local domain in which $\ell$ is a unit. Let $X$ be proper over $\mathbb{Z}$ and let $I$ be a family of ideals on the points of $X \times \operatorname{Spec} A$. Let $F$ be a coefficient on the pairs $(B, x)$, with $B$ a test over $A$ and $x \in X(B)$, and let $\beta$ be a map to $F$ from the coefficient $\mathbb{Z}/\ell$ that is bijective where $I = 0$. If the locus $I = 0$ is dense for $F$, then $F$ is detected at points.

Lean: `New.Variety.IdealFamily.isDetectedAtPoints_of_proper` (Lib/Cohomology/ProperBaseChange/Theorem.lean).

The idea is that the locus $W = \{I = 0\}$ is proper over $A$, and over a test $c$ the cohomology with coefficients $F$ is that of $W_c$ with coefficients $\mathbb{Z}/\ell$. The two corollaries above then give the two properties. Section 5 uses this theorem, with $X$ a power of $\mathbb{P}^1$, to prove that the Leray-Hirsch maps are bijective.
