---
title: The projective line and smooth base change
lean:
  - Lib/Cohomology/ProjectiveLine/ChernClass.lean
  - Lib/Cohomology/LerayHirsch.lean
  - Lib/Cohomology/ProjectiveLine/ConstantLineFormula.lean
  - Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean
  - Lib/General/Geometry/EtaleCharts.lean
  - Lib/Cohomology/SmoothBaseChange.lean
decls:
  - New.Variety.projLine
  - New.Variety.shortExact_kummerSeq
  - New.Variety.tateGen
  - New.Variety.isCohomEquiv_tensorPoint_tateGen
  - New.Variety.etaClass
  - New.Variety.lerayHirsch
  - New.Variety.isLerayHirschBasis_of_reprBy
  - New.Variety.TorsionCoeff.HasLineFormula
  - New.Variety.hasLineFormula_locallyConstant
  - New.Variety.IsCharting
  - New.Variety.IsCharted
  - New.Variety.isBijective_algToBaseChange
  - New.Variety.isTestCohomEquiv_baseChangeTransition
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The projective line and smooth base change

This section computes the cohomology of $\mathbb{P}^1$ over a base, in the form of a projective line formula. It then states the analogue of smooth base change. The coefficients are again killed by a prime $\ell$, and $\ell$ is invertible on the base.

### The projective line as a functor

The source does not take $\mathbb{P}^1$ from a library of schemes. It defines the functor directly.

**Definition (Projective line).** For a commutative ring $B$, let $\mathbb{P}^1(B)$ be the set of pairs $(u, v) \in B \times B$ modulo the relation $(1 + uv)v' = v(1 + u'v')$. The pair $(u, v)$ stands for the point with row $(1 + uv : v)$. Two pairs are related when the determinant of their rows is zero.

Lean: `New.Variety.projLine` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

The row $(1 + uv, v)$ is unimodular, since $(1 + uv) - u \cdot v = 1$. The presentation is chosen so that every point has a row whose first entry is $1$ modulo the second.

**Example (Local rings).** Let $B$ be a local ring and $(a : b)$ a point of the classical $\mathbb{P}^1(B)$ with $(a, b)$ unimodular. If $a$ is a unit, the row $(1, b/a)$ has the form $(1 + uv, v)$ with $u = 0$ and $v = b/a$. If $a$ is not a unit, then $b$ is a unit. For any unit $\lambda$ the element $\lambda a - 1$ lies in the unit ideal $(\lambda b)$, so $\lambda a = 1 + u \lambda b$ for some $u$. In both cases the point has a row of the required form. So on local rings the functor of the definition gives all points of the classical projective line. Test rings are not local in general, but their local rings are valuation rings (Section 3), and the coefficients of this section are local in the Zariski sense.

### The Kummer sequence and the class $\eta$

Let $g$ be a functor from a category $\mathcal{C}$ to tests over a ring $A$. Write $\mathbb{G}_m$ for the functor of units along $g$. The source uses the following form of the Kummer sequence.

**Lemma (Kummer sequence).** Let $\mathbb{T}$ be the kernel of evaluation at $1$, $\operatorname{Hom}(\mathbb{Q}, \mathbb{G}_m) \to \mathbb{G}_m$. Then $0 \to \mathbb{T} \to \operatorname{Hom}(\mathbb{Q}, \mathbb{G}_m) \to \mathbb{G}_m \to 0$ is a short exact sequence of functors along $g$.

Lean: `New.Variety.shortExact_kummerSeq` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

*Proof.* Only surjectivity needs an argument. A test ring is absolutely integrally closed. So every unit $y$ has a compatible system of roots: a homomorphism $\chi$ from $\mathbb{Q}$ to the units with $\chi(1) = y$. $\square$

The group $\mathbb{T}(c)$ is a Tate module for all primes at once.

The class $\mathcal{O}(1)$ enters as a 1-cocycle. Each point of $\mathbb{P}^1$ has a chosen row. A ring map $f$ carries the chosen row of $q$ to a unit multiple of the chosen row of $f(q)$. This unit is a 1-cocycle from $\mathbb{Z}[\mathbb{P}^1]$ to $\mathbb{G}_m$, and it defines an extension of $\mathbb{Z}[\mathbb{P}^1]$ by $\mathbb{G}_m$.

**Definition (The class $\eta$).** The class $\eta \in \operatorname{Ext}^2(\mathbb{Z}[\mathbb{P}^1], \mathbb{T})$ is the Yoneda product of the extension class of the cocycle of $\mathcal{O}(1)$, in $\operatorname{Ext}^1(\mathbb{Z}[\mathbb{P}^1], \mathbb{G}_m)$, with the class of the Kummer sequence, in $\operatorname{Ext}^1(\mathbb{G}_m, \mathbb{T})$.

Lean: `New.Variety.etaClass` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

This is the first Chern class of $\mathcal{O}(1)$, built from its two classical ingredients. The class lives in the coefficient $\mathbb{T}$. To multiply a class with values in $\mathbb{Z}/\ell$ by $\eta$, the source needs a generator of $\mathbb{T}$ modulo $\ell$.

**Definition (Generator of the Tate module).** Let $A$ be local and absolutely integrally closed, with $\ell$ invertible in $A$. The section $\varepsilon$ of $\mathbb{T}$ is the image under $A \to g(c)$ of a fixed homomorphism $\chi : \mathbb{Q} \to A^\times$ with $\chi(1) = 1$ and $\chi(1/\ell)$ a root of the $\ell$-th cyclotomic polynomial.

Lean: `New.Variety.tateGen` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

**Lemma (Twisting by $\varepsilon$).** Let $A$ be as above. Let $S$ be a functor along $g$ whose values are killed by $\ell$, and let $F$ have Zariski descent along $g$. Then $x \mapsto x \otimes \varepsilon$, from $S$ to $S \otimes \mathbb{T}$, is an equivalence for $F$: it induces bijections on $\operatorname{Ext}^n(-, F)$ for all $n$.

Lean: `New.Variety.isCohomEquiv_tensorPoint_tateGen` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

With this lemma the source turns $\eta$ into a class of degree $2$ from $M$ to $M$ on the points of $\mathbb{P}^1$, for every coefficient $M$ killed by $\ell$ with Zariski descent. This is the product with $\eta$. It plays the role of the cup product with $c_1(\mathcal{O}(1)) \in H^2(\mathbb{P}^1, \mathbb{Z}/\ell(1))$, after the choice of a root of unity identifies $\mathbb{Z}/\ell(1)$ with $\mathbb{Z}/\ell$.

**Remark (Formalization).** The homomorphism $\chi$ of the generator is chosen by `Nonempty.some`, from a proof that such a $\chi$ exists ([ChernClass.lean](lean:Lib/Cohomology/ProjectiveLine/ChernClass.lean#L116)). So $\varepsilon$ is a fixed choice, with no canonical meaning. The product with $\eta$ depends on this choice, and this book does not study how. The hypothesis that $A$ is local and absolutely integrally closed is what makes $\chi$ exist. A root of the cyclotomic polynomial exists because $A$ is absolutely integrally closed, and it is primitive in each local ring because $\ell$ is a unit.

### Leray-Hirsch for Ext of functors

The classical Leray-Hirsch theorem says the following. Let $E \to B$ be a fibre bundle with fibre $F$ and $R$ a ring. Assume that $H^n(F; R)$ is a free $R$-module of finite rank for each $n$, and let $c_1, \dots, c_r$ be classes on $E$ that restrict to a basis of the cohomology of each fibre. Then the map $\bigoplus_i H^*(B) \to H^*(E)$, $(w_i) \mapsto \sum_i \pi^*(w_i) \cdot c_i$, is an isomorphism (Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4D.1). The source proves an abstract form of this theorem for Ext groups of functors.

**Definition (Leray-Hirsch map).** Let $\Phi$ be an exact functor between categories of functors to abelian groups, and let $\theta_i \in \operatorname{Ext}^{d_i}(\Phi G, F)$ for $i$ in a set $I$. For a functor $S$, the Leray-Hirsch map sends a finitely supported family $(w_i)$ of classes in the total group $\bigoplus_n \operatorname{Ext}^n(S, G)$ to $\sum_i \theta_i \circ \Phi(w_i)$, in the total group of $\operatorname{Ext}(\Phi S, F)$. The family $\theta$ is a Leray-Hirsch basis at $S$ if this map is bijective.

Lean: `New.Variety.lerayHirsch` (Lib/Cohomology/LerayHirsch.lean).

**Theorem (Leray-Hirsch from representable functors).** Let $\varphi : \mathcal{C} \to \mathcal{A}$ be a functor, $I$ a finite set, and $\theta_i \in \operatorname{Ext}^{d_i}(G \circ \varphi, F)$. If $\theta$ is a Leray-Hirsch basis at $\mathbb{Z}[h_c]$ for every object $c$ of $\mathcal{A}$, then it is a Leray-Hirsch basis at every functor $S : \mathcal{A} \to \mathrm{Ab}$.

Lean: `New.Variety.isLerayHirschBasis_of_reprBy` (Lib/Cohomology/LerayHirsch.lean).

*Proof sketch.* The functors $S$ at which the map is bijective form a closed class: the condition passes along short exact sequences by the five lemma on long exact sequences. Every functor has a resolution by direct sums of functors $\mathbb{Z}[h_c]$. A direct sum of such functors is $\mathbb{Z}$ of a disjoint union, and cohomology turns a disjoint union into a product. Since $I$ is finite and each $\mathbb{Z}[h_c]$ has cohomology only in degree $0$ (Section 2), the families of classes on the disjoint union are the products of the families on the summands. So bijectivity on each summand gives bijectivity on the sum. An induction on the degree, with the five lemma, then reaches every $S$. $\square$

### The projective line formula

Let $M$ be a coefficient along $g$ killed by $\ell$, with Zariski descent. On the category of points of $\mathbb{P}^1$ over $g$ there are two classes from $M$ to $M$: the class $1$ in degree $0$ and the product with $\eta$ in degree $2$.

**Definition (Projective line formula).** The coefficient $M$ satisfies the projective line formula if the classes $1$ and $\eta$ are a Leray-Hirsch basis at every functor $S$. In words, $H(\mathbb{P}^1 \times S) = H(S) \oplus \eta\, H(S)$ for every $S$.

Lean: `New.Variety.TorsionCoeff.HasLineFormula` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

The classical formula is $H^n(\mathbb{P}^1_X, \mathbb{Z}/\ell) \cong H^n(X, \mathbb{Z}/\ell) \oplus H^{n-2}(X, \mathbb{Z}/\ell(-1))$ for a scheme $X$ on which $\ell$ is invertible. The head of the source file cites SGA 4½, SGA 5 and Milne, *Étale Cohomology*, for it, with no numbers.

**Theorem (Projective line formula for $\mathbb{Z}/\ell$).** Let $A$ be a valuation ring that is local and absolutely integrally closed, with $\ell$ a unit in $A$, and let $A \to \mathbb{C}_\ell$ be an injective ring map. Then the coefficient of locally constant functions $\operatorname{Spec} B \to \mathbb{Z}/\ell$, on tests $B$ over $A$, satisfies the projective line formula.

Lean: `New.Variety.hasLineFormula_locallyConstant` (Lib/Cohomology/ProjectiveLine/ConstantLineFormula.lean).

*Proof sketch.* The source reduces the formula to tests over algebraically closed fields $k$ over $A$. There the cohomology of $\mathbb{P}^1_k$ has a basis over the point that contains $\eta$, unless $\eta \cdot 1 = 0$. If $\eta \cdot 1$ were zero over one such field, the vanishing would spread to the generic point of $A$. To exclude this, the source uses a second theory, the tilted theory, on tests over $\mathbb{C}_\ell$ with coefficients $R \mapsto R^\flat \otimes N$ for a module $N$ over the tilt $\mathcal{O}^\flat$. For this theory the projective line formula holds by a separate argument: the perfect $\mathbb{P}^1$ is covered by two discs ([TiltedLineFormula.lean](lean:Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean#L1041)). If $\eta$ acted as zero on the point, the formula for the tilted theory would make the cohomology of the point zero. For a suitable $N$ this cohomology is $\mathfrak{m}^\flat / \pi \mathfrak{m}^\flat$, with $\pi \neq 0$ in the maximal ideal $\mathfrak{m}^\flat$, which is not zero. $\square$

The $\ell$-adic perfectoid computation is the reason for the hypothesis $A \to \mathbb{C}_\ell$.

**Remark (Formalization).** The register of findings has a row on the tilted file (F-109 in [Citations and docstrings](/chapter/register-of-findings/)). The index of the source and the paragraph on literature in the file call its main result a Künneth formula over a field, after SGA 4 XVII 5.4.3. The head of the file and its lemmas give a projective line formula for the tilted theory and a result on Leray-Hirsch bases over the closed fibre of a local domain. This chapter follows the head and the lemmas. In the theorem above, the map $A \to \mathbb{C}_\ell$ is a hypothesis given by instances: `[Algebra A ℂ_[ℓ]]` and `[FaithfulSMul A ℂ_[ℓ]]`. The statement does not depend on the choice of the map, since the conclusion does not mention it.

### Smooth base change

The classical theorem says that for a smooth morphism $g : S' \to S$, a quasi-compact and quasi-separated morphism $f : X \to S$ and a torsion sheaf $F$ of order invertible on $S$, the base change map $g^* R^q f_* F \to R^q f'_* (g'^* F)$ is an isomorphism. The head of the source file cites SGA 4, Exposé XV, 2.1, and Exposé XVI, 1.2, and Stacks Project Tag 0EYQ, for its form. The book has not checked these numbers against the originals. The source states a different form, with a valuation ring $A$ of $\bar{\mathbb{Q}}$ as base and the inclusion of the generic point as base change. It compares $Y_A$ with $Y_{\bar{\mathbb{Q}}}$. The base change $\operatorname{Spec} \bar{\mathbb{Q}} \to \operatorname{Spec} A$ is not smooth, and $Y$ is not assumed proper. So the book does not claim that this form follows from the classical theorem. The head of the file calls it smooth base change.

The source replaces smoothness by a covering condition.

**Definition (Charting).** Let $X$ be a functor on $k$-algebras and $V$ a subfunctor. Then $V$ is a charting of $X$ if two conditions hold. (a) $V$ is Zariski locally all of $X$: for each $y \in X(B)$ and each maximal ideal $\mathfrak{m}$ of $B$ there is $a \notin \mathfrak{m}$ such that $y$ lies in $V$ after every map $B \to B'$ that makes $a$ a unit. (b) $\mathbb{Z}[V]$ lies in every closed class of functors that contains $\mathbb{Z}[h_R]$ for the coordinate ring $R$ of each chart of $X$ whose coordinates are all units.

Lean: `New.Variety.IsCharting` (Lib/General/Geometry/EtaleCharts.lean).

A chart of dimension $d$ is an étale map to affine space $\mathbb{A}^d$. A chart whose coordinates are units is étale over the torus $\mathbb{G}_m^d$. Condition (b) says that $V$ is built from such charts by extensions, in the sense of a closed class.

**Definition (Charted scheme).** A scheme $Y$ over $R$ is charted over an $R$-algebra $k$ if the functor of points of $Y$ on $k$-algebras has a subfunctor that is a charting.

Lean: `New.Variety.IsCharted` (Lib/General/Geometry/EtaleCharts.lean).

The reduction from schemes to tests over the base uses one more lemma. For $Y$ over $R$ and an $R$-algebra $A$, the cohomology of $Y_A$ on all test rings agrees with the cohomology of $Y$ on tests over $A$. The reason is that a point of $Y_A$ with values in a test ring $c$ includes a map $A \to c$, which makes $c$ a test over $A$ ([SmoothBaseChange.lean](lean:Lib/Cohomology/SmoothBaseChange.lean#L73)).

Lean: `New.Variety.isBijective_algToBaseChange` (Lib/Cohomology/SmoothBaseChange.lean).

**Theorem (Smooth base change).** Let $\ell$ be a prime and $A$ a valuation ring of the algebraic closure $\Omega$ of $\mathbb{Q}$, with a prime $p$ in its maximal ideal and with $\ell$ a unit in $A$. Let $R \to A$ be a ring map and $Y$ a scheme over $R$ that is charted over $R$. Then pull-back along $Y_\Omega \to Y_A$ gives bijections $H^n(Y_A, \mathbb{Z}/\ell) \to H^n(Y_\Omega, \mathbb{Z}/\ell)$ for all $n$.

Lean: `New.Variety.isTestCohomEquiv_baseChangeTransition` (Lib/Cohomology/SmoothBaseChange.lean).

*Proof sketch.* Compare the cohomology on tests over $A$ with the cohomology on tests over $\Omega$. Let $c$ be a test over $A$ in which the maximal ideal of $A$ generates the unit ideal. Then every nonzero element of $A$ is a unit in $c$, since $A$ has rank one, and $A \to c$ extends to $\Omega$ in exactly one way. So the tests over $\Omega$ are the tests over $A$ off the closed fibre. For a space $X$ over $A$, the comparison is then bijective on $\mathbb{Z}[X]$ if and only if $\mathbb{Z}[X] / \mathbb{Z}[X_{\mathrm{off}}]$ has no cohomology, where $X_{\mathrm{off}}$ is the part of $X$ off the closed fibre. The spaces with this property form a closed class. It contains the point, since $A$ and $\Omega$ are domains and both sides are the constant $\mathbb{Z}/\ell$. It contains each standard étale chart over affine space, by two excisions and a duality on products of $\mathbb{P}^1$ that uses the projective line formula. A Mayer-Vietoris argument over finite covers by such charts, and the charting condition, then give all of $Y$. $\square$

**Remark (Formalization).** (1) The base $A$ is a term of type `ClosurePlace`, which is any valuation subring of $\Omega$. The hypothesis `hp : A.valuation p < 1` puts $p$ in the maximal ideal. It is used to show that $A$ has rank one. (2) The prime $\ell$ enters through the instance `[ThePrime ℓ]` and the hypothesis `hℓ : IsUnit (ℓ : A)`. (3) There is no hypothesis of smoothness and no hypothesis of properness. The instance `[IsCharted Y R]` stands in for smoothness. The theorem is about the chart condition, not about smooth morphisms. A smooth scheme has étale charts locally, but the source does not prove in this file that every smooth scheme is charted. (4) Inside the proof the source builds an `Algebra Ω ℂ_[ℓ]` instance from `Classical.ofNonempty`, an arbitrary embedding of $\Omega$ into an algebraic closure of $\mathbb{Q}_\ell$ ([SmoothBaseChange.lean](lean:Lib/Cohomology/SmoothBaseChange.lean#L266)). The statement does not mention this choice.
