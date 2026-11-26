---
title: Test rings and l-adic cohomology
lean:
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Cohomology/Etale/DenseSubfunctors.lean
  - Lib/Cohomology/Etale/ProperFunctors.lean
  - Lib/Cohomology/Etale/FilteredLimits.lean
  - Lib/Cohomology/Etale/EllAdicCohomology.lean
decls:
  - New.Variety.IsTest
  - New.Variety.TestRing
  - New.Variety.isTest_of_preValuationRing
  - New.Variety.IsTest.pi
  - New.Variety.IsTest.localization
  - New.Variety.IsTest.quotient
  - New.Variety.IsTest.filtered_colimit
  - New.Variety.IsTest.exists_valuationSubring_atPrime
  - New.Variety.locConstCoeff
  - New.Variety.IsTestCohomEquiv
  - New.Variety.zeroPoints
  - New.Variety.hasPartitions_locConstCoeff
  - New.Variety.TestCohomology.mayer_vietoris_bijective
  - New.Variety.continuousUpTo_locConstCoeff
  - New.Variety.ellAdicCoeff
  - New.Variety.ellAdicCohom
  - New.Variety.ellAdicCohom.galoisAction
  - New.Variety.exists_ellAdicCoeff_modShortExact
  - New.Variety.finite_H_ellAdicCoeff
  - New.Variety.IsCohomEquiv.bijective_ellAdicPull
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Test rings and l-adic cohomology

This section fixes the category $\mathcal{C}$ of Section 2 for the étale part of the theory. It defines the test rings, the coefficients $\Lambda$ and $\mathbb{Z}_\ell$, and the $\ell$-adic cohomology of a scheme.

### Test rings

A ring $A$ is *absolutely integrally closed* if every monic polynomial of positive degree over $A$ has a root in $A$. A field is absolutely integrally closed exactly when it is algebraically closed.

**Definition (Test ring).** A commutative ring $A$ is a *test ring* if it has three properties.

1. $A$ is absolutely integrally closed.
2. $A$ is reduced.
3. For all $a, b \in A$ there is an idempotent $e \in A$ with $a \mid eb$ and $b \mid (1 - e)a$.

The category of test rings is the full subcategory of commutative rings on the test rings.

Lean: `New.Variety.IsTest` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.TestRing` (Lib/Cohomology/Etale/Basic.lean).

The third property says that $\operatorname{Spec} A$ splits into two open and closed parts. On the part where $e = 1$, the element $a$ divides $b$. On the part where $e = 0$, the element $b$ divides $a$. So a test ring is locally a ring in which any two elements are comparable for divisibility.

**Lemma (Valuation rings are test rings).** An absolutely integrally closed domain in which of any two elements one divides the other is a test ring.

Lean: `New.Variety.isTest_of_preValuationRing` (Lib/Cohomology/Etale/Basic.lean).

*Proof.* A domain is reduced. For $a, b$, take $e = 1$ if $a \mid b$ and $e = 0$ if $b \mid a$. $\square$

So every algebraically closed field is a test ring, and so is every valuation ring of an algebraically closed field. The class of test rings is stable under the usual operations.

**Lemma (Stability of test rings).** Products of test rings, localisations of a test ring, quotients of a test ring by a radical ideal, and filtered colimits of test rings in commutative rings are test rings.

Lean: `New.Variety.IsTest.pi` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.IsTest.localization` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.IsTest.quotient` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.IsTest.filtered_colimit` (Lib/Cohomology/Etale/FilteredLimits.lean).

**Proposition (Local rings of a test ring).** Let $A$ be a test ring and $\mathfrak{p}$ a prime ideal of $A$. Then $A_{\mathfrak{p}}$ is an absolutely integrally closed local domain in which of any two elements one divides the other. There are an algebraically closed field $K$ and a valuation subring $O$ of $K$ with an $A$-algebra structure for which $O$ is a localisation of $A$ at $\mathfrak{p}$.

Lean: `New.Variety.IsTest.exists_valuationSubring_atPrime` (Lib/Cohomology/Etale/Basic.lean).

*Proof.* The localisation is a test ring and it is local. In a local ring the only idempotents are $0$ and $1$, so of any two elements one divides the other. A reduced ring with this property is a domain: if $ab = 0$ and $a \mid b$, then $b = ac$ and $b^2 = abc = 0$, so $b = 0$. A domain in which divisibility is total is a valuation ring of its fraction field $K$. The field $K$ is algebraically closed, because a monic polynomial over $K$ can be scaled to a monic polynomial over $A_{\mathfrak{p}}$. $\square$

The residue field of an absolutely integrally closed local domain is algebraically closed. The source records this as an instance ([Basic.lean](lean:Lib/Cohomology/Etale/Basic.lean#L662)).

The test rings play the role of the points of the arc topology of Bhatt and Mathew, and of the strictly totally disconnected rings of Scholze. The head of the file on filtered limits cites Scholze, *Berkovich motives*, arXiv 2412.03382 (2024), Theorem 4.1 and Lemmas 4.7 and 4.8, and Bhatt and Mathew, *The arc-topology*, Duke Math. J. 170 (2021), Proposition 5.2 and Theorem 5.4, for descent and limits from functors on such rings. The book has not compared these places with the papers.

### The coefficients

**Definition (Locally constant coefficients).** For an abelian group $\Lambda$, the coefficient $\underline{\Lambda}$ on test rings sends $A$ to the group of locally constant functions $\operatorname{Spec} A \to \Lambda$.

Lean: `New.Variety.locConstCoeff` (Lib/Cohomology/Etale/Basic.lean).

A *space over rings* is a functor $X$ from commutative rings to sets. Its cohomology with coefficients in $\Lambda$ is $H^n(X, \Lambda) = H^n(\mathbb{Z}[X|_{\mathrm{test}}], \underline{\Lambda})$, where $X|_{\mathrm{test}}$ is the restriction of $X$ to test rings. A map $u : X \to Y$ is a *$\Lambda$-equivalence* if it induces bijections $H^n(Y, \Lambda) \to H^n(X, \Lambda)$ for all $n$.

Lean: `New.Variety.IsTestCohomEquiv` (Lib/Cohomology/Etale/Basic.lean).

For a scheme $X$ over $\operatorname{Spec} R$, the source takes the functor of points $B \mapsto X(\operatorname{Spec} B)$ with its map to $h_R$ (`New.Variety.pointsToBase`). For a subset $I \subseteq R$, the *zero points* are the points whose structure map $R \to B$ kills $I$. For an ideal $I$ they form the space of points of the closed subscheme $V(I)$.

Lean: `New.Variety.zeroPoints` (Lib/Cohomology/Etale/Basic.lean).

The *unit points* (`New.Variety.unitPoints`) are the points whose structure map sends $I$ to units. They form the space of points of an open subscheme when $I$ is finite.

### Why presheaves are enough

The definition of $H^n$ uses all functors on test rings, with no sheaf condition. The coefficients $\underline{\Lambda}$ satisfy descent for the cuts of a test ring along an idempotent.

**Lemma (Partitions).** A test ring can be cut along an idempotent $e$, by the quotient $A/(e)$, and the locally constant functions on the spectrum of a product $B_1 \times B_2$ of test rings are the pairs of such functions on the factors.

Lean: `New.Variety.hasPartitions_locConstCoeff` (Lib/Cohomology/Etale/DenseSubfunctors.lean).

From this the source deduces that the cohomology with coefficients $\underline{\Lambda}$ of a space whose points live only over the zero ring vanishes. It then proves Mayer-Vietoris in the following form.

**Proposition (Mayer-Vietoris on test rings).** Let $U, V \leq W$ be subfunctors of a space $Y$ over rings. Assume that $U \cup V$ is dense in $W$ for $\underline{\Lambda}$, and that every point of $U \cap V$ lies over the zero ring. Then restriction $H^n(W, \Lambda) \to H^n(U, \Lambda) \times H^n(V, \Lambda)$ is bijective for every $n$.

Lean: `New.Variety.TestCohomology.mayer_vietoris_bijective` (Lib/Cohomology/Etale/ProperFunctors.lean).

The representable $h_A$, for a test ring $A$, has $H^0(h_A, \Lambda) = \underline{\Lambda}(A)$ and no higher cohomology, by the Example of Section 2. The source also proves that this is continuous: for a filtered diagram of test rings $A_j$ with colimit $A$, the group $H^n(h_A, \Lambda)$ is the colimit of the groups $H^n(h_{A_j}, \Lambda)$.

Lean: `New.Variety.continuousUpTo_locConstCoeff` (Lib/Cohomology/Etale/FilteredLimits.lean).

**Remark (Formalization).** The classical form of the theory is the étale cohomology of a scheme with coefficients in a constant torsion sheaf (Milne, *Étale Cohomology*, Chapter III). The source does not define étale cohomology. It defines $H^n(X, \Lambda)$ as an Ext group of presheaves on test rings, as above. The head of [FilteredLimits.lean](lean:Lib/Cohomology/Etale/FilteredLimits.lean#L40) says that equality with étale cohomology "is neither proved nor used". This book does not claim that the two theories agree, and no statement of the source depends on it. The argument does not need more, because every later use of the theory goes through statements that the source proves for its own groups: the base change theorems of Sections 4 and 5, the Galois action and finiteness below, and the Woods Hole formula of Section 7. A Galois representation built in Volume 8 is a representation on these groups. Its properties are the ones that the source proves for it. They are not properties that the classical theory would give.

### The l-adic coefficient

Fix a prime $\ell$. The source fixes it with the class `ThePrime ℓ`, whose argument is an out-parameter. So there is one prime $\ell$ in scope in each statement, and Lean finds it by instance search.

**Definition (The coefficient $\mathbb{Z}_\ell$).** The coefficient $\mathbb{Z}_\ell$ on test rings sends $A$ to the ring $W(C(A))$ of $\ell$-typical Witt vectors of the ring $C(A)$ of locally constant functions $\operatorname{Spec} A \to \mathbb{F}_\ell$, as a module over $\mathbb{Z}_\ell = W(\mathbb{F}_\ell)$.

Lean: `New.Variety.ellAdicCoeff` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

The ring $C(A)$ is a perfect $\mathbb{F}_\ell$-algebra, so its Witt vectors are $\ell$-torsion free and $\ell$-adically complete, with $W(C(A))/\ell = C(A)$. When $\operatorname{Spec} A$ is connected, $C(A) = \mathbb{F}_\ell$ and the value is $\mathbb{Z}_\ell$. This explains the name.

**Proposition (Reduction modulo $\ell$).** (a) There is a map $q : \mathbb{Z}_\ell \to \underline{\mathbb{F}_\ell}$ of coefficients such that $0 \to \mathbb{Z}_\ell \xrightarrow{\ell} \mathbb{Z}_\ell \xrightarrow{q} \underline{\mathbb{F}_\ell} \to 0$ is exact. (b) For every coefficient $N$ and every $n$, the $\mathbb{Z}_\ell$-module $H^n(N, \mathbb{Z}_\ell)$ is derived $\ell$-complete.

Lean: `New.Variety.exists_ellAdicCoeff_modShortExact` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

The file proves the same with $\ell^k$ and the Witt vectors of length $k$ (`New.Variety.exists_ellAdicCoeff_modShortExact_pow`). Two consequences follow by successive approximation.

**Corollary (Finiteness).** If $H^n(N, \mathbb{F}_\ell)$ is finite, then $H^n(N, \mathbb{Z}_\ell)$ is a finitely generated $\mathbb{Z}_\ell$-module.

Lean: `New.Variety.finite_H_ellAdicCoeff` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

**Corollary (Equivalences lift).** If $\alpha : M \to N$ is an equivalence for $\underline{\mathbb{F}_\ell}$, then pull-back along $\alpha$ is bijective on $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} H^n(-, \mathbb{Z}_\ell)$ for every $n$.

Lean: `New.Variety.IsCohomEquiv.bijective_ellAdicPull` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

So the base change theorems of Sections 4 and 5, which are stated for $\mathbb{F}_\ell$, hold for the $\ell$-adic groups too.

### The l-adic cohomology of a scheme

Let $R$ be a commutative ring and $\Omega$ an $R$-algebra. For a scheme $X$ over $\operatorname{Spec} R$, let $X_\Omega$ be the space $B \mapsto X_\Omega(B)$ of points of the base change $X \times_R \Omega$ (`New.Variety.geomPoints`).

**Definition ($\ell$-adic cohomology).** The $\ell$-adic cohomology of $X$ over $\Omega$ in degree $n$ is
$$H^n_\ell(X) = \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} H^n(\mathbb{Z}[X_\Omega|_{\mathrm{test}}], \mathbb{Z}_\ell).$$
It is a contravariant functor from schemes over $R$ to $\mathbb{Q}_\ell$-vector spaces.

Lean: `New.Variety.ellAdicCohom` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

**Definition (Galois action).** Let a group $\Gamma$ act on $\Omega$ by $R$-algebra automorphisms. Then $g \in \Gamma$ acts on $X_\Omega$ through its action on $\Omega$, and so on $H^n_\ell(X)$. This gives a representation of $\Gamma$ on $H^n_\ell(X)$, and pull-back along a map $X \to Y$ over $R$ commutes with it (`New.Variety.ellAdicCohom.map_galoisAction`).

Lean: `New.Variety.ellAdicCohom.galoisAction` (Lib/Cohomology/Etale/EllAdicCohomology.lean).

Volume 8 uses these groups and this action for models of Shimura varieties, with $\Gamma$ a Galois group that acts on $\Omega$ ([Building the representations](/chapter/building-representations/)).

**Remark (Formalization).** The definition puts no condition on $\Omega$, on $X$ or on the action. For an arbitrary $\Omega$ the groups $H^n_\ell(X)$ have no known meaning, and the definition still returns a vector space. The source does not prove that $H^n_\ell(X)$ is finite dimensional in general, and it does not prove that the action is continuous. Each use in Volume 8 proves the properties it needs for the case at hand. The finiteness above turns a finiteness mod $\ell$ into a finiteness over $\mathbb{Z}_\ell$, and so it is the tool for such proofs.
