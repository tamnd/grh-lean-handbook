---
title: Almost descent and the adic step
lean:
  - Lib/PadicComparison/Descent/AlmostDescent.lean
  - Lib/PadicComparison/Completion.lean
  - Lib/General/Algebra/CohomologyBaseChange.lean
decls:
  - New.Variety.almostCoeff
  - New.Variety.MaxIdealFlat.exists_smul_eq
  - New.Variety.IsAcyclicAt
  - New.Variety.exists_faithfullyFlat_padicTest
  - New.Variety.isCover_of_points
  - New.Variety.IsAcyclicOnPerfect
  - New.Variety.isAcyclicAt_perfectTilt
  - New.Variety.isAcyclicOnPerfect_almostCoeff
  - New.Variety.IsDerivedComplete
  - New.Variety.Comparison.IsBijective.of_mod
  - New.Variety.HasFlatBaseChange.isBijective_of_isReductionMod
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Almost descent and the adic step

This section proves the descent result on which the primitive comparison rests. It says that the points of a perfect $\mathcal{O}^\flat$-algebra in tilts of $p$-adic tests have no higher cohomology, for coefficients that are killed by $p^\flat$ and multiplied by the maximal ideal of $\mathcal{O}^\flat$. Section 5 uses it at the point, where the comparison starts. The second half of the section gives the adic step. It passes from a comparison modulo $p$ to a comparison of $p$-adic coefficients, and Section 5 uses it to lift the primitive comparison to period rings.

### Almost purity

Let $X$ be a perfectoid space over $\mathbb{C}_p$, and let $\mathcal{O}^+$ be the integral structure sheaf. Scholze proves that for affinoid perfectoid $X = \mathrm{Spa}(R, R^+)$ the cohomology $H^i_v(X, \mathcal{O}^+)$ is almost zero for $i > 0$, and $H^0_v(X, \mathcal{O}^+) = R^+$ almost. Here "almost zero" means killed by the maximal ideal of $\mathcal{O}_C$. The source cites Scholze, *Étale cohomology of diamonds*, arXiv 1709.07343, Theorem 8.7 and Proposition 8.8, and for perfect rings Bhatt and Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math. 209 (2017), Theorem 4.1.

The source states this in a form without spaces or sheaves. The site is the category of $p$-adic tests, and the "space" of a perfect $\mathcal{O}^\flat$-algebra $b$ is the functor $S \mapsto \mathrm{Hom}(b, S^\flat)$. The coefficients are almost from the start: the maximal ideal is part of the coefficients.

### Almost coefficients

Let $\mathfrak{m}$ be the maximal ideal of $\mathcal{O}^\flat$. For an $\mathcal{O}^\flat$-module $M$, write $b \mapsto b \otimes_{\mathcal{O}^\flat} M$ for the functor from $\mathcal{O}^\flat$-algebras to $\mathcal{O}^\flat$-modules.

**Definition (Almost coefficients).** For an $\mathcal{O}^\flat$-module $N$, the almost coefficients are the functor $b \mapsto b \otimes N \otimes \mathfrak{m}$, all tensor products over $\mathcal{O}^\flat$.
Lean: `New.Variety.almostCoeff`, with `New.Variety.tensorCoeff` (Lib/PadicComparison/Descent/AlmostDescent.lean).

The classical almost isomorphism $f : A \to B$ becomes an isomorphism after $- \otimes \mathfrak{m}$, because $\mathfrak{m}$ is flat and $\mathfrak{m} \otimes \mathfrak{m} = \mathfrak{m}$. So the factor $\mathfrak{m}$ turns the almost statements into exact ones. The basic input is a strong form of $\mathfrak{m}^2 = \mathfrak{m}$.

**Lemma.** Let $m \in \mathfrak{m}$ and let $t \neq 0$ in $\mathcal{O}^\flat$. Then $m = s k$ with $k \in \mathfrak{m}$ and $s \in \mathcal{O}^\flat$, and $t$ divides some power of $s$.
Lean: `New.Variety.MaxIdealFlat.exists_smul_eq` (Lib/PadicComparison/Descent/AlmostDescent.lean).

*Proof.* The ring $\mathcal{O}^\flat$ is absolutely integrally closed, so $m = s^2$ for some $s$. Then $s$ is not a unit, so $s \in \mathfrak{m}$. Put $k = s$. In the valuation ring $\mathcal{O}^\flat$ of rank one, every $t \neq 0$ divides some power of every non-unit. $\square$

### Acyclicity

The cohomology of a functor $N$ with coefficients $F$ is the Ext group $H^n(N, F) = \mathrm{Ext}^n(N, F)$ of [Chapter 2](/chapter/cohomology-ext/), in the category of functors to abelian groups. For an object $B$, write $h_B = \mathrm{Hom}(B, -)$ and $\mathbb{Z}[h_B]$ for its free abelian group. By Yoneda, $H^0(\mathbb{Z}[h_B], F) = F(B)$, and $H^n(\mathbb{Z}[h_B], F) = 0$ for $n > 0$.

**Definition (Acyclic at an object).** Let $\varphi : \mathcal{C}' \to \mathcal{C}$ be a functor, $F$ coefficients on $\mathcal{C}$ and $B$ an object of $\mathcal{C}$. Then $F$ is acyclic at $B$ along $\varphi$ if restriction along $\varphi$,
$$H^n(\mathbb{Z}[h_B], F) \to H^n(\mathbb{Z}[h_B \circ \varphi], F \circ \varphi),$$
is bijective for all $n$. So the cohomology of $h_B \circ \varphi$ is $F(B)$ in degree $0$ and zero in positive degrees.
Lean: `New.Variety.IsAcyclicAt` (Lib/General/Algebra/CohomologyBaseChange.lean).

**Definition (Acyclic on perfect algebras).** Coefficients $F$ on $\mathcal{O}^\flat$-algebras are acyclic on perfect algebras if $F$ is acyclic along the tilt $S \mapsto S^\flat$ at every perfect $\mathcal{O}^\flat$-algebra $b$.
Lean: `New.Variety.IsAcyclicOnPerfect` (Lib/PadicComparison/Descent/AlmostDescent.lean).

In words: on $p$-adic tests, the functor $S \mapsto \mathrm{Hom}(b, S^\flat)$ with coefficients $S \mapsto F(S^\flat)$ has the cohomology $F(b)$, in degree $0$. This is the hypothesis of the primitive comparison in Section 5. The main theorem of this section gives it for almost coefficients.

**Theorem (Almost descent).** Let $N$ be an $\mathcal{O}^\flat$-module with $p^\flat N = 0$. Then the almost coefficients $b \mapsto b \otimes N \otimes \mathfrak{m}$ are acyclic on perfect algebras.
Lean: `New.Variety.isAcyclicOnPerfect_almostCoeff` (Lib/PadicComparison/Descent/AlmostDescent.lean).

The theorem is the case of all $\mathcal{O}^\flat$-algebras of the same statement on the category of perfect $\mathcal{O}^\flat$-algebras, `New.Variety.isAcyclicAt_perfectTilt`. The passage is formal: maps of perfect algebras from $b$ to a tilt are maps of algebras. The proof of the perfect case has three steps.

**Lemma (Faithfully flat tests over a valuation ring).** Let $V$ be a perfect $\mathcal{O}^\flat$-algebra that is a valuation domain, in which $p^\flat$ is neither zero nor a unit. Then there are a $p$-adic test $S$ and an $\mathcal{O}^\flat$-algebra map $\varphi : V \to S^\flat$ such that $V/\ker \varphi \to S^\flat$ is faithfully flat and $p^\flat$ divides every element of $\ker \varphi$.
Lean: `New.Variety.exists_faithfullyFlat_padicTest` (Lib/PadicComparison/Descent/AlmostDescent.lean).

*Proof.* Let $\pi$ be the map from $\mathcal{O}_C \otimes_{A_{\inf}} W(V)$ to the residue field of $V$. It is defined because the kernel of $\theta$ is generated by $\xi$, and $\xi$ reduces to $p^\flat$, a non-unit of $V$. The ring $\mathcal{O}_C \otimes W(V)$ has no $p$-torsion, because $p^\flat$ is regular on the domain $V$. The kernel of $\pi$ is a prime ideal that contains $p$. So `New.Variety.exists_cell_over` of Section 2 gives a map $\rho$ to a cell $W$ that sends $\ker \pi$ to non-units. By the theorem on points of perfect algebras of Section 2, $\rho$ comes from a map $\varphi : V \to W^\flat$. The tilt of the valuation ring $W$ is a valuation ring, and the image of $V$ in it is a valuation ring too. So the inclusion is flat. The map $\varphi$ is local: if $\varphi(v)$ is a unit, then so is its untilt $\rho(1 \otimes [v])$, so $1 \otimes [v] \notin \ker \pi$. A flat local map of local rings is faithfully flat. Last, if $v \in \ker \varphi$ and $v$ did not divide by $p^\flat$, then $v \mid p^\flat$ in the valuation ring $V$, and $p^\flat$ would vanish in the tilt, where it is regular. $\square$

**Lemma (v-descent).** Let $p^\flat N = 0$, and let $y : b \to b'$ be a map of perfect $\mathcal{O}^\flat$-algebras. Assume that every map from $b$ to the tilt of a test factors through $y$. Then $h_{b'} \to h_b$ is a cover for the almost coefficients of $N$, on the category of perfect $\mathcal{O}^\flat$-algebras.
Lean: `New.Variety.isCover_of_points` (Lib/PadicComparison/Descent/AlmostDescent.lean).

Here a map $q : Y \to X$ of functors is a cover for $F$ if the inclusion of its image subfunctor into $X$ induces bijections on cohomology with coefficients $F$ (`New.Variety.IsCover`, in `Lib/Cohomology/Etale/BijectiveComparisons.lean`). This is the descent condition of [Chapter 2](/chapter/cohomology-ext/).

*Proof.* The source argues by strong induction on the degree. Suppose that $z \neq 0$ is a relative class of least degree $n$ over some perfect $b$-algebra $E$. Two steps push $z$ to a perfect algebra $B'$ such that $E \to B'$ factors through a perfect valuation ring $V$, and the class stays nonzero over $V$. The short exact sequences of coefficients $0 \to M \otimes \Phi \to M' \otimes \Phi \to M'' \otimes \Phi \to 0$, with the minimality of $n$, control the images. If $p^\flat$ were zero or a unit in $V$, the class would survive in the zero ring, which is absurd. So the lemma on faithfully flat tests applies. It gives a test $S$ and $\varphi : V \to S^\flat$, faithfully flat over $V/\ker \varphi$, with $\ker \varphi \subseteq p^\flat V$. The point $b \to V \to S^\flat$ lifts to $b'$ by hypothesis. The class survives in $V/\ker \varphi$, because $p^\flat$ kills $N$ and so $\ker \varphi$ acts by zero on the coefficients. It vanishes there by descent along the faithfully flat map $V/\ker \varphi \to S^\flat$. This is a contradiction. $\square$

**Theorem (Acyclicity on perfect algebras).** Let $p^\flat N = 0$, and let $b$ be a perfect $\mathcal{O}^\flat$-algebra. On the category of perfect $\mathcal{O}^\flat$-algebras, the points of $b$ in the tilts of tests are acyclic for the almost coefficients of $N$.
Lean: `New.Variety.isAcyclicAt_perfectTilt` (Lib/PadicComparison/Descent/AlmostDescent.lean).

*Proof.* By induction on $r$, the comparison maps are bijective in degrees below $r$, for all perfect $b$ at once. Every perfect $b$ has a map $y : b \to b'$ that is onto on points in tilts, with the claim known for $b'$. If $b$ has a point in some tilt, the theorem on points of perfect algebras and the universal covering test of Section 2 give one test $S_0$ through which all points of $b$ factor. Then $b' = S_0^\flat$, and the claim for $b'$ holds because the tilt is fully faithful. If $b$ has no point, then $b'$ is the zero ring, and both sides vanish. The lemma on v-descent says that $y$ is a cover. Čech descent then gives one more degree for $b$ from the fibre powers $b' \otimes_b \dots \otimes_b b'$. These are again perfect, and the induction hypothesis applies to them. $\square$

**Remark (Formalization).** The theorem is used in two places. The period map of Section 5 applies it with $N = \mathcal{O}^\flat \otimes_{A_{\inf}} S$ for a period ring pair $(S, K)$. The finiteness of $V^n(Y)$ applies it with $N$ the zero module (the type `Unit`). For $N = 0$, the almost coefficients are zero, and the acyclicity is trivial. So the finiteness theorem of Section 5 does not depend on almost descent in an essential way. It needs only some module $M$ with acyclic coefficients $b \mapsto b \otimes M$, and the zero module is such a module.

### Derived completeness

The second half of the section passes from coefficients modulo $p$ to $p$-adic coefficients. The source uses derived completeness in place of $p$-adic completeness, because cohomology groups need not be separated.

**Definition (Derived completeness).** Let $W$ be a ring, $\pi \in W$ and $X$ a $W$-module. $X$ is derived $\pi$-complete if the map $(x_j)_{j \ge 0} \mapsto (x_j - \pi x_{j+1})_{j \ge 0}$ on sequences in $X$ is bijective.
Lean: `New.Variety.IsDerivedComplete`, with `New.shiftDiff` (Lib/PadicComparison/Completion.lean).

The cokernel of this map on $\prod_{j \ge 0} X$ is $\mathrm{Ext}^1(W[1/\pi], X)$, and its kernel is $\mathrm{Hom}(W[1/\pi], X)$, for $\pi$ a nonzerodivisor. So the definition is the classical one: $\mathrm{Hom}(W[1/\pi], X) = \mathrm{Ext}^1(W[1/\pi], X) = 0$ (Stacks Project, Tag 091N, for the case of a principal ideal). An adically complete module is derived complete (`New.Variety.IsDerivedComplete.of_isAdicComplete`). Derived completeness passes to products, to retracts, and to cohomology (`New.Variety.IsDerivedComplete.cohomology`). The key property is Nakayama's lemma in the form of successive approximation: in a derived complete module, a submodule on which multiplication by $\pi$ is onto is zero.

**Theorem (The adic step).** Let $\alpha : N' \to N \circ \varphi$ be a map of functors. Let $0 \to \Phi \xrightarrow{a} \Phi \to G \to 0$ and $0 \to \Phi' \xrightarrow{a} \Phi' \to G' \to 0$ be exact sequences of coefficients, and let $\beta : \Phi \circ \varphi \to \Phi'$ induce $\gamma : G \circ \varphi \to G'$. Assume:

1. every $H^n(N', \Phi')$ is derived $a$-complete;
2. $H^n(N, \Phi)$ is derived $a$-complete whenever the kernel of the comparison map $H^n(N, \Phi) \to H^n(N', \Phi')$ is $a$-divisible;
3. the comparison maps $H^n(N, G) \to H^n(N', G')$ for $\gamma$ are bijective in every degree.

Then the comparison maps $H^n(N, \Phi) \to H^n(N', \Phi')$ for $\beta$ are bijective in every degree.
Lean: `New.Variety.Comparison.IsBijective.of_mod` (Lib/PadicComparison/Completion.lean).

*Proof.* The two short exact sequences give a map of long exact sequences, by the comparison of [Chapter 2](/chapter/cohomology-ext/). In these sequences the first map is multiplication by $a$. The comparison mod $a$ is injective in degree $n$ and surjective in degree $n - 1$. A diagram chase shows that the kernel $K_n$ of the comparison in degree $n$ is $a$-divisible: an element of $K_n$ is $a$ times an element of $K_n$. By hypothesis 2, the source group is derived complete, and a divisible submodule of a derived complete module is zero. So $K_n = 0$. For surjectivity, the comparison is onto mod $a$, by the injectivity mod $a$ in degree $n + 1$. Successive approximation in the derived complete target (hypothesis 1) then shows that every element is in the image. $\square$

The source uses the adic step through one corollary, for the base change of coefficients.

**Theorem (Completed base change).** Let $W$ be a discrete valuation ring with uniformizer $p$, $S$ a flat $W$-algebra, $\Theta$ a functor to $W$-algebras and $X$ a functor to $S$-algebras. Assume that $W$, $S$, every $\Theta(A)$ and every $X(A)$ are $p$-torsion-free and $p$-adically complete. Assume that the cohomology of $N$ commutes with flat base change of coefficients. Let $j : S \otimes_W \Theta \to X$ be a map that is bijective modulo $p$. Assume that $H^n(N, \Theta)$ has finite rank over $W$ for every $n$ where the kernel of $H^n(j)$ is $p$-divisible. Then $H^n(j) : H^n(N, S \otimes_W \Theta) \to H^n(N, X)$ is bijective for all $n$.
Lean: `New.Variety.HasFlatBaseChange.isBijective_of_isReductionMod` (Lib/PadicComparison/Completion.lean).

*Proof.* Apply the adic step with $a = p$. Both $S \otimes \Theta$ and $X$ are $p$-torsion-free, so multiplication by $p$ gives the two short exact sequences, and both reduce mod $p$ to $X/p$. The target is derived complete because $X$ is complete. For the source, flat base change gives $H^n(N, S \otimes \Theta) = S \otimes_W H^n(N, \Theta)$. A module of finite rank over a complete discrete valuation ring has bounded torsion, and its base change to a complete flat $S$ is then derived complete (`New.Variety.IsDerivedComplete.baseChange`). $\square$

**Remark (Formalization).** The hypothesis of finite rank is stated only in the degrees where the kernel is $p$-divisible. This form lets the source prove finiteness and bijectivity together: in Section 5, the finiteness of $H^n$ with $\mathbb{Z}_p$-coefficients is an input, and it comes from the primitive comparison with $\mathbb{F}_p$-coefficients. The source cites Bhatt, *Torsion completions are bounded*, J. Pure Appl. Algebra (2019) for the bounded torsion, but proves the case of finite rank over a discrete valuation ring by hand.
