---
title: The primitive comparison and the period map
lean:
  - Lib/PadicComparison/Primitive/ComparisonTheorem.lean
  - Lib/PadicComparison/Primitive/PeriodCoefficients.lean
  - Lib/PadicComparison/Primitive/Periods.lean
  - Lib/PadicComparison/HodgeTate/PeriodMap.lean
decls:
  - New.Variety.PadicTest.bijective_generic_points
  - New.Variety.locConstToTilt
  - New.Variety.primitiveMap
  - New.Variety.tiltTheory
  - New.Variety.finite_and_primitive_comparison
  - New.Variety.finite_padic_cohomology
  - New.Variety.ellAdicCohom.continuous_galoisAction
  - New.Variety.IsPeriodRingPair
  - New.Variety.isPeriodRingPair_OC
  - New.Variety.CoeffCompBijective.periodAlg_of_almostCoeff
  - New.Variety.primitivePeriodMap_isBijective
  - New.Variety.exists_primitive_period_comparison
  - New.Variety.IsPadicPeriodMap
  - New.Variety.exists_period_map
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The primitive comparison and the period map

This section states the primitive comparison theorem of the source and its three corollaries: finiteness of the $p$-adic cohomology, continuity of the Galois action, and the period map with coefficients in a period ring pair. It combines the almost descent of Section 3 at the point with the duality machine of Section 4.

### The classical result

Let $X$ be a proper smooth rigid analytic variety over $C = \mathbb{C}_p$. Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), Theorem 1.3, proves that the map $H^i_{\mathrm{et}}(X, \mathbb{F}_p) \otimes \mathcal{O}_C/p \to H^i_{\mathrm{et}}(X, \mathcal{O}_X^+/p)$ is an almost isomorphism, and that $H^i_{\mathrm{et}}(X, \mathbb{F}_p)$ is finite. A tilted form of the theorem replaces $\mathcal{O}_C/p$ by $\mathcal{O}^\flat$ and $\mathcal{O}_X^+/p$ by the tilted structure sheaf. The source names Scholze 2013, Theorems 1.3 and 5.1, as the source of the result, and Zavyalov, *Poincaré duality in abstract 6-functor formalisms*, arXiv 2301.03821, Theorem 3.3.3 and Application 1.3.4, as the source of the method.

The source does not use almost mathematics for finiteness. It puts the maximal ideal $\mathfrak{m}$ of $\mathcal{O}^\flat$ into the coefficients, and it gets finiteness from the duality of Section 4. The docstring of `PeriodMap.lean` says that the result "is deduced from the duality comparison on products of projective lines, without almost finiteness."

### The valuative criterion

Let $c$ be a $p$-adic test with ring $c_{\mathrm{prod}} = \prod_i V_i$, a product of cells, and generic ring $c_{\mathrm{prod}}[1/p]$.

**Lemma (Valuative criterion).** Let $Y$ be proper over $R$, and make $\mathrm{Spec}\, c_{\mathrm{prod}}$ and $\mathrm{Spec}\, c_{\mathrm{prod}}[1/p]$ into schemes over $R$ compatibly. Then restriction $Y(c_{\mathrm{prod}}) \to Y(c_{\mathrm{prod}}[1/p])$ of points over $R$ is bijective.
Lean: `New.Variety.PadicTest.bijective_generic_points` (Lib/PadicComparison/Primitive/ComparisonTheorem.lean).

*Proof sketch.* Injectivity holds because $Y$ is separated and $c_{\mathrm{prod}} \to c_{\mathrm{prod}}[1/p]$ is injective. For surjectivity, $p \ne 0$ in each cell $V_i$, so the projection to $V_i$ extends to a map from $c_{\mathrm{prod}}[1/p]$ to the fraction field of $V_i$. The valuative criterion of properness gives a point over each $V_i$. These points glue to a point over the product, because $Y$ is quasi-compact. $\square$

This lemma is the only place where properness enters the primitive comparison. It identifies the points of $Y$ in $p$-adic tests with the points of $Y$ in the generic rings, which are tests over $\Omega$.

### The primitive map

For a test ring $A$, write $\mathrm{LC}(A)$ for the ring of locally constant functions $\mathrm{Spec}\, A \to \mathbb{F}_p$.

**Definition (From locally constant functions to the tilt).** For a $p$-adic test $c$ with ring $R$, the map $\mathrm{LC}(R[1/p]) \to R^\flat$ extends a locally constant function from $\mathrm{Spec}\, R[1/p]$ to $\mathrm{Spec}\, R$, restricts it to $\mathrm{Spec}\, R/p$, reads it as the element $x$ of $R/p$ whose germ at each prime is the value there, and sends it to the constant sequence $(x, x, \ldots)$. This sequence lies in $R^\flat$ because $t^p = t$ in $\mathbb{F}_p$.
Lean: `New.Variety.locConstToTilt` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

**Definition (Primitive map).** The primitive map is the natural map of $\mathcal{O}^\flat$-algebras $\mathcal{O}^\flat \otimes_{\mathbb{F}_p} \mathrm{LC}(R[1/p]) \to R^\flat$ that extends the map above.
Lean: `New.Variety.primitiveMap` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

**Remark (Formalization).** The definition of `New.Variety.locConstToTilt` uses `choose` to pick, for each test $c$, a ring map $\varphi_c : \mathrm{LC}(R/p) \to R/p$ with the property that the germ of $\varphi_c(x)$ at each prime $q$ is the constant $x(q)$. The choice does not matter. The map from $R/p$ to the product of its localizations is injective, so the property fixes $\varphi_c$. The proof of naturality in the source uses exactly this injectivity.

**Definition (Tilted theory).** Let $M$ be an $\mathcal{O}^\flat$-module such that the coefficients $b \mapsto b \otimes M$ are acyclic on perfect $\mathcal{O}^\flat$-algebras. The tilted theory is the theory for the prime $\ell = p$ on $p$-adic tests, along $R \mapsto R[1/p]$, with coefficients $R \mapsto R^\flat \otimes_{\mathcal{O}^\flat} M$.
Lean: `New.Variety.tiltTheory` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

The axioms of a theory concern closed loci. For an ideal $I$ of $R[1/p]$, the maps of tests that kill $I$ are those whose tilt factors, uniquely, through a perfect quotient $R^\flat/J$. The ideal $J$ consists of the elements of $R^\flat$ that become zero near $I$. The acyclicity hypothesis on $M$ then gives the axioms.

### The primitive comparison

Let $\Omega$ be an algebraic closure of $\mathbb{Q}$ with a map to $\mathbb{C}_p$. Let $Y$ be proper over $R$ and charted over $\Omega$. Write $X$ for the points of $Y_\Omega$ on test rings.

**Theorem (Primitive comparison).** Let $M$ be an $\mathcal{O}^\flat$-module such that the coefficients $b \mapsto b \otimes M$ are acyclic on perfect $\mathcal{O}^\flat$-algebras. Then:

1. the cohomology of $\mathbb{Z}[X]$ commutes with flat extension of coefficients;
2. each $H^n(X, \mathbb{F}_p)$ is finite; and
3. if $R \to \Omega \to \mathbb{C}_p$ agrees with a map $R \to \mathcal{O}_C$, then the primitive map tensored with $M$ induces a bijection in every degree. It goes from the cohomology of $Y_\Omega$ with coefficients $A \mapsto \mathcal{O}^\flat \otimes \mathrm{LC}(A) \otimes M$ to the cohomology of $S \mapsto Y(S)$ on $p$-adic tests with coefficients $S \mapsto S^\flat \otimes M$.

Lean: `New.Variety.finite_and_primitive_comparison` (Lib/PadicComparison/Primitive/ComparisonTheorem.lean).

*Proof.* Choose a basis $(b_i)$ of $M$ over $\mathbb{F}_p$. The classes $x \mapsto b_i \otimes x$ of degree $0$ make the tilted theory into a compared theory $D$ along $R \mapsto R[1/p]$ in the sense of Section 4. Both the tilted theory and the locally constant theory satisfy the projective line formula. By the basis, flat base change and the isomorphism $M \otimes \mathrm{LC} \cong (\mathcal{O}^\flat \otimes \mathrm{LC}) \otimes_{\mathcal{O}^\flat} M$, the Leray-Hirsch map of $D$ on a functor with flat base change is the comparison map of part 3.

At the point $\mathrm{Spec}\, \Omega$, both $\mathcal{O}^\flat$ and $\Omega$ are initial, so the comparison at the point is an instance of the acyclicity hypothesis at $b = \mathcal{O}^\flat$. The cohomology of the point with locally constant coefficients is the constants $\mathbb{F}_p$, because $\Omega$ is a domain. So $\mathbb{Z}[\mathrm{pt}]$ is good for $D$.

Over a field, goodness of $\mathbb{Z}[Y]$ is goodness of the pair $(Y, \mathrm{off}(Y))$. The theorem on charted functors of Section 4 now gives that $\mathbb{Z}[X]$ is good on tests over $\Omega$: the Leray-Hirsch map is bijective and the total cohomology mod $p$ is finite. Restriction from all test rings to tests over $\Omega$ is bijective on cohomology, and this carries parts 1 and 2 to $X$. For part 3, the valuative criterion identifies the points in $p$-adic tests with the points in the generic rings. $\square$

The source claims that this proof needs no almost mathematics beyond the acyclicity hypothesis at the point. Lean accepts the theorem, if the reported checks hold.

### Finiteness and continuity

The geometric $p$-adic cohomology of $Y$ is $V^n(Y) = \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H^n(Y_\Omega, \mathbb{Z}_p)$, where $\mathbb{Z}_p$ means the coefficient $A \mapsto W(\mathrm{LC}(A))$. The Lean name is `New.Variety.ellAdicCohom`.

**Theorem (Finiteness).** Let $Y$ be proper over $R$ and charted over $\Omega$. Then $H^n(Y_\Omega, \mathbb{Z}_p)$, computed on test rings, is a finitely generated $\mathbb{Z}_p$-module. So $V^n(Y)$ is finite-dimensional over $\mathbb{Q}_p$.
Lean: `New.Variety.finite_padic_cohomology` (Lib/PadicComparison/Primitive/ComparisonTheorem.lean).

*Proof.* Choose an embedding of $\Omega$ in $\mathbb{C}_p$. The primitive comparison, with $M = 0$, gives the finiteness of $H^n(Y_\Omega, \mathbb{F}_p)$. Finiteness modulo $p$ lifts to $\mathbb{Z}_p$. The finite dimension of $V^n(Y)$ is then an instance, by base change from $\mathbb{Z}_p$ to $\mathbb{Q}_p$. $\square$

**Remark (Formalization).** Two points matter here. First, the proof applies the primitive comparison with $M$ the zero module, the type `Unit`. The acyclicity hypothesis for $M = 0$ is trivial, so finiteness does not rest on almost descent, as Section 3 says. Second, the proof chooses the embedding of $\Omega$ in $\mathbb{C}_p$ by `IsAlgClosed.lift`. The statement does not mention $\mathbb{C}_p$, so the choice does not enter the result.

**Theorem (Continuity).** Let $Y$ be proper over $R$ and charted over $\Omega$, and let $\mathrm{Gal}(\Omega/K)$ act $R$-linearly. For $x \in V^n(Y)$ and a $\mathbb{Q}_p$-linear map $l : V^n(Y) \to \overline{\mathbb{Q}}_p^N$, the map $g \mapsto l(g x)$ is continuous.
Lean: `New.Variety.ellAdicCohom.continuous_galoisAction` (Lib/PadicComparison/Primitive/ComparisonTheorem.lean).

*Proof sketch.* Reduce to a pure tensor $a \otimes t$ and to continuity at one point $g_0$. The cohomology $H^n(Y_\Omega, \mathbb{Z}_p)$ is finitely generated, so its image under a linear map is compact and so bounded. So $p^k$ maps the image into any given neighbourhood of $0$. Modulo $p^k$, the class $t$ is the pull-back of a class over the subalgebra generated by a finite set $s$ of elements of $\Omega$, because the cohomology of a proper scheme commutes with filtered colimits. If $g$ fixes $s$, then $g t - t$ is divisible by $p^k$. $\square$

**Remark (Formalization).** Continuity is stated through linear maps to $\overline{\mathbb{Q}}_p^N$, not through a topology on $V^n(Y)$. This is the form that `New.Variety.exists_isEigenQuotient` in `Lib/Shimura/Eigenspace.lean` asks for, and `New.Variety.Model.exists_galois_rep` passes the theorem to it at line 737. No topology on $V^n(Y)$ is needed. The proof uses finiteness, so it also depends on the primitive comparison.

### Period ring pairs

**Definition (Period ring pair).** Let $S$ be an $A_{\inf}$-algebra and $K$ an $S$-algebra. The pair $(S, K)$ is a period ring pair if $S$ is $p$-torsion-free and $p$-adically complete, $p$ divides the image of $\xi$ in $S$, and the image of $\tau = [\varepsilon^{1/p}] - 1$ in $K$ is a unit.
Lean: `New.Variety.IsPeriodRingPair` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

**Lemma.** $(\mathcal{O}_C, \mathbb{C}_p)$ is a period ring pair. The map $A_{\inf} \to \mathcal{O}_C$ is $\theta$, which kills $\xi$, and $\theta(\tau) \ne 0$ is a unit of the field $\mathbb{C}_p$.
Lean: `New.Variety.isPeriodRingPair_OC` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

Section 7 gives the second example, $(A_{\max}, B_{\max})$, through the class `New.Variety.CrysPeriodAlgebra`.

For a period ring pair, the period coefficients on $p$-adic tests are $c \mapsto K \otimes_S (S \otimes_{A_{\inf}} W(c^\flat))^\wedge$, where the hat is $p$-adic completion.

**Theorem (From almost coefficients to period coefficients).** Let $\psi$ and $\psi'$ be functors to $\mathcal{O}^\flat$-algebras with perfect values on which $p^\flat$ is a non-zero-divisor, compared by $\beta$ along $\varphi$, and let $\alpha : N' \to N \circ \varphi$. Let $(S, K)$ be a period ring pair with $K$ flat over $S$. Assume that the cohomology of $N$ commutes with flat extension of coefficients, and that the cohomology of $N'$ commutes with $K \otimes -$ for coefficients that factor through $\psi'$. If the comparison is bijective for the coefficients $b \mapsto b \otimes (\mathcal{O}^\flat \otimes S) \otimes \mathfrak{m}$, then it is bijective for the coefficients $b \mapsto K \otimes (S \otimes W(b))^\wedge$.
Lean: `New.Variety.CoeffCompBijective.periodAlg_of_almostCoeff` (Lib/PadicComparison/Primitive/PeriodCoefficients.lean).

*Proof sketch.* Put $P(b) = (S \otimes W(\mathfrak{m})) \otimes W(b)$. The ideal $W(\mathfrak{m})$ of $A_{\inf}$ reduces to $\mathfrak{m}$ modulo $p$. The adic step of Section 3 lifts bijectivity from the almost coefficients to the completion of $P$, and flatness passes it to $K \otimes -$. The ideal $W(\mathfrak{m})$ contains $\tau$, and $\tau$ is a unit of $K$. So after completion and $K \otimes -$, $P$ is isomorphic to $b \mapsto S \otimes W(b)$. $\square$

This theorem is the reason for the conditions on $\tau$ and $\xi$. The unit $\tau$ removes the almost ideal, and the condition on $\xi$ makes the reduction modulo $p$ go through $\mathcal{O}^\flat$.

### The period comparison

**Theorem (Primitive comparison with period coefficients).** Let $(S, K)$ be a period ring pair with $K$ flat over $S$, and let $\theta$ identify a functor $\Psi$ on $p$-adic tests with the period coefficients. Let $\alpha : N' \to N \circ (R \mapsto R[1/p])$. Assume that $N$ and $N'$ have flat base change, that each $H^n(N, \mathbb{Z}_p)$ is finite over $\mathbb{Z}_p$, and that the primitive map is bijective on cohomology along $\alpha$ for the almost coefficients of $\mathcal{O}^\flat \otimes_{A_{\inf}} S$. Then the natural map $K \otimes W(\mathrm{LC}) \to \Psi$ induced by the primitive map is bijective on cohomology along $\alpha$, in every degree.
Lean: `New.Variety.primitivePeriodMap_isBijective` (Lib/PadicComparison/Primitive/Periods.lean).

*Proof sketch.* The map is a composite of four maps. The first and the last are isomorphisms. The second, $W(\mathrm{LC}) \otimes S \to (S \otimes W(\mathcal{O}^\flat \otimes \mathrm{LC}))^\wedge$, is bijective modulo $p$, and the completed base change of Section 3 makes it bijective on cohomology. This step uses the finiteness of $H^n(N, \mathbb{Z}_p)$. The third is the primitive map on period coefficients, which is bijective by the theorem above. $\square$

**Theorem (Existential form).** Under the same conditions on $(S, K)$ and $\theta$, there is a natural map $\gamma : K \otimes W(\mathrm{LC}) \to \Psi$ with $\gamma(a \otimes x) = \theta(a \otimes 1 \otimes x')$, where $x'$ is the image of $x$ under the Witt vector map of `New.Variety.locConstToTilt`, and $\gamma$ is bijective on cohomology under the conditions of the previous theorem.
Lean: `New.Variety.exists_primitive_period_comparison` (Lib/PadicComparison/Primitive/Periods.lean).

### The period map

Let $e : \Omega \to \overline{\mathbb{Q}}_p$ agree with $R \to \mathcal{O}_C$ on $R$. Let a group $\Gamma$ act on $\Omega$ by ring maps that fix $R$, and let $j : \Gamma \to G_p$ satisfy $j(g)(e(x)) = e(g x)$. For $g \in G_p$, the twist of a $p$-adic test by $g$ keeps the ring and composes the structure map $\mathcal{O}_C \to c_{\mathrm{prod}}$ with $g$.

**Definition (Period map).** A $p$-adic period map is a family of $K$-linear maps $J_Y : K \otimes V^n(Y) \to H^n(\mathbb{Z}[Y(-)], \Psi)$, where $Y(-)$ is the functor of $R$-points of $Y$ in $p$-adic tests, such that:

1. $J$ commutes with pull-back along maps $W \to Y$;
2. $J$ carries $\sigma \otimes g$ to the pull-back along $\beta$ and the twist by $j(g)$, whenever $\beta$ acts as $\sigma$ on the elements $\theta(a \otimes 1 \otimes w)$ with $w$ a Witt vector whose coordinates are fixed by Frobenius; and
3. $J_Y$ is bijective if $Y$ is proper and charted over $\Omega$.

Lean: `New.Variety.IsPadicPeriodMap` (Lib/PadicComparison/HodgeTate/PeriodMap.lean).

**Theorem (Period map).** Let $(S, K)$ be a period ring pair with $K$ flat over $S$, and let $\theta$ identify $\Psi$ with the period coefficients. Then a $p$-adic period map exists.
Lean: `New.Variety.exists_period_map` (Lib/PadicComparison/HodgeTate/PeriodMap.lean).

*Proof.* Put $J_Y = \gamma^* \circ \mathrm{bc} \circ E$. Here $E$ writes $K \otimes V^n(Y)$ as $K \otimes_{\mathbb{Z}_p} H^n(Y_\Omega, \mathbb{Z}_p)$, $\mathrm{bc}$ moves $K$ into the coefficients, and $\gamma^*$ is the pull-back along the map $\gamma$ of the existential form, along the comparison of points in $p$-adic tests with points in test rings. Naturality is naturality of each piece. Equivariance holds because Witt vectors of locally constant $\mathbb{F}_p$-valued functions are fixed by Frobenius. For bijectivity, the primitive comparison, applied with the acyclicity of the almost coefficients of $\mathcal{O}^\flat \otimes_{A_{\inf}} S$ from Section 3, gives the bijectivity of the primitive map on these coefficients. Almost descent applies because $p^\flat$ kills $\mathcal{O}^\flat \otimes_{A_{\inf}} S$ when $p$ divides $\xi$ in $S$. The finiteness theorem gives the finiteness of $H^n(Y_\Omega, \mathbb{Z}_p)$. Flat base change holds for both sides, and the valuative criterion identifies the points. $\square$

**Remark (Formalization).** The theorem is an existence statement. It does not give a global name to $J$. The Hodge-Tate result of Section 6 and the crystalline result of Section 7 call `New.Variety.exists_period_map` inside their proofs, and they use only the three properties. So a reader of those proofs can treat $J$ as any map with the three properties. The bijectivity in property 3 is the bijectivity of the period map. It is not a bijectivity of the Hodge-Tate map $\lambda_h$ of Section 6, which the source does not prove.
