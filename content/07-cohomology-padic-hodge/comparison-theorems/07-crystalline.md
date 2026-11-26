---
title: The crystalline comparison and the congruence relation
lean:
  - Lib/PadicHodge/PeriodRings/CrystallineRings.lean
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/PadicComparison/Descent/TestCategory.lean
  - Lib/PadicComparison/Crystalline/DividedPowerEnvelope.lean
  - Lib/PadicComparison/Crystalline/ComparisonMap.lean
  - Lib/PadicComparison/ToricTower.lean
  - Lib/PadicComparison/CrystallineFrobenius.lean
  - Lib/Cohomology/Etale/Basic.lean
decls:
  - New.Period.Amax
  - New.Period.Bmax
  - New.Period.linearFrob
  - New.Period.IsWeilPair
  - New.Variety.pdIdeal
  - New.Variety.IsCompleteTorsionFree.existsUnique_witt_lift
  - New.Variety.CrysPeriodAlgebra
  - New.Variety.exists_crysPeriodAlgebra
  - New.Variety.crysPeriodCoeff
  - New.Variety.HasCrysComparison
  - New.Variety.compatibleRoots
  - New.Variety.IsLine
  - New.Variety.CompatibleRootsAreLines
  - New.Variety.PadicTest.isLine_compatibleRoots
  - New.Variety.hasCrysComparison_of_etale
  - New.Variety.hasCrysComparison_chart
  - New.Variety.span_range_crysComparison_pull_eq_top
  - New.Variety.CongruenceRelation
  - New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The crystalline comparison and the congruence relation

This section treats the last of the three results that the main argument uses by name. Let $Y$ be a proper charted scheme over a noetherian ring $R$. First, the representation of a decomposition group at a $p$-adic place on $V^n(Y)$ is crystalline. Second, a congruence relation between maps $W \to Y$ on the special fibre gives a relation between Frobenius operators on $B_{\max} \otimes V^n(Y)$. The period rings come from [the chapter on period rings](/chapter/period-rings/).

### The classical result

Let $X$ be a proper smooth scheme over $W(k)$, with $k$ perfect of characteristic $p$. Fontaine's crystalline conjecture gives an isomorphism $B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} H^n_{\mathrm{et}}(X_{\overline{K}}, \mathbb{Q}_p) \cong B_{\mathrm{cris}} \otimes_{K_0} H^n_{\mathrm{cris}}(X_k / W(k))[1/p]$, compatible with Frobenius, Galois action and filtrations. So the étale cohomology is crystalline. The source cites Faltings, *Crystalline cohomology and $p$-adic Galois representations* (1989), and Bhatt, Morrow and Scholze, *Integral $p$-adic Hodge theory*, Publ. Math. IHÉS 128 (2018), Theorem 1.1(i).

For the congruence relation, the source cites Scholl, *Motives for modular forms*, Invent. Math. 100 (1990), §4.2.3, through Katz and Messing, Invent. Math. 23 (1974), Theorem 2(2), and for a ramified base Berthelot and Ogus, Invent. Math. 72 (1983). The literature compares characteristic polynomials through cycle classes. The source instead carries a relation between maps on points of the special fibre directly to a relation between operators.

**Remark (Formalization).** The header of `Lib/PadicComparison/CrystallineFrobenius.lean` says that there is no integral form, no Hodge-Tate decomposition, and no identification with étale or crystalline cohomology. The source proves that $V^n(Y)$ is crystalline (enough fixed periods in $B_{\max}$) and the relation below. It does not identify $D_{\mathrm{cris}}$ with a crystalline cohomology group.

### The period rings A_max and B_max

**Definition (The period rings).** The ring $A_{\max}$ is the $p$-adic completion of $A_{\inf}[X]/(pX - \xi)$. The ring $B^+$ is $A_{\max}[1/p]$, and $B_{\max}$ is $B^+[1/\mu]$ with $\mu = [\varepsilon] - 1$.
Lean: `New.Period.Amax` (Lib/PadicHodge/PeriodRings/CrystallineRings.lean).
Lean: `New.Period.Bmax` (Lib/PadicHodge/PeriodRings/CrystallineRings.lean).

These are Colmez's rings. The docstring of `Bmax` says that it replaces Fontaine's $B_{\mathrm{cris}}$, which gives the same crystalline representations. The source does not prove or use this fact.

**Definition (Crystalline period algebra).** A structure of `CrysPeriodAlgebra` is an $A_{\inf}$-algebra structure on $A_{\max}$ with four properties: $A_{\max}$ is $p$-torsion-free and $p$-complete, $p$ divides the image of $\xi$, the image of $\tau = [\varepsilon^{1/p}] - 1$ is a unit in $B_{\max}$ (a period ring pair as in Section 5), and $p^3$ divides the image of $\mu$, and the image of $\mu$ is a unit in $B_{\max}$.
Lean: `New.Variety.CrysPeriodAlgebra` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

**Definition (The divided power ideal).** For a ring $S$, the ideal $\mathfrak{d}(S)$ is the set of the $x \in S$ such that $n!$ divides $x^n$ for every $n$.
Lean: `New.Variety.pdIdeal` (Lib/PadicComparison/Descent/TestCategory.lean).

The map $\mathcal{O}_C \to A_{\max}/\mathfrak{d}$ is `New.Variety.integersToPdQuotient`. It factors $A_{\inf} \to A_{\max}/\mathfrak{d}$ through Fontaine's map $\theta$, because $p \in \mathfrak{d}(A_{\max})$ and $p$ divides the image of $\xi$.

**Theorem (A twisted structure on A_max).** Let $N \ge 0$ and let $y \in \mathcal{O}_C$ with $p \mid y^N$. Then there is a structure $h$ of `CrysPeriodAlgebra` such that (a) $\mathbb{Z}_p$ acts on $A_{\max}$ through $A_{\inf}$ as it acts directly, (b) the structure map commutes with the monoid generated by Frobenius and $G_p$, and (c) the map $\mathcal{O}_C \to A_{\max}/\mathfrak{d}(A_{\max})$ kills $y$.
Lean: `New.Variety.exists_crysPeriodAlgebra` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

*Proof sketch.* Let $\sigma = \varphi^{\max(N, 3)}$ and let $A_{\inf}$ act on $A_{\max}$ through $\sigma$ followed by the natural map. The natural map sends the ideal $(p, \xi)$ into $(p)$. Since $[\varepsilon] \equiv 1$ modulo $\xi$, the element $\sigma(\mu)$ lies in $(p, \xi)^{\max(N,3)}$, so $p^3$ divides its image. Both $\tau$ and $\mu$ divide $\mu$, so their images under $\sigma$ become units in $B_{\max}$. The element $\sigma$ fixes $\mathbb{Z}_p$ and is central, which gives (a) and (b). For (c), write $y = t^\sharp$. The image of $y$ is the class of $\sigma[t]$, and the constant coefficient of $\sigma(t)$ has untilt $y^{p^{\max(N,3)}}$, a multiple of $p$. So $\sigma[t] \in (p, \xi)$, and its image lies in $\mathfrak{d}$. $\square$

**Remark (Formalization).** The structure $h$ depends on $N$, so on the place and the prime of $R$ in the main theorem. So $A_{\inf}$ does not act on $A_{\max}$ in the standard way. The results below take `CrysPeriodAlgebra` as an instance argument and hold for each such twist.

### Divided powers and Witt vector lifts

**Theorem (Lifts modulo divided powers).** Let $S$ be $p$-torsion-free and $p$-complete, and let $b$ be a perfect ring with $p = 0$. Each ring map $f : b \to S/\mathfrak{d}(S)$ has exactly one lift $g : W(b) \to S$ such that $g(x) \equiv f(x_0)$ modulo $\mathfrak{d}(S)$ for every Witt vector $x$, where $x_0$ is its zeroth coefficient.
Lean: `New.Variety.IsCompleteTorsionFree.existsUnique_witt_lift` (Lib/PadicComparison/Crystalline/DividedPowerEnvelope.lean).

In the classical theory, the ideal $\mathfrak{d}$ takes the place of the divided power thickening.

### The comparison on charts

**Definition (Crystalline coefficients).** On $p$-torsion-free $p$-complete $A_{\max}$-algebras $D$, the coefficient functor sends $D$ to $B_{\max} \otimes_{A_{\max}} D$.
Lean: `New.Variety.crysPeriodCoeff` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

**Definition (Crystalline comparison).** For a functor $P$ from $\mathcal{O}_C$-algebras to types, `HasCrysComparison P` says that a restriction map is bijective in every degree. It goes from the cohomology of $D \mapsto P(D/\mathfrak{d}(D))$ on $p$-torsion-free $p$-complete $A_{\max}$-algebras $D$, with the crystalline coefficients, to the cohomology of $P$ on $p$-adic tests. On a test $S$, the coefficients are $B_{\max} \otimes D_S$, where $D_S$ is the completed $A_{\max} \otimes W(S^\flat)$.
Lean: `New.Variety.HasCrysComparison` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

**Definition (Characters).** The functor on $\mathcal{O}_C$-algebras times $B\mathbb{N}$ sends $A$ to the monoid maps $\chi : (\mathbb{Q}_{\ge 0}, +) \to (A, \cdot)$. A map $(f, k)$ sends $\chi$ to $\eta^k \cdot (f \circ \chi)$, where $\eta$ is the character $s \mapsto (\varepsilon^s)^\sharp$. For a unit $y$, the root systems of $y$ are the characters $\chi$ with $\chi(1) = y$.
Lean: `New.Variety.compatibleRoots` (Lib/PadicComparison/ToricTower.lean).

**Definition (Lines).** Let $Y$ be a functor on $C \times B\mathbb{N}$ and $a$ a map from $Y$ to a functor $U$ on $C$, with $\mathbb{N}$ acting trivially on $U$. Then $a$ is a line for coefficients $F$ if $H^n(U, F) \to H^n(Y, F)$ is bijective for every $n$.
Lean: `New.Variety.IsLine` (Lib/PadicComparison/ToricTower.lean).

**Definition (Root systems are lines).** For a functor $\psi$ to $\mathcal{O}_C$-algebras, the root systems are lines if, for every object $A$ and unit $y$ of $\psi(A)$, the root systems of $y$ form a line over $\mathrm{Hom}(A, -)$.
Lean: `New.Variety.CompatibleRootsAreLines` (Lib/PadicComparison/ToricTower.lean).

**Theorem (Root systems on tests).** Let $M$ be a module such that the coefficients $B \mapsto B^\flat \otimes M$ make $\mathrm{Hom}(b, (-)^\flat)$ acyclic for every perfect $b$. Let $c$ be a $p$-adic test and $v$ a unit of its ring. Then the root systems of $v$ (a) have flat base change and (b) form a line over the functor that $c$ represents.
Lean: `New.Variety.PadicTest.isLine_compatibleRoots` (Lib/PadicComparison/ToricTower.lean).

*Proof sketch.* With one root system of $v$ fixed, the functor of root systems is $\mathrm{Hom}(\mathrm{Per}(c^\flat), (-)^\flat)$, for the perfect ring $\mathrm{Per}$ of periodic sequences. Through tilting, the twist by $(\varepsilon^a)^\sharp$ becomes the shift on periodic sequences. The acyclicity hypothesis and the Wang sequence of the homotopy quotient give both claims. $\square$

**Theorem (Étale over a monoid algebra).** Let $G$ be a commutative monoid that is a module over $\mathbb{Q}_{\ge 0}$, and let $B$ be an $\mathcal{O}_C$-algebra étale over $\mathcal{O}_C[G]$. Assume `CrysPeriodAlgebra`. Then `HasCrysComparison` holds for $\mathrm{Hom}(B, -)$.
Lean: `New.Variety.hasCrysComparison_of_etale` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

**Theorem (Charts).** Assume `CrysPeriodAlgebra`, and let $\mathcal{O}_C$ be an $R$-algebra. Let $t_1, \ldots, t_d$ be units of an $R$-algebra $B$ such that $R[X_1, \ldots, X_d] \to B$, $X_i \mapsto t_i$, is étale. Then `HasCrysComparison` holds for the functor of $R$-algebra maps from $B$ to $\mathcal{O}_C$-algebras.
Lean: `New.Variety.hasCrysComparison_chart` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

*Proof sketch.* Adjoin all roots of the $t_i$. The ring $B' = \mathcal{O}_C[G] \otimes B$ with $G = \mathbb{Q}_{\ge 0}^d$ is étale over $\mathcal{O}_C[G]$, so the previous theorem applies to $B'$. The root systems of each $t_i$ form lines on both sides, by the two results on root systems. One coordinate at a time, the comparison descends from $B'$ to $B$. $\square$

**Theorem (Crystalline classes span).** Let $S$ be a $p$-torsion-free $p$-complete discrete valuation ring with uniformizer $p$. Let $V$ be a subfunctor with `IsCharting V`, and let $i$ identify two reductions of $D/\mathfrak{d}(D)$, over $\mathcal{O}_C$ and over $S$. Suppose that the cohomology of $V$ on $p$-adic tests with coefficients $B_{\max} \otimes D$ is a finite $B_{\max}$-module in every degree. Then in each degree $n$ it is spanned over $B_{\max}$ by the classes pulled back along the crystalline comparison from $H^n$ of $D \mapsto V(D/\mathfrak{d}(D))$.
Lean: `New.Variety.span_range_crysComparison_pull_eq_top` (Lib/PadicComparison/Crystalline/ComparisonMap.lean).

*Proof sketch.* The charting property of Section 4 reduces the claim to charts, where `hasCrysComparison_chart` applies. The finiteness hypothesis then bounds the rank of an independent family of pulled-back classes, which gives the span. $\square$

**Remark (Formalization).** The theorem carries `attribute [-instance] addCommGroupH in`. The instance `New.Variety.addCommGroupH` is equal by definition to the Mathlib group structure on cohomology, with addition through a named constant to avoid time-outs. The attribute removes it for this proof and does not change the statement.

### The congruence relation

**Definition (Weil pairs).** A pair $(s, m)$ with $s \in G_p$ and $m \in \mathbb{N}$ is a Weil pair if $s^{-1}$ is a Frobenius element of degree $p^m$ for the valuation ring of $\overline{\mathbb{Q}}_p$.
Lean: `New.Period.IsWeilPair` (Lib/PadicHodge/Crystalline/Basic.lean).

**Definition (Congruence relation).** Let $u_i : W \to Y$, $a_i \in \mathbb{N}$ and $m_i \in \mathbb{Z}$, and let $\mathfrak{w}$ be a set of elements of $R$. The congruence relation holds if $\sum_i m_i [F^{a_i}(u_i(x))] = 0$ in the free abelian group on points, for every point $x$ of $W$ with values in a field of characteristic $p$ that kills $\mathfrak{w}$. Here $F$ is the Frobenius.
Lean: `New.Variety.CongruenceRelation` (Lib/Cohomology/Etale/Basic.lean).

**Definition (The linear Frobenius).** For a representation $\rho$ on $T$, the operator $\beta_{s,m}$ is a chosen $B_{\max}$-linear endomorphism of $B_{\max} \otimes T$. If some linear map agrees with $\varphi^m s \otimes \rho(s)$ on $D_{\mathrm{pcris}}(\rho)$, then $\beta_{s,m}$ is one such map. In the other case its value is not specified.
Lean: `New.Period.linearFrob` (Lib/PadicHodge/Crystalline/Basic.lean).

**Theorem (Crystalline representation and congruence relation).** Let $R \to K \to \Omega$ with $R$ noetherian and $K$ a field, and let $A$ be the valuation ring of a $p$-adic place of $\Omega$ over $K$ that contains $R$. Let $W$ and $Y$ be proper over $R$ and charted over $\Omega$, and let $Y$ also be charted over $R$. Let $u_i : W \to Y$, $a_i \in \mathbb{N}$, $m_i \in \mathbb{Z}$ and $\gamma_i$ in the decomposition group of $A$ for a finite index set. Suppose that `CongruenceRelation` holds for the prime of the $r \in R$ with valuation less than $1$, and that each $(\gamma_i, a_i)$ is a Weil pair. Let $\rho$ be the representation of the decomposition group on $V^n(Y)$. Then:

1. $\rho$ is crystalline;
2. $\sum_i m_i \, (u_i^* \otimes B_{\max}) \circ \beta_{\gamma_i, a_i} = 0$ on $B_{\max} \otimes V^n(Y)$.

Lean: `New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel` (Lib/PadicComparison/CrystallineFrobenius.lean).

*Proof sketch.* A Frobenius element of the decomposition group gives a Weil pair of positive degree, so the residue ring $k$ of $R$ below the place is a finite field. Choose $x$ and $N$ with $p \mid x^N$ such that a power of $x$ divides the image of the prime. The twisted structure on $A_{\max}$ for $y = x$ gives $k \to A_{\max}/\mathfrak{d}$, and the Witt vector lift gives $W(k) \to A_{\max}$. Take the period map $J$ of Section 5 for $(A_{\max}, B_{\max})$. By Zariski descent the charting subfunctor $V$ is dense, so $J$ followed by restriction to $V$ is an isomorphism. For each crystalline class $z$ choose a period $C(z)$ that maps to its pull-back. A Weil pair $(s, a)$ sends $C(z)$ to the pull-back along $F^a$. The spanning theorem with $S = W(k)$ shows that the $C(z)$ span. The case $a = 0$ makes each $C(z)$ fixed, so $\rho$ is crystalline. The relation on points gives the relation on each $C(z)$. $\square$

**Remark (Formalization).** The operator $\beta_{s,m}$ is defined with `Classical.epsilon`, so part 2 is about the chosen operator. When $\rho$ is potentially crystalline and $(s, m)$ is a Weil pair, `New.Period.linearFrob_apply` shows that $\beta_{s,m}$ acts as $\varphi^m s \otimes \rho(s)$ on $D_{\mathrm{pcris}}(\rho)$, and the docstring of `linearFrob` says that such a map is unique. Part 1 gives this hypothesis, so the choice does not matter. Without part 1, part 2 would say nothing about Frobenius.

**Remark (Formalization).** The steps `choose J` and `choose C` occur only in the proof. $V^n(Y)$ is the $\ell$-adic cohomology of Volume 7 at $\ell = p$. The crystalline property uses $B_{\max}$, not $B_{\mathrm{cris}}$.

**Remark (Formalization).** Volume 8 calls the theorem in `Lib/Shimura/Eigenspace.lean`. At line 674, in `New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient`, it uses part 2. At lines 743 to 746, in `New.Variety.Model.exists_galois_rep`, it uses part 1 with an empty index set, where `CongruenceRelation` holds by simplification.
