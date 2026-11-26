---
title: The other tools
lean:
  - Lib/General/Algebra
  - Lib/General/NumberTheory
decls:
  - New.Variety.IsAbsIntegrallyClosed
  - New.shiftDiff
  - New.free_finite_of_rank_le
  - New.DiscreteModule.IsHigmanProjective
  - New.Variety.algBaseChangeAdj
  - New.expSubst
  - New.rpow_le_norm_factorial
  - New.Rows.places_levelModulus
  - New.Variety.LongExactSeq.Hom.four_lemma
  - New.Variety.LongExactSeq.Hom.five_lemma
  - New.nullstellensatz_exists_le_ker
  - New.exists_le_weight_of_mem_vanishingIdeal_pow
  - New.Variety.perfectRing_of_etale
  - New.DiscreteSeries.eval_derivative_nodal
  - New.norm_coeff_expSubst_le_one
  - New.primePowerSeries
  - New.isCMField_of_forall_exists_conj
  - New.differentIdeal_eq_span_of_dvd
  - New.card_selfAdjoint
  - New.Selmer.gaussVal
  - New.Selmer.gaussVal_mul
  - New.Selmer.le_ellVal_geom_sum
  - New.chiK
  - New.QuadField
  - New.genIndex_det_orthogonal_mul_submoduleIndex_sq
  - New.isAlgebraic_of_norm_complexToCp_le
  - New.SUnit.dirichlet_unit_theorem
  - New.classNumber_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The other tools

The two folders `Lib/General/Algebra` and `Lib/General/NumberTheory` have 26 files and 9,991 lines. Sections 2 to 7 describe six of them: `FittingIdealsAndLengths.lean`, `SharpMinors.lean`, `BlockFittingBound.lean`, `CoefficientRings.lean`, `CoefficientInclusion.lean` and `LargeResidueField.lean`, with parts of `PadicLimitsValuation.lean` and `GaussValuation.lean`. The other files are tools for other volumes. Each one serves a small number of importers, and the chapter that uses a tool is the right place to read it in full. This section gives, for each file, its main declaration, a short statement and its importers. The statements are paraphrases of the docstrings of the source, checked against the Lean statements for the declarations named in a `Lean:` line.

### Algebra for geometry and cohomology

**Absolutely integrally closed rings** (`AbsIntegrallyClosed.lean`, 155 lines). A ring is absolutely integrally closed if every monic polynomial of positive degree has a root. The file defines this property and the power of Frobenius $x \mapsto x^{p^f}$, and it shows that the property passes to subrings that are integrally closed in the ring. The importers are in `Lib/Cohomology`, `Lib/PadicHodge` and `Lib/General`.

Lean: `New.Variety.IsAbsIntegrallyClosed` (Lib/General/Algebra/AbsIntegrallyClosed.lean).

**Adic completion** (`AdicCompletion.lean`, 771 lines). The file has the operator $(x_j) \mapsto (x_j - \pi x_{j+1})$ on sequences, maps of adic completions, the extension of a linear map into an $I$-adically complete module, and a freeness criterion: over a ring complete for a maximal ideal $(p, z)$, a module of bounded rank with the right reduction is free and finite. The docstring refers to `Lib.PadicComparison.Completion` for sources. The importers are in `Lib/PadicHodge` and `Lib/ClassField`, which [the Kisin frames](/chapter/kisin-frames/) and Volume 5 describe.

Lean: `New.shiftDiff`, `New.free_finite_of_rank_le` (Lib/General/Algebra/AdicCompletion.lean).

**Base change for cohomology** (`CohomologyBaseChange.lean`, 305 lines). For a flat module the base change map on cohomology admits dévissage. The file also gives the adjunction for the functor $A \mapsto S \otimes_k A$ on $k$-algebras. The docstring names the Yoneda lemma, the exactness of tensoring with a flat module and the tensor and Hom adjunction as the arguments. [Cohomology as Ext on test rings](/chapter/cohomology-ext/) and [the comparison theorems](/chapter/comparison-theorems/) use it.

Lean: `New.Variety.algBaseChangeAdj` (Lib/General/Algebra/CohomologyBaseChange.lean).

**Long exact sequences** (`LongExactSequences.lean`, 569 lines). The file defines long exact sequences and their morphisms, proves the four and five lemmas for them, and builds the long exact Ext sequences in both variables. It also shows that cohomology commutes with disjoint unions and products. Its only importer is in `Lib/Cohomology`, described in [Cohomology as Ext on test rings](/chapter/cohomology-ext/).

Lean: `New.Variety.LongExactSeq.Hom.four_lemma`, `New.Variety.LongExactSeq.Hom.five_lemma` (Lib/General/Algebra/LongExactSequences.lean).

**Perfect algebras** (`PerfectAlgebras.lean`, 541 lines). Perfect monoid algebras, the perfection of a quotient $B/t$, charts of perfect blowups, and the lifting of étale algebras. An étale algebra over a perfect ring with $p = 0$ is perfect. The docstring refers to `Lib.PadicComparison.Descent.AlmostDescent` for sources. [The comparison theorems](/chapter/comparison-theorems/) use it.

Lean: `New.Variety.perfectRing_of_etale` (Lib/General/Algebra/PerfectAlgebras.lean).

**Multivariate polynomials** (`MultivariatePolynomials.lean`, 440 lines). A weak Nullstellensatz for algebras of finite type, a several-variable Hensel lemma, and a weighted form of the Combinatorial Nullstellensatz with multiplicity: a nonzero polynomial that vanishes to order $d$ at enough suitable points has a monomial of weighted degree at least $d$. The docstring cites Alon, *Combinatorial Nullstellensatz* (1999), and Ball and Serra, *Punctured combinatorial Nullstellensätze* (2009). After `PadicLimitsValuation.lean`, this file has the most importers in the two folders: three in `Lib/Cohomology`, and one each in `Lib/DiscreteSeries`, `Lib/General`, `Lib/Shimura` and `New/UpperBound`.

Lean: `New.nullstellensatz_exists_le_ker`, `New.exists_le_weight_of_mem_vanishingIdeal_pow` (Lib/General/Algebra/MultivariatePolynomials.lean).

**Higman's criterion and the Cartan map** (`CartanMap.lean`, 640 lines). The file reduces statements about finite $\ell$-power torsion discrete $G$-modules to simple cases. Its main result says that a function with values in $\mathbb{Q}_{\geq 0}$ that is multiplicative in short exact sequences is $1$ on a class of finite modules as soon as it is $1$ on the modules with Higman's property. The docstring reads this as the fact that the Cartan map has finite cokernel (Serre, *Linear Representations of Finite Groups*, Theorem 35). Its importer is in `Lib/ClassField`, for local duality and the Greenberg and Wiles cocycle counts.

Lean: `New.DiscreteModule.IsHigmanProjective` (Lib/General/Algebra/CartanMap.lean).

### Power series and moduli

**Integral power series** (`IntegralPowerSeries.lean`, 285 lines). The chain rule for substitutions of power series, the exponential $\exp(a)$ of a power series without constant term, and Legendre's formula in the form $p^{-n/(p-1)} \leq \| n! \|$ for the $p$-adic norm. The importers are in `Lib/CM` and `New/Congruences`.

Lean: `New.expSubst`, `New.rpow_le_norm_factorial` (Lib/General/Algebra/IntegralPowerSeries.lean).

**Series bounds** (`SeriesBounds.lean`, 426 lines). Bounds for the coefficients of integral series. The exponential $\exp(g)$ is integral if $g(0) = 0$ and $v(g) \geq 1/(p - 1)$. The docstring cites Bosch, Güntzer and Remmert, *Non-Archimedean Analysis*, for the equality of the Gauss norm and the supremum norm. The importers are in `Lib/CM`, `New/Congruences` and `New/Derivatives`.

Lean: `New.norm_coeff_expSubst_le_one` (Lib/General/Algebra/SeriesBounds.lean).

**Series congruences** (`SeriesCongruences.lean`, 395 lines). The series $\sum_{i \in I} z^{p^i}$, their products in characteristic $p$, and the continuity of substitution. All three importers are in `New/Derivatives`.

Lean: `New.primePowerSeries` (Lib/General/Algebra/SeriesCongruences.lean).

**Level and modulus** (`LevelModulus.lean`, 392 lines). Moduli $\mathfrak{m}$ of a number field, the places that divide $M^c Q$, and functions of vectors modulo $\mathfrak{m}$ read as Schwartz and Bruhat functions on finite adelic vectors. The docstring refers to `Lib.Weil.MixedModel.ZeroTerm` for sources. The importers are in `Lib/SiegelWeil` and `New/UpperBound`.

Lean: `New.Rows.places_levelModulus` (Lib/General/Algebra/LevelModulus.lean).

**Residue sums** (`ResidueSums.lean`, 113 lines). Sums of $f(x_i)/P'(x_i)$ over the roots of a monic nodal polynomial $P$, by Lagrange interpolation. The one importer is in `New/Appendix`.

Lean: `New.DiscreteSeries.eval_derivative_nodal` (Lib/General/Algebra/ResidueSums.lean).

### Number fields

**CM fields** (`CMFields.lean`, 212 lines). A criterion for a number field to be CM, and presentations of the finite adeles of $L = E[x]/(P)$ for a CM field $E$. [Odd classes](/chapter/odd-classes/) in Volume 3 describes the use.

Lean: `New.isCMField_of_forall_exists_conj` (Lib/General/NumberTheory/CMFields.lean).

**Embeddings and the different** (`EmbeddingsAndDifferent.lean`, 276 lines). Complex conjugation on a CM field, the volume $2^{r_2}/\sqrt{|\operatorname{disc} E|}$, and a criterion for $f'(x)$ to generate the different ideal.

Lean: `New.differentIdeal_eq_span_of_dvd` (Lib/General/NumberTheory/EmbeddingsAndDifferent.lean).

**Frobenius orbits** (`FrobeniusOrbits.lean`, 269 lines). The finite places $w$ of a field $E$ with an involution, their norms $q_w$, the split condition $\bar{w} \neq w$, and the number of self-adjoint elements in a finite field with an involution. It has seven importers, in seven folders.

Lean: `New.card_selfAdjoint` (Lib/General/NumberTheory/FrobeniusOrbits.lean).

**Gauss valuation** (`GaussValuation.lean`, 507 lines). For a radius $\rho$ and $g = \sum y_i Y^i$, the Gauss valuation is $v_\rho(g) = \min_i (v(y_i) + \rho i)$. It is additive on products, and $v(g(y)) \geq v_\rho(g)$ when $v(y) \geq \rho$. The file also has the bound for geometric sums of Section 7. The docstring cites Bosch, Güntzer and Remmert. The importers are in `New/Congruences`.

Lean: `New.Selmer.gaussVal`, `New.Selmer.gaussVal_mul`, `New.Selmer.le_ellVal_geom_sum` (Lib/General/NumberTheory/GaussValuation.lean).

**The imaginary quadratic field** (`ImaginaryQuadraticField.lean`, 588 lines). The Legendre symbol $(\cdot / d)$ as an integer valued character, and the field $\mathbb{Q}(\sqrt{-d})$ for a prime $d \equiv 7 \pmod 8$, with its different and its inertia degrees.

Lean: `New.chiK`, `New.QuadField` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

**Lattice covolumes** (`LatticeCovolumes.lean`, 801 lines, the longest file of the two folders). Determinants of integral matrices, preimage lattices, and Jacobi's identity between a lattice and its dual, used for covolumes of lattices in $(E \otimes \mathbb{R})^n$. The one importer is in `New/Spanning`.

Lean: `New.genIndex_det_orthogonal_mul_submoduleIndex_sq` (Lib/General/NumberTheory/LatticeCovolumes.lean).

**An $\ell$-adic test for algebraicity** (in `PadicLimitsValuation.lean`). If the $\ell$-adic norms of the images of $x \in \mathbb{C}$ under all field isomorphisms $\mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ have a common bound, then $x$ is algebraic over $\mathbb{Q}$. The proof sends a transcendental number to transcendental elements of unbounded norm. The same file has the Teichmüller limits that its docstring traces to Serre, *Local Fields*, Chapter II.

Lean: `New.isAlgebraic_of_norm_complexToCp_le` (Lib/General/NumberTheory/PadicLimitsValuation.lean).

### $S$-units and the class number

Two results of `SUnitsAndClassNumber.lean` (280 lines) are classical theorems, so the handbook states them in full.

**Theorem (Dirichlet's $S$-unit theorem).** Let $K$ be a number field and $S$ a finite set of finite places of $K$. The group of $S$-units of $K$ is finitely generated, and its rank $r$ satisfies
$$r + 1 = \# S + \# \{\text{infinite places of } K\}.$$

Lean: `New.SUnit.dirichlet_unit_theorem` (Lib/General/NumberTheory/SUnitsAndClassNumber.lean).

For $S$ empty this is Dirichlet's unit theorem (Neukirch, *Algebraic Number Theory*, Chapter I, Theorem 7.4). The source deduces it from the unit theorem of Mathlib and the finiteness of the class number. The valuations at $S$ map the $S$-units to $\mathbb{Z}^S$ with kernel the units of $\mathcal{O}_K$, and the image has full rank because a power of each prime of $S$ is principal.

**Remark (Formalization).** The source states the rank as `finrank ℤ (Additive (S.unit K))`, with `S.ncard` for $\# S$. For an infinite $S$, `Set.ncard` would be $0$, a junk value, so the hypothesis that $S$ is finite matters. The theorem has it as `hS : S.Finite`. The statement puts $r + 1$ on the left, so it has no subtraction of natural numbers, which Lean truncates at $0$.

**Theorem (A class number bound).** A number field $F$ of degree $n$ and discriminant $d$ has class number
$$h_F \leq (2^n |d|)^{n+1}.$$

Lean: `New.classNumber_le` (Lib/General/NumberTheory/SUnitsAndClassNumber.lean).

The docstring calls this "a crude consequence of Minkowski's bound". Minkowski's bound is at most $2^n |d|$, so each class has an integral ideal $I$ of norm $k \leq 2^n |d|$. Such an $I$ is $(k, \alpha)$, and only $\alpha$ modulo $k$ matters. There are at most $B \cdot B^n$ pairs $(k, \alpha \bmod k)$ with $B = 2^n |d|$. The bound is far from sharp. The source needs only an explicit bound, not a good one.
