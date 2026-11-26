---
title: Junk values and chosen objects
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - Lib/Adelic/TraceFormula/TraceComparison.lean
  - Lib/Adelic/AutomorphicForms/Basic.lean
  - Lib/Adelic/Hecke/Basic.lean
  - New/Determinant/Chain/TriangleNorms.lean
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/CM/KroneckerLimit.lean
  - Lib/ClassField/HeckeL/EulerProduct.lean
  - New/Reduction/ShortAndEnough.lean
  - New/Derivatives/Vacuum/IntegralVacuum.lean
  - New/Derivatives/Field/WeilData.lean
  - New/Congruences/LocalLoss/Basic.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
  - Lib/Adelic/QuotientMeasure/Basic.lean
  - Lib/ClassField/Local/ArtinMap.lean
  - Lib/ClassField/Global/ArtinMap.lean
  - Lib/GaloisRep/Main/AllRanks.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Junk values and chosen objects

Mathlib makes every function total. A division by $0$ gives $0$. A sum `∑'` of a family that is not summable gives $0$. A Bochner integral of a function that is not integrable gives $0$. A `finsum` or a `finprod` with infinite support gives $0$ or $1$. These values are called junk values. They keep statements short, and they are sound. But a definition with a junk value can mean less than its name says, and an identity between two junk values says nothing. The chapter [reading the Lean](/chapter/reading-the-lean/) explains the conventions with examples.

A related kind of definition picks an object by choice. `Classical.choose h` picks a witness of a proof `h` of an existence statement. `Classical.epsilon P` picks an element that satisfies `P` if one exists, and an arbitrary element otherwise. Such an object has only the properties that the lemmas next to it prove. It has no formula, and a reader cannot compute it.

This section lists the definitions of both kinds where a reader must be careful. The first table has the junk values, and the second the chosen objects.

### Junk values

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-032, explained | [New/Spanning/Unfolding/Setup.lean:669](lean:New/Spanning/Unfolding/Setup.lean#L669)-671, 680-682 | `amplitude` is a Bochner integral. It is $0$ if the integrand is not integrable. `amplitudeSum` is a `tsum`. It is $0$ if the family is not summable. | An identity that exchanges sums and integrals needs explicit summability. Without it both sides can be $0$. The source proves the summability with a majorant. | [reading-the-lean](/chapter/reading-the-lean/), [moments](/chapter/moments/) |
| F-033, explained | [New/Determinant/Twist/FitTwists.lean:78](lean:New/Determinant/Twist/FitTwists.lean#L78)-80; [New/OneLift/HeckeValues/TwistedRatio.lean:160](lean:New/OneLift/HeckeValues/TwistedRatio.lean#L160), 209 | `CriticalPair.ratio` is a quotient of two norms of L-values. It is $0$ if the denominator is $0$. `algPart_pos` (line 160) and `ratio_eq_algPart_div` (line 209) give the ratio as a quotient of two positive numbers. | The positivity comes back through the algebraic part, not through the definition. | [reading-the-lean](/chapter/reading-the-lean/), [hecke-values](/chapter/hecke-values/) |
| F-034, explained | [Lib/DiscreteSeries/FlenstedJensen/Defs.lean:93](lean:Lib/DiscreteSeries/FlenstedJensen/Defs.lean#L93), 197 | `weightMinors` is a `finprod` of quotients by `det g`. For a singular $g$ each factor is a division by $0$. Then infinitely many factors can be $0/0 = 0$, the support is infinite, and the `finprod` is $1$ by convention. `formalDegree` (line 197) is the inverse of an integral, so it is $0$ if the integral diverges or is $0$. | The formal degree is positive only after a proof of square integrability. The minors have a meaning only on invertible matrices. | [discrete-series](/chapter/discrete-series/) |
| F-035, explained | [Lib/Adelic/TraceFormula/TraceComparison.lean:665](lean:Lib/Adelic/TraceFormula/TraceComparison.lean#L665), 680-681 | `trace_comparison` equates `LinearMap.trace` on two spaces `levelSpace`. The trace of Mathlib is $0$ on a space that is not finite-dimensional. | The result has content only where the spaces are finite-dimensional. The book must say where that is proved. | [trace-formula](/chapter/trace-formula/) |
| F-036, explained | [Lib/Adelic/AutomorphicForms/Basic.lean:120](lean:Lib/Adelic/AutomorphicForms/Basic.lean#L120)-124; [Lib/Adelic/Hecke/Basic.lean:73](lean:Lib/Adelic/Hecke/Basic.lean#L73) | In `IsForm`, if the function $e$ is not integrable, the convolution condition is empty. Then every bounded automorphic function is a form of type $e$. `heckeFun` is a `finsum` over $G/K$ with representatives `q.out`. A `finsum` is $0$ if the support is infinite. | The space of forms is large unless $e$ is integrable. The Hecke operator is the one of the textbook only for finite support. | [automorphic-forms](/chapter/automorphic-forms/) |
| F-037, explained | [New/Determinant/Chain/TriangleNorms.lean:141](lean:New/Determinant/Chain/TriangleNorms.lean#L141), 385-390 | `SquareCommutes` (line 141) divides by `conj β'`. If `β' = 0` the factor is $0$. `ne_zero_of_squareCommutes` (line 390, with its docstring at lines 385-389) then proves that `β'` has no zero, from the injectivity of the maps. | Nonvanishing comes from the chain, not from the identity. | [chain-determinant](/chapter/chain-determinant/) |
| F-038, explained | [New/Determinant/Twist/FitTwists.lean:100](lean:New/Determinant/Twist/FitTwists.lean#L100), 126; [New/OneLift/HeckeValues/CharacterLiftNorm.lean:64](lean:New/OneLift/HeckeValues/CharacterLiftNorm.lean#L64) | `RankOneIndex z` ends in `Fin (2 * z - 20)`, with subtraction in $\mathbb{N}$. `HasLiftRank` asks that the type has $2z$ elements and that $2 \leq z$. So the field at line 126 forces $z \geq 10$. | Truncated subtraction hides a bound. The main pairs have $z > m$ with $m \geq 10000$, so nothing is lost. | [reading-the-lean](/chapter/reading-the-lean/), [twists-critical-pairs](/chapter/twists-critical-pairs/) |
| F-039, explained | [New/Reduction/Zeros/PrimeError.lean:410](lean:New/Reduction/Zeros/PrimeError.lean#L410) | The docstring says that the residue formula at $s = 1$ is a "division by zero, of value 0". The function has no pole there. The lemma `isPolar_primeRemainder` follows at line 414. | The value at $1$ is correct only by the junk convention. | [weighted-prime-remainder](/chapter/weighted-prime-remainder/), [polar-functions](/chapter/polar-functions/) |
| F-040, explained | [Lib/CM/KroneckerLimit.lean:332](lean:Lib/CM/KroneckerLimit.lean#L332); [Lib/ClassField/HeckeL/EulerProduct.lean:63](lean:Lib/ClassField/HeckeL/EulerProduct.lean#L63)-74 | In the Kronecker limit formula the term $l = 0$ is $0$, since `0 ^ (-s) = 0` in Lean. `heckeCoeff` (lines 63-64) is $0$ on $S$. `eulerProd` (lines 72-74) is extended from $(1, \infty)$. Its docstring (lines 66-71) says that for $s < 1$ it "has no meaning". | The sum is over all $l$, not over $l \neq 0$ as in the textbook. Values of `eulerProd` below $1$ are junk. | [cm-elliptic-curves](/chapter/cm-elliptic-curves/), [class-field-theory](/chapter/class-field-theory/) |
| F-140, open | [Lib/Adelic/TraceFormula/TraceComparison.lean:665](lean:Lib/Adelic/TraceFormula/TraceComparison.lean#L665); line 25 | `New.trace_comparison` asks for both `[HasPrimitiveRoot5040 E]` and `hE : Even (Core.numInfPlaces E)`. In mathematics the first gives the second: $\varphi(5040) = 1152$ divides the degree of $E$, so the number of infinite places of a CM field $E$ is even. The source has no lemma that derives `hE` from the root of unity. | The hypothesis `hE` is redundant in mathematics. In the source it is a separate hypothesis that each user must discharge. | [adeles-hermitian-spaces](/chapter/adeles-hermitian-spaces/) |

### Chosen objects

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-041, explained | `grh/GUIDE.md:136` | Many objects come from `choose` or `epsilon`. The source has 307 lines with `.choose` or `Classical.epsilon`, 67 of them with `epsilon`. | Such an object has only the properties of the lemmas next to it. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-042, open | [New/Reduction/ShortAndEnough.lean:41](lean:New/Reduction/ShortAndEnough.lean#L41), 170; [New/Derivatives/Vacuum/IntegralVacuum.lean:280](lean:New/Derivatives/Vacuum/IntegralVacuum.lean#L280) | `divisibilityError` is `exists_err_gaugeLe_compositeLift.choose`. `seesawConst` is `(seesaw_identity besselForm besselPoint).choose`. `vacuumBoundConst (P : Parameters) : ℕ` is a `choose`. By its type it depends only on $P$. | The book needs the statements behind these constants in human form. The type of `vacuumBoundConst` shows that it does not depend on the data. | [theorems-a-b-c](/chapter/theorems-a-b-c/), [data-and-sizes](/chapter/data-and-sizes/) |
| F-043, open | [New/Derivatives/Field/WeilData.lean:420](lean:New/Derivatives/Field/WeilData.lean#L420)-422 | `instWeilDataE` picks a splitting character with `.some`. | It is not known whether any statement depends on the pick. | [field-at-primes](/chapter/field-at-primes/) |
| F-044, open | [New/Congruences/LocalLoss/Basic.lean:491](lean:New/Congruences/LocalLoss/Basic.lean#L491) | `instance localChart` is a chosen `PadicPlaceEmbedding`. | If another embedding is built elsewhere, the two must agree. No comparison has been found. | [local-loss](/chapter/local-loss/) |
| F-045, explained | [New/Congruences/FirstOrder/TraceRelations.lean:74](lean:New/Congruences/FirstOrder/TraceRelations.lean#L74)-75 | `oddClassBound` is `(exists_length_shaOdd_le ...).choose`. | It is the only place where the size of the odd classes enters. | [denominator-bound](/chapter/denominator-bound/) |
| F-046, open | [New/Spanning/Unfolding/Setup.lean:647](lean:New/Spanning/Unfolding/Setup.lean#L647)-648; `New/Spanning/RemainingTerms/SiegelLemma.lean:158-159` | `classCutoff` and `sublatticeBasis` are chosen and irreducible. | The book must say which lemmas pin them down. | [poincare-series](/chapter/poincare-series/), [remaining-terms](/chapter/remaining-terms/) |
| F-047, explained | [Lib/Adelic/QuotientMeasure/Basic.lean:75](lean:Lib/Adelic/QuotientMeasure/Basic.lean#L75) | `chosenCutoff := Classical.epsilon (IsCutoff ν)`. It is an unspecified function if no cutoff exists. | Each lemma about it must first prove that a cutoff exists. | [reduction-theory](/chapter/reduction-theory/) |
| F-048, explained | [Lib/ClassField/Local/ArtinMap.lean:124](lean:Lib/ClassField/Local/ArtinMap.lean#L124)-131; [Lib/ClassField/Global/ArtinMap.lean:218](lean:Lib/ClassField/Global/ArtinMap.lean#L218) | `artinMap` (line 129) is an `epsilon`. Its docstring says: "This file does not prove that such an f exists". The docstring is out of date. The file `Global/ArtinMap.lean` imports this file and proves `New.abelianLift_artinMap_eq_finprod` (line 218) for the same `artinMap`, with no extra hypothesis. | A stale docstring, not an open gap. Cite the product formula of the global file, not the docstring. | [class-field-theory](/chapter/class-field-theory/) |
| F-049, explained | [Lib/GaloisRep/Main/AllRanks.lean:623](lean:Lib/GaloisRep/Main/AllRanks.lean#L623)-624 | `Isotypic.galRep := Classical.epsilon (Attached ...)`. It is arbitrary if no attached representation exists. | The Galois representation is a chosen object with the weak property of F-053. | [attached-representations](/chapter/attached-representations/) |
| F-050, explained | `Lib/Weil/Construction/AdelicRepresentation.lean:808-809`; `Lib/Weil/MixedModel/NamedData.lean:78`; `Lib/Weil/Lift.lean:269-270` | `lineTheta` and `schrodingerOp` use `choose`. `jointHarmonicAt` is an `epsilon`, and it is an arbitrary polynomial if none exists. | The Weil representation is built from chosen pieces. | [weil-representation](/chapter/weil-representation/) |
| F-051, explained | `Lib/PadicHodge/Crystalline/Basic.lean:224-225`; `Lib/GLn/SchurModule/Basic.lean:177-178`; `Lib/Cohomology/Hodge/GrothendieckSymbol.lean:941-942`; `Lib/CM/Sigma/Basic.lean:469-470` | `linearFrob` (in place of a Weil-Deligne representation), `BasisTableau` (which need not be semistandard) and `pointClass` are `epsilon` definitions. The sigma function `PeriodPair.σ` is a `choose`. | Each has only the properties of its existence lemma. | [period-rings](/chapter/period-rings/), [weyl-modules](/chapter/weyl-modules/), [cm-elliptic-curves](/chapter/cm-elliptic-curves/) |

### How to read a junk value

A row of the first table asks one question of a reader: where does the content come back? For each row the answer is a lemma of the source, or an open question.

For F-032 the content comes back through a majorant. The integral `New.Filling.amplitudeMajorant` takes values in $[0, \infty]$ and so has no junk value, and a lemma proves that the sum of the majorants is finite. Then summability and integrability follow, and the exchange of sum and integral is a real identity.

For F-033 the content comes back through the algebraic part. The ratio is a quotient of two norms. Its definition does not exclude a zero denominator. The lemma `ratio_eq_algPart_div` rewrites it as a quotient of two algebraic parts, and `algPart_pos` proves that each is positive.

For F-037 the content comes back through the injectivity of the maps of the chain. The factor $\beta'$ in the definition of `SquareCommutes` can be $0$ in principle, and then the condition says nothing. The lemma `ne_zero_of_squareCommutes` proves that this does not happen. Section 6 shows that the proof uses another form of the same argument (F-121).

For F-035 and F-036 the content comes back through finite dimension and finite support. A chapter that uses these definitions must cite the lemma that proves the finiteness, or say that the result is used only in a form that does not need it.

For F-038, F-039 and F-040 the junk value is harmless. In F-038 the bound $z \geq 10$ is weaker than the size of the main pairs. In F-039 the function has no pole at $s = 1$, and the formula gives there the value of the convention. In F-040 the extra term $l = 0$ is $0$.
