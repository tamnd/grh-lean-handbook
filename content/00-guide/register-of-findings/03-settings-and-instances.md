---
title: Settings and instances
lean:
  - Lib/Speed.lean
  - Lib/Cohomology/Hodge/GrothendieckSymbol.lean
  - Lib/Weil/DualPair/GaloisLaw.lean
  - Lib/General/Algebra/LongExactSequences.lean
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
  - New/OneLift/ComparisonOperator/GluingMaps.lean
  - Lib/Adelic/Adeles/Basic.lean
  - New/Congruences/FitTwistsExist.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/UpperBound/Objects/Rows.lean
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - New/Spanning/Unfolding/Setup.lean
  - New/Congruences/LocalLoss/Basic.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Settings and instances

This section has the findings on the settings of the source: the options of the build, the changes to the instances and to the simp set of Mathlib, the sealed and irreducible definitions, and the instances that the source adds. None of these findings concerns soundness. The kernel checks every proof, whatever the settings of the elaborator were. They concern what a reader sees. A reader who opens a file of the source in a plain session of Lean, or who copies a proof into a project with plain Mathlib, can see other instances, another simp set and other unfoldings. Then a statement that looks the same can elaborate to another term.

The chapter [reading the Lean](/chapter/reading-the-lean/) explains these settings in its section on the settings. The rows below give the places and the counts.

### The global options

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-017, explained | [Lib/Speed.lean:13](lean:Lib/Speed.lean#L13)-47; `grh/lakefile.toml` | `attribute [instance 20]` lowers the priority of 84 instances of Mathlib. Every file imports `Lib/Speed` through `Lib/Base`. The lakefile sets `maxHeartbeats = 4000000` (20 times the default), `maxSynthPendingDepth = 3`, `--tstack=400000` and `autoImplicit = false`. | Instance search in the source differs from plain Mathlib. A reader who builds one file with the default options can get timeouts. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-018, explained | [Lib/Speed.lean:54](lean:Lib/Speed.lean#L54)-69, 72, 76-77 | `attribute [simp ←, simp]` removes 64 lemmas of Mathlib from the default simp set of every importer. Among them are `Nat.card_eq_zero_of_infinite`, `Nat.sub_eq_zero_of_le`, `tsum_empty` and `CharP.cast_eq_zero`. `New.IsVoid` (line 72) is a synonym of `IsEmpty`. A simp lemma of priority 1001 (lines 76-77) rewrites `IsEmpty α` to it and stops there. | A proof replayed in plain Mathlib sees another simp set. Lemmas on junk values do not fire on their own. A reader meets `IsVoid` in goals and must know that it is `IsEmpty`. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-019, open, [issue 17](https://github.com/tamnd/grh-lean-handbook/issues/17) | [Lib/Speed.lean:6](lean:Lib/Speed.lean#L6)-8; `grh/README.md:36`; `grh/GUIDE.md:141` | The documents say that with `Lib/Speed` emptied every file still compiled. This was checked on Lean 4.33.1. The file `lean-toolchain` pins v4.35.0. | The claim is not verified on the pinned version. Soundness does not depend on it, but the claim that the settings only change speed does. | [reading-the-lean](/chapter/reading-the-lean/) |

### Sealed definitions and transparency

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-020, explained | [Lib/Cohomology/Hodge/GrothendieckSymbol.lean:802](lean:Lib/Cohomology/Hodge/GrothendieckSymbol.lean#L802); [Lib/Weil/DualPair/GaloisLaw.lean:48](lean:Lib/Weil/DualPair/GaloisLaw.lean#L48) | The source has 135 lines with `seal` and 3 lines with `unseal`. All but two end with `in`. The two lines `seal H.map` and `unseal finitePart` have no `in` and act to the end of their files. | Sealing changes what `rfl` and `simp` can see. The two lines without `in` change a whole file. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-021, explained | [Lib/General/Algebra/LongExactSequences.lean:336](lean:Lib/General/Algebra/LongExactSequences.lean#L336); [New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean:549](lean:New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L549); [New/OneLift/ComparisonOperator/GluingMaps.lean:344](lean:New/OneLift/ComparisonOperator/GluingMaps.lean#L344), 361, 948 | The option `backward.isDefEq.respectTransparency false` occurs on 33 lines. The 5 lines with `in` are all in `New`: three in `GluingMaps`, one in `PeriodsOfFalseLifts` and one in the file `BaseLevelOfLabel.lean` (line 65). The 28 lines without `in` are all in `Lib`, 20 of them in `Lib/Cohomology`, and act to the end of their section or file. | Unification then unfolds past the usual transparency. A lemma can elaborate in a way that a plain session does not reproduce. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-031, explained | [New/Spanning/Unfolding/Setup.lean:647](lean:New/Spanning/Unfolding/Setup.lean#L647); `New/Spanning/RemainingTerms/SiegelLemma.lean:158`; [New/Congruences/LocalLoss/Basic.lean:117](lean:New/Congruences/LocalLoss/Basic.lean#L117)-118; `Lib/Weil/Construction/AdelicRepresentation.lean:154`; `New/Spanning/RemainingTerms/SchurOrbit.lean:794`; `New/UpperBound/Seesaw/UnfoldingStages.lean:705` | 15 definitions are `@[irreducible]`, for example `classCutoff`, `sublatticeBasis` and `crystallineLoss` (the definition is at line 118). `synthInstance.maxSize 999` has no `in` and acts to the end of its file. `SchurOrbit` and `UnfoldingStages` raise `synthInstance.maxHeartbeats` and `synthInstance.maxSize` with `in`. | Only the lemmas next to an irreducible definition reach its content. Some files need a larger instance search to compile. | [reading-the-lean](/chapter/reading-the-lean/) |

### Instances that the source adds

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-022, explained | many files | The source has 35 lines of global `attribute [instance ...]`, one of them in `Lib/Speed`. It has 83 lines of `attribute [local instance ...]` and 3 lines of `attribute [-instance ...]`. | A global attribute outlives its file and acts in every importer. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-023, open | `Lib/Cohomology/Etale/BijectiveComparisons.lean:671`; `Lib/DiscreteSeries/Haar/CayleyChart.lean:379`; `Lib/Adelic/Adeles/Basic.lean:75`; `Lib/GaloisRep/TaylorWiles.lean:93`; `Lib/ClassField/Places/ProfiniteGalois.lean:38`; `Lib/General/NumberTheory/CoefficientRings.lean:30`; `Lib/Shimura/AbelianScheme/Basic.lean:54`, 66 | Global instances: `subsingleton_of_projective`, `measureSpaceU`, a default `PlaceEmbedding E` of low priority, `TaylorWilesPlaces.apart`, and `IsAlgClosure K Ω` for every field $K$ of characteristic $0$. Priority 10 for instances on subalgebras. A global `Hom.addCommGroup` and a reducible instance `ModuleObj.homModule`. | None is unsound. Each can decide which instance a later statement uses, in every importer. It is not checked whether a statement of `New` picks up one of them. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-024, open | `Lib/Weil/Periods/DescentVanishing.lean:137`; `Lib/PadicComparison/Descent/TestCategory.lean:358`, 360; `Lib/PadicComparison/Primitive/Periods.lean:55` | A global `MulAction` of low priority on matrices, column by column. Global instances `Algebra Ainf OFlat` and `Algebra Ainf OC`. A local `Algebra ℤ_[p] b` through `compHom`. | These can form diamonds with instances of Mathlib. No one has checked that they do not. | [reading-the-lean](/chapter/reading-the-lean/), [comparison-theorems](/chapter/comparison-theorems/) |
| F-025, open | [Lib/Adelic/Adeles/Basic.lean:96](lean:Lib/Adelic/Adeles/Basic.lean#L96); [New/Congruences/FitTwistsExist.lean:463](lean:New/Congruences/FitTwistsExist.lean#L463)-464 | A global `DecidableEq (InfinitePlace E) := Classical.decEq _`. In `FitTwistsExist` a `convert` is needed because two `DecidableEq` instances agree only propositionally. | Mixed instances of decidability block `rfl` and `rw`. It is not known whether the same mismatch occurs elsewhere. | [reading-the-lean](/chapter/reading-the-lean/), [proof-of-regular-families](/chapter/proof-of-regular-families/) |
| F-026, explained | `New/Derivatives/Field/ChosenPlaces.lean:58`; `New/Determinant/Chain/NormOfChain.lean:51`; `New/Spanning/MainTerm/BadTypes.lean:40`; `New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean:65`, 67 | `attribute [local instance low] Fintype.ofFinite`. `AuxiliaryPrimeTie` also gives priority 1100 to two instances of hom classes. | `Fintype.ofFinite` uses choice. Its `Finset.univ` is not definitionally equal to that of another `Fintype` instance. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-027, open | [New/Reduction/Lattices/TwistedLattice.lean:138](lean:New/Reduction/Lattices/TwistedLattice.lean#L138); [New/OneLift/ComparisonOperator/GluingMaps.lean:65](lean:New/OneLift/ComparisonOperator/GluingMaps.lean#L65)-68 | Fields of a structure become instances: `normedAddCommGroup`, `innerProductSpace`, `fintypeCoord`. `GluingMaps` puts a norm and an inner product on `SecondFactorFormValues` from the positive definite Weyl Gram matrix `weylGramOver_posDef`. | The inner product is not the obvious one. It is not checked whether it is the Petersson product. | [twisted-lattices](/chapter/twisted-lattices/), [comparison-operator-1](/chapter/comparison-operator-1/) |
| F-028, explained | [New/Reduction/Data/Magnitudes.lean:49](lean:New/Reduction/Data/Magnitudes.lean#L49), 164; [New/UpperBound/Objects/Rows.lean:528](lean:New/UpperBound/Objects/Rows.lean#L528) | `HasLogBound D u F l` has `l` as an `outParam`, so instance search computes the exponent. `attribute [grind! .]` is put on `le_constantBound`, `r_odd` and `m_even`. `Rows` removes `m_even` from `grind` again. | Many proofs of sizes are found by instances and by `grind`, not written. The book must state the bounds that the automation finds. | [reading-the-lean](/chapter/reading-the-lean/), [data-and-sizes](/chapter/data-and-sizes/) |
| F-029, explained | `grh/GUIDE.md:153`, 155 | Some data are classes: `ThePrime p`, `PadicIso ℓ`, `CMType E`, `WeilData E`. Statements do not name them. A hypothesis written `(h : ... := by tac)` is proved by `tac` when the caller omits it. | A reader must find the hidden data of each statement. A call site does not show these hypotheses. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-030, open | [Lib/DiscreteSeries/FlenstedJensen/Defs.lean:161](lean:Lib/DiscreteSeries/FlenstedJensen/Defs.lean#L161); [New/UpperBound/Objects/Rows.lean:481](lean:New/UpperBound/Objects/Rows.lean#L481) | `class HasGap (h : outParam ℕ)`: instance search fixes the gap. `Rows` gives the instance `hasGap_paramW` with the gap `D.gap`. | The gap that search finds may differ from the one that a statement intends. No one has checked each use. | [discrete-series](/chapter/discrete-series/), [upper-bound-objects](/chapter/upper-bound-objects/) |

### How to use these rows

A reader who only reads statements needs little from this section. The settings change how Lean finds a proof, not what the kernel accepts. Three rows can change what a statement means to a reader.

The first is F-018. A reader who sees `IsVoid α` in a goal or in a hypothesis must read it as `IsEmpty α`. The two are the same proposition, by `.rfl`, so the change is only of the name.

The second is F-028, together with F-029 and F-030. Here an argument of a statement is not written by the caller. It is found by instance search or filled by a tactic. The statement as printed then hides a number, such as the exponent `l` of a bound `HasLogBound D u F l`, or the gap of `HasGap`. A reader who wants the size must find the instance that search uses. For `HasGap` the register marks this as open, because the gap that search finds in a given context has not been checked against the gap that each statement intends.

The third is the group F-023 to F-027. A global instance of the source can be found in a statement of a file far from its own. Two different instances of one class can then meet, and a reader can see two terms that print alike and are not definitionally equal. The register marks four of these rows as open, because no one has checked that a statement of `New` meets such a diamond. The row F-025 shows one real case, where a `convert` closes the gap.
