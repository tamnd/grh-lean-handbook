---
title: The map of the files
lean:
  - New/Congruences/FitTwistsExist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the files

The folder `New/Congruences` has 53 Lean files with 34,811 lines in total, counted with `wc -l`. It has one top file and five subfolders. This section lists the files of each subfolder with their line counts and the first heading of their module docstrings, and it gives the chapter of this volume that treats each part.

### The top file and the imports

The top file is [FitTwistsExist.lean](lean:New/Congruences/FitTwistsExist.lean#L1), with 535 lines. It proves the theorem on regular families and every step of Sections 3, 5 and 6 that is not imported. It imports five files:

1. `New.Congruences.FirstOrder.DenominatorBound`, for Ribet's method and the bound for denominators;
2. `New.Congruences.GaloisRepresentations.RowsFromEigensystems`, for the main summands of the lifts;
3. `New.Congruences.Selmer.TwistingTheorem`, for the twisting theorem;
4. `New.Determinant.Chain.NormOfChain`, a file on chain determinants from outside the folder;
5. `New.OneLift.HeckeValues.CentralAction`, from Volume 11, for the bound on the line of a main pair.

The definitions of Section 3, in `New/Determinant/Twist/FitTwists.lean`, come in through these imports, not directly.

The subfolders depend on each other in one direction. The files of `Lifting` are imported by `LocalLoss` (through `LocalLoss/CrystallineCocycles.lean`). The files of `LocalLoss` are imported by `GaloisRepresentations/SelmerHypotheses.lean`, by `FirstOrder/FittingBlock.lean` and `FirstOrder/TraceRelations.lean`, and by `Selmer/MainSummands.lean`. The three folders `FirstOrder`, `GaloisRepresentations` and `Selmer` meet in the top file.

### The order of the chapters

The chapters of the volume follow the imports of the files: each file of a chapter imports only files of earlier chapters or of other volumes, with the exceptions below. The list gives each chapter with the chapters of this volume that its files import.

```
 1 regular-families-plan      <- 5, 10, 11
 2 ribet-elements             <- 5, 11
 3 first-order-deformations   <- 2, 4, 5
 4 tied-traces                <- 2
 5 main-summands              <- 4
 6 tied-selmer-groups         <- 4
 7 exponent-lattices          <- (Vol 5, 7)
 8 cup-products               <- 7
 9 local-loss                 <- 5, 8
10 twisting-theorem           <- 4, 5, 6, 9
11 denominator-bound          <- 2, 3, 4, 5, 9
12 proof-of-regular-families  <- 1
```

Chapters 1, 2 and 3 use results of later chapters. This chapter follows the top file, which imports the last steps (chapters 5, 10 and 11). In chapter 2, `FittingBlock.lean` imports `LocalLoss/Basic.lean` (chapter 5), and `RibetElement.lean` imports `TraceRelations.lean` (chapter 11). In chapter 3, `KummerMaps.lean` imports `EvenClasses.lean` and `AuxiliaryPrimeTie.lean` imports `TiedTraces.lean` (chapter 4), and `HeckeStrings.lean` imports `SelmerHypotheses.lean` (chapter 5). A reader of these chapters takes the results of the later chapters as known.

### FirstOrder: Ribet's method to first order

The folder has 15 files and 10,789 lines. It builds Ribet's element for a conjugate self-dual representation, the first-order deformations at auxiliary places, and the bound for denominators of Section 4. The chapters are [Ribet elements](/chapter/ribet-elements/), [first order deformations](/chapter/first-order-deformations/), [tied traces and even classes](/chapter/tied-traces/) (for `OnePrime`, `TiedTraces`, `EvenClasses` and `TateTwistCocycles`) and [the bound for denominators](/chapter/denominator-bound/) (for `TraceRelations` and `DenominatorBound`).

| File | Lines | First heading |
|---|---|---|
| RibetMethod | 563 | Amitsur's formula and Ribet's method for matrices over an algebra |
| FittingBlock | 763 | Modules of functions, Fitting ideals and trace ideals for Ribet's method |
| RibetMatrices | 1,017 | Tied rows and the matrices of Ribet's method to first order |
| RibetLemma | 685 | Ribet's method to first order over a discrete valuation ring |
| RibetElement | 420 | Ribet's element for conjugate self-dual representations |
| TrianglePrimes | 706 | Taylor-Wiles places in a triangle for the even classes, with prescribed Frobenii |
| KummerMaps | 866 | Kummer maps |
| HeckeStrings | 496 | Chains of roots for weak lifts, and Hecke-stable subspaces of forms |
| AuxiliaryPrimeTie | 714 | The family of operators at the auxiliary places |
| TiedTraces | 816 | Tied traces and the dictionary at one auxiliary place |
| OnePrime | 865 | Norms, logarithms and first-order deformations of the norm |
| EvenClasses | 264 | Even classes and auxiliary places for Selmer cocycles |
| TateTwistCocycles | 299 | Cocycles of Tate twists: the even part and the triangle cost |
| TraceRelations | 982 | Constants, trace relations, lattices and local defects for Ribet's method |
| DenominatorBound | 1,333 | The bound for denominators |

The constants of Section 5 are in `TraceRelations.lean`, except the twist error, which is in `GaloisRepresentations/SelmerHypotheses.lean`, and the defect bound and the crystalline loss, which are in `LocalLoss/Basic.lean`. The definition `IsAuxTwist` is in `EvenClasses.lean`. The lift generators and the two theorems of Section 4 are in `DenominatorBound.lean`.

### GaloisRepresentations: the main summands

The folder has 5 files and 3,432 lines. It attaches Galois representations to the eigensystems of the lifts, and it proves that they have main summands. The chapter is [main summands](/chapter/main-summands/), which also treats `LocalLoss/Basic.lean`.

| File | Lines | First heading |
|---|---|---|
| AttachedRepresentations | 704 | Lift settings and conjugate self-duality of attached Galois representations |
| BaseLevelOfLabel | 663 | Base data whose forms contain those with given labels in a lift setting |
| RowsAndColumnsFromLabels | 762 | Main summands and conjugate self-dual representations from type polynomials |
| RowsFromEigensystems | 564 | Main summand conditions on Hodge-Tate jumps and existence of main summands for Hecke eigensystems |
| SelmerHypotheses | 739 | Bad places, ℓ-adic avatars and hypotheses on conjugate self-dual representations |

The file `SelmerHypotheses.lean` holds the definitions that the rest of the volume shares: the bad places, the twist error, `IsMainSummandLike`, `HasDivisibleSelmerLengthLe`, `HasLiftTrace` and `IsMainSummand`. It is also the only file of the folder that Volume 11 imports, through `New/OneLift/HeckeValues/TwistedValueHeights.lean`.

### Selmer: tied Selmer groups and the twisting theorem

The folder has 16 files and 8,446 lines. It proves the twisting theorem: first a general form for Selmer data, then the form for main summands and Stickelberger systems. The chapters are [tied Selmer groups](/chapter/tied-selmer-groups/) and [the twisting theorem](/chapter/twisting-theorem/).

| File | Lines | First heading |
|---|---|---|
| AuxiliaryPrimes | 496 | Auxiliary primes, anticyclotomic characters, slopes and ties |
| SelmerData | 721 | Selmer data, tied Selmer groups and classes as functions |
| MainSummands | 354 | Main summands are Selmer data |
| OneSystem | 473 | The universal twist and one system of equations for all twists |
| Untied | 578 | The failure to be tied |
| Descent | 704 | The descent |
| Count | 559 | The dual of a tied Selmer group and the count |
| Mirror | 707 | Reciprocity at conjugate primes |
| ClassSums | 477 | L-values of a pair as integral measures, and avatars of tame characters |
| LValueSystems | 408 | The Stickelberger systems of the L-values |
| StickelbergerSystems | 324 | Stickelberger systems |
| StickelbergerLine | 539 | Stickelberger systems on a line |
| Line | 686 | Restriction to a line |
| RootsOfUnity | 513 | Roots of unity with polynomials hardly more divisible at $\zeta - 1$ than at given points |
| GeneralTheorem | 456 | Twisting, general form |
| TwistingTheorem | 451 | The twisting theorem |

The lemma `coprime_prod_q_of_isAuxiliary`, which the top file uses for the coprimality of the modulus, is in `ClassSums.lean`. The file `AuxiliaryPrimes.lean` is in [tied traces and even classes](/chapter/tied-traces/). The chapter on tied Selmer groups has `SelmerData`, `Count`, `OneSystem`, `Mirror`, `Untied` and `Descent`. The chapter on the twisting theorem has the other nine files. It comes after the local loss, since `MainSummands.lean` imports `LocalLoss/LocalLattices.lean`.

### LocalLoss: the local loss above ℓ

The folder has 5 files and 2,524 lines. It bounds the defect of the crystalline condition at the places above $\ell$, which gives the term $\mathrm{localDefectBound}$ of Section 5. The chapter is [the local loss](/chapter/local-loss/), for all files but `Basic.lean`, which is in [main summands](/chapter/main-summands/).

| File | Lines | First heading |
|---|---|---|
| Basic | 661 | Local loss above ℓ: main summand weights, b-places, crystalline relations and crystalline colength |
| CrystallineCocycles | 649 | Crystalline cocycles and the defect of a crystalline lattice at a place above ℓ |
| CrystallineDefect | 669 | The defect of the dual of a summand at a place above ℓ |
| LocalLattices | 273 | Tame classes from roots of unity and lattices read at a place above ℓ |
| TateDualBound | 272 | A bound for non-crystalline cocycles modulo $\ell^m$ by the Tate dual lattice |

### Lifting: cup products on Kisin modules

The folder has 11 files and 9,085 lines. It is the largest part of the local argument. It bounds cup products of cocycles on the sides of a Kummer chart, with lattices, depths and jumps. The chapters are [exponent lattices and Kummer charts](/chapter/exponent-lattices/) (`ExponentLattices`, `HodgeExpansion`, `CupProductBound`, `SidePoints`, `TameCharts`) and [cup products](/chapter/cup-products/) (the other six files).

| File | Lines | First heading |
|---|---|---|
| CupOrthogonalityBounds | 600 | From sides to lattices: few low jumps, b-letters and tame types |
| CupProductBound | 1,248 | Sides of a pairing, cokernel killers and the pairing lemma for cup products |
| CutExponentBounds | 1,052 | Exponent bounds by cuts for paired sides of a Kummer chart: sparse thick letters, two sizes |
| DeepPoints | 411 | Deep points and scaled cup coboundaries for a gap below zero or nonpositive jumps |
| ExponentLattices | 1,184 | Lattices with prescribed orders, depth steps and the depth lemma |
| FewLowJumps | 1,030 | Few low jumps: length lost to depth and a submodule cupping to zero |
| HodgeExpansion | 774 | Exponents of lattice elements in a Hodge basis and the length of one step on a line |
| LongGap | 477 | The long gap lemma for a side of a Kummer chart, by expansion in powers of E |
| SafeMoves | 826 | Safe moves and the walk for pairings of sides of a Kummer chart |
| SidePoints | 845 | Jump windows, the gap condition and points of the sides of a Kummer chart |
| TameCharts | 638 | Tame Kummer charts and the power of p that kills cokernels of Kisin modules |

### The totals

The five subfolders have $10{,}789 + 3{,}432 + 8{,}446 + 2{,}524 + 9{,}085 = 34{,}276$ lines, and with the 535 lines of the top file the folder has 34,811 lines. About a third of the lines are in the local argument (`LocalLoss` and `Lifting`, 11,609 lines). Ribet's method and the twisting theorem have about 19,000 lines together. The top file, which this chapter follows in full, is less than 2 percent of the folder.

[The proof of the existence of regular families](/chapter/proof-of-regular-families/), the last chapter of the volume, puts the parts together and follows the top file again with all the inputs proved.
