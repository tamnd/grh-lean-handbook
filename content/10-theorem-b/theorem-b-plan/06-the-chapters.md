---
title: The chapters of this volume
lean:
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapters of this volume

The volume has fourteen chapters. The order of the chapters is the order of the Lean files: each file of a chapter imports only files of earlier chapters or of other volumes, with the exceptions below. The list gives each chapter with the chapters of this volume that its files import.

```text
 2 few-translates        <- (earlier volumes)
 3 equal-multiplicities  <- 11
 4 bessel-real-place     <- 6, 7, 10, 12
 5 local-frames          <- 4
 6 real-densities        <- 4, 5
 7 anatomy-of-a-term     <- 4
 8 finite-densities      <- 5, 7
 9 frame-counts          <- 7
10 poincare-series       <- 4, 9
11 remaining-terms       <- 4, 7, 9, 10
12 main-term             <- 7, 8, 10, 11
13 moments               <- 2, 11, 12
14 proof-of-theorem-b    <- 3, 10, 13
```

Chapters 3 and 4 use results of later chapters. In chapter 3, `MainTerm/BadTypes.lean` imports `RemainingTerms/Size.lean` (chapter 11). In chapter 4, `Bessel/Basic.lean` imports `MainTerm/SieveSystem.lean` (chapter 12), `Bessel/OpenCellBound.lean` imports `Unfolding/Link.lean` (chapter 7), and `Bessel/FillingData.lean` imports `Frames/RealBandLimits.lean` (chapter 6) and `Unfolding/Climbing.lean` (chapter 10). A reader of chapters 3 and 4 takes these results as known.

The layers of Section 3 are spread over the order. Layer 1 is chapter 2, layer 2 is chapter 3, layer 3 is chapters 4, 10 and 13, and layer 4 is chapters 5 to 9, 11 and 12.

### One paragraph per chapter

[Theorem B and its plan](/chapter/theorem-b-plan/). This chapter. It states Theorem B and its input, works out the model case, lists the four layers and the conventions.

[Few translates suffice](/chapter/few-translates/). Layer 1. It proves that a spread family has few maps whose ranges span almost all of the target, by a greedy cover. It also proves the theorem on one translate from a near isometry and a second moment, and the lemma on functions of positive type that the moment bound uses.

[Equal multiplicities by the trace formula](/chapter/equal-multiplicities/). Layer 2. It compares the traces of Hecke operators on the definite space and on the target, and deduces that the two spaces have the same dimension. It also proves that the bad types of $\bar G$ are rare, which bounds the share that the projection $e_0$ removes.

[Bessel functions at a real place](/chapter/bessel-real-place/). Layer 3. It builds the Bessel system at each real place as an average of a discrete series coefficient. It proves the size, the decay and the bound for derivatives, and it cuts the function to a bounded support.

[Frames, depth and gains](/chapter/local-frames/). Layer 4. It defines the lengths, levels and gauges of frames, proves Plancherel's formula on quadrics, and writes the densities as integrals over pairs of frames. It bounds one frame, the gains at one position, and the sum over shells.

[Local densities at the real places](/chapter/real-densities/). Layer 4. It computes the densities at the real places by shells and gauges, and it proves the local bounds of cut Bessel functions under the sizes at a real place.

[The anatomy of a term](/chapter/anatomy-of-a-term/). Layer 4. It sets up the data of the filling theorem and the level structure of the Bessel data. It sorts the terms $\gamma$ of the amplitude sums into identity terms, main terms and remaining terms, bounds the terms by the box and Siegel's lemma, and describes the link of a term.

[Local densities at the finite places](/chapter/finite-densities/). Layer 4. It computes the densities at the finite places by the standard level, fiber measures, depth, heads and the finite Bessel vector, and it bounds the density at the last entry.

[Reduced points and frame counts](/chapter/frame-counts/). Layer 4. It gives the weight of Schur's test at one real place, the orthogonal lifts of a link, the reduced points, and the lattice of a link. It counts the frames of near terms in boxes and over a lattice of small discriminant.

[Poincaré series and unfolding](/chapter/poincare-series/). Layer 3. It sums the amplitudes over blocks, decides which filling terms contribute by climbing the flags, and defines the Poincaré series. It proves the Petersson formula for the filling, proves that the filling of $D$ is admissible, and writes the Poincaré map as a Poincaré series of the Bessel function.

[The remaining terms](/chapter/remaining-terms/). Layer 4. It bounds the remaining terms by their size and their number. The number comes from lattices of given corank, the gain from the congruences modulo $M$, and the sum over pairs from Schur's test.

[The main term](/chapter/main-term/). Layer 4. It writes the main terms as Kloosterman sums, which are orbital integrals at the finite places, times integrals at the real places. A one-sided sieve and Siegel's formula bound their second moment by a product of local densities.

[Moments of the Poincaré map](/chapter/moments/). Layer 3. It expands the squares, proves the near isometry of $P$ and of $e_0P$, the bound for the identity terms, and the second moment over the whole group. It shows each exchange of a sum and an integral with its convergence.

[The proof of Theorem B](/chapter/proof-of-theorem-b/). It assembles [Theorem](/decl/New.Data.isSpread_goodPoincare/) from the three layers, then [Theorem](/decl/New.Data.enough_forms/) from it and the bound for the ramified forms.

### Prerequisites

The volume uses these chapters of four earlier volumes.

From [the proof in outline](/chapter/theorem-and-plan/): [Theorems A, B and C](/chapter/theorems-a-b-c/) for the place of Theorem B in the whole argument, and [the data and its sizes](/chapter/data-and-sizes/) for the data $D$ and its size bounds.

From the volume on unitary groups and automorphic forms: [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) for the groups and the lattices, [quotients and reduction theory](/chapter/reduction-theory/) for the convergence of Poincaré series, [automorphic forms on unitary groups](/chapter/automorphic-forms/) for the spaces of forms and their inner products, [a simple trace formula](/chapter/trace-formula/) for layer 2, and [congruence subgroups and Haar moduli](/chapter/congruence-subgroups/) for the level $K(M)$ and the volumes.

From the volume on representations: [discrete series through one matrix coefficient](/chapter/discrete-series/) and [Laplace's method for discrete series coefficients](/chapter/laplace-method/) for the Bessel functions, [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/) for the subgroup $R$ and the integrals over the big cell, and [characters of GL_n over a finite field](/chapter/finite-gln/) for the idempotents and the bad types.

From the volume on theta and the Siegel-Weil formula: [Bessel periods and one step of unfolding](/chapter/bessel-periods/) for the unfolding of a period over a Bessel subgroup, which is the step that the Petersson formula repeats.
