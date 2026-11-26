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

The volume has twelve chapters. The diagram shows which chapters use the results of which. An arrow from $A$ to $B$ means that $B$ uses a result of $A$. This chapter is left out.

```text
few-translates ------------------------> moments
real-densities -----> bessel-real-place
bessel-real-place --> poincare-series --> anatomy-of-a-term
bessel-real-place --> remaining-terms
anatomy-of-a-term --> remaining-terms --> main-term
real-densities -----> main-term
finite-densities ---> main-term
remaining-terms ----> moments
main-term ----------> moments
few-translates -----------------------> proof-of-theorem-b
equal-multiplicities -----------------> proof-of-theorem-b
moments ------------------------------> proof-of-theorem-b
```

The order of the chapters follows the four layers, not the arrows. The chapter on Bessel functions uses a local bound from [the chapter on densities at the real places](/chapter/real-densities/), which comes later.

### One paragraph per chapter

[Theorem B and its plan](/chapter/theorem-b-plan/). This chapter. It states Theorem B and its input, works out the model case, lists the four layers and the conventions.

[Few translates suffice](/chapter/few-translates/). Layer 1. It proves that a spread family has few maps whose ranges span almost all of the target, by a greedy cover. It also proves the theorem on one translate from a near isometry and a second moment, and the lemma on functions of positive type that the moment bound uses.

[Equal multiplicities by the trace formula](/chapter/equal-multiplicities/). Layer 2. It compares the traces of Hecke operators on the definite space and on the target, and deduces that the two spaces have the same dimension. It also proves that the bad types of $\bar G$ are rare, which bounds the share that the projection $e_0$ removes.

[Bessel functions at a real place](/chapter/bessel-real-place/). Layer 3. It builds the Bessel system at each real place as an average of a discrete series coefficient. It proves the size, the decay and the bound for derivatives, and it cuts the function to a bounded support.

[Poincaré series and unfolding](/chapter/poincare-series/). Layer 3. It defines the filling data, the cutoffs and the Poincaré series. It proves the Petersson formula for the filling, and it proves that the filling of $D$ is admissible.

[Moments of the Poincaré map](/chapter/moments/). Layer 3. It proves the near isometry of $P$ and of $e_0P$, the bound for the identity terms, and the second moment over the whole group. It shows each exchange of a sum and an integral with its convergence.

[The anatomy of a term](/chapter/anatomy-of-a-term/). Layer 4. It sorts the terms $\gamma$ of the amplitude sums into identity terms, main terms and remaining terms. It describes the link of a term, and it moves the common vectors of two flags up the flags to decide which terms contribute.

[The remaining terms](/chapter/remaining-terms/). Layer 4. It bounds the remaining terms by their size and their number. The number comes from lattice points and Siegel's lemma, the gain from the congruences modulo $M$, and the sum over pairs from Schur's test.

[The main term](/chapter/main-term/). Layer 4. It writes the main terms as Kloosterman sums, which are orbital integrals at the finite places, times integrals at the real places. A one-sided sieve bounds their second moment by a product of local densities.

[Local densities at the real places](/chapter/real-densities/). Layer 4. It computes the densities at the real places by shells and gauges, and it proves the local bounds of cut Bessel functions under the sizes at a real place.

[Local densities at the finite places](/chapter/finite-densities/). Layer 4. It computes the densities at the finite places by depth, heads, fixed lines and correlations of frames.

[The proof of Theorem B](/chapter/proof-of-theorem-b/). It assembles [Theorem](/decl/New.Data.isSpread_goodPoincare/) from the three layers, then [Theorem](/decl/New.Data.enough_forms/) from it and the bound for the ramified forms.

### Prerequisites

The volume uses these chapters of four earlier volumes.

From [the proof in outline](/chapter/theorem-and-plan/): [Theorems A, B and C](/chapter/theorems-a-b-c/) for the place of Theorem B in the whole argument, and [the data and its sizes](/chapter/data-and-sizes/) for the data $D$ and its size bounds.

From the volume on unitary groups and automorphic forms: [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) for the groups and the lattices, [quotients and reduction theory](/chapter/reduction-theory/) for the convergence of Poincaré series, [automorphic forms on unitary groups](/chapter/automorphic-forms/) for the spaces of forms and their inner products, [a simple trace formula](/chapter/trace-formula/) for layer 2, and [congruence subgroups and Haar moduli](/chapter/congruence-subgroups/) for the level $K(M)$ and the volumes.

From the volume on representations: [discrete series through one matrix coefficient](/chapter/discrete-series/) and [Laplace's method for discrete series coefficients](/chapter/laplace-method/) for the Bessel functions, [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/) for the subgroup $R$ and the integrals over the big cell, and [characters of GL_n over a finite field](/chapter/finite-gln/) for the idempotents and the bad types.

From the volume on theta and the Siegel-Weil formula: [Bessel periods and one step of unfolding](/chapter/bessel-periods/) for the unfolding of a period over a Bessel subgroup, which is the step that the Petersson formula repeats.
