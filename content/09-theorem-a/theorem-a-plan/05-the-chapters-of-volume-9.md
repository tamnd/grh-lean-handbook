---
title: The chapters of Volume 9
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapters of Volume 9

The fourteen later chapters of the volume prove the inputs of Section 3. The list gives each chapter with the chapters of this volume that it uses. An entry in brackets is an earlier volume.

```
 2 upper-bound-objects    <- (Vol 4, 6)
 3 seesaw-identity-1      <- 2
 4 field-at-primes        <- (Vol 3)
 5 integral-vacuum        <- 4
 6 cm-formal-group        <- 5
 7 normal-forms           <- 3, 5, 6
 8 theta-kernels-gauges   <- 3, 5, 7
 9 short-columns-gain     <- 2, 6, 7, 8
10 chain-valuation        <- 8, 9
11 seesaw-identity-2      <- 2, 3, 9, 10
12 archimedean-size       <- 2, 9, 10
13 elementary-divisors    <- (Vol 5)
14 divisibility           <- 2, 10, 12, 13
15 proof-of-theorem-a     <- 11, 12, 14
```

The order is the order of the Lean files: each file of a chapter imports only files of earlier chapters, with three exceptions in chapter 2. There are three lines of work. The seesaw line is 2, 3, then 11. The arithmetic line is 4 to 8: the field, the vacuum, the formal group, the count and the kernels. The two lines meet in chapters 9 and 10, which give the gain and the valuation of a chain. Then come the size (12), the elementary divisors (13) and the divisibility (14).

Chapter 2 uses three results of later chapters. The columns use admissible combinations (chapter 3). The Poincaré map uses the evaluation at edge pairs (chapter 3). The characters at the level use full marks (chapter 10). A reader of chapter 2 takes these three results as known; chapters 3 and 10 prove them.

*Chapter 2.* [The objects of the upper bound](/chapter/upper-bound-objects/) sets up the labels, the weights $\kappa$, the grids, the laws of the lifts at the level $N$, the chains, the columns and rows of the diagrams, the composite lift and the chain data of Section 3, and the Poincaré map as a Bessel period.

*Chapter 3.* [The seesaw identity, part 1](/chapter/seesaw-identity-1/) defines admissible combinations, standard lines and edge pairs, unfolds the inner product with the Poincaré series in stages, writes the integral as a sum over cosets, and cuts the sum.

*Chapter 4.* [The field $E$ at the primes](/chapter/field-at-primes/) describes the splitting of the small primes and of $N$ in $E$, the different, the Weil data and the chosen places.

*Chapter 5.* [The integral vacuum and tight frames](/chapter/integral-vacuum/) builds the vacuum data that are integral at every prime, from tight frames, and finds short vectors at the chosen places.

*Chapter 6.* [The CM curve, its formal group and the normal form](/chapter/cm-formal-group/) studies the derivatives of theta functions of a CM elliptic curve through its formal group: the Frobenius congruence and the exponent theorem. It defines the couplings and proves that theta products have the normal form at the nonsplit primes.

*Chapter 7.* [The count and the divisibility of standard data](/chapter/normal-forms/) counts the divisibility of a jet of a series with the normal form. The bounds are of Legendre type, as in Exercise 3. It then fixes the archimedean scale of the vacuum and bounds the derivatives of standard data.

*Chapter 8.* [Theta kernels and gauges](/chapter/theta-kernels-gauges/) studies one theta kernel: its conjugates under $\mathrm{Aut}(\mathbb{C})$, which act on jets semilinearly, and the raising operators. It proves that a kernel with integral vacuum data maps integral forms to integral forms, measured by gauges.

*Chapter 9.* [Short columns and the gain](/chapter/short-columns-gain/) proves the theorem on short source forms, defines the gain at each prime, bounds the losses from near pairs, and proves that the divisibility bound is at least the gain.

*Chapter 10.* [Marked primes and the valuation of a chain](/chapter/chain-valuation/) proves that a full mark exists, defines the scaled Hecke operators, proves the gauge bound for a chain of theta lifts, and expands the glued tensor of a chain datum.

*Chapter 11.* [The seesaw identity, part 2](/chapter/seesaw-identity-2/) evaluates on neighbour lattices, chooses a good datum, assembles the chain datum, and proves the seesaw identity of Section 3, with the constant of the remark there.

*Chapter 12.* [The archimedean size of the composite lift](/chapter/archimedean-size/) counts the classes, bounds the allowed losses, and proves the theorem on the size of the composite lift and the lemma on the good part.

*Chapter 13.* [Elementary divisors of a Hecke operator](/chapter/elementary-divisors/) computes elementary divisors with a Frobenius cycle, a root lemma, a cone of Pieri type, a defect count and an average over a Schur algebra.

*Chapter 14.* [Divisibility prime by prime](/chapter/divisibility/) proves the theorem on the divisibility of the composite lift. It treats the level $N$, the Hecke edges and the mark operator, and the nonsplit primes, and it chooses the submodule $S$.

*Chapter 15.* [The proof of Theorem A](/chapter/proof-of-theorem-a/) gives the proof of Section 4 with the passage to the target in full.

### Prerequisites

The volume uses the following chapters of earlier volumes.

*Volume 3.* The CM field $E = K(\zeta_{q_1})$, its infinite places and the group $(\mathbb{Z}/q_1)^\times$ that acts on them are in [CM fields, towers and places](/chapter/cm-fields/). The twists are characters of finite ideles, from [class field theory on finite ideles](/chapter/class-field-theory/). Chapters 4 and 6 use [CM elliptic curves](/chapter/cm-elliptic-curves/).

*Volume 4.* The hermitian spaces $X_j$, $Y_j$ and their unitary groups over the adeles are in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). The algebraic forms on definite unitary groups, their Petersson inner products and the Weyl lattices are in [automorphic forms on unitary groups](/chapter/automorphic-forms/). The classes and the levels are in [quotients and reduction theory](/chapter/reduction-theory/) and [congruence subgroups and Haar moduli](/chapter/congruence-subgroups/).

*Volume 5.* Chapter 13 uses Schur modules and Green's theory of the characters of finite general linear groups, from [integral Weyl modules and branching](/chapter/weyl-modules/) and [characters of $\mathrm{GL}_n$ over a finite field](/chapter/finite-gln/). The Bessel subgroups of the Poincaré map are in [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/).

*Volume 6.* The theta kernels come from [the Weil representation from a vacuum](/chapter/weil-representation/) and [local theta in the Fock model](/chapter/local-theta/). The lifts and the classical seesaw are in [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), and the first step of the unfolding is in [Bessel periods and one step of unfolding](/chapter/bessel-periods/).
