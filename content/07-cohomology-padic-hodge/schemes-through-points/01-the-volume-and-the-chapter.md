---
title: The volume and the chapter
lean:
  - Lib/General/Geometry/LineBundles.lean
  - Lib/General/Geometry/ProjectiveSpace.lean
  - Lib/General/Geometry/SerreTheorem.lean
  - Lib/General/Geometry/EtaleCharts.lean
  - Lib/Shimura/Eigenspace.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chapter

This chapter opens Volume 7. The volume gives the geometry and the cohomology that the source uses to make Galois representations: schemes and line bundles, a cohomology of schemes, the period rings of $p$-adic Hodge theory, Kisin modules, the comparison theorems and some commutative algebra. Of all the volumes of this book, this one is the farthest from the textbooks. The source does not import the classical objects. It builds its own objects and proves on them the properties that the argument needs. This first section gives the plan of the volume, says how the volume serves the three theorems, and states what the volume costs. It then says what this chapter does.

### The plan of the volume

The volume has six chapters.

1. *Schemes through their points* (this chapter). Functions on the ring-valued points of a scheme, line bundles as cocycles of such functions, the Picard group, projective space and projective embeddings, the Frobenius, a case of Serre's theorem on the sections of powers of a line bundle, and étale charts.
2. [Cohomology as Ext on test rings](/chapter/cohomology-ext/). The cohomology of the source: Ext groups of sheaves on a category of test rings. The chapter says what it is and what it is not. It gives base change, Hodge cohomology and the Woods Hole formula, which is half of the holomorphic Lefschetz formula of Atiyah and Bott.
3. [Period rings and crystalline representations](/chapter/period-rings/). The rings $A_{\inf}$, $B_{\max}$ and $B_{\mathrm{dR}}^+$, admissible and crystalline representations, Hodge-Tate jumps, and the rank formula of Bloch and Kato.
4. [Kisin frames and limits](/chapter/kisin-frames/). Kisin modules, the frame theorem, and limits of crystalline representations.
5. [The comparison theorems on test objects](/chapter/comparison-theorems/). Almost descent, the primitive comparison theorem, the Hodge-Tate period map and the crystalline comparison.
6. [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/). The commutative algebra that bounds Selmer groups.

### How the volume serves the three theorems

The source reduces the Generalized Riemann Hypothesis to a main inequality, and it derives the main inequality from three theorems on lattices of automorphic forms. [The plan](/chapter/theorem-and-plan/) describes the reduction. The source claims all three theorems. This book explains the claims. It does not say that they are correct.

*Theorems A and B.* The proofs of Theorems A and B do not use the geometry, the cohomology or the period rings of this volume. Some lemmas of commutative algebra of Chapter 6 are used in many places of the main argument.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) bounds the denominators of lattices of forms on definite unitary groups. One step needs regular families of Hecke eigensystems, and [the plan of regular families](/chapter/regular-families-plan/) in Volume 12 proves their existence with Selmer groups. The Selmer groups need Galois representations attached to automorphic forms, and these come from the cohomology of Shimura varieties in Volume 8. Volume 8 needs this volume for the cohomology, its finiteness, its Frobenius and its crystalline property.

The proof reaches this volume through one chain of declarations. In the files of the main argument, the result `New.GaloisRep.sphericalCompat_std` (`Lib/GaloisRep/Main/AllRanks.lean`, line 465) gives the attached representations. It uses `New.GaloisRep.exists_rep_of_cuspidal_type` (`Lib/GaloisRep/Main/SeedRepresentation.lean`, line 822). That proof applies `New.Variety.Model.exists_galois_rep` at line 544. The proof of `New.Variety.Model.exists_galois_rep` (`Lib/Shimura/Eigenspace.lean`) uses the Woods Hole formula `New.Variety.ellAdicCohom.woods_hole` at line 458 and the crystalline relation `New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel` at line 674. So the whole of the cohomology of Volume 7 and the Shimura part of Volume 8, about 95,000 lines of the library, enter the proof through one theorem.

Two objects of this chapter are arguments of that chain. At line 458 of `Lib/Shimura/Eigenspace.lean`, the source calls the Woods Hole formula with two atlases, both made by `New.Variety.hasAtlas_algPointsOf` of [Section 7](/chapter/schemes-through-points/), and with the projective embedding `X.projective i` of the integral model. That field of the integral model has the type `New.Variety.HasProjEmbedding` of [Section 5](/chapter/schemes-through-points/). At lines 449, 508 and 576 of the same file, the source makes the class `New.Variety.IsCharted` from an atlas, by `New.Variety.HasAtlas.exists_isCharting`. So the line bundles, the projective embeddings and the charts of this chapter carry the geometry of the Shimura varieties into the cohomology.

### The cost of the volume

The book states the cost of this volume here, and each chapter of the volume repeats it.

1. The $\ell$-adic cohomology of the source is an Ext group of sheaves on test rings. The source never shows that it equals étale cohomology. The file `Lib/Cohomology/Etale/FilteredLimits.lean` says that this equality "is neither proved nor used".
2. "Crystalline" in the source means admissible for the ring $B_{\max}$ of Colmez. It does not use the ring $B_{\mathrm{cris}}$ of Fontaine.
3. The proof uses only the properties that the source proves for its own objects: finiteness, base change, a fixed point formula, the Hodge-Tate map, crystallinity and a relation for the Frobenius. It never imports a theorem stated for the classical objects. So the gap between the objects of the source and the classical objects does not break the argument. It means only that a reader cannot take a textbook theorem and apply it to the objects of the source without a proof of the comparison.
4. The files of the main argument use no theorem of the cohomology or of the comparison theorems by name. No file of the main argument imports the geometry of this chapter. The cohomology reaches the main argument only through the chain above. From $p$-adic Hodge theory the main argument uses four names directly: `New.Period.IsCrystalline`, `New.Period.crysCocycles`, `New.Lift.KummerChart.JumpLattice` and `New.Lift.KummerChart.JumpLattice.frame_theorem`. These serve the local conditions of the Selmer groups of Volume 12.

For this chapter the cost is the following. A scheme is a scheme of Mathlib, but a line bundle is not a sheaf of modules. It is a cover with a cocycle of functions on points. The Picard group is a quotient of such cocycles. The source does not compare it with the Picard group of Mathlib or with $H^1(X, \mathcal{O}_X^\times)$. Section 3 gives the comparison as a remark and an exercise. The geometry is used only for projective embeddings, for the line bundles of abelian schemes, and for the Hecke tower of Volume 8.

### What this chapter does

The chapter has two kinds of content. The first is the classical geometry: the functor of points of a scheme, invertible sheaves and the Picard group, morphisms to projective space, and Serre's theorem. The chapter states it with sources where a reader can find the proofs. The second is the form in which the source states the same objects. The two forms differ, and each difference gets a remark on the formalization.

The model case is the affine line. A regular function on a scheme $X$ is a morphism $X \to \mathbb{A}^1_{\mathbb{Z}} = \operatorname{Spec} \mathbb{Z}[T]$. So it gives, for each ring $A$ and each point $t \colon \operatorname{Spec} A \to X$, an element $f(t) \in A$, and these elements are compatible with all ring maps $A \to B$. The source takes this description as the definition. A function on points is any rule $t \mapsto f(t)$. It is regular on an open set $U$ if it is compatible with ring maps at the points that land in $U$. The source proves that a regular function on $U$ comes from a section over $U$. Then a line bundle is an open cover with transition functions $g_{ij}$, regular on the overlaps, with $g_{ii} = 1$ and $g_{ij} g_{jk} = g_{ik}$. There are no sheaves and no restriction maps.

The chapter follows the files of `Lib/General/Geometry` in the order in which they build on each other.

### The sections

Section 2 gives the functions on points, regularity, the evaluation of sections, gluing of morphisms, and the descent of functions along a flat, surjective, quasi-compact morphism. Section 3 gives line bundles as cocycles, their sections and frames, isomorphism, the Picard group with its group law and pull-back, the triviality of the Picard group of a local ring, and descent of frames. Section 4 gives projective space, the bundle $\mathcal{O}(1)$, homogeneous coordinates and linear systems, and the morphism to projective space that a linear system defines. Section 5 gives projective embeddings, the closed immersion that an embedding defines, the affine charts, and the Segre and Veronese embeddings. Section 6 gives the absolute Frobenius, its action on the Picard group, and the case of Serre's theorem that the source proves. Section 7 gives dense families of complex points and the étale charts and atlases that the cohomology of Chapter 2 needs. Section 8 has the exercises and the notes.

### What the chapter uses

The chapter uses the theory of schemes of a first course, as in Hartshorne, *Algebraic Geometry*, Chapter II: schemes, morphisms, open and closed immersions, proper and flat morphisms, and $\operatorname{Proj}$ of a graded ring. It uses these objects in the form of Mathlib. From commutative algebra it uses noetherian rings, localization and the Hilbert basis theorem. The chapter does not use cohomology of sheaves, apart from one remark that compares the Picard group of the source with $H^1(X, \mathcal{O}_X^\times)$.
