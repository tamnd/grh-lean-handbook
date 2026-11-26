---
title: The volume and the chapter
lean:
  - Lib/Shimura/Eigenspace.lean
  - Lib/Shimura/ComplexTheta/AppellHumbertData.lean
  - Lib/Shimura/Uniformisation/HolomorphicFamilies.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chapter

This chapter opens Volume 8. The volume explains how the source attaches Galois representations to automorphic forms. The source makes them from the cohomology of a family of abelian varieties with extra structure, the PEL Shimura varieties of unitary groups. So the volume starts with abelian varieties over $\mathbb{C}$, goes on to an integral model and a congruence relation at good primes, and ends with the representations themselves. This first section gives the plan of the volume, says how the volume serves the three theorems, and states what the volume costs. It then says what this chapter does.

### The plan of the volume

The volume has five chapters.

1. *Complex abelian varieties through theta functions* (this chapter). Theta functions on complex tori, the theorem of Appell and Humbert, the dimension formula of Frobenius, the theta group, abelian schemes in the form of the source, and the uniformization $A(\mathbb{C}) \cong V/L$.
2. [An integral model without a moduli problem](/chapter/integral-model/). The PEL datum of the source, good reduction, the theta-null points and the Hecke tower. The source does not represent a moduli functor. It takes the closure of a set of theta-null points in a projective space.
3. [The congruence relation](/chapter/congruence-relation/). The congruence relation between Hecke operators and the Frobenius, and the Galois representation on a quotient of the cohomology cut out by a Hecke eigensystem.
4. [What attached means](/chapter/attached-representations/). The sense in which a representation is attached to a form: agreement at most Frobenius elements, the difference between "kills" and "characteristic polynomial", and pseudocharacters.
5. [Building the representations](/chapter/building-representations/). Limits, base change, theta lifts and local-global compatibility at split places.

### How the volume serves the three theorems

The source reduces the Generalized Riemann Hypothesis to a main inequality, and it derives the main inequality from three theorems on lattices of automorphic forms. [The plan](/chapter/theorem-and-plan/) describes the reduction. The source claims all three theorems. This book explains the claims. It does not say that they are correct.

*Theorems A and B.* The proofs of Theorems A and B do not use this volume.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) bounds the denominators of lattices of forms on definite unitary groups. One step needs regular families of Hecke eigensystems. [The plan of regular families](/chapter/regular-families-plan/) in Volume 12 proves their existence with Selmer groups, and Selmer groups need Galois representations attached to automorphic forms. This volume supplies them.

The proof reaches this volume through one chain of declarations. The result `New.GaloisRep.sphericalCompat_std` (`Lib/GaloisRep/Main/AllRanks.lean`, line 465) gives the attached representations. It uses `New.GaloisRep.exists_rep_of_cuspidal_type` (`Lib/GaloisRep/Main/SeedRepresentation.lean`, line 822). That proof applies `New.Variety.Model.exists_galois_rep` (`Lib/Shimura/Eigenspace.lean`, line 689) at line 544. The proof of `New.Variety.Model.exists_galois_rep` uses the Woods Hole formula `New.Variety.ellAdicCohom.woods_hole` at line 458 and the crystalline relation `New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel` at line 674. So the cohomology of Volume 7, about 65,000 lines, and the 29,422 lines of `Lib/Shimura` enter the proof through one theorem.

The files of the main argument, in the folder `New`, use no theorem of `Lib/Shimura` by name. They use only small utilities of the Hecke data, such as `classAut_eq_bot`. Three files of `New` import `Lib/Shimura/Uniformisation/HolomorphicFamilies.lean`, but they use no name from it. So the whole of this chapter reaches the main argument only through the chain above: the uniformization of this chapter is used to build the integral model of Chapter 2, and the model carries the cohomology.

### The cost of the volume

The book states the cost of this volume here, and each chapter of the volume repeats it.

1. The source builds its own objects. An abelian scheme is the class `New.IsAbelianScheme` of [Section 4](/chapter/complex-abelian-varieties/). A line bundle is a cocycle of functions on points, as in [Schemes through their points](/chapter/schemes-through-points/). The cohomology is the Ext group of Volume 7, and "crystalline" means admissible for the ring $B_{\max}$. None of these objects is compared with the classical object in Lean.
2. No moduli functor is represented. The docstring of `Lib/Shimura/Eigenspace.lean` says: "No moduli functor is represented, nothing is transferred to $GL_n$, and no dimension is computed here."
3. The Galois representation of `New.Variety.Model.exists_galois_rep` has a dimension $m$ that the statement does not determine. The source states good reduction (unramified or crystalline at safe places), annihilation of the geometric Frobenius by the Hecke polynomial, and the occurrence of given Hodge-Tate weights at one embedding. It states no dimension and no semisimplicity. Other embeddings and multiplicities are not controlled.
4. The proof uses only the properties that the source proves for its own objects. So the gap between these objects and the classical objects does not break the argument. It means that a reader cannot apply a textbook theorem to the objects of the source without a proof of the comparison.

For this chapter the cost is the following. The theta functions of Sections 2 and 3 are the classical ones, with one change of convention in the form $B$, which Section 2 explains. The abelian schemes of Section 4 ask for surjective multiplication by every $m \neq 0$ in place of connected fibres. Section 4 gives an argument, not checked in Lean, that the two conditions agree. The uniformization of Section 6 is a structure on the group of points with an analytic calculus made from functions on points, not from an analytification of the scheme.

### What this chapter does

The chapter has one theorem at its center. Let $A$ be an abelian variety over $\mathbb{C}$ of dimension $d$, embedded in projective space by a line bundle $N$ whose class obeys the parallelogram law. Then $A(\mathbb{C}) \cong \mathbb{C}^d/L$ for a lattice $L$, and the homogeneous coordinates of the point $e(z)$ that $z \in \mathbb{C}^d$ defines are theta functions $\theta_i(z)$ of one type $(B, \chi)$, with a positive Riemann form. The first half is [Theorem](/decl/New.LineBundle.IsProjEmbedding.nonempty_uniformisation/). The second half is [Theorem](/decl/New.Uniformisation.appell_humbert/). The integral model of Chapter 2 is built from these theta coordinates.

The model case is an elliptic curve. Take $V = \mathbb{C}$ and $L = \mathbb{Z} + \tau\mathbb{Z}$ with $\operatorname{Im}\tau > 0$. The Jacobi theta function
$$\vartheta(z) = \sum_{n \in \mathbb{Z}} \exp(\pi i n^2 \tau + 2\pi i n z)$$
satisfies $\vartheta(z + 1) = \vartheta(z)$ and $\vartheta(z + \tau) = \exp(-\pi i \tau - 2\pi i z)\,\vartheta(z)$. The space of entire functions with the same two rules has dimension $1$. If the factor $\exp(-\pi i\tau - 2\pi i z)$ is replaced by its $n$-th power, the space has dimension $n$, and for $n \geq 3$ these functions embed $\mathbb{C}/L$ in $\mathbb{P}^{n-1}$. All of this chapter is the generalization of these facts to any dimension, in a form that does not choose a basis of $L$.

The chapter goes from analysis to geometry. Sections 2 and 3 are pure complex analysis on $V$: theta functions, their translations, the dimension formula and the absence of base points. Sections 4 and 5 are algebraic geometry over any base: abelian schemes, the pairing of the Picard group, isogenies and lifts of translations to sections of line bundles. Section 6 joins the two by the uniformization.

### The sections

Section 2 defines theta functions of type $(B, \chi)$, the Appell-Humbert conditions, the Riemann form, the twisted translations and the dual lattice, and works out the elliptic model case. Section 3 proves the dimension formula $(\dim)^2 = [L^\perp : L]$, the irreducibility of the theta group, and the absence of base points for multiples $nB$ with $n \geq 2$. Section 4 gives abelian schemes in the form of the source, the pairing and the parallelogram law, the formula $[m]^* c = m^2 c$, and the results on isogenies and torsion. Section 5 gives lifts of translations, the criterion $z \in K(L)$, and theta structures with their rigidity. Section 6 gives holomorphic families of points, the Lie exponential, the uniformization and the Appell-Humbert theorem. Section 7 gives moduli points and torus models, which link this chapter to the next one. Section 8 has the exercises and the notes.

### What the chapter uses

The chapter uses the analytic theory of complex tori at the level of Mumford, *Abelian Varieties*, Sections 1 to 3, or Birkenhake and Lange, *Complex Abelian Varieties*, Chapters 1 to 3. From algebraic geometry it uses smooth and proper morphisms, flatness and the Picard group, and the description of schemes through their points in [Schemes through their points](/chapter/schemes-through-points/). From analysis it uses Liouville's theorem, the identity theorem for entire functions of several variables, and the Fourier analysis of periodic functions on $V/L$.
