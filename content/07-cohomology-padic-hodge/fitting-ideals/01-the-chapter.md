---
title: The algebra for Selmer bounds
lean:
  - Lib/General/Algebra/FittingIdealsAndLengths.lean
  - Lib/General/Algebra/SharpMinors.lean
  - Lib/General/Algebra/BlockFittingBound.lean
  - Lib/General/NumberTheory/CoefficientRings.lean
  - Lib/General/NumberTheory/PadicLimitsValuation.lean
  - Lib/General/NumberTheory/CoefficientInclusion.lean
  - Lib/General/NumberTheory/LargeResidueField.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The algebra for Selmer bounds

This chapter closes Volume 7. It gives the commutative algebra that the source uses to bound Selmer groups and to make congruences by Ribet's method. The objects are modules over a discrete valuation ring $O$, their lengths, the valuations of determinants, and the zeroth Fitting ideal of a quotient of a free module. The chapter also gives the coefficient rings of the $\ell$-adic Galois representations of the source: the rings of integers of the finite Galois extensions of $\mathbb{Q}_\ell$ inside an algebraic closure $\overline{\mathbb{Q}}_\ell$. A last section lists the other files of the two folders of the chapter, and the notes end with a summary of the volume.

### Where the chapter sits

The source reduces the Generalized Riemann Hypothesis to a main inequality, and it derives the main inequality from three theorems on lattices of automorphic forms. [The plan](/chapter/theorem-and-plan/) describes the reduction. The source claims all three theorems. This book explains the claims. It does not say that they are correct.

The proof of Theorem C needs regular families of Hecke eigensystems. [The plan of regular families](/chapter/regular-families-plan/) in Volume 12 proves that they exist. That proof bounds Selmer groups from above, and it makes Selmer classes from congruences between automorphic forms. Both steps are counts of lengths. An upper bound for a Selmer group is a bound for the length of a module of cocycles that obey linear relations. A congruence gives a lower bound for the length of a congruence module, and Ribet's method turns it into an element of a Fitting ideal. This chapter gives the general algebra of both steps. Volume 12 applies it to Galois groups and Hecke algebras.

The results of this chapter that the main argument uses by name are these. The files are those of `New/Congruences`.

- The bound for the length of a module cut out by relations, in the tied Selmer groups (`Selmer/SelmerData.lean`). See [the tied Selmer groups](/chapter/tied-selmer-groups/).
- The bound for the length of the kernel of a matrix by the valuation of its determinant, in `Selmer/Untied.lean`, `Selmer/MainSummands.lean` and `Selmer/SelmerData.lean`.
- The exact length of a matrix kernel by maximal minors, in `Selmer/OneSystem.lean`.
- The relative lengths and their rules, in `Selmer/Untied.lean`, `FirstOrder/TraceRelations.lean` and `Lifting/FewLowJumps.lean`. See [the denominator bound](/chapter/denominator-bound/) and [the cup products](/chapter/cup-products/).
- The Fitting ideal bounds, in `FirstOrder/FittingBlock.lean`. See [the Ribet elements](/chapter/ribet-elements/).
- Cardinality against length, in `Selmer/Count.lean` and `LocalLoss/TateDualBound.lean`. See [the local loss](/chapter/local-loss/).
- The coefficient rings, the normalized length and the large residue fields, in `Selmer/Line.lean`, `Selmer/MainSummands.lean`, `Selmer/GeneralTheorem.lean`, `Selmer/TwistingTheorem.lean` and `FirstOrder/RibetElement.lean`. See [the twisting theorem](/chapter/twisting-theorem/).

So, as [the first chapter](/chapter/schemes-through-points/) of the volume says, some lemmas of commutative algebra of this chapter are used in many places of the main argument. The rest of the volume enters the proof through one chain of declarations. This chapter enters it through many short uses.

### The cost of the volume

The first chapter of the volume states its cost, and each chapter repeats it.

1. The $\ell$-adic cohomology of the source is an Ext group of sheaves on test rings. The source never shows that it equals étale cohomology.
2. "Crystalline" in the source means admissible for the ring $B_{\max}$ of Colmez. It does not use the ring $B_{\mathrm{cris}}$ of Fontaine.
3. The proof uses only the properties that the source proves for its own objects. It never imports a theorem stated for the classical objects. So a reader cannot take a textbook theorem and apply it to the objects of the source without a proof of the comparison.
4. The files of the main argument use no theorem of the cohomology or of the comparison theorems by name. The cohomology reaches the main argument through one chain of declarations.

For this chapter the cost is small, and it is of a different kind. The objects are the classical ones, or special cases of them. The differences are these.

- The Fitting ideal is defined for a quotient $R^\iota / N$ of a free module with a fixed finite basis, not for an abstract finitely presented module. The source proves the properties that it uses for this form only.
- The theorem on elementary divisors of the source does not state that the diagonal entries divide each other. Each proof here uses only the diagonal form.
- The valuation $v$ on $\overline{\mathbb{Q}}_\ell$ is truncated: it is $0$ on elements of norm greater than $1$. This is a junk value, and Section 7 says where it matters.
- The normalized length uses a uniformizer chosen by `choose`. The source proves that the value does not depend on the choice.
- A file of the chapter lowers the priority of six instances of Mathlib for all files that import it.

### The model case

Let $p$ be a prime, let $M$ be an $n \times n$ matrix over $\mathbb{Z}_p$ with $\det M \neq 0$, and let $k \geq 1$. Let $M$ act on $(\mathbb{Z}/p^k)^n$. How large is its kernel? By the theorem on elementary divisors there are invertible matrices $P$, $Q$ and exponents $a_1, \dots, a_n$ with $M = Q \operatorname{diag}(p^{a_1}, \dots, p^{a_n}) P$. Invertible matrices do not change the size of a kernel. The kernel of multiplication by $p^{a}$ on $\mathbb{Z}/p^k$ has $p^{\min(a, k)}$ elements. So the kernel of $M$ has length $\sum_i \min(a_i, k)$, where the length of a finite $\mathbb{Z}_p$-module with $p^e$ elements is $e$. This is at most $\sum_i a_i = v_p(\det M)$, with equality when $k \geq a_i$ for all $i$.

Three ideas of the chapter are in this computation. First, a length is bounded by the valuation of a determinant. Second, the bound is exact when the modulus is large, and then the length of the kernel equals the length of the cokernel $\mathbb{Z}_p^n / M \mathbb{Z}_p^n$. Third, the determinant is the generator of the zeroth Fitting ideal of that cokernel. The source needs these facts in a relative form: a module of cocycles inside a module of all functions, and a Fitting ideal that changes as relations are added.

### The plan of the chapter

Section 2 gives the coefficient rings in the abstract, as discrete valuation rings, and the lengths and relative lengths of modules over them. Section 3 gives relations, the modules of functions that obey them, cocycles, and the bound by rank times length. Section 4 compares lengths with determinants: the kernel bound, the duality lemma for lattices, and the exact formula by maximal minors. Section 5 gives the zeroth Fitting ideal and the theorem that bounds its change by a length. Section 6 gives the block form of the determinant bound that Ribet's lemma uses. Section 7 gives the coefficient rings inside $\overline{\mathbb{Q}}_\ell$, the valuation, the normalized length and the large residue fields. Section 8 lists the other files of the folders. Section 9 has the exercises, the notes, and the summary of the volume.

### What the chapter uses

The chapter uses commutative algebra at the level of Atiyah and Macdonald, *Introduction to Commutative Algebra*: discrete valuation rings (Chapter 9), modules of finite length (Chapter 6), and Noetherian rings. It uses the theorem on elementary divisors for matrices over a principal ideal domain. For Fitting ideals it uses Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20.2. For local fields it uses Serre, *Local Fields*, Chapters I and II. Section 7 uses the algebraic closure $\overline{\mathbb{Q}}_\ell$ and its norm, as in Mathlib.
