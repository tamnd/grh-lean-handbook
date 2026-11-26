---
title: What the chapter proves
lean:
  - New/Spanning/RemainingTerms/OneRealPlace.lean
  - New/Spanning/Unfolding/ReducedPoints.lean
  - New/Spanning/RemainingTerms/FramesOverLattice.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter proves the counting tools for the terms of the amplitude sums. A term is a rational element $\gamma$ of the unitary group. The terms are sorted and described in [the anatomy of a term](/chapter/anatomy-of-a-term/). Two later chapters use the tools of this chapter: [Poincaré series and unfolding](/chapter/poincare-series/) and [the remaining terms](/chapter/remaining-terms/). The place of the chapter in the proof of Theorem B is shown in [Theorem B and its plan](/chapter/theorem-b-plan/), and the whole argument in [the theorem and the plan](/chapter/theorem-and-plan/). The chapter is in layer 4.

The source is ten files with 6645 lines: seven in the folder `New/Spanning/RemainingTerms` and three in `New/Spanning/Unfolding`. Each file imports only files of earlier chapters of this volume, mostly [the anatomy of a term](/chapter/anatomy-of-a-term/), and files of other volumes. No file imports a file of a later chapter.

### The data

The data are those of [the anatomy of a term](/chapter/anatomy-of-a-term/). A CM field $E$ with $f$ infinite places carries a shape $\mathfrak s$. The space $V$ has a basis

$$e_0, \dots, e_{\varrho - 1},\quad x_1, \dots, x_k,\quad z,\quad e^*_{\varrho - 1}, \dots, e^*_0.$$

The pairs $e_a, e^*_a$ are hyperbolic planes. The space $X_0 = \operatorname{span}(x_i)$ has index set $\kappa$ and dimension $k$, and $h(z, z) = -N$. The *frame* is $f = (f_0, \dots, f_\varrho) = (e_0, \dots, e_{\varrho - 1}, z)$, with $n = \varrho + 1$ vectors. The span of the $e_a$ is $A$. For a term $\gamma$, the matrix $Z$ of the products of $f$ with $\gamma f$ is `S.frameProducts γ`, and $D_l$ is its leading minor of order $l$. The first $\varrho$ rows of $Z$ are the *isotropic rows* $\Xi_0$. The level is $M$, and $b$ is the large size parameter. For the sizes of $M$, $N$, $b$ and the other constants, see [the data and their sizes](/chapter/data-and-sizes/).

Two notions from the anatomy of a term are used everywhere.

- $\gamma$ has *norm-one pairs from level* $j$ (`New.NormOnePairOccursFrom j γ`) if there is a $c$ with $c\bar c = 1$ such that, for each index $a \geq j$, the flags of $f$ and $\gamma f$ share a vector $f x = \gamma f y$ with $x_a = c$, $y_a = 1$, and $x_b = y_b = 0$ for $b > a$.
- $\gamma$ has *cell rank* $j \leq \varrho + 1$ (`New.Filling.HasCellRank`) if it has norm-one pairs from level $j$, $D_j \neq 0$, and the discriminant `S.termDisc γ` is nonzero exactly when $j = \varrho + 1$.

The group $\mathsf U_c(M)$ (`S.classUnipotent c`) consists of the rational unipotent elements of level $M$ for the class $c$. Its subgroup $\mathsf U^0_c$ (`S.classUnipotent₀ c`) consists of the elements that fix every frame vector. In this chapter an element of $\mathsf U^0_c$ is a *move*. If $u$ is a move, then $u\gamma$ has the same matrix $Z$ as $\gamma$.

### The results

The chapter has three parts.

1. **The weight at one real place.** Schur's test in [the remaining terms](/chapter/remaining-terms/) needs a weight on the real group $G_1$. The weight is a power of the ratio $\nu(y)$ of the volumes of the projections of $\gamma f$ and of $f$ to the negative space at $y$. The chapter shows that $\nu(y)^{-(k + i)}$, as a function of a move, has a majorant with a finite integral. The bound is $(2\rho^2)^{(i+1)i}(2^{i+1}\theta^{2(j - i)})^k/|\delta|^{k+i}$, where $\delta$ is a minor of $Z$.
2. **Reduced points and cutoffs.** A *reduced point* is a point whose matrix above the diagonal has its entries in a fixed fundamental domain. Each point has exactly one coset of moves that makes it reduced. With this fact the chapter builds a partition of unity, the class cutoffs, and computes the integral of a cutoff. The integral is the covolume `S.unipotentCovolume`. It also proves a packing bound: the frames $\gamma f$ of the weights with a common point in a box are few.
3. **Frame counts over a lattice.** The link of a term has orthogonal lifts and a lattice with a discriminant. The chapter bounds this discriminant by the gauge of the term. Then it counts the near terms whose link lies over a fixed lattice, up to moves. The count is at most $b^{2000n^6(l+1)f}$.

### The sketch

The weight. Let $\gamma$ have norm-one pairs from level $j$ and put $i = \min(\varrho, j)$. The shared vectors cancel in $\nu(y)$. So $\nu(y)$ is a determinant on the subframe $f_0, \dots, f_{i-1}, z$. A Gram-Schmidt basis $\omega$ of the negative space gives a triangular matrix $L$. The inequality of Ostrowski and Taussky gives $\nu(y) \geq 2^{-i-1}|\delta|\det(1 + vv^*)/|\det L|^2$. Here the columns of $v$ lie in $X_0$, and a move changes $v$ by an affine map. Hua's integral then bounds the integral over the moves.

The reduced points. The coordinates of a point above the diagonal of its frame block form a unitriangular matrix. A move multiplies this matrix by a unitriangular matrix of level $M$, and an induction on the distance from the diagonal gives the unique coset. The packing bound uses a rigidity fact: an algebraic integer whose conjugates all have modulus less than $1$ is $0$. So two different frames $\gamma f$ near one point are far apart, and a volume count bounds their number.

The frame counts. For a near term of cell rank $j$, the vectors of $A \cap \gamma A$ give the *shared vectors*. These are integral and small, so they are few. Two terms with the same $Z$ and the same shared vectors, whose frames agree modulo a large integer, differ by a move. Three rounds of a colouring argument count the remaining freedom by lattice indices. Each index is at most $b^{2n^3f}$.

### The sections

- [The weight at one real place](/chapter/frame-counts/#the-weight-at-one-real-place) proves the majorant for $\nu(y)^{-(k+i)}$.
- [Reduced points](/chapter/frame-counts/#reduced-points) proves the unique coset and the colouring bounds.
- [Cutoffs, rigidity and packing](/chapter/frame-counts/#cutoffs-rigidity-and-packing) builds the class cutoffs and proves the packing bound.
- [The integral of a cutoff](/chapter/frame-counts/#the-integral-of-a-cutoff) computes the integral of a class cutoff.
- [Orthogonal lifts and the lattice of a link](/chapter/frame-counts/#orthogonal-lifts-and-the-lattice-of-a-link) bounds the discriminant of the link lattice.
- [Shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves) constructs moves from congruences.
- [Frames over a lattice](/chapter/frame-counts/#frames-over-a-lattice) proves the frame count.
- [Exercises and notes](/chapter/frame-counts/#exercises-and-notes) has exercises and references.

The statements in this chapter are those of Lean. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument is correct as a proof of Theorem B.
