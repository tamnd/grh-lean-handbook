---
title: What the chapter proves
lean:
  - New/Spanning/Unfolding/AmplitudeSums.lean
  - New/Spanning/Unfolding/Climbing.lean
  - New/Spanning/Unfolding/PoincareSeries.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is layer 3 of the proof of Theorem B, the unfolding. It builds the Poincaré series of the filling data, proves the Petersson formula that writes their inner products as amplitude sums, and proves the facts about amplitude sums that layer 4 uses: they converge, they move under the Bessel group by a scalar, they vanish unless the characters agree, and the identity block is the identity. It also proves that the filling of the data $D$ satisfies the standing hypotheses `IsAdmissible`, and that the Poincaré series of $D$ is a Bessel period.

The place of the chapter in the whole argument is shown in [the theorem and the plan](/chapter/theorem-and-plan/). Its place in the proof of Theorem B is shown in [Theorem B and its plan](/chapter/theorem-b-plan/), in the part [unfolding and bounds](/chapter/theorem-b-plan/#unfolding-and-bounds). The sizes of the data are fixed in [the data and its sizes](/chapter/data-and-sizes/).

### The objects

Fix admissible filling data $S$ over a CM field $E$ ([Definition](/decl/New.Filling/) and [Definition](/decl/New.Filling.IsAdmissible/)). The notation is that of [the anatomy of a term](/chapter/anatomy-of-a-term/).

1. $G$ is the unitary group of the hermitian space $V$ of $S$. $G_\infty = \prod_v G_1$ is the product over the $f$ infinite places $v$ of one copy of the complex unitary group $G_1$.
2. The classes $c$ are the double cosets of [the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block). Each class has a chosen representative $h_c$ and a group $\mathsf{U}_c(M)$ of rational unipotent points.
3. $K$ is the stabilizer of the lattice. $\bar G$ is the finite group of reductions at the chosen places above $M = p_0p_1$. A term over the block $(c, s, c')$ is a rational $\gamma$ with $h_c^{-1}\gamma h_{c'} \in K$ of reduction $s$.
4. $W = \bigotimes_v W_v$ is the tensor product of the Bessel functions at the infinite places, with values in $\mathbb{C}^I$, where $I$ is the set of Bessel coordinates. $W^\flat$ is its cut. The kernel of a term is $W(y)\otimes\overline{W(\gamma^{-1}y)}$, or the same with $W^\flat$.
5. $\beta_c$ is the chosen cutoff of the class $c$, and $\nu$ is the covolume of the unipotent group ([the cutoff is a choice](/chapter/theorem-b-plan/#conventions-that-change-the-meaning)).
6. The amplitude of $\gamma$ is $\int \beta_c(y)\beta_{c'}(\gamma^{-1}y)\,W(y)\otimes\overline{W(\gamma^{-1}y)}\,dy$. The amplitude sum $\mathcal{A}(c, s, c')$ over a set $T$ is the sum of the amplitudes of the elements of $T$ over the block.

### The results

The chapter proves the following results. Each is stated and proved in full in the section given.

1. *Convergence* (section 2). The amplitudes over a block are summable, with a majorant that is finite. The kernels of $W$ and $W^\flat$ give amplitude sums that differ by at most $\nu b^{-k^3f}/2$. A change of the weight $\beta_c \otimes \beta_{c'}$ does not change an amplitude sum.
2. *Moving blocks* (section 3). Translation by the Bessel group moves the block $(c, s, c')$ and multiplies the amplitude sum by a character value. So the sum vanishes unless $s$ agrees, and the block of $s = 1$ is $\nu$ times the identity matrix if $c = c'$ and $0$ otherwise.
3. *Climbing* (section 4). If the characters of a term do not agree, its amplitude is $0$. If they agree, a common vector of the frame and its image climbs up the flags. So a term whose characters agree and whose discriminant vanishes has a cell rank.
4. *Reduced groups and the term structure* (section 5). The orders of the reduced images of the Bessel groups, and the rank of the common isotropic space of a term in terms of its cell rank.
5. *The Petersson formula* (section 6). The inner product of two Poincaré series is $\operatorname{vol}(K(M))$ times an amplitude sum over all terms.
6. *Admissibility* (section 7). The filling of the data $D$ satisfies `IsAdmissible`. Its proof needs the mass of the frames and the order of the classes.
7. *The series as a period* (section 8). For one choice of a real point and a linear form, the form that represents the Bessel period of a source form of $D$ is the Poincaré series of the Bessel function. The proof of Theorem B uses this identity.

Section 9 has exercises and notes.

### What the chapter uses

The chapter uses these parts of the book.

1. [The anatomy of a term](/chapter/anatomy-of-a-term/): the terms, the frame products, the discriminant, the cell rank, the character $\chi$ of the unipotent group, strong approximation for the unipotent group and the Eichler maps.
2. [Bessel functions at a real place](/chapter/bessel-real-place/): the Bessel systems, their decay majorants and their orthonormality.
3. [Counts of frames](/chapter/frame-counts/): the packing count of the terms and the integral of a cutoff. This is chapter 9 of this volume.
4. The background of Volumes 4 to 6: quotient measures and cutoffs ([reduction theory](/chapter/reduction-theory/)), Bessel periods ([Bessel periods](/chapter/bessel-periods/)) and the ratio of masses ([Siegel-Weil](/chapter/siegel-weil/)). Each is stated in one line where it is used.

No file of this chapter imports a file that the plan of the volume puts in a later chapter. The files import files of chapters 4, 7 and 9 of this volume, of Volume 9 ([the objects of the upper bound](/chapter/upper-bound-objects/)) and of the library.

### A sketch

The Poincaré series of a source vector $(c, i)$ is the sum over the rational points $\gamma$ of $G$ of a translate of the cut Bessel coordinate $\beta_c W_i$ that is supported on one coset of the principal level. The series converges absolutely, because the Bessel functions decay faster than the number of terms grows. The inner product of two series folds one of them: the integral over the quotient becomes an integral over $G_\infty$ against the other series. The second series, evaluated at the point of class $c$, is a sum over the terms of the block. So the inner product is an amplitude sum.

An amplitude sum is invariant under the double action of the unipotent group, $\gamma \mapsto u\gamma u'^{-1}$, up to the factor $\chi(u)^{-1}\chi(u')$. Where this factor is not $1$ on the stabilizer of a term, the integral of the term over the quotient is $0$. Where it is $1$, the characters agree. Then an Eichler map along a common vector of the frame $f = (e_1, \ldots, e_\varrho, z)$ and of $\gamma f$ moves the vector one step up both flags. At the top the norms of the two coefficients are equal. This gives the cell rank.

The identity block unfolds to the inner products of the Bessel functions at each place, which are orthonormal. The admissibility of $D$ is a list of size bounds. Each comes from the sizes of the data and from the mass of a frame, a product of volumes of unit spheres.

### Conventions

The sums and integrals of this chapter follow [the conventions of Theorem B](/chapter/theorem-b-plan/#conventions-that-change-the-meaning). A Bochner integral of a function that is not integrable is $0$. A sum `tsum` of a family that is not summable is $0$. The cutoffs take values in $[0, \infty]$, and `toReal` sends $\infty$ to $0$. Each theorem below says where it proves convergence. The representatives $h_c$, the cutoffs $\beta_c$ and the Bessel systems are chosen. The theorems hold for every choice.
