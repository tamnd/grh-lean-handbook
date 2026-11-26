---
title: What the chapter proves
lean:
  - New/Spanning/Frames/StandardLevel.lean
  - New/Spanning/Frames/FiberMeasures.lean
  - New/Spanning/Frames/BesselVector.lean
  - New/Spanning/Frames/FiniteDepth.lean
  - New/Spanning/Frames/TopCorrelation.lean
  - New/Spanning/Frames/TopFloor.lean
  - New/Spanning/Frames/FiniteShells.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

[The chapter on local frames](/chapter/local-frames/) proves bounds for a local density in the language of an abstract place. A place there has a ring $A$, place data $F$ and a gauge $\Gamma$, and four facts are left as hypotheses: the gauge exists, the shells exist, a far position has a deep vector, and the measures are normalized. This chapter supplies all of them at the finite places, and it then computes the densities that the main term needs. It is the finite companion of [the chapter on the real places](/chapter/real-densities/).

The source is seven files of the folder `New/Spanning/Frames`, with 5016 lines: `StandardLevel`, `FiberMeasures`, `BesselVector`, `FiniteDepth`, `TopCorrelation`, `TopFloor` and `FiniteShells`. In the guide of the folder (lean:New/Spanning/Frames/Lengths.lean#L15) they are step 4, "the finite places".

### Why the finite places are easier and harder

At a finite place every set in sight is a lattice or a coset of a lattice. The box $K$ of the place data is the group of integral isometries, the sizes of the gauge are the fractional ideals $\alpha^{-j}R$, and the depth of a position is the index of an ideal. So volumes become indices, and inequalities between volumes become divisibilities.

The hard part is that the Bessel function is not given. At a real place it is a Bessel function of the discrete series ([Bessel functions at a real place](/chapter/bessel-real-place/)). At the finite places the source builds it: it extends the Bessel character of $\mathsf{U}$ to $\mathsf{U}K(g)$, and it takes the vector of the translates of this extension by the cosets of $K(g)$ in a group $Z$ with $K(g) \le Z \le K$. Its norms, its correlations and the masses of the congruence subgroups must then be computed exactly, because the main term compares a mass with its error.

### The model case

Take for $A$ the unramified quadratic extension of $\mathbb{Q}_p$, with $R$ its ring of integers and the Galois conjugation as involution, and take the smallest frame, $\varrho = 0$ and $n = 1$. Then there is one floor, the frame is the single vector $z$, and the position $x$ is an integral isometry. The level $g = p^e$ gives the congruence subgroup $K(p^e)$ of the isometries congruent to $1$ modulo $p^e$. The common denominator ideal of the entries of $(x - 1)/g$ is $J = p^{c}R$ with $c \ge 0$, of index $[R : J] = p^{2c}$, and $c = 0$ exactly when $x \in K(p^e)$. The dyadic shell of index $t$ holds the $x$ with $2^{t-1} < [R : J] \le 2^t$. A large index forces a deep vector, so the integral over a shell decays like a power of $2^{-t}$, and the decay pays for the number of ideals in the shell.

### What the chapter uses

- The abstract theory of local frames: place data, gauges, the forms $\mathcal{I}_j$, the majorant $\mathsf{F}^*_j$, depth and shells ([local frames](/chapter/local-frames/)).
- Congruence subgroups $K(g)$, the modulus $|\cdot|$ and the generalised index $\iota$ ([congruence subgroups and Haar moduli](/chapter/congruence-subgroups/)).
- Fibre measures of hermitian forms and disintegrations ([fibre measures and hermitian quadrics](/chapter/congruence-subgroups/#fibre-measures-and-hermitian-quadrics)).
- The local densities, the ideal zeta value $\zeta_R(\mu)$ and the kernels with bounded masses on the standard space ([Siegel-Weil](/chapter/siegel-weil/)).
- The floors and the Bessel groups $\mathsf{U}$ and $H$ ([floors and the Bessel subgroup](/chapter/bessel-bruhat/)).
- The finite head weight `New.finHeadWeight` and the Bessel lattice basis ([the anatomy of a term](/chapter/anatomy-of-a-term/)).

The notation is that of [local frames](/chapter/local-frames/): $n = \varrho + 1$, the frame $e_0, \dots, e_{\varrho-1}, z$, the groups $\mathsf{U}$, $H$ and $G^{(l)}$, the group measure $\mathsf{M}$, the Heisenberg measures $\eta_l$, the depth $\delta_a$ with the stable products $\mathfrak{d}_a$, the volume exponent $s$, the head density $\kappa_j$, the shell normalization $\mathcal{N}(W)$ and the gauge loss $\Lambda$. In addition $R$ is the ring of integers, $K = K(1)$, and $k$ is the rank of $X_0$.

No file of this chapter imports a file of a later chapter of this volume. `StandardLevel` imports `New/Spanning/Unfolding/BesselLevelStructure`, which belongs to the earlier [chapter on the anatomy of a term](/chapter/anatomy-of-a-term/).

### The plan

1. [The lattice datum](/chapter/finite-densities/#the-lattice-datum). Place data from an integral lattice, and the gauge of scale $\alpha$.
2. [Masses at the standard level](/chapter/finite-densities/#masses-at-the-standard-level). The masses of $K(g)$ and $K$.
3. [The finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector). The vector $W_Z$ and its norms.
4. [Depth and heads](/chapter/finite-densities/#depth-and-heads). Depth as an index, integral heads, and far means deep.
5. [Shells, decay and mass](/chapter/finite-densities/#shells-decay-and-mass). Decay in the frequency and the mass integral.
6. [The top floor](/chapter/finite-densities/#the-top-floor). The density at the last entry, its Fourier transform and its positivity.
7. [Exercises](/chapter/finite-densities/#exercises).

### The two results that leave the chapter

[The main term](/chapter/main-term/) uses two results of this chapter most. The exact statements are in the sections named.

The *decay in the frequency* ([Theorem](/decl/New.Floors.IntegralPlace.IsLargeLatticeData.enorm_floorForm_le/)): the form of floor $j$ with a character weight of frequency $\xi$ is at most the mass ratio times $\sqrt{\iota(\xi)}^{\,t}$, times the inverse sixth power of the denominator index of $\xi$, times $(2/|g|)^{L}$ for a large exponent $L$, times the finite head weights of $p$ and $q$.

The *mass with an error* ([Theorem](/decl/New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error/)): the mass integral of $Z$ is at most $\mathsf{M}(Z)\mathsf{M}(K(g))(\mathsf{M}(Z) + Q^{-t})$. The first term comes from the positions in $K(g)$; the error comes from the shells.

### How to read the chapter

The sections are in logical order. Sections 2 and 3 are needed everywhere. Section 4 depends on them only. Sections 5 and 6 depend on all of 2 to 4, and section 6 does not depend on section 5. A reader who wants only the two results above can read sections 2 to 5.
