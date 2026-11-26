---
title: The volume and the chapter
lean:
  - Lib/Weil/Construction/HeisenbergModel.lean
  - Lib/Weil/Construction/WeilOperators.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chapter

This chapter opens Volume 6. The volume builds the theta correspondence for unitary groups over a CM field: the Weil representation, the local theta correspondence at the real places, the global theta lifts and the seesaw, the periods over Bessel subgroups, the Siegel-Weil formula and the Rallis inner product formula. This first section gives the plan of the volume and says how each chapter serves Theorems A, B and C. It then says what this chapter proves and what it uses.

### The plan of the volume

The volume has six chapters. Each one uses the objects of the chapters before it.

1. *The Weil representation from a vacuum* (this chapter). The Heisenberg group of a hermitian space, the Weil representation of the adelic unitary group, the theta functional, the mixed models of a split space, and Weil's theorem that the theta functional is invariant under the rational points.
2. [Local theta in the Fock model](/chapter/local-theta/). The local theta correspondence at the real places, in the Fock model. An argument of Howe replaces the full Howe duality theorem.
3. [Theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). The theta kernels and their growth, the lifts between definite unitary groups, the Galois law for the lifts, and the seesaw identity for periods.
4. [Bessel periods and one step of unfolding](/chapter/bessel-periods/). Periods over a Bessel subgroup, and one step of the unfolding of a period of a theta lift.
5. [The Siegel-Weil formula](/chapter/siegel-weil/). The Siegel-Weil formula in Weil's range of convergence, and Siegel's mass formula.
6. [Doubling and the Rallis inner product formula](/chapter/rallis-inner-product/). The doubling method, the Rallis inner product formula and the tower of theta lifts.

### How the volume serves the three theorems

The source reduces the Generalized Riemann Hypothesis to a main inequality, and the main inequality comes from three theorems on one lattice of automorphic forms. [The plan](/chapter/theorem-and-plan/) describes the reduction. The volume serves the three theorems as follows.

*Theorem A.* [Theorem A: the plan](/chapter/theorem-a-plan/) is the upper bound of the argument. Its proof uses a chain of theta lifts, a seesaw identity and a bound at the archimedean places. The theta kernels of that chain come from this chapter and from [local theta in the Fock model](/chapter/local-theta/). The lifts and the classical seesaw are in [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). The first step of the unfolding is in [Bessel periods and one step of unfolding](/chapter/bessel-periods/).

*Theorem B.* [Theorem B: the plan](/chapter/theorem-b-plan/) uses only Chapter 4 of this volume. It needs the unfolding of a period over a Bessel subgroup. The Petersson formula of Volume 10 repeats this step.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) uses all six chapters. It takes the Fock model and the mixed models of the theta kernels from this chapter. It takes the dual pairs, the definite lifts and the seesaw from Chapter 3. It takes the false lifts and the comparison operator from Chapter 4, and the constants of the exchange identity from Chapter 5. From Chapter 6 it takes the injectivity of a single theta lift and the identity for the determinant of a chain.

[The reading paths](/chapter/how-to-read/) give the same dependencies in the order of reading.

### What this chapter does

Let $E$ be a CM field with totally real subfield $F$, and let $V$ be a hermitian space over $E$ of dimension $n$. The classical construction of the Weil representation goes as follows. Restrict the scalars of $V$ to $F$ and take the trace of the hermitian form. This gives a symplectic space $W$ over $F$ of dimension $2n$. The Heisenberg group of $W(\mathbb{A}_F)$ has, by the Stone-von Neumann theorem, one irreducible unitary representation with a given central character. The symplectic group acts on the Heisenberg group, and so it acts on this representation up to scalars. This gives a projective representation of $\mathrm{Sp}(W)(\mathbb{A}_F)$. Weil shows that its cocycle is trivial on the rational points, and that it becomes a true representation on a double cover, the metaplectic group. On the unitary group $U(V)$, a choice of a splitting character makes it a true representation.

The source takes another route. It does not use the Stone-von Neumann theorem, a Schrödinger model or the metaplectic group. It starts from one function, the vacuum $e$ on $W$, which is the matrix coefficient of the vacuum vector. At the real places $e$ is a Gaussian. At the finite places $e$ is the indicator of a self-dual lattice times a semicharacter. The vacuum defines a space of functions by a reproducing kernel, and the Heisenberg group acts on this space. The chapter proves the following results in this setting.

1. Schur's lemma for the model: a bounded operator that commutes with the Heisenberg operators is a scalar, and an invariant sesquilinear form is a multiple of the inner product.
2. The Weil operators of a group that acts on $W$ satisfy a cocycle relation, and the cocycle is an explicit double integral of three vacua.
3. On the unitary group of a hermitian space, this double integral is $1$. At the real places this is a Gaussian integral. At the finite places it is a Gauss sum, and its value is $1$ because of positivity at the split places and a congruence modulo $4$ at the inert places.
4. So the unitary group itself, not a cover, acts on the space $\mathcal{S}(V)$ of the adelic model.
5. There is a theta functional $\theta$ on $\mathcal{S}(V)$, unique up to a scalar. The source normalizes it with Landherr's theorem.
6. Weil's invariance theorem: $\theta(\omega(\gamma) f) = \theta(f)$ for every rational point $\gamma$ of the unitary group.

The proof of the invariance theorem uses the mixed models of a split space. A splitting of $V$ into a hyperbolic part and a smaller space $V_0$ gives a zero term, slices and a law for the Levi subgroup. The theta functional of $V$ is a sum over the rational points of the slices. Two Siegel parabolic subgroups then generate the unitary group of a split space, and a doubling argument with $V \oplus V^-$ gives the general case.

### The sections

Section 2 gives the abstract Heisenberg datum, the vacuum, the model, superposition and Schur's lemma. Section 3 gives the Weil operators of a multiplier action, the cocycle relation and the Weil representation of an action with cocycle $1$. Section 4 gives the Fock model at the real places: the Gaussian vacuum, the multiplier, the proof that the cocycle is $1$, and the polynomial vectors. Section 5 gives the finite places: the Weil data, the lattice vacuum, the multiplier, the Gauss sum and the proof that the cocycle is $1$. Section 6 gives the adelic representation, the theta functional and its normalization. Section 7 gives the mixed models and Weil's invariance theorem. Section 8 has the exercises and the notes.

### What the chapter uses

The chapter uses the hermitian spaces with a point, the adelic unitary group $G = G_\infty \times G_f$ and Landherr's theorem of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). It uses the standard additive character of the adeles and the self-dual measures of Tate's thesis. It uses Haar measure on a locally compact abelian group, dominated convergence, and Fubini's theorem. It does not use the Stone-von Neumann theorem or the theory of the metaplectic group. The condition that $E$ contains a primitive root of unity of order $5040$ from [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) gives the congruence modulo $4$ that makes the Gauss sum equal to $1$ at the inert places.
