---
title: The chapter
lean:
  - Lib/Adelic/QuotientMeasure/Basic.lean
  - Lib/Adelic/Reduction/FiniteVolume.lean
  - Lib/Adelic/Reduction/DefiniteClassSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter

This chapter studies the quotient $\Gamma_V \backslash G$ of the adelic unitary group by the rational points of a space $V$. It gives four things. First, it gives a way to integrate over a quotient by a discrete group without a fundamental domain. Second, it gives the unfolding identities that turn an integral of a sum over $\Gamma$ into an integral over a smaller quotient. Third, it gives the geometry of numbers over $E$: the two theorems of Minkowski, the first minimum of a space and the short bases of its lattice. Fourth, it gives the finite volume of $\Gamma_V \backslash G$, Weil's criterion for the convergence of theta integrals, the compactness criterion of Mahler, and the finiteness of classes for definite spaces.

The notation is that of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). So $E$ is a CM field with maximal totally real subfield $F$, $f = [F : \mathbb{Q}]$ is the number of infinite places of $E$, and $s$ is a choice of $n$ signs. The group $G = G_\infty \times G_f$ is the adelic unitary group of the standard form $\varepsilon_s$, and $K_0$ is the standard level with $\operatorname{vol}(K_0) = 1$. A space $V = (J, x)$ has $x^* J x = \varepsilon_s$, rational points $\Gamma_V \subset G$, finite rational points $\Gamma_{V,f} \subset G_f$, and base lattice $E^n \cap x_f \hat{\mathcal{O}}_E^n$. The space $I_n$ is $(1, 1)$ with all signs $+1$. These objects are defined in [the spaces of the source](/chapter/adeles-hermitian-spaces/#hermitian-spaces-with-a-point).

### The classical theory

Reduction theory begins with Hermite and Minkowski. A positive definite real quadratic form in $n$ variables is equivalent under $\mathrm{GL}_n(\mathbb{Z})$ to a *reduced* form, and the reduced forms make a set that meets only finitely many of its translates. In the language of groups: let $K = O(n)$, let $A$ be the positive diagonal matrices and let $N$ be the upper unipotent matrices of $\mathrm{GL}_n(\mathbb{R})$. For $t > 0$ and a compact set $\omega \subset N$, the *Siegel set* is
$$\mathfrak{S}_{t, \omega} = \omega \, A_t \, K, \qquad A_t = \{a \in A : a_i / a_{i+1} \le t \text{ for all } i\},$$
with the convention that matrices act on the right of row vectors, or the mirror image of this convention. For $t \ge 2/\sqrt{3}$ and $\omega$ large enough, $\mathrm{GL}_n(\mathbb{R}) = \mathrm{GL}_n(\mathbb{Z}) \, \mathfrak{S}_{t,\omega}$, and the set of $\gamma \in \mathrm{GL}_n(\mathbb{Z})$ with $\gamma \mathfrak{S} \cap \mathfrak{S} \ne \emptyset$ is finite. A Siegel set has finite volume for the Haar measure of $\mathrm{SL}_n(\mathbb{R})$, so $\mathrm{SL}_n(\mathbb{Z}) \backslash \mathrm{SL}_n(\mathbb{R})$ has finite volume. Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, Chapter 4, give this theory for $\mathrm{GL}_n$ and then for all arithmetic groups.

Borel and Harish-Chandra extended the theory to every reductive group $\mathbf{G}$ over $\mathbb{Q}$ (A. Borel and Harish-Chandra, *Arithmetic subgroups of algebraic groups*, Ann. of Math. 75 (1962)). An arithmetic subgroup $\Gamma$ of $\mathbf{G}(\mathbb{R})$ has a fundamental set that is a finite union of translates of Siegel sets. The quotient $\Gamma \backslash \mathbf{G}(\mathbb{R})$ has finite volume if and only if $\mathbf{G}$ has no nontrivial character over $\mathbb{Q}$. It is compact if and only if $\mathbf{G}$ is anisotropic over $\mathbb{Q}$. The criterion of compactness is due to Borel and Harish-Chandra, and to Mostow and Tamagawa. Godement gave an adelic treatment (R. Godement, *Domaines fondamentaux des groupes arithmétiques*, Séminaire Bourbaki, exposé 257, 1962/63).

The adelic form of the theory has a second finiteness result. For a reductive group $\mathbf{G}$ over a number field and an open compact subgroup $K$ of the finite adelic points, the double coset space $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_{F,f}) / K$ is finite. Its cardinality is the *class number* of $K$. For the orthogonal group of a quadratic form, it is the number of classes in the genus of a lattice. Borel proved the general case in *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16 (1963), §§4.5 to 5.8, and Platonov and Rapinchuk give it in Chapter 8. For a unitary group $U(V)$ of a hermitian space over a CM field, the group has no character over $F$ and is anisotropic over $F$ when $V$ is definite at some real place. So $\Gamma_V \backslash G$ has finite volume for every space $V$, and it is compact when $V$ is definite.

The last classical tool is Mahler's compactness criterion. A set of lattices in $\mathbb{R}^m$ of bounded covolume is relatively compact in the space of lattices if and only if the lengths of their nonzero vectors are bounded below by one positive number. Cassels, *An Introduction to the Geometry of Numbers*, Chapter V, proves it, and Chapter VIII gives Minkowski's second theorem on successive minima, which is the main input.

### What the source proves

The source does not build Siegel sets or fundamental domains. It integrates over a quotient $\Gamma \backslash X$ by a *cutoff*: a measurable function $\beta \ge 0$ on $X$ whose sum over each orbit of $\Gamma$ is $1$. The measure $\beta \mu$ on $X$ then computes integrals of $\Gamma$-invariant functions over $\Gamma \backslash X$. Section 2 gives this construction and shows that the result does not depend on the cutoff. Section 3 gives the unfolding identities in this language. They are the only tools that the argument uses to move between quotients.

The finiteness results are then proved by counting. Section 4 proves Minkowski's two theorems for adelic lattices over $E$, with explicit constants in $f$, $n$ and the root discriminant of $E$. Section 5 defines the *first minimum* of a space, and from it the *height* of a point $g \in G$: the inverse of the first minimum of the moved space $(J, xg)$, cut off below at $1$. It proves that the base lattice of a moved space has a basis of vectors of length at most a constant times the inverse first minimum. Section 6 uses these bounds to prove, for every space $V$ and every compact set $\Omega$ of $n \times t$ matrices with $2t < n$:
$$\int_{\Gamma_V \backslash G} \#\{\xi \in M_{n \times t}(E) : (x g)^{-1} \xi \in \Omega\} \, dg < \infty,$$
in the normalization of the source. The case $t = 0$ is the finite volume of $\Gamma_V \backslash G$. The same section proves the half of Mahler's criterion that the argument needs: the points of bounded height lie in $\Gamma_V C$ for one compact set $C$. For a definite space all heights are $1$, so $\Gamma_V \backslash G$ is compact. Last, for the definite space $I_n$ the double cosets $\Gamma_{V,f} \backslash G_f / K$ are finite for every level $K$, and the integral over $\Gamma_V \backslash G$ becomes a finite class sum.

### Where the argument uses the chapter

[The plan](/chapter/theorem-and-plan/) reduces the Generalized Riemann Hypothesis to three theorems on theta lifts. The source uses this chapter in four places.

1. Every inner product of automorphic forms, every theta integral and every period is an integral against the quotient measure of Section 2. The source uses this measure in 33 files of the argument.
2. The unfolding identities of Section 3 write the seesaw integrals of [Theorem A: the plan](/chapter/theorem-a-plan/) as sums over cosets. In [Theorem B: the plan](/chapter/theorem-b-plan/) they unfold the Poincaré series, and the vanishing criterion for twisted functions removes the nonconstant terms of the climbing step.
3. The finite volume and Weil's criterion make the theta integrals converge. The short bases of Section 5 bound the theta kernel of the comparison operator in [Theorem C: the plan](/chapter/theorem-c-plan/). Minkowski's second theorem gives the frames of Siegel's lemma in the remaining terms of Theorem B.
4. The compactness of the definite quotient and the class sums turn integrals over a definite quotient into finite sums. This is how the forms on definite unitary groups of [automorphic forms](/chapter/automorphic-forms/) become functions on finite sets. Theorems A and C use this.

### The plan of the chapter

Section 2 builds the quotient measure. Section 3 gives the unfolding identities. Section 4 proves Minkowski's theorems over $E$. Section 5 treats the first minimum, the height and short bases. Section 6 proves the finite volume, Weil's criterion, Mahler's criterion and the finiteness of classes. Section 7 has exercises and the notes.

The proofs of Section 6 are the longest of the chapter. They are elementary, but they need the counts of Section 4 in a precise form. A reader who wants only the statements can read the theorems of Sections 2, 5 and 6 and skip the proofs.
