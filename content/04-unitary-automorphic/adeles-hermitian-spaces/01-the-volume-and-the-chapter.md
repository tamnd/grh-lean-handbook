---
title: The volume and the chapter
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Unitary/Defs.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chapter

This chapter opens Volume 4. The volume builds the automorphic side of the argument: unitary groups over a CM field, their adelic points, the quotients by the rational points, the automorphic forms on these quotients, one comparison of traces, and the levels and their volumes. This first section gives the plan of the volume and says how each chapter serves Theorems A, B and C. It then says what this chapter proves and what it uses.

### The plan of the volume

The volume has five chapters. Each one takes the objects of the chapters before it and adds one layer.

1. *Adeles and hermitian spaces* (this chapter). The adeles of a CM field $E$, the hermitian spaces over $E$, the unitary groups and their adelic points, the Haar measures, and three classical theorems: Witt's extension theorem, the Iwasawa decomposition and Landherr's theorem.
2. [Quotients and reduction theory](/chapter/reduction-theory/). Integration on a quotient $\Gamma \backslash G$ by a cutoff function, Minkowski's theorems, the finite volume of the quotient, and Mahler's criterion of compactness.
3. [Automorphic forms on unitary groups](/chapter/automorphic-forms/). Forms of a given type on definite and indefinite unitary groups, cuspidality, the finite dimension of a space of forms of fixed level, Hecke operators, and the gauges that measure the size of a form at a $p$-adic place.
4. [A simple trace formula](/chapter/trace-formula/). A comparison of traces of Hecke operators across two hermitian spaces of the same rank and different signatures, for test functions that are cuspidal at one place.
5. [Congruence subgroups and Haar moduli](/chapter/congruence-subgroups/). Congruence subgroups, characters of profinite groups, and the moduli of Haar measures.

### How the volume serves the three theorems

The source reduces the Generalized Riemann Hypothesis to a main inequality, and the main inequality comes from three theorems on one lattice of automorphic forms. [The plan](/chapter/theorem-and-plan/) describes the reduction. The volume serves the three theorems as follows.

*Theorem A.* [Theorem A: the plan](/chapter/theorem-a-plan/) builds a chain of theta lifts between unitary groups of hermitian spaces $X_0, \dots, X_m$ and $Y_0, \dots, Y_m$ over $E$. The spaces and their groups over the adeles are the objects of this chapter. The algebraic forms on definite unitary groups, their Petersson inner products and the Weyl lattices are in Chapter 3. The classes and the levels are in Chapters 2 and 5.

*Theorem B.* [Theorem B: the plan](/chapter/theorem-b-plan/) needs all five chapters. Chapter 2 gives the convergence of the Poincaré series. Chapter 3 gives the spaces of forms and their inner products. Chapter 4 gives the count of dimensions: the target lives on an indefinite space, and the comparison of traces moves the count to definite spaces, where the quotient is a finite set of classes. The argument uses the comparison only through one theorem, which [equal multiplicities](/chapter/equal-multiplicities/) states. Chapter 5 gives the level $K(M)$ and its volume.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) measures the denominators of lattices of forms on definite unitary groups. It uses the definite spaces of this chapter, the class sets of Chapter 2, the forms and Hecke operators of Chapter 3, and the volumes of levels of Chapter 5. The theta lifts that it uses are in Volume 6.

### What this chapter does

The chapter has two kinds of content. The first is classical background, stated with the sources where a reader can find the proofs. The second is the form in which the source states the same objects. The two forms differ in several places, and each difference gets a remark on the formalization.

The classical objects are these. Let $E$ be a CM field. So $E$ is a totally imaginary quadratic extension of a totally real field $F = E^+$, and complex conjugation $x \mapsto \bar x$ is the nontrivial automorphism of $E$ over $F$. [CM fields, towers and places](/chapter/cm-fields/) gives the facts on CM fields and their places that this chapter uses. A hermitian space over $E$ is a finite dimensional vector space $V$ over $E$ with a nondegenerate form $h$ that is linear in the second variable and that satisfies $h(y, x) = \overline{h(x, y)}$. Its unitary group $U(V)$ is an algebraic group over $F$, and its adelic points $U(V)(\mathbb{A}_F)$ form a locally compact group. The rational points $U(V)(F)$ form a discrete subgroup. The automorphic forms of Chapter 3 are functions on the quotient $U(V)(F) \backslash U(V)(\mathbb{A}_F)$.

The source makes four choices that the classical theory does not make.

1. Its ring of adeles is a product of one copy of $\mathbb{C}$ for each infinite place of $E$ and the finite adeles of $E$. This is the adele ring of $E$ only if $E$ is totally complex. A CM field is totally complex, so the choice costs nothing in this book, but the name hides the hypothesis.
2. The unitary group is a group of matrices over the adeles of $E$, not a group scheme over $F$. The finite part is the group of matrices $g$ over the finite adeles of $E$ with $g^* g = 1$.
3. A hermitian space is a matrix $J$ over $E$ together with a chosen adelic point $x$. The point puts the form into a standard shape: $\mathrm{diag}(s)$ at every infinite place for one fixed list of signs $s$, and the identity at every finite place. So the source can describe only the spaces that are locally the identity at every finite place, and the signature is the same at all infinite places.
4. The field $E$ must contain a primitive root of unity of order $5040 = 7!$. Then $E$ is unramified over $E^+$ at every finite place. Several proofs of the chapter use this condition.

The chapter states the classical theorems first. Then it states the forms that the source proves, and it says what the argument uses. Landherr's theorem is the main example. The classical theorem classifies all hermitian spaces over $E$. The source proves only that two of its spaces with the same signs are isometric over $E$, and the remainder of the argument uses only this.

### The sections

Section 2 gives the adeles of a number field and the form of the source: the finite adeles, the integral adeles $\hat{\mathcal{O}}$, the density of $E$ in the finite adeles, the measures and the standard additive character. Section 3 gives the classical theory of hermitian spaces over a CM extension: the local classification, Landherr's theorem, Witt's theorem, and the unitary groups and their adelic points. Section 4 gives the spaces and groups of the source: the standard form, the groups $G_\infty$, $G_f$ and $G$, the standard level $K_0$, the spaces with a point, and the standing condition on roots of unity. Section 5 gives Witt's theorem in the source, over $E$ and over $\hat{\mathcal{O}}$, and the Iwasawa decomposition. Section 6 gives Landherr's theorem in the source, its proof by Hasse's norm theorem and strong approximation, and its use for rational points. Section 7 has the exercises and the notes.

### What the chapter uses

The chapter uses the algebraic number theory of a first course: Dedekind domains, completions at finite places, and the norm and the trace of an extension. From class field theory it uses one theorem, Hasse's norm theorem for cyclic extensions, in the form of [class field theory on finite ideles](/chapter/class-field-theory/). From analysis it uses Haar measure on a locally compact group and the Fourier analysis on the adeles of Tate's thesis, in the form in which the source states it. The chapter does not use the theory of algebraic groups beyond the definitions.
