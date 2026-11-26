---
title: The chapter and its place
lean:
  - Lib/Adelic/Hecke/Basic.lean
  - Lib/Adelic/Hecke/ClassSums.lean
  - Lib/Adelic/AutomorphicForms/Basic.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter is the third chapter of Volume 4. It gives the automorphic forms that the source uses, on definite and on indefinite unitary groups. It also gives the Hecke operators that act on them, the finite sums over classes that replace integrals on a definite group, and the $p$-adic gauges that measure the size of a form at a prime. [The plan](/chapter/theorem-and-plan/) explains how the source reduces the Generalized Riemann Hypothesis to three theorems on one lattice of automorphic forms. This section says which parts of this chapter each of the three theorems uses.

### What comes before

[Adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) gives the objects of this chapter, and we keep its notation. Thus $E$ is a CM field with a CM type, $F = E^+$ is its totally real subfield, and $n$ is a finite index set. A family of signs $s$ fixes the archimedean group $G_\infty$, a product over the infinite places of $E$ of unitary groups $U(\operatorname{diag} s)$. The finite group $G_f$ is the unitary group of the identity form over the finite adeles of $E$, and $G = G_\infty \times G_f$. The standard level $K_0 \subset G_f$ is the stabilizer of the lattice $\hat{\mathcal{O}}_E^n$, and the Haar measure on $G_f$ gives $K_0$ volume $1$. A *level* is an open subgroup $K \subseteq K_0$, and $[K_0 : K]$ is its index. A hermitian space $V = (J, x)$ with $x^* J x = \operatorname{diag} s$ has a group $\Gamma_V \subset G$ of rational points and a finite part $\Gamma_{V,f} \subset G_f$. The standard definite space $I_n$ has all signs $+1$ and point $1$.

[Quotients and reduction theory](/chapter/reduction-theory/) gives the measure on $\Gamma_V \backslash G$, the height of a point, Minkowski's theorems, and Mahler's criterion of compactness. This chapter uses these results in Sections 4 and 5. Where a result of that chapter enters a proof, we state it in full at that place.

### The plan of the chapter

The chapter has nine sections.

1. *The chapter and its place* (this section).
2. *Classical automorphic forms.* Modular forms of weight $k$ and level $\Gamma_0(N)$, automorphic forms on a reductive group over the adeles in the sense of Borel and Jacquet, cusp forms, the finite dimension of a space of cusp forms of fixed type, and the classical Hecke operators. Nothing in this section is new. It fixes the model that the later sections follow.
3. *Hecke operators and class sums.* The space of vectors of a representation on which a subgroup $K$ acts by a character, the Hecke operator of a function on $G/K$, and the class sum: the sum over the finite set $\Gamma \backslash G / K$ of the values of a function, each one divided by the order of a stabilizer. On a definite group the class sum takes the place of the integral over the quotient.
4. *Forms of a type.* The source's automorphic functions and its forms of type $e$, for a function $e$ on $G_\infty$: bounded automorphic functions that the right convolution by $e$ fixes. The Petersson product, the representation of $G_f$ on forms, and the kernels $e_\lambda$ attached to discrete series parameters.
5. *Cuspidality and finite dimension.* Forms of type $e$, for a cusp kernel $e$, have vanishing constant terms and decay rapidly in the height. The space of such forms of a fixed level is finite-dimensional.
6. *Algebraic forms on definite groups.* For a definite space, the forms are functions on $G_f$ with values in a finite-dimensional representation of the rational group. At a level where all stabilizers are trivial, such a form is a vector-valued function on the finite set of double cosets $\Gamma_{V,f} \backslash G_f / K$.
7. *Automorphic forms as algebraic forms, and eigenforms.* On the standard definite space, forms of type $e_\lambda$ are the same as algebraic forms of the matching weight. The Petersson product is a class sum. A finite-dimensional space of algebraic forms that the Hecke operators at almost all split places preserve is spanned by eigenforms.
8. *The $p$-adic gauge.* The size at a prime $p$ of the value of an algebraic form, and the integrality of class sums.
9. *Exercises and notes.*

### How the three theorems use the chapter

*Theorem A.* [Theorem A: the plan](/chapter/theorem-a-plan/) shows that the source forms are spanned by forms whose lifts are short at every archimedean place and divisible by large powers of the small primes. The lifts land in spaces of algebraic forms on definite groups (Section 6). The divisibility is read through the $p$-adic gauge of Section 8, and the Hecke operators of Section 3 enter the divisibility at the primes. The forms supported on one double coset (Section 6) are the building blocks of the columns of the lift. The finite dimension of Section 5 enters through the rows of the lift, which are forms of type $e_\lambda$ on an indefinite group.

*Theorem B.* [Theorem B: the plan](/chapter/theorem-b-plan/) shows that a few translates of the image of the source fill almost all of the target. It uses the Poincaré series of Section 4, the forms of type $e$ of Section 4, the dimension formula $\#(\Gamma \backslash G_f / K) \cdot \dim W$ of Section 6, and the Hecke operators of Section 3.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) gives the matching lower bound for the covolume of a family of target forms. It uses the forms of type $e$ and the Petersson product of Section 4, the finite dimension of Section 5 for auxiliary forms of deep level, the identity of Section 7 between the Petersson product and a class sum, and the integrality of Section 8. The congruences that Theorem C needs ([regular families: the plan](/chapter/regular-families-plan/)) use the spanning by eigenforms of Section 7 and the unitary pairing on algebraic forms that the spanning needs.

Each later section ends with a part that names the chapters where the argument uses its objects.

### Conventions

All vector spaces are over $\mathbb{C}$ unless we say otherwise. For a subgroup $K$ of a group $G$ and a function $F$ on $G$, the function $F$ is *right $K$-invariant* if $F(gk) = F(g)$ for all $g \in G$ and $k \in K$. For a function $F$ on $G = G_\infty \times G_f$ and a subgroup $K$ of $G_f$, we say that $F$ *has level $K$* if $F(g \cdot (1, k)) = F(g)$ for all $g \in G$ and $k \in K$. A sum over an infinite index set with infinitely many nonzero terms has no meaning in this chapter unless we say how the source assigns it a value. Section 3 says how.
