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

This chapter gives the automorphic forms that the source uses on unitary groups, the Hecke operators, the class sums that replace integrals on a definite group, and the $p$-adic gauges. [The plan](/chapter/theorem-and-plan/) explains how the source reduces the Generalized Riemann Hypothesis to three theorems on one lattice of automorphic forms. This section says which parts of this chapter each of the three theorems uses.

### What comes before

[Adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) gives the objects of this chapter, and we keep its notation. Thus $E$ is a CM field with a CM type, $F = E^+$ is its totally real subfield, and $n$ is a finite index set. A family of signs $s$ fixes the archimedean group $G_\infty$, a product over the infinite places of $E$ of unitary groups $U(\operatorname{diag} s)$. The finite group $G_f$ is the unitary group of the identity form over the finite adeles of $E$, and $G = G_\infty \times G_f$. The standard level $K_0 \subset G_f$ is the stabilizer of the lattice $\hat{\mathcal{O}}_E^n$, and the Haar measure on $G_f$ gives $K_0$ volume $1$. A *level* is an open subgroup $K \subseteq K_0$, and $[K_0 : K]$ is its index. A hermitian space $V = (J, x)$ with $x^* J x = \operatorname{diag} s$ has a group $\Gamma_V \subset G$ of rational points and a finite part $\Gamma_{V,f} \subset G_f$. The standard definite space $I_n$ has all signs $+1$ and point $1$.

[Quotients and reduction theory](/chapter/reduction-theory/) gives the measure on $\Gamma_V \backslash G$, the height of a point, Minkowski's theorems, and Mahler's criterion of compactness. Sections 4 and 5 use these results.

### The plan of the chapter

The chapter has ten sections.

1. *The chapter and its place* (this section).
2. *Classical automorphic forms.* Modular forms, adelic automorphic forms in the sense of Borel and Jacquet, cusp forms and classical Hecke operators: the model for the later sections.
3. *Hecke operators and class sums.* Level spaces, Hecke operators, and the class sum over the finite set $\Gamma \backslash G / K$, which takes the place of the integral on a definite group.
4. *Forms of a type.* Bounded automorphic functions fixed by right convolution with a function $e$ on $G_\infty$, the Petersson product, and the kernels $e_\lambda$.
5. *Cuspidality and finite dimension.* For a cusp kernel $e$, forms of type $e$ decay rapidly, and those of a fixed level form a finite-dimensional space.
6. *Algebraic forms on definite groups.* Vector valued functions on $G_f$, and at a free level on the finite set $\Gamma_{V,f} \backslash G_f / K$.
7. *Automorphic forms as algebraic forms.* On $I_n$, forms of type $e_\lambda$ are algebraic forms, and the Petersson product is a class sum.
8. *Hecke eigenforms.* Hecke polynomials, and spanning by eigenforms.
9. *The $p$-adic gauge.* The size of a form at a prime $p$, and the integrality of class sums.
10. *Exercises and notes.*

### How the three theorems use the chapter

*Theorem A.* [Theorem A: the plan](/chapter/theorem-a-plan/) shows that the source forms are spanned by forms whose lifts are short at every archimedean place and divisible by large powers of the small primes. The lifts land in spaces of algebraic forms on definite groups (Section 6). The divisibility is read through the $p$-adic gauge of Section 9, and the Hecke operators of Section 3 enter the divisibility at the primes. The finite dimension of Section 5 enters through the rows of the lift, which are forms of type $e_\lambda$ on an indefinite group.

*Theorem B.* [Theorem B: the plan](/chapter/theorem-b-plan/) shows that a few translates of the image of the source fill almost all of the target. It uses the Poincaré series of Section 4, the forms of type $e$ of Section 4, the dimension formula $\#(\Gamma \backslash G_f / K) \cdot \dim W$ of Section 6, and the Hecke operators of Section 3.

*Theorem C.* [Theorem C: the plan](/chapter/theorem-c-plan/) gives the matching lower bound for the covolume of a family of target forms. It uses the forms of type $e$ and the Petersson product of Section 4, the finite dimension of Section 5 for auxiliary forms of deep level, the identity of Section 7 between the Petersson product and a class sum, and the integrality of Section 9. The congruences that Theorem C needs ([regular families: the plan](/chapter/regular-families-plan/)) use the spanning by eigenforms of Section 8 and the unitary pairing on algebraic forms that the spanning needs.

### Conventions

All vector spaces are over $\mathbb{C}$ unless we say otherwise. For a function $F$ on $G = G_\infty \times G_f$ and a subgroup $K$ of $G_f$, we say that $F$ *has level $K$* if $F(g \cdot (1, k)) = F(g)$ for all $g \in G$ and $k \in K$.
