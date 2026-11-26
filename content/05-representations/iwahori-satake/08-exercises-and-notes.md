---
title: Exercises, notes and the summary of Volume 5
lean:
  - Lib/LocalGL/Iwahori/HeckeDegrees.lean
  - Lib/LocalGL/SphericalChainLemma.lean
  - Lib/Weil/Unramified/HeckeTransfer.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\binom{N}{j}_q$ be the number of subspaces of dimension $j$ of $k^N$, where $k$ has $q$ elements. Show the identity $\binom{N+1}{j}_q = \binom{N}{j}_q + q^{N+1-j}\binom{N}{j-1}_q$ for $j \geq 1$. Then show by induction on $N$ that
$$e_j(1, q, \ldots, q^{N-1}) = q^{j(j-1)/2}\binom{N}{j}_q.$$
This is the step of the example of section 4 that gives $t_j = \binom{N}{j}_q$ for the trivial representation.

*Hint.* For the first identity, fix a hyperplane $H$ of $k^{N+1}$. A subspace $U$ of dimension $j$ is either in $H$, or $U \cap H$ has dimension $j - 1$. For a fixed $W \subseteq H$ of dimension $j - 1$, count the subspaces $U \not\subseteq H$ with $U \cap H = W$: they correspond to the lines of $k^{N+1}/W$ that are not in $H/W$, and there are $q^{N+1-j}$ of them. For the second identity, use $e_j(1, \ldots, q^N) = e_j(1, \ldots, q^{N-1}) + q^N e_{j-1}(1, \ldots, q^{N-1})$ and the equality $j(j-1)/2 - (j-1)(j-2)/2 = j - 1$.

**Exercise 2.** Use Exercise 1 to show that
$$\prod_{l<n}(1 - q^l X) = \sum_{i=0}^{n} (-X)^i\, q^{i(i-1)/2}\binom{n}{i}_q.$$
Conclude that a vector fixed by all of $G_f$ has the Hecke polynomial of the example on fixed vectors in section 7 (Lean: `New.SiegelWeil.hasHeckePolynomial_qPochhammer`). Do the case $n = 2$ by hand: there are $q + 1$ lines in $k^2$, and $(1 - X)(1 - qX) = 1 - (q + 1)X + qX^2$.

*Hint.* Expand the product. The coefficient of $(-X)^i$ is $e_i(1, q, \ldots, q^{n-1})$. For the conclusion, a fixed vector $v$ has $T_{w,i}\,v = \binom{n}{i}_q\, v$, since $T_{w,i}$ is a sum over the subspaces of codimension $i$ of $k^n$, and the number of these is the number of subspaces of dimension $i$.

**Exercise 3.** Let $t = \operatorname{diag}(\varpi, 1, \ldots, 1)$. Show that the double coset $I_1 t I_1$ is the union of exactly $q^{N-1}$ left cosets $gI_1$. Compare with the example after the theorem on Iwahori degrees in section 4 (Lean: `New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`).

*Hint.* The number of cosets is the index of $I_1 \cap t I_1 t^{-1}$ in $I_1$. Conjugation by $t$ multiplies the entry at $(i, j)$ by $t_i/t_j$. So the entries at $(0, j)$ with $j > 0$ get the factor $\varpi$, the entries at $(i, 0)$ with $i > 0$ get the factor $\varpi^{-1}$, and the other entries do not change. An element of $I_1$ is in $t I_1 t^{-1}$ if and only if its entries at $(0, j)$, $j > 0$, are in $\mathfrak{p}$. Each of these $N - 1$ entries gives a factor $q$ in the index.

**Exercise 4.** Let $N = 2$, and let $P$ be the Hecke polynomial of a spherical eigenvector of a unitary representation, with roots $y_0$ and $y_1$ and $|y_0| \geq |y_1|$. Use the lemma on symmetry of section 6 to show that either $|y_0|^2 = |y_1|^2 = q$, or $y_1 = q/\bar y_0$. Then use the bound of the chain lemma to show that $1 \leq |y_i|^2 \leq q^2$ for $i = 0, 1$.

*Hint.* The number $q/\bar y_0$ is a root. If it is $y_0$, then $|y_0|^2 = q$; apply the same argument to $y_1$. If it is $y_1$, then $|y_0||y_1| = q$. For the bound, look at $c = y_1$. If $qy_1$ is not a root, the chain lemma gives $|y_1|^2 \geq 1$. If $qy_1 = y_0$, then $|y_1|^2 q = |y_0||y_1| = q$. In both cases $|y_1|^2 \geq 1$, and so $|y_0|^2 = q^2/|y_1|^2 \leq q^2$. Compare with the complementary series of $\mathrm{GL}_2$ in section 6.

**Exercise 5.** Let $P$ be the Hecke polynomial of a spherical eigenvector of a unitary representation of $\mathrm{GL}_N$, and assume that $1$ is a root of $P$. Show that the roots of $P$ are $1, q, \ldots, q^{N-1}$, and that $t_j = \binom{N}{j}_q$ for all $j$. So the eigenvalues are those of the trivial representation.

*Hint.* Apply the theorem on chains of section 6 to $c = 1$ with $k = N$: then $|c|^2 q^k = q^N$. So $1, q, \ldots, q^{N-1}$ are roots. They are distinct since $q > 1$, and $P$ has degree $N$ and is monic, so $P = \prod_{i<N}(X - q^i)$. Compare the coefficients of $P$ with those of section 4, and use Exercise 1.

**Exercise 6.** Let $N = 2$. The exponent of the Steinberg representation has $(y_0, y_1) = (1, q)$, as in the example of section 5. Show that these numbers satisfy the relations of the chain lemma for the trivial representation: they are the roots of $X^2 - (q + 1)X + q$, and they form a chain of length $2$. Explain why this does not contradict the absence of a spherical vector in the Steinberg representation.

*Hint.* The chain lemma and the formula of Satake are about spherical eigenvectors, and the Steinberg representation has none. The theorem at the start of section 5 says: if $\theta$ is unramified, $|\theta_i(\varpi)|$ does not increase with $i$, and an exponent for $\xi_\theta$ vanishes on the spherical vectors, then the exponent is $0$. In the Steinberg representation every exponent vanishes on the spherical vectors. So the theorem shows that a nonzero exponent cannot be sorted, and $(1, q)$ is in the wrong order.

**Exercise 7.** In the setting of the transfer through a theta lift in section 7, let $y$ have the Hecke polynomial $p(X) = \prod_{l<n}(1 - q^l c X)$ at $w$, for a number $c \neq 0$. This is the Hecke polynomial of a vector on which the group acts by a character of the determinant with value $c$ at the uniformiser (Lean: `New.SiegelWeil.hasHeckePolynomial_of_apply_eq_smul_det`). Show that the theta lift of $y$ has the Hecke polynomial $\prod_{l<n+k}(1 - q^l\alpha X)$ if and only if $c = \beta$. Describe the roots of the lift for other values of $c$, and find the chains in the sense of section 6.

*Hint.* By the theorem on the Hecke polynomial of a theta lift, the lift has the polynomial
$$\prod_{l<k}(1 - q^l\alpha X)\cdot\prod_{l<n}(1 - q^{k+l}\alpha\beta^{-1}c\,X).$$
The roots are $q^l\alpha$ for $l < k$ and $q^{k+l}\alpha\beta^{-1}c$ for $l < n$. They form one chain of length $n + k$ if and only if $\alpha\beta^{-1}c = \alpha$. Otherwise there are a chain of length $k$ and a chain of length $n$, which can overlap.

## Notes and references

The spherical Hecke algebra and the map that the formula of Satake describes are from Satake, *Theory of spherical functions on reductive algebraic groups over $\mathfrak{p}$-adic fields*, Publ. Math. IHES 18 (1963). The Iwahori subgroup and the structure of its Hecke algebra are from Iwahori and Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings of $\mathfrak{p}$-adic Chevalley groups*, Publ. Math. IHES 25 (1965). The quadratic relation of section 3 is the relation $(T_s - q)(T_s + 1) = 0$ of that paper, in the form that the source needs. Borel, *Admissible representations of a semi-simple group over a local field with vectors fixed under an Iwahori subgroup*, Invent. Math. 35 (1976), relates the Iwahori fixed vectors to the Jacquet module. The source names Casselman, *The unramified principal series of $p$-adic groups I. The spherical function*, Compositio Math. 40 (1980), and Haines, Kottwitz and Prasad, *Iwahori-Hecke algebras*, arXiv:math/0309168, as the standard references for exponents and Iwahori-Hecke algebras. A textbook account of the spherical theory for $\mathrm{GL}_2$ is chapter 4 of Bump, *Automorphic Forms and Representations*, Cambridge University Press (1997).

The source does not use the Jacquet module or the Bernstein centre. It works with the pro-$p$ Iwahori subgroup $I_1$, with the means $U_t$, and with exponents as linear forms. This is the reason for the elementary proofs of sections 2 to 5. The standard results that correspond to them are the existence of exponents on the Jacquet module, which is in Casselman's paper, and the theory of the principal series of $\mathrm{GL}_N$ in Bernstein and Zelevinsky, *Induced representations of reductive $\mathfrak{p}$-adic groups I*, Ann. Sci. ENS 10 (1977).

The unitary dual of $\mathrm{GL}_N$ over a $p$-adic field is in Tadić, *Classification of unitary representations in irreducible representations of general linear group (non-Archimedean case)*, Ann. Sci. ENS 19 (1986). The chain lemma of section 6 is a weaker statement for the spherical case, with an algebraic proof from the pairing identities. Section 6 compares the two. The unramified theta correspondence, which section 7 uses at split places, is in the papers of Howe, Rallis and Kudla that section 7 names.

The source uses the results of this chapter in later volumes. The passage from an Iwahori eigenform to a spherical eigenform with a given Hecke polynomial is [Theorem](/decl/New.IsIwahoriEigen.exists_hasHeckePolyAt/). The Hecke polynomials at split places are the local data of the Galois representations in [Building the representations](/chapter/building-representations/). The transfer of Hecke polynomials through theta lifts is used with the theta lifts of [Theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). Lean accepts the statements of this chapter, if the reported checks hold.

## Summary of Volume 5

Volume 5 collects the facts about representations of local groups that the three main theorems of the source use. It does not use the global theory of automorphic forms. Each chapter gives the definitions of the source, the statements in full, and the proofs that the source formalizes.

1. [Discrete series through one matrix coefficient](/chapter/discrete-series/) defines an explicit function $c_\lambda$ on $U(p, q)$ for a parameter $\lambda$ far from the walls. It proves the properties of a discrete series coefficient: decay, Schur orthogonality, the formal degree, the character on the compact torus, the holomorphic case and the vanishing of constant terms.
2. [Laplace's method for discrete series coefficients](/chapter/laplace-method/) shows that $c_\lambda$ is close to a Gaussian near the identity when $\lambda$ is large in a fixed direction. It gives a lower bound for a period of two coefficients on $U(p, q)$ and $U(p + 1, q)$.
3. [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/) builds the Bessel subgroup of a split unitary group, a Bruhat decomposition on the big cell over a field and over a ring of integers, and explicit Haar measures on the unipotent groups with upper bounds.
4. [Integral Weyl modules and branching](/chapter/weyl-modules/) constructs lattices in the polynomial representations of products of $\mathrm{GL}_n$ from products of minors, with integer Gram matrices, norm bounds and integer branching matrices to $\mathrm{GL}_{n-1}$.
5. [Characters of GL_n over a finite field](/chapter/finite-gln/) constructs the characters of $\mathrm{GL}_n(k)$ with a squarefree label, proves Green's theorem for them, and proves the Shintani lifting along an extension of prime degree.
6. This chapter, [Iwahori exponents, Satake and the chain lemma](/chapter/iwahori-satake/), finds exponents of Iwahori fixed vectors, computes the Hecke eigenvalues of spherical vectors from them by the formula of Satake, and proves a chain lemma for the Hecke polynomial of a unitary representation. It also computes the Hecke polynomials at split places and their transfer through theta lifts.

The real chapters 1 to 3 give the archimedean local data: test functions, their coefficients and their periods. The chapters 4 to 6 give the algebraic and nonarchimedean data: coefficient systems with integral structure, types at the finite places, and Hecke polynomials. The later volumes put these local facts into the global arguments for Theorems A, B and C. The plans are in [the plan of Theorem A](/chapter/theorem-a-plan/), [the plan of Theorem B](/chapter/theorem-b-plan/) and [the plan of Theorem C](/chapter/theorem-c-plan/).
