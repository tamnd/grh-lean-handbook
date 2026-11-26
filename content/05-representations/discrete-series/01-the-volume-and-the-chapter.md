---
title: The volume and the chapter
lean:
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chapter

This section opens Volume 5. It gives the plan of the volume and says which of the three main theorems of the source uses each chapter. Then it gives the plan of this chapter: what it proves, what it uses, and a sketch of the argument. The reading paths of the whole book are in [how to read this book](/chapter/how-to-read/).

### The plan of the volume

The argument of the source rests on three theorems on automorphic forms on unitary groups. They are stated and planned in their own volumes: Theorem A, the short forms, in [the plan of Theorem A](/chapter/theorem-a-plan/); Theorem B, enough forms, in [the plan of Theorem B](/chapter/theorem-b-plan/); and Theorem C, the long forms, in [the plan of Theorem C](/chapter/theorem-c-plan/). Each of the three theorems needs facts about representations of local groups. Volume 5 collects these facts. It has six chapters. Three are about the real unitary group $U(p,q)$, and three are about groups over finite fields, over $p$-adic fields and over the integers.

1. This chapter, *Discrete series through one matrix coefficient*. It defines one explicit function $c_\lambda$ on $U(p,q)$ for each parameter $\lambda$ far from the walls, and proves the facts about $c_\lambda$ that a discrete series coefficient has: decay, Schur orthogonality, the formal degree, the character on the compact torus, the holomorphic case, and the vanishing of constant terms. The source files of Theorems A, B and C all use it. Theorem A uses the cusp kernel built from $c_\lambda$ to make its spaces of forms finite dimensional. Theorem B uses the formal degree and the stable orbital integrals of the kernel $e_\lambda = d_\lambda \overline{c_\lambda}$. Theorem C uses the holomorphic case, the peaks of holomorphic forms and the decay bounds.
2. [Laplace's method for discrete series coefficients](/chapter/laplace-method/). For a parameter that is large in a fixed direction, $c_\lambda$ is close to a Gaussian near the identity. This gives lower bounds for periods. The source files of Theorems B and C use it.
3. [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/). Bessel functions on unitary groups, the measures on Bruhat cells, and the local data at the complex place. The source files of Theorems A, B and C use it.
4. [Integral Weyl modules and branching](/chapter/weyl-modules/). Lattices in the representations of $GL_n$ with explicit norms, and their branching to $GL_{n-1}$. The source files of Theorems A, B and C use it.
5. [Characters of $GL_n$ over a finite field](/chapter/finite-gln/). Green functions and the Shintani lift for the labels that the argument needs. The source files of Theorems A, B and C use it.
6. [Iwahori exponents, Satake and the chain lemma](/chapter/iwahori-satake/). Exponents of Iwahori fixed vectors, the Satake parameters and a chain lemma for unitary groups. The source files of Theorems A and C use it.

The statement "the source files of Theorem X use the chapter" means this: some file under the folder of the theorem in the source (`New/UpperBound` for A, `New/Spanning` for B, `New/Determinant`, `New/OneLift` and `New/Congruences` for C) names a declaration of the chapter. A reader who wants only one of the three theorems can read the chapters of this volume that it uses. This chapter comes first for each of the three.

### What this chapter proves

Let $G = U(p,q)$, the group of complex matrices $g$ of size $n = p + q$ with $g^* J g = J$, where $J$ is a diagonal matrix with $p$ entries $+1$ and $q$ entries $-1$. Let $K = G \cap U(n) \cong U(p) \times U(q)$. Harish-Chandra proved that $G$ has a discrete series: irreducible unitary representations whose matrix coefficients are square integrable. Their parameters are regular weights $\lambda$ of the compact torus, shifted by $\rho$. The classical theory is in Section 2 of this chapter.

The source does not construct these representations. It works with one explicit function for each parameter. For $\lambda$ with a large gap between its entries of opposite sign, it defines a function $c_\lambda$ on $G$ by an integral over $K$, after Flensted-Jensen. Classically $c_\lambda$ is the matrix coefficient of a unit vector in the lowest $K$-type of the discrete series with parameter $\lambda$. The source proves the following properties of $c_\lambda$ directly, without the representation.

- $c_\lambda(1) = 1$, $c_\lambda(g^{-1}) = \overline{c_\lambda(g)}$, and $c_\lambda$ is real analytic. It is an eigenfunction of the Casimir operator with eigenvalue $|\lambda|^2 - |\rho|^2$.
- $|c_\lambda(g)| \le (2/\|g\|)^c$ for every natural number $c$ up to the gap. So $c_\lambda$ is square integrable when the gap is large.
- Schur orthogonality: $d_\lambda \int_G c_\lambda(xya)\overline{c_\lambda(y)}\,dy = c_\lambda(x) c_\lambda(a)$, where $d_\lambda = (\int_G |c_\lambda|^2)^{-1}$ is the formal degree. So $e_\lambda = d_\lambda \overline{c_\lambda}$ is an idempotent for convolution.
- Rigidity: in any unitary representation of polynomial growth, a vector of the lowest $K$-type with Casimir eigenvalue at least $|\lambda|^2 - |\rho|^2$ has the matrix coefficient $c_\lambda$, up to its norm.
- Harish-Chandra's formula: $d_\lambda$ is the Weyl dimension of the representation of $U(n)$ with highest weight $\lambda - \rho$, and the stable orbital integrals of $e_\lambda$ on the compact torus give the conjugate of Weyl's character.
- In the holomorphic chamber $c_\lambda$ is an explicit quotient of products of principal minors, and it reproduces holomorphic functions.
- Integration against an idempotent kernel kills bounded continuous functions that are invariant under a unipotent radical. This is the step that makes the kernel $e_\lambda$ produce cusp forms.

The chapter also explains the measure on $G$. The source takes the Haar measure normalised by the compact dual: the same construction gives $U(n)$ the mass $1$. Section 6 answers the spec question Q-68 on the additive character `wave`.

### The sketch

The argument has three layers. The first layer is the definition. A discrete series coefficient of the lowest $K$-type must transform on both sides under $K$ by the representation of highest weight $\Lambda = \lambda + \rho_n - \rho_c$. For $k \in K$ this coefficient is a polynomial in the entries of $k$: a product $m_\Lambda(k)$ of principal minors. Flensted-Jensen wrote the coefficient on all of $G$ as an average over $K$ of such products, divided by one more product of minors. The source takes this integral as the definition.

The second layer is analysis on $G$. Fischer's inequality bounds the integrand, and this gives $|c_\lambda(g)|^2|\det a_g|^c \le 1$, where $a_g$ is the block diagonal part of $g$. Since $|\det a_g| \ge (\|g\|/2)^2$, $c_\lambda$ decays like a power of $\|g\|$, and the power grows with the gap. A covering argument on $G$ shows that $(2/\|g\|)^c$ is integrable for $c > 8n^2$. The Casimir equation and the decay make the space $U(\mathfrak g)c_\lambda$ a module inside $L^2(G)$. The lowest $K$-type of $c_\lambda$ occurs once. This gives Schur orthogonality.

The third layer identifies the constants. The formal degree comes from the orbital integrals of $e_\lambda$ on the compact torus. They give a Laurent polynomial, and one coefficient of it is $d_\lambda \int_K |m_\Lambda|^2$. Weyl's dimension formula evaluates $\int_K |m_\Lambda|^2$. In the holomorphic chamber the integral over $K$ can be computed. The result is a quotient of minors, and the theory of holomorphic functions applies to it.

### The sizes

All the main results need a gap between the entries of $\lambda$ of opposite sign. The gap is $500n^3 + A$, where $A$ depends on the result: $A$ is the extra decay that the result needs. The formula for the formal degree takes $A = 10n^5$. The holomorphic case needs a gap $\gamma > 500n^3 + A + n + 1$ in the weight. These sizes are far from optimal. Classically the discrete series exists for every regular $\lambda$, and all its $K$-finite matrix coefficients are square integrable. The large gap is the price of a proof that does not build the representation. The later volumes choose parameters with a very large gap, so the price is not a problem for the argument.

### The order of the chapter

Section 2 gives the classical theory with the model case $U(1,1)$. Section 3 gives the source's definitions: parameters, products of minors, the coefficient and the formal degree. Section 4 proves the first properties and the decay. Section 5 proves orthogonality, rigidity and Harish-Chandra's formula. Section 6 treats the holomorphic case, the cusp kernel, the measure and the question Q-68. Section 7 has the exercises and the notes.
