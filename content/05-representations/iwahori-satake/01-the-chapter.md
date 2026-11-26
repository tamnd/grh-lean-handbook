---
title: The chapter
lean:
  - Lib/LocalGL/Iwahori/ParahoricStructure.lean
  - Lib/LocalGL/Iwahori/HeckeDegrees.lean
  - Lib/LocalGL/SphericalChainLemma.lean
decls:
  - New.IsExponent
  - New.IsExponent.apply_partialHecke
  - New.Patching.chain_lemma
  - New.Patching.isRoot_chain_of_norm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter

This chapter is about unramified representations of $\mathrm{GL}_N$ over a nonarchimedean local field. It has three results. The first is Satake's formula: on a spherical vector, the Hecke operators act by the elementary symmetric functions of $N$ numbers. The second is a converse in terms of exponents: a nonzero sorted unramified exponent forces a nonzero spherical vector. The third is the unitary chain lemma: if the representation is unitary, the roots of the Hecke polynomial come in chains, and the top root of a chain is not small. The source uses the third result in the argument on congruences of Volume 12, and it uses the first two to compare Hecke eigenvalues with the labels of Galois representations in Volume 8.

The chapter is the last chapter of Volume 5. Its last section has a summary of the volume.

### The setting

Let $F$ be a field with a discrete valuation, with ring of integers $\mathcal{O}$, maximal ideal $\mathfrak{p}$ and a finite residue field $k$ with $q$ elements. In most statements $F$ is the completion $E_w$ of a number field $E$ at a finite place $w$, and $q$ is the norm of $w$. Let $\varpi$ be a uniformiser. Lean writes the valuation multiplicatively, with values in $\mathbb{Z}_{\geq 0}^{\times}$ and a zero element. So $v(\varpi) = \exp(-1)$, and $v(a) \leq 1$ says that $a$ is integral. The normalised absolute value is $|a| = q^{\log v(a)}$, so that $|\varpi| = q^{-1}$.

Let $G = \mathrm{GL}_N(F)$ and $K = \mathrm{GL}_N(\mathcal{O})$. A representation $\rho$ of $G$ on a complex vector space $V$ is smooth if every vector is fixed by an open subgroup. A vector is spherical if $K$ fixes it. For a compact open subgroup $H$, the mean over $H$ is the integral of $\rho(h)x$ for the Haar measure of total mass $1$ on $H$. It is a projection onto the $H$-fixed vectors. Lean calls it `compactMean`.

For $0 \leq j \leq N$ let $T_j$ be the Hecke operator of the double coset $K \operatorname{diag}(\varpi, \ldots, \varpi, 1, \ldots, 1) K$, with $j$ entries $\varpi$. On a spherical vector $x$ it is
$$T_j x = \sum_{g} \rho(g) x,$$
where $g$ runs over representatives of the cosets $gK$ in the double coset. These cosets correspond to the lattices $L$ with $\varpi\mathcal{O}^N \subseteq L \subseteq \mathcal{O}^N$ and $\dim_k \mathcal{O}^N / L = j$. So there are $\binom{N}{j}_q$ of them, the Gaussian binomial coefficient. The Hecke polynomial of a spherical eigenvector $x$ with $T_j x = t_j x$ is
$$P(X) = \sum_{j=0}^{N} (-1)^j q^{j(j-1)/2} t_j X^{N-j}.$$

### The three results

Satake's formula says that $P(X) = \prod_i (X - y_i)$, where the $y_i = \theta_i(\varpi)$ come from an unramified character $\theta$ of the diagonal torus. The book does not use the Satake isomorphism. It proves the formula in the following form. Let $l$ be a linear form on $V$ that is an exponent for $\theta$ (the definition is in section 2). Then
$$l(T_j x) = \frac{e_j(y_1, \ldots, y_N)}{q^{j(j-1)/2}}\, l(x)$$
for each spherical $x$, where $e_j$ is the $j$-th elementary symmetric function. If $l(x) \neq 0$ and $x$ is an eigenvector, then $t_j = e_j(y)/q^{j(j-1)/2}$, and the polynomial is $\prod_i (X - y_i)$. This is [Theorem](/decl/New.IsExponent.apply_partialHecke/) in section 4.

The converse says that the exponent sees a spherical vector. If $\theta$ is unramified and $|\theta_i(\varpi)|$ does not increase with $i$, then an exponent for $\theta$ that vanishes on the spherical vectors is zero. Section 5 proves this, and shows how to sort an exponent so that the hypothesis holds.

The chain lemma is the main result of the chapter. Let $\rho$ be smooth and unitary, and let $x \neq 0$ be a spherical eigenvector with Hecke polynomial $P$.

1. If $P(c) = 0$ and $P(qc) \neq 0$, then $|c|^2 \geq q^{N-2}$.
2. If $P(c) = 0$ and $|c|^2 q^k = q^N$, then $c, cq, \ldots, cq^{k-1}$ are all roots of $P$.
3. An operator at the pro-$p$ Iwahori level sees only the top root of a chain.

These are [Theorem](/decl/New.Patching.chain_lemma/) and [Theorem](/decl/New.Patching.isRoot_chain_of_norm/) in section 6.

### An example

Take $N = 2$ and the trivial representation on $V = \mathbb{C}$. Every vector is spherical. The operator $T_1$ is a sum over the $q + 1$ lattices of index $q$ in $\mathcal{O}^2$ that contain $\varpi\mathcal{O}^2$, that is, over the lines in $k^2$. So $t_1 = q + 1$. The operator $T_2$ has the single lattice $\varpi\mathcal{O}^2$, so $t_2 = 1$. The Hecke polynomial is
$$P(X) = X^2 - (q + 1)X + q = (X - 1)(X - q).$$
The roots are $1$ and $q$, and they form a chain of length $2$. The root $c = q$ has $P(qc) = P(q^2) \neq 0$, and $|c|^2 = q^2 \geq q^{0}$. The root $c = 1$ has $|c|^2 q^2 = q^2$, so part 2 with $k = 2$ predicts the chain $1, q$. The trivial representation is the extreme case: its roots $1, q, \ldots, q^{N-1}$ form one chain of length $N$.

At the other extreme are the tempered representations. In the unitary normalisation one writes $y_i = q^{(N-1)/2}\alpha_i$. The case $\alpha_i = 1$ for all $i$ comes from the trivial character of the torus, induced to $G$ with the normalised induction. The case $|\alpha_i| = 1$ for all $i$ is the tempered case. In this normalisation the bound of part 1 reads $|\alpha| \geq q^{-1/2}$ for the top root of a chain. Section 6 compares this with the complementary series of $\mathrm{GL}_2$.

### The method

The method is elementary. It uses no Jacquet modules and no classification of representations. The Jacquet module of $\rho$ is replaced by linear forms $l$ with
$$l\bigl(\rho(t)\, \bar m(x)\bigr) = \xi(t)\, l(x)$$
for every dominant diagonal $t$ and every $x$, where $\bar m$ is the mean over the pro-$p$ Iwahori subgroup $I_1$. Such a form is an exponent. The spherical Hecke operators are replaced by partial sums over lattices, one sum for each $r$ and $j$: the sum over the lattices of colength $j$ that contain the first $r$ basis vectors. Two counts of hyperplanes relate these partial sums. The first count gives Satake's formula. With the second count and the unitary form, it gives the chain lemma.

The chain lemma also follows from Tadić's classification of the unitary dual of $\mathrm{GL}_N$, together with the work of Bernstein and Zelevinsky. The Lean proof does not use the classification. The cost is that the bound of part 1 is weaker than what the classification gives. The source needs only this weaker bound.

### Plan of the chapter

Section 2 defines the pro-$p$ Iwahori subgroup $I_1$, the parahoric subgroups, the operators $U_t$ and the exponents. It proves the decomposition of Iwasawa and Bruhat and the product formula $U_t U_{t'} = U_{tt'}$. Section 3 proves the quadratic relation for a simple transposition and deduces that some $U_t$ is injective. Section 4 proves Satake's formula through the partial Hecke sums, and computes the degree of an Iwahori double coset. Section 5 proves the converse and the sorting of exponents. Section 6 proves the chain lemma. Section 7 moves the results to split places of a CM field, where the source uses them, and states the transfer of Hecke polynomials by the theta lift. Section 8 has the exercises, the notes, and the summary of Volume 5.

The chapter uses the definitions of Hecke operators and of means over compact subgroups from [Automorphic forms on unitary groups](/chapter/automorphic-forms/). It uses the characters of $\mathrm{GL}_N(k)$ from [Characters of GL_n over a finite field](/chapter/finite-gln/) at one place in section 5.

The proofs in this chapter follow the Lean proofs. Lean accepts them if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
