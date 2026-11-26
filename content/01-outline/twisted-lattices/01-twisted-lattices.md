---
title: A lower bound for a covolume
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
  - New/Reduction/Lattices/Colength.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A lower bound for a covolume

This chapter proves one inequality of the geometry of numbers. It is a lower bound for the covolume of a family of vectors in terms of the denominators of the family. In its simplest form it is Liouville's inequality: a nonzero algebraic integer has a conjugate of absolute value at least $1$. The chapter states the inequality in the abstract setting of a *twisted lattice*, and proves it from the product formula for $\mathbb{Q}$. Theorem C applies it to the lattice of integral target forms. Nothing in this chapter uses automorphic forms.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof compares two bounds for one number. The number is the logarithm of the squared covolume of a large family $y_1, \dots, y_n$ of target forms, corrected by its index. Theorems A and B give the family. Theorem A says that each $y_i$ is short at every archimedean place, and that the family has small denominators at every prime. Hadamard's inequality turns the first statement into an upper bound for the covolume. Theorem C gives a lower bound for the same covolume. This chapter supplies the notions of index and covolume, Hadamard's inequality, and the lower bound that Theorem C uses. [Why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/) explains the method. [The lattice of integral target forms](/chapter/integral-target-forms/) builds the twisted lattice of the application. [Theorems A, B and C](/chapter/theorems-a-b-c/) and [the main inequality](/chapter/main-inequality/) use the results.

### The inequality in words

Let $V$ be a complex vector space of finite dimension, and let $y_1, \dots, y_n, z_1, \dots, z_{n'}$ be a basis of $V$, where the auxiliary vectors $z_j$ complete the family $y$ to a basis. A twisted lattice gives, for each twist $\xi$, a linear map $\Theta_\xi$ from $V$ to an inner product space with a notion of integral vector at every prime. The twist $1$ is the trivial twist. The inequality of the chapter reads
$$c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}} \geq 0.$$
Here $c$ bounds the logarithm of the squared covolume of $\Theta_1 y$ at every archimedean place, $\delta$ bounds the logarithm of the index of $y$, $b_{\mathrm{short}}$ bounds the squared length of each $\Theta_1 z_j$, $b_{\mathrm{denom}}$ bounds the denominators of the $z_j$, and $b_{\mathrm{volume}}$ bounds the height of the ratio of the volumes of $\Theta_1$ and $\Theta_{\xi}$ for one twist $\xi = \xi_\iota$ at each prime. The precise statement is [Theorem](/decl/New.TwistedLattice.covolume_add_index_nonneg/).

In Theorem C the three auxiliary terms have explicit sizes. In the notation of [the data and its sizes](/chapter/data-and-sizes/), the source takes
$$b_{\mathrm{short}} = 2x_1^2 b^2, \qquad b_{\mathrm{denom}} = b, \qquad b_{\mathrm{volume}} = d_T\,(b + f a \log^4 b - \mathrm{mainAmount}),$$
where $d_T$ is the dimension of the space of target forms. With $n'(2x_1^2b^2 + b) \leq d_T b$ and $b \leq f a \log^4 b$, the inequality becomes
$$c + 2\delta \geq d_T\,(\mathrm{mainAmount} - 3 f a \log^4 b).$$
This is the statement of Theorem C. Section 6 of this chapter does the arithmetic.

### The proof in one paragraph

Let $\mathrm{Gram}(\xi)$ be the Gram determinant of the vectors $\Theta_\xi y_1, \dots, \Theta_\xi z_{n'}$. Since $y \cup z$ is a basis and $\Theta_1$ is injective, $\mathrm{Gram}(1) \neq 0$. The proof bounds this one number at every place. At an archimedean place, Fischer's and Hadamard's inequalities bound $|\sigma\,\mathrm{Gram}(1)|$ by $\exp(c + n' b_{\mathrm{short}})$. At a prime $\ell$ and an isomorphism $\iota\colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, the proof writes
$$\mathrm{Gram}(1) = \mathrm{Gram}(\xi_\iota) \cdot \frac{Z(1)}{Z(\xi_\iota)},$$
where $Z(\xi)$ is the squared volume of $\Theta_\xi$. The index bound makes $\mathrm{Gram}(\xi_\iota)$ almost integral at $\iota$, and the height bound controls the ratio. The product formula says that a nonzero algebraic number cannot be small at every place. So the bounds at all places add up to a number at least $0$, which is the inequality.

### What the chapter uses

The chapter uses Hadamard's and Fischer's inequalities, the Cauchy-Schwarz inequality for determinants, the Smith normal form over a valuation ring, the product formula for $\mathbb{Q}$, and a criterion for a complex number to be algebraic. The source proves all of them, and the chapter states each one.

### The plan of the chapter

Section 2 does the model cases: Liouville's inequality in rank one, then lattices in $\mathbb{R}^n$ with Minkowski's and Hadamard's inequalities. Section 3 defines heights over the isomorphisms $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ and proves the product formula in the form that the source uses. Section 4 defines twisted lattices, the index and the covolume. Section 5 defines the colength, which produces index bounds. Section 6 proves the inequality and shows how Theorem C uses it. Section 7 has exercises and notes.

### Notation

Throughout, $\ell$ is a prime, $\iota$ is an isomorphism of fields $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, and $\sigma$ is an automorphism of the field $\mathbb{C}$. The norm on $\overline{\mathbb{Q}}_\ell$ is the unique extension of the $\ell$-adic absolute value, so $\|\ell\| = \ell^{-1}$. A family indexed by $\iota$ has one member for each pair of a prime $\ell$ and an isomorphism $\iota$ over $\ell$. We write $\iota \mid \ell$ for such a pair. Logarithms are natural. A "covolume at most $c$" always means that the *squared* covolume is at most $e^c$, as in the source.
