---
title: The chapter and its place
lean:
  - Lib/DiscreteSeries/Bessel/Basic.lean
  - Lib/DiscreteSeries/Bruhat/FloorGroups.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter builds the group theory and the measure theory that Theorem B needs on a split unitary group. The group is the unitary group of a hermitian form with $\varrho$ hyperbolic planes, a definite space of dimension $k$ and one more vector of negative length. The chapter defines a Bessel subgroup $S = \mathsf U H$ of this group, its additive character, and the functions on the group that transform by this character. It proves a Bruhat decomposition on the big cell, over a field and over a ring of integers. Then it builds explicit Haar measures on the unipotent groups, and measures on the orbits of the frame, and it proves upper bounds for these measures. At the complex place all constants are explicit.

### Where the chapter sits

The plan of the proof is in [the theorem and its plan](/chapter/theorem-and-plan/). Theorem B says that there are enough automorphic forms of a given type: few translates of a small family of Poincaré series span a space of the right dimension. Its plan is in [Theorem B and its plan](/chapter/theorem-b-plan/). The Poincaré series are sums over $\mathsf U(\mathcal O) \backslash \Gamma$ of a function $W$ on the real group that transforms on the left by a character of $\mathsf U$. Their inner products unfold into sums over double cosets $\mathsf U \gamma \mathsf U$, with integrals over $\mathsf U \backslash G$ (see [Poincaré series and unfolding](/chapter/poincare-series/)). Each double coset has a representative from the big cell. Its terms are bounded by integrals of $|W|^2$ over pieces of the group, and these integrals are bounded by explicit measures of sets of frames (see [Bessel functions at a real place](/chapter/bessel-real-place/) and [local densities at the real places](/chapter/real-densities/)).

This chapter supplies the tools for these steps, in the order in which they are proved:

1. The groups: floors, the floor groups $H_l$, the unipotent groups $\mathcal N_l$ and $\mathcal N_{<l}$, the Bessel subgroup $S$ and its character.
2. The Heisenberg groups $\mathcal N_a$ of the floors, and the factorisation of $\mathsf U$ as a product $\mathcal N_0 \cdots \mathcal N_{\varrho - 1}$ with unique factors.
3. The big cell: an element $\gamma$ with nonzero leading minors of its frame matrix is $u^{-1} w_p \sigma u'$, with unique factors; over a ring the factors are integral when the minors are units.
4. Explicit measures on $\mathsf U^0$ and $\mathsf U$, homogeneous balls, tubes and the measure on $\mathsf U \backslash G_1$.
5. Bessel functions and a Schur bound for their convolutions.
6. Places with a Plancherel inequality, measures on quadrics, and the fibre bounds for the orbit maps.
7. The complex place: polar coordinates, the Cartan decomposition of the last floor, the hyperboloid and the sphere fibres, with explicit densities.

The sizes of the data of the proof, such as $\varrho \ge 10^5$, are fixed in [the data and its sizes](/chapter/data-and-sizes/). The results of this chapter hold for every $\varrho$ and every $k$, with two exceptions that the text states: the hyperboloid and sphere results need $k \ge 2$.

### What the chapter uses

The chapter uses linear algebra over a commutative ring with an involution, the unitary group $U(J) = \{g : g^* J g = J\}$ of a hermitian matrix $J$, and Haar measure on locally compact groups. It uses the Eichler transformations of a hermitian space, the cutoff construction of a measure on a quotient (see [quotients and reduction theory](/chapter/reduction-theory/)), and the explicit Haar measure $[\mathrm{haarU}](/decl/New.haarU/)$ of a compact unitary group from [discrete series through one matrix coefficient](/chapter/discrete-series/). It uses the idempotent kernels of that chapter in Section 5.

### The model case $\varrho = 0$

The simplest case has no hyperbolic plane. Then the space has basis $x_i$ ($i \in \kappa$) and $z$, with $h(x_i, x_j) = \delta_{ij}$, $h(x_i, z) = 0$ and $h(z, z) = -1$. The group is $U(k, 1)$. The frame is the single vector $z$. The unipotent group $\mathsf U$ is trivial, since all basis vectors have the same level. The Bessel subgroup is $S = H = U(k)$, the fixer of $z$. A Bessel function is a function $W$ on $U(k, 1)$ with $W(hy) = \rho(h) W(y)$ for $h \in U(k)$. The frame matrix of $y$ is the $1 \times 1$ matrix $h(z, yz)$. The big cell is the set where this number is not zero, and it is the whole group, since $|h(z, yz)| \ge 1$ by the reverse Cauchy-Schwarz inequality for a vector of negative length. The orbit of $z$ is the hyperboloid $\{v : h(v, v) = -1\}$. Section 7 computes the image of Haar measure on this hyperboloid. For $k = 1$ the group is $U(1, 1)$, and the hyperboloid is $\{(a, c) \in \mathbb C^2 : |a|^2 - |c|^2 = -1\}$.

### The model case $\varrho = 1$

With one hyperbolic plane the basis is $e_0$, $x_i$, $z$, $e_0^*$, with $h(e_0, e_0^*) = 1$ and all other products of $e_0$ and $e_0^*$ zero. The levels are $0$ at $e_0$, $1$ on the middle block and $2$ at $e_0^*$. The frame is $(e_0, z)$. The group $\mathsf U$ is the unipotent radical of the stabiliser of the isotropic line $\langle e_0 \rangle$. It is a Heisenberg group. An element $\nu(v, \beta)$ sends $e_0^*$ to $e_0^* + v + (\beta - \tfrac12 h(v, v)) e_0$, where $v$ lies in the middle block and $\beta$ is purely imaginary. The character of $\mathsf U$ reads the coefficient of $e_0$ in $\nu z$, which is $-h(v, z)$. A Bessel function transforms by $\exp(c - \bar c)$ of this coefficient. The frame matrix of $\gamma$ is the $2 \times 2$ matrix
$$Z(\gamma) = \begin{pmatrix} h(e_0, \gamma e_0) & h(e_0, \gamma z) \\ h(z, \gamma e_0) & h(z, \gamma z) \end{pmatrix}.$$
The big cell is the set where $h(e_0, \gamma e_0) \ne 0$. On it $\gamma = u^{-1} w_p \sigma u'$, where $w_p$ swaps the lines of $e_0$ and $e_0^*$ with a scalar $p$, and $\sigma$ fixes $e_0$ and $e_0^*$. This is the classical Bruhat decomposition of a group of rank one.

### A sketch of the main proofs

The descent is by floors. The floor of $e_a$ and $e^*_a$ is $a$, the floor of $z$ is $\varrho$, and the floor of $x_i$ is $\varrho + 1$. The group $H_l$ fixes all basis vectors of floor below $l$. So $H_0$ is the whole group, $H_\varrho$ is the unitary group of the middle block, $H_{\varrho + 1}$ is $H \cong U(k)$, and $H_{\varrho + 2}$ is trivial.

For the big cell, the leading minor $\delta_{j+1}$ of $Z(\gamma)$ does not change under $\mathsf U$ on both sides. At the step $j$ the element has the form $w \sigma$ with $\sigma \in H_j$, and $\delta_{j+1}$ is a product of earlier scalars and the pivot $h(e_j, \sigma e_j)$. So the pivot is a unit. Two Heisenberg elements of floor $j$ then move $\sigma$ into $H_{j+1}$, up to a Weyl element of floor $j$. Uniqueness follows from a comparison of columns.

For the measures, each floor has a Heisenberg group, and Haar measure on it is the image of Lebesgue measure. The convolution of these measures is a Haar measure on $\mathsf U$. The orbit map $g \mapsto g^{-1} f_b$ sends Haar measure to a measure on a quadric. The fibre bounds compare these images with explicit measures on quadrics, through a disintegration of Lebesgue measure along the hermitian form. At the complex place the disintegration is explicit: polar coordinates on $\mathbb C^k$ and the area of the sphere.

### What is not here

The chapter builds no Bessel model and no representation. A Bessel function in this chapter is a function with two transformation laws, nothing more. The Schur bound of Section 5 is proved from an idempotent kernel, not from the theory of discrete series representations. No uniqueness of Bessel models is used.

**Remark (Formalization).** The source does not construct a Bessel model. The head of [UnipotentHaarMeasure.lean](lean:Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean#L40) says so in these words: "No Bessel model is constructed here." The argument needs only functions with the two transformation laws and the measure bounds of this chapter. The structure that the source calls a Bessel function is `New.IsBesselFunction` in [Basic.lean](lean:Lib/DiscreteSeries/Bessel/Basic.lean#L662).
