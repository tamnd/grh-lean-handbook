---
title: What the chapter proves
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/FillingData.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter builds the analytic input of Theorem B at one real place. The output is a *Bessel system*: a vector valued function $W$ on the real unitary group $G_1$, a second function $W^\flat$ that agrees with $W$ on a large bounded region and vanishes outside a slightly larger one, and a list of bounds for the two. The Poincaré series of [the chapter on Poincaré series](/chapter/poincare-series/) are series of translates of $W$ and $W^\flat$. Every bound on the terms of these series that is local at a real place comes from the bounds proved here.

The main result is [Theorem](/decl/New.Data.exists_besselSystem/), stated in [the section on unfolding and bounds](/chapter/theorem-b-plan/#unfolding-and-bounds) and proved in [the last section](/chapter/bessel-real-place/#the-bessel-system-of-the-data). In words: for each real place $v$ of the field of the admissible data $D$, there is a Bessel system with the size parameter $b$ and the decay rate $f$ of $D$, whose full function is an average of a matrix coefficient of the discrete series with the parameter $\lambda_v$ that $D$ fixes at $v$.

### The model case: Petersson's kernel

In rank one the construction is classical. Let $f$ be a holomorphic cusp form of weight $k$ for $\mathrm{SL}_2(\mathbb{Z})$, and let $P_m$ be the Poincaré series of weight $k$ and index $m \geq 1$. The Petersson formula expresses the Fourier coefficients of $P_m$ by Kloosterman sums $S(m, n; c)$ and the values of the Bessel function $J_{k-1}(4\pi\sqrt{mn}/c)$. The function $J_{k-1}$ enters because the unfolded inner product $\langle P_m, P_n\rangle$ is an integral over the big Bruhat cell of $\mathrm{SL}_2(\mathbb{R})$, and on that cell the Whittaker function of weight $k$ paired with its translate gives $J_{k-1}$. The source names this kernel as the model in FillingData.lean: Petersson, *Über die Entwicklungskoeffizienten der automorphen Formen* (1932), and the integrals of NIST DLMF §10.22.

The source replaces $\mathrm{SL}_2(\mathbb{R})$ by an indefinite unitary group $G_1$ of large rank, the Whittaker function by a function $W$ that transforms by a character of a unipotent group $\mathsf U$ and by a representation of a compact group $H$, and the Bessel function $J_{k-1}$ by the integral of $W$ against its translate over the big cell. No closed formula for this integral is used. The chapter proves bounds for it instead.

### Which "Bessel"

The word has three meanings in the literature. It names the classical functions $J_\nu$. It names the *Bessel models* of representations, in which a function transforms on the left by a character of a unipotent group times a representation of a reductive subgroup that normalizes it. And it names the *Bessel distributions* on the open cell, which pair two such models. In this chapter a Bessel function is a function of the second kind, defined in [the chapter on Bessel subgroups and the big cell](/chapter/bessel-bruhat/) as [Definition](/decl/New.IsBesselFunction/). It is not a classical $J_\nu$. Its pairing with a translate, the integral $\int W(y) \otimes \overline{W(\gamma^{-1}y)}\,dy$, plays the part of $J_{k-1}$. The source calls this pairing [besselOrbitalIntegral](/decl/New.besselOrbitalIntegral/).

### The output

A Bessel system for a shape $\mathfrak s$, a real $b$ and a natural number $f$ is the structure [Definition](/decl/New.BesselSystem/). Its fields say, in summary:

1. $W$ and $W^\flat$ are continuous functions from $G_1$ to $\mathbb{C}^I$ for a finite nonempty set $I$, and both are Bessel functions for a unitary representation $\rho$ of $H = U(k)$ on $\mathbb{C}^I$.
2. $\rho$ is irreducible: only scalar matrices commute with all $\rho(h)$.
3. $\int_{\mathsf U\backslash G_1}\|W\|^2 = |I|$, the cut $W^\flat$ is close to $W$ in $L^2$, and both decay in a length function on $\mathsf U\backslash G_1$.
4. $W^\flat$ vanishes where the length exceeds $b^{6n+2}$, with $n = \varrho + 1$.
5. $W$ has a Schur bound: convolutions of $W$ and of its right derivatives with integrable functions are bounded in $L^2(\mathsf U\backslash G_1)$, with the constant $|I|/\deg$ for a positive number $\deg$.
6. $8r \leq b$, where $r = 2\varrho + k + 1$ is the size of the matrices of $G_1$.
7. $W^\flat$ has local bounds: a family of forms $J_i(p, q)$, one for each floor, that satisfies the hypotheses of the one sided sieve of [the chapter on the main term](/chapter/main-term/).

From these fields the chapter derives two more results that its users need. The coordinates of $W$ are orthonormal in $L^2(\mathsf U\backslash G_1)$ ([Lemma](/decl/New.BesselSystem.orthonormal/)), which [the chapter on Poincaré series](/chapter/poincare-series/) uses for the term $\gamma = 1$ of an amplitude sum (`New.Filling.amplitudeSum_besselS_one_eq_ite`, New/Spanning/Unfolding/AmplitudeSums.lean). And the pairing of $W^\flat$ with its translate by $\gamma$ is bounded on the open cell by an explicit power of the Gram discriminant of $\gamma$ ([Theorem](/decl/New.BesselSystem.enorm_integral_pairKernel_cut_le/)), which [the chapter on the remaining terms](/chapter/remaining-terms/) uses.

### The plan of the construction

The construction has five steps, one for each of the next five sections.

1. [The group and the length](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length). The group $G_1$, its frame $(e_0, \dots, e_{\varrho-1}, z)$, the Bessel subgroup $S = \mathsf U H$, and the length $\ell(y) = \inf_{s \in S}(\|sy\| + 1)$, which measures the size of a point of $S\backslash G_1$.
2. [Averages](/chapter/bessel-real-place/#bessel-functions-as-averages). For a point $x \in G_1$ and a unit vector $v$, the average $W_x(y) = \int_R c_\lambda(x^{-1}sy)\,\pi(s)^{-1}v\,ds$ of the discrete series coefficient $c_\lambda$ over the group $R = \mathsf U \rtimes H$ is a Bessel function. Convolution with $\deg \cdot c_\lambda$ reproduces it, and its squared norm is a period.
3. [A point with a large period](/chapter/bessel-real-place/#a-point-with-a-large-period). Laplace's method gives a point $x$ of length at most $b^{5n}$ at which the period is not small compared with the volume of a ball. So $W_x$ is not small in $L^2$.
4. [Decay and the cut](/chapter/bessel-real-place/#decay-and-the-cut). The decay of $c_\lambda$ gives a majorant for $W_x$ in terms of the length. After normalization, a cutoff in the length gives $W^\flat$.
5. [Schur bounds](/chapter/bessel-real-place/#schur-bounds-and-orthonormality) and [the open cell](/chapter/bessel-real-place/#the-open-cell-bound). Harish-Chandra's derivative kernels give the Schur bound. A section of the Gram map, a mean value inequality and a Sobolev inequality turn it into the open cell bound.

[The last section](/chapter/bessel-real-place/#the-bessel-system-of-the-data) checks the size conditions for the data $D$ and assembles the system. The local bounds of item 7 are not proved in this chapter. They come from [Lemma](/decl/New.Floors.exists_hasLocalBounds_of_isCutBessel/) of [the chapter on local densities at the real places](/chapter/real-densities/), which is a later chapter of this volume. The file FillingData.lean imports it.

### Conventions

The notation follows [the conventions of the volume](/chapter/theorem-b-plan/#conventions-that-change-the-meaning). The space at the real place is $\varrho$ hyperbolic planes, a positive definite space $X_0$ of rank $k$ with the basis $(x_i)_{i \in \kappa}$, and a line spanned by $z$ with $h(z, z) = -1$. So $n = \varrho + 1$ is the number of frame vectors and $r = 2\varrho + k + 1$ is the size of the matrices. Norms of matrices are $L^2$ operator norms for the basis $e_a, x_i, z, e^*_a$, which is orthonormal for the standard inner product. The numbers $b$ and $f$ are the size parameter and the decay rate. For the data $D$ the rate $f$ is the number of infinite places. The letter $r$ in Volume 0 denotes a different number, $r \approx x^5$; in this chapter $r$ is always the size of the matrices of $G_1$.

All integrals over $\mathsf U\backslash G_1$ are written $\int_{\mathsf U\backslash G_1}$ and mean integrals over $G_1$ for [the quotient measure](/decl/New.besselQuotMeasure/) of [the chapter on Bessel subgroups](/chapter/bessel-bruhat/), applied to functions whose norm is left invariant under $\mathsf U$.
