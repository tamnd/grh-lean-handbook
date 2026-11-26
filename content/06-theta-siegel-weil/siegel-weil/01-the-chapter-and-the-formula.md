---
title: The chapter and the formula
lean:
  - Lib/SiegelWeil/Formula/WeilRange.lean
  - Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean
  - Lib/SiegelWeil/OneVector/SiegelClassSum.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and the formula

The Siegel-Weil formula says that an integral of theta functions over a unitary group is an Eisenstein series. This chapter proves the formula in the range where both sides converge absolutely. It then takes the formula for one vector, which is Siegel's formula for the representations of a number by a hermitian form, and obtains an estimate for the ratio of the masses of two genera of unimodular lattices. The last section treats neighbour lattices and a reproducing formula for holomorphic minors. Doubling, the tower of theta integrals and the singular forms are in [the Rallis inner product formula](/chapter/rallis-inner-product/).

### The classical statement

Let $F$ be a number field and $\mathbb{A}$ its adeles. Let $W$ be a symplectic space over $F$ of dimension $2p$ and $V$ a quadratic space over $F$ of dimension $m$. The pair $(\mathrm{Sp}(W), O(V))$ is a dual pair, and the Weil representation $\omega$ acts on the Schwartz-Bruhat space $\mathcal{S}(V(\mathbb{A})^p)$. For $\varphi$ in this space the theta function is
$$\theta(g, h; \varphi) = \sum_{\xi \in V(F)^p} \big(\omega(g, h)\varphi\big)(\xi).$$
It is a function on $\mathrm{Sp}(W)(F)\backslash \mathrm{Sp}(W)(\mathbb{A})$ in $g$ and on $O(V)(F)\backslash O(V)(\mathbb{A})$ in $h$. The function $g \mapsto (\omega(g)\varphi)(0)$ is a section of a representation induced from the Siegel parabolic subgroup $P$, the stabilizer of a Lagrangian. Its Eisenstein series is
$$E(g, \varphi) = \sum_{\gamma \in P(F)\backslash \mathrm{Sp}(W)(F)} \big(\omega(\gamma g)\varphi\big)(0).$$
Weil proved in *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5, that in a range where the theta integral and the Eisenstein series converge absolutely,
$$\int_{O(V)(F)\backslash O(V)(\mathbb{A})} \theta(g, h; \varphi)\, dh = E(g, \varphi),$$
for the invariant measure of total mass $1$. Weil treats all the classical dual pairs, the unitary case included. The source cites this theorem.

When $V$ is definite, one Fourier coefficient of the formula is Siegel's mass formula: the weighted mean over a genus of the number of representations of a number is a product of local densities.

### The setting of the source

The source works over a CM field $E$ with Weil data, as in [the Weil representation from a vacuum](/chapter/weil-representation/). There is no symplectic group. Both members of the pair are unitary groups. The space $S$ is a hermitian space of rank $2p$ with a complete splitting into $p$ hyperbolic planes. The space $T$ is a hermitian space of rank $m$. Both spaces are unimodular at every finite place. The Weil representation acts on the space $\mathcal{S}(\mathrm{Hom}(S, T))$ of [Chapter 1](/chapter/weil-representation/), the integrable coefficients against the vacuum. The group of $S$ plays the part of $\mathrm{Sp}(W)$, and the group of $T$ the part of $O(V)$.

The source writes the Eisenstein series as a sum over the Lagrangians of $S$, the subspaces equal to their own orthogonal. By Witt's theorem $U(S)(E)$ acts transitively on them, with a Siegel parabolic subgroup as stabilizer, so this sum has the terms of the sum over $P(E)\backslash U(S)(E)$. The term of a Lagrangian $L$ is its zero term $\mathrm{ev}_L$, the value at $0$ in the Schrödinger model along $L$ (Section 2).

### The main result

Section 5 states the main result with all hypotheses and proves it.

*Theorem (Siegel-Weil formula in Weil's range).* Let $S$ have a complete splitting into $p$ hyperbolic planes, and let the rank $m$ of $T$ satisfy $2p < m$. Then the operator norms of the zero terms $\mathrm{ev}_L$ are summable over the Lagrangians $L$ of $S$. For every $f \in \mathcal{S}(\mathrm{Hom}(S, T))$ the function $h \mapsto \theta(\omega(1, h) f)$ is integrable over $[U(T)]$, and
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \sum_{L} \mathrm{ev}_L(f).$$

The source states the formula at $g = 1$. Applied to $\omega(g, 1) f$ it gives the formula at every $g$. The measure is the quotient measure of [reduction theory](/chapter/reduction-theory/). It is finite and nonzero.

### The plan of the proof

The source attributes the method to Andrianov, Harris and Garrett. It has four parts.

1. *Convergence.* Siegel sets reduce every point to a torus element in a cusp. Along the torus the zero terms decay faster than the number of Lagrangians at a given height grows, when $2p < m$ (Sections 2 and 3).
2. *A vanishing principle.* The difference $\ell$ of the two sides, as a functional of $f$, is invariant under the group of $T$ and the rational points of $S$. By the Hecke transfer of [Volume 5](/chapter/iwahori-satake/) at a split place, a maximum principle shows that $\ell$ is zero if it is bounded in the cusp by the Eisenstein series of the vacuum (Section 4).
3. *Induction on the rank.* Split off one isotropic line of $S$. The formula for the smaller space shows that $\ell$ tends to $0$ along the torus, and Siegel sets turn this into the bound of Section 4 (Section 5).
4. *Conclusion.* The vanishing principle gives $\ell = 0$.

The Hecke operators at a split place replace an analysis of the constant terms of the Eisenstein series.

### The applications

Section 6 applies the formula to the hyperbolic plane $S$ and the definite space $T = E^\kappa$ with the form $x^* x$, $\kappa \geq 3$. The Fourier coefficient at a totally positive $\alpha$ gives Siegel's formula: the class sum of the numbers of vectors of norm $\alpha$ is the class sum of $1$ times a power of the discriminant, the factors at the infinite places and a density at the finite places. Section 7 bounds the densities by Gauss sums and an ideal zeta function. Section 8 applies Siegel's formula to the vectors of norm $1$ in the standard lattice of rank $j + 1$, and gets the ratio of the masses of the genera of rank $j + 1$ and $j$ up to an error of $2/2^u$.

[Theorem B: the plan](/chapter/theorem-b-plan/) uses Siegel's formula and the mass ratio. The main term of the spanning argument in [Volume 10](/chapter/main-term/) uses `New.classSum_eq_mul_normDensity`, and the frame mass estimate in [Poincaré series](/chapter/poincare-series/) uses `New.abs_log_mass_ratio_sub_le`. [The Rallis inner product formula](/chapter/rallis-inner-product/) applies `New.SiegelWeil.siegel_weil` to the doubled space.

### What the reader needs

The reader needs the Weil representation, the theta functional, the splittings, the slices and the Levi law of [Chapter 1](/chapter/weil-representation/), the quotient measure and Mahler's criterion from [reduction theory](/chapter/reduction-theory/), and the Hecke transfer at a split place from [Volume 5](/chapter/iwahori-satake/). The dual pair notation is that of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). No result of [Chapter 2](/chapter/local-theta/) enters.

**Remark (Formalization).** The source proves the formula for unitary pairs over a CM field with Weil data only, and only for spaces that are unimodular at every finite place. Its range $2p < m$ is stronger than the range of Weil, which asks for a condition on the Witt index of $T$. The source says this in the docstring of `New.SiegelWeil.theta_normalisedTorus_le`. The applications take $m$ large, so the argument needs no more. The docstring of `New.SiegelWeil.siegel_weil` calls the right side a mean. The Lean statement has the integral on the left and the total mass times the sum on the right. The two agree after division by the mass.

Lean: `New.SiegelWeil.siegel_weil`, `New.SiegelWeil.theta_normalisedTorus_le` (Lib/SiegelWeil/Formula/WeilRange.lean; Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).
