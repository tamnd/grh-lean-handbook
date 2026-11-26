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

The Siegel-Weil formula says that an integral of theta functions over a unitary group is an Eisenstein series. This chapter states the formula as the source proves it, in the range where both sides converge absolutely, and gives the proof. It then takes the formula for one vector, which is Siegel's formula for the number of representations of a number by a hermitian form. From this the chapter obtains an estimate for the ratio of the masses of two genera of unimodular lattices. The source uses this estimate in Theorem B. The last section treats two tools that the source keeps in the same folder: neighbour lattices and a reproducing formula for holomorphic minors.

### The classical statement

Let $F$ be a number field and $\mathbb{A}$ its adeles. Let $W$ be a symplectic space over $F$ of dimension $2p$ and $V$ a quadratic space over $F$ of dimension $m$. The pair $(\mathrm{Sp}(W), O(V))$ is a dual pair, and the Weil representation $\omega$ acts on the Schwartz-Bruhat space $\mathcal{S}(V(\mathbb{A})^p)$. For $\varphi$ in this space the theta function is
$$\theta(g, h; \varphi) = \sum_{\xi \in V(F)^p} \big(\omega(g, h)\varphi\big)(\xi).$$
It is a function on $\mathrm{Sp}(W)(F)\backslash \mathrm{Sp}(W)(\mathbb{A})$ in $g$ and on $O(V)(F)\backslash O(V)(\mathbb{A})$ in $h$. The function $g \mapsto (\omega(g)\varphi)(0)$ is a section of a representation induced from the Siegel parabolic subgroup $P$, the stabilizer of a Lagrangian. Its Eisenstein series is
$$E(g, \varphi) = \sum_{\gamma \in P(F)\backslash \mathrm{Sp}(W)(F)} \big(\omega(\gamma g)\varphi\big)(0).$$
Weil proved in *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5, that in a range where the theta integral and the Eisenstein series converge absolutely,
$$\int_{O(V)(F)\backslash O(V)(\mathbb{A})} \theta(g, h; \varphi)\, dh = E(g, \varphi),$$
for the invariant measure of total mass $1$. Weil works with all the classical dual pairs, and the unitary case is one of them. The source cites this paper and this theorem for its own statement.

The left side is a mean of theta functions over a genus. The right side has a Fourier expansion whose coefficients are products of local densities. When $V$ is definite, the formula for one coefficient is Siegel's mass formula for the representations of a number: the weighted mean of the number of representations over the classes of a genus is a product of local densities.

### The setting of the source

The source works over a CM field $E$ with Weil data, as in [the Weil representation from a vacuum](/chapter/weil-representation/). There is no symplectic group. Both members of the pair are unitary groups. The space $S$ is a hermitian space of rank $2p$ with a complete splitting into $p$ hyperbolic planes. The space $T$ is a hermitian space of rank $m$. Both spaces are unimodular at every finite place. The Weil representation of the pair acts on the space $\mathcal{S}(\mathrm{Hom}(S, T))$ of [Chapter 1](/chapter/weil-representation/), the integrable coefficients against the vacuum, and not on Schwartz-Bruhat functions. The group of $S$ plays the part of $\mathrm{Sp}(W)$ and the group of $T$ plays the part of $O(V)$.

The source writes the Eisenstein series as a sum over the Lagrangians of $S$. A Lagrangian is a subspace of $E^{2p}$ that is equal to its own orthogonal. The group $U(S)(E)$ acts transitively on the Lagrangians by Witt's theorem, and the stabilizer of one Lagrangian is the rational points of a Siegel parabolic subgroup. So the sum over $P(E)\backslash U(S)(E)$ and the sum over Lagrangians have the same terms. The term of a Lagrangian $L$ is its zero term $\mathrm{ev}_L$: the value at $0$ in the Schrödinger model along $L$. Section 2 defines it.

### The main result

The main result of the chapter is the following. Section 5 states it with all hypotheses and gives the proof.

*Theorem (Siegel-Weil formula in Weil's range).* Let $S$ have a complete splitting into $p$ hyperbolic planes, and let the rank $m$ of $T$ satisfy $2p < m$. Then the operator norms of the zero terms $\mathrm{ev}_L$ are summable over the Lagrangians $L$ of $S$. For every $f \in \mathcal{S}(\mathrm{Hom}(S, T))$ the function $h \mapsto \theta(\omega(1, h) f)$ is integrable over $[U(T)]$, and
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \sum_{L} \mathrm{ev}_L(f).$$

The source states the formula at $g = 1$. Since the formula holds for every $f$, it holds for $\omega(g, 1) f$, and this gives the formula at every $g$ in the group of $S$. The measure is the quotient measure of [reduction theory](/chapter/reduction-theory/). It is finite and nonzero, so the formula says that the mean of the theta function is the Eisenstein series.

### The plan of the proof

The proof follows a method that the source attributes to Andrianov, Harris and Garrett. It has four parts.

1. *Convergence.* Siegel sets reduce every point of the group of $S$ to a torus element in a cusp. Along the torus the zero terms decay, and the number of Lagrangians at a given height grows slower than the decay when $2p < m$. This gives the summability of the Eisenstein series and the integrability of the theta function (Sections 2 and 3).
2. *A vanishing principle.* Let $\ell$ be the difference of the two sides, as a functional of $f$. It is invariant under the group of $T$ and under the rational points of $S$. At a split place the Hecke operators of $S$ and $T$ are related by the Hecke transfer of [Volume 5](/chapter/iwahori-satake/). A maximum principle then shows that $\ell$ is zero if it is bounded in the cusp by the Eisenstein series of the vacuum (Section 4).
3. *Induction on the rank.* Split off one isotropic line of $S$. The formula for the smaller space, by induction, shows that $\ell$ tends to $0$ along the torus. Siegel sets turn this into the bound that Section 4 needs (Section 5).
4. *Conclusion.* The vanishing principle gives $\ell = 0$.

The proof does not compute the constant terms of the Eisenstein series. It uses the Hecke operators at a split place in place of an analysis of the constant terms.

### The applications

Section 6 applies the formula to the hyperbolic plane $S$ of rank $2$ and to the definite space $T = E^\kappa$ with the form $x^* x$, of rank at least $3$. The Lagrangians of the hyperbolic plane are the line of $k$ and the lines of $l + \jmath^{-1}\beta k$ for $\beta$ in the totally real subfield $E^+$. The zero terms are Fourier integrals. The Fourier coefficient at a totally positive $\alpha$ gives Siegel's formula: the class sum of the numbers of vectors of norm $\alpha$ is a product of the class sum of $1$, a power of the discriminant, the factors at the infinite places and a density at the finite places. Section 7 bounds that density, and the local densities at a single place, by Gauss sums and an ideal zeta function. Section 8 applies Siegel's formula to the vectors of norm $1$ in the standard lattice of rank $j + 1$. This gives the ratio of the masses of the genera of rank $j + 1$ and $j$, up to an error of $2/2^u$.

[Theorem B: the plan](/chapter/theorem-b-plan/) uses Siegel's formula and the mass ratio. The main term of the spanning argument in [Volume 10](/chapter/main-term/) uses `New.classSum_eq_mul_normDensity`, and the frame mass estimate in [Poincaré series](/chapter/poincare-series/) uses `New.abs_log_mass_ratio_sub_le`. [The Rallis inner product formula](/chapter/rallis-inner-product/) applies `New.SiegelWeil.siegel_weil` to the doubled space.

### What the reader needs

The reader needs the Weil representation, the theta functional, the splittings, the slices and the Levi law of [Chapter 1](/chapter/weil-representation/). The reader needs the quotient measure and Mahler's criterion from [reduction theory](/chapter/reduction-theory/), and the Hecke polynomials at a split place and the Hecke transfer from [Volume 5](/chapter/iwahori-satake/). The dual pair notation is that of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). No result of the local theory of [Chapter 2](/chapter/local-theta/) enters.

**Remark (Formalization).** The source proves the formula for unitary pairs over a CM field with Weil data only, and only for spaces that are unimodular at every finite place. Its range $2p < m$ is stronger than the range of Weil, which asks for a condition on the Witt index of $T$. The source says this in the docstring of `New.SiegelWeil.theta_normalisedTorus_le`. The proof does not need more, because the applications in the source take $m$ large. The docstring of `New.SiegelWeil.siegel_weil` calls the right side a mean. The Lean statement has the integral on the left and the total mass times the sum on the right. The two agree after division by the mass.

Lean: `New.SiegelWeil.siegel_weil`, `New.SiegelWeil.theta_normalisedTorus_le` (Lib/SiegelWeil/Formula/WeilRange.lean; Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).
