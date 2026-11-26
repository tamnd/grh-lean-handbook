---
title: The chapter and its place
lean:
  - Lib/SiegelWeil/Formula/WeilRange.lean
  - Lib/SiegelWeil/RallisInner/Doubling.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
decls:
  - New.SiegelWeil.siegel_weil
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This is the last chapter of Volume 6. It applies the Siegel-Weil formula of [the Siegel-Weil formula](/chapter/siegel-weil/) to a doubled space. The result is the Rallis inner product formula: the Petersson product of two theta lifts is an integral of a matrix coefficient of the Weil representation against the two forms. The source uses this formula for one purpose above all. It proves that a theta lift in a large rank is injective on the forms of a fixed level. The chapter then turns to the tower of theta lifts. It computes the constant term of a theta integral along an isotropic line, and it proves a vanishing criterion for singular forms after Freitag. The last section ends with a summary of the volume.

### What the chapter proves

The chapter has six results. The numbers give the sections.

1. *The doubling identity* (Section 2). Let $S$ be a hermitian space of rank $n$ and $T$ a hermitian space of rank $m$, with $2n < m$. For a clean datum $f$, the integral over $[U(T)]$ of the product of two theta kernels is the volume of $[U(T)]$ times a sum of matrix coefficients over the rational points of $U(S)$.
2. *The inner product formula* (Section 3). Integrate the doubling identity against two rapidly decreasing functions on $[U(S)]$. The Petersson product of the two lifts is the volume of $[U(T)]$ times an absolutely convergent integral over the adelic group $U(S)(\mathbb{A})$.
3. *Sharp data* (Section 3). For a datum that is sharp at a level $J$, the finite part of this integral is a constant $c \neq 0$ times a series of translates, the *Rallis series*, over the places off the level.
4. *The unramified series and injectivity* (Section 4). The Rallis series converges absolutely for $2n < m$. It is close to the identity, so it is injective. Hence the theta lift is injective on the forms of level $J$. In rank one the sum of the coefficients is a partial Hecke $L$-value over a partial Euler product.
5. *The tower* (Section 5). Add a hyperbolic plane to each space of a dual pair. The constant term of the larger theta integral along the new isotropic line is a constant $\gamma$ times a smaller theta integral, and $|\gamma|$ is a positive constant times a Hecke $L$-value with factors at the ramified places.
6. *Singular forms* (Section 6). A Fourier coefficient of a function with enough shear invariance vanishes at all points that fix a frame if it vanishes at the points with a unimodular index.

### Where the results are used

The plan of Theorem C is in [Theorem C: the plan](/chapter/theorem-c-plan/). Chapter 1 of this volume says that Theorem C takes two things from this chapter: the injectivity of a single theta lift, and the identity for the determinant of a chain. In the source the injectivity is the theorem `New.SiegelWeil.exists_petersson_formLift_eq_rallisSeries` of Section 4. The source uses it in `Lib/GaloisRep/Main/ThetaLift.lean` and in `New/Determinant/Norms/AdjointThetaLift.lean`. The identity for the determinant uses the products $L_*$ of $L$-values and the constant terms of Section 5. They occur in the files of `New/Determinant/Exchange` and in `New/OneLift/HeckeValues/TwistedRatio.lean`. The vanishing criterion of Section 6 is used in `New/Determinant/Exchange/StableSpacesStandardData.lean`.

The chapter uses three earlier chapters of the volume.

- From [the Weil representation from a vacuum](/chapter/weil-representation/) it uses the Weil representation $\omega$ on the space $\mathcal{S}(V)$ of the adelic model, the theta functional $\theta$, and the mixed models of a split space.
- From [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) it uses the twisted Weil representation `New.pairWeil` of $U(S) \times U(T)$, the theta kernel `New.pairThetaKer`, the lift `New.Space.lift`, the lift of forms `New.formLift` and the edges `New.IsEdge` between types of real vectors.
- From [the Siegel-Weil formula](/chapter/siegel-weil/) it uses the Siegel-Weil formula in Weil's range. This is the theorem below.

**Theorem (Siegel-Weil formula in Weil's range).** Let $S$ be a hermitian space that is split into $p$ hyperbolic planes, with a complete splitting $P$, and let $T$ have rank $m > 2p$. Then the operator norms of the zero terms along the Lagrangians $L$ of $S$ are summable. For every datum $f$ in $\mathcal{S}(\operatorname{Hom}(S, T))$ the function $h \mapsto \theta(\omega(1, h) f)$ is integrable on $[U(T)]$, and
$$\int_{[U(T)]} \theta(\omega(1, h) f)\, dh = \operatorname{vol}([U(T)]) \sum_{L} Z_L(f),$$
where $Z_L(f)$ is the value at $0$ of $f$ in the Schrödinger model of a splitting along $L$.

Lean: `New.SiegelWeil.siegel_weil` (Lib/SiegelWeil/Formula/WeilRange.lean).

The proof of this theorem is in [the Siegel-Weil formula](/chapter/siegel-weil/). This chapter uses it as a black box, and only once: in the proof of the doubling identity of Section 2. There $S$ is replaced by the doubled space $S \oplus S^-$, which has a complete splitting into $n$ hyperbolic planes. The condition $m > 2p$ becomes $m > 2n$. All results of Sections 2 to 4 carry this condition.

### A sketch of the method

Let $f$ and $f'$ be two data in $\mathcal{S}(\operatorname{Hom}(S, T))$, and let $y$ and $y'$ be two functions on $[U(S)]$. The lift of $y$ by $f$ is the function
$$\Theta_f(y)(h) = \int_{[U(S)]} \theta(\omega(g, h) f)\, y(g)\, dg$$
on $U(T)(\mathbb{A})$. Its Petersson product with $\Theta_{f'}(y')$ is a triple integral. Exchange the order of the integrals. The inner integral is over $[U(T)]$, and it is the integral of a product of two theta kernels. The doubling method writes this product as one theta kernel on the doubled space $S \oplus S^-$, for the datum $f \otimes \bar f'$. The Siegel-Weil formula turns the inner integral into a sum over the Lagrangians of $S \oplus S^-$. For a clean datum only the graphs of the isometries of $S$ contribute. These graphs are in bijection with the rational points of $U(S)$. So the inner integral is a sum over $\gamma \in U(S)(E)$ of the matrix coefficient $\langle f', \omega(g'^{-1} \gamma g) f \rangle$. The sum unfolds one of the two integrals over $[U(S)]$. The result is
$$\langle \Theta_{f'}(y'), \Theta_f(y) \rangle = \operatorname{vol}([U(T)]) \int_{U(S)(\mathbb{A})} \langle f', \omega(g) f \rangle\, \langle y', R(g) y \rangle\, dg,$$
with $R$ the right translation. This is the inner product formula. It has a real part, a part at the places of the level and an unramified part. For a sharp datum the part at the level is a constant. The unramified part is the Rallis series.

### The model case

In the simplest case all signs of $S$ agree, so that $S$ is definite at every real place. Let $L$ be a Lagrangian of the doubled space $S \oplus S^-$, where $S^-$ is $S$ with the form multiplied by $-1$. A vector of $L$ of the form $(x, 0)$ is isotropic in $S \oplus S^-$, so $\langle x, x \rangle = 0$ in $S$. As $S$ is definite, $x = 0$. Hence $L$ meets $S \oplus 0$ only in $0$. By a count of dimensions, $L$ is then the graph $\{(\phi(x'), x')\}$ of a linear map $\phi$ from $S^-$ to $S$. The graph is isotropic exactly when $\phi$ is an isometry. So in the model case every Lagrangian of $S \oplus S^-$ is the graph of an isometry of $S$, and no condition on $f$ is needed. For spaces of mixed signs a Lagrangian can contain a nonzero vector $(x, 0)$. The source then adds a condition at one finite place, which makes the term of such a Lagrangian vanish. It calls the data that satisfy one of the two conditions *clean*.

### Conventions

The notation follows the source.

- $E$ is a CM field with Weil data, as in [the Weil representation from a vacuum](/chapter/weil-representation/). $F$ is its real subfield.
- $S$ is a hermitian space with a point, of rank $n$ and signs $s$; $T$ is one of rank $m$ and signs $t$. In Lean they are `S : Space E n s` and `T : Space E m t`, with `card n` and `card m` the ranks.
- `New.G E s` is the adelic unitary group $U(S)(\mathbb{A})$. A point is a pair of a real point in `GInf E s` and a finite point in `Gf E n`.
- `S.Γ` is the group of rational points of $U(S)$, and `S.quotMeasure` is the measure on the quotient $[U(S)]$.
- `New.stdLevel E n` is the group $K_0$ of finite points that are integral at all places, the stabilizer of $\hat{\mathcal{O}}^n$. `New.localLevel n A` is the group of finite points integral at the places of $A$.
- `New.pairWeil S T a b` is the Weil representation of $U(S) \times U(T)$ twisted by two characters $a$, $b$ of $[U(1)]$, and `New.Space.dataInner` is the inner product on the data.
- `S.petersson` is the Petersson product on $[U(S)]$.

**Remark (Formalization).** All results of Sections 2 to 4 are stated for $2n < m$, that is, in Weil's range of absolute convergence. The source does not treat the boundary case $2n = m$ or the regularized Siegel-Weil formula. The forms are rapidly decreasing functions on $[U(S)]$, not cusp forms. The source does not prove the full Rallis inner product formula with the $L$-function of a cuspidal representation. It keeps the unramified part as a sum over cosets and evaluates it only in rank one.
