---
title: What the chapter proves
lean:
  - New/Determinant/Exchange/OneSquare.lean
  - New/Determinant/Chain/SquareLaw.lean
  - New/Determinant/AuxiliaryForms/GridPaths.lean
  - New/Determinant/AuxiliaryForms/PathData.lean
decls:
  - New.Exchange.one_square_identity_of_isEdgeFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter applies the exchange identity to a square of four hermitian spaces. Two spaces $U_1$ and $U_2$ sit at the ends of the square, and two spaces $A$ and $A'$ sit in the middle. A form on $U_1$ can go to $U_2$ in two ways. It can go up through $A$: a theta lift to $A$, then a transposed lift to $U_2$. It can go down through $A'$: a transposed lift to $A'$, then a lift to $U_2$. The *one square identity* says that the two paths satisfy a finite *square law*: on matched data modulo $\mathfrak{m}$, a weighted sum of the second path is a constant $\kappa/c$ times a weighted sum of the first path. The chapter proves this identity from the [exchange identity](/chapter/exchange-identity-2/), and it explains why the constant $\kappa$ may be $0$.

The second half of the chapter sets up the combinatorics that later chapters use to chain squares together. A path in a grid of spaces is a word in the letters "down" and "right". A pair of such paths with a diagonal block covers a set of squares, and one *turn* adds one square. The chapter defines these paths, proves an induction principle over turns, and defines the data that a path carries: the theta lifts along its edges, the matrix tuples on its edges, and the period of a pair of paths.

### The statement

Let $E$ be a CM field with Weil data. Let $A'$, $A$, $U_1$ and $U_2$ be hermitian spaces over $E$ with bases indexed by finite types $n$, $n'$, $n_1$ and $n_2$, and with signs $s$, $s'$, $s_1$ and $s_2$ at the infinite places. Put $W = U_1 \oplus U_2$. Write $\operatorname{neg}(s)$ for the number of signs $-1$ of $s$, and $|n|$ for the cardinality of $n$. A *type* of forms on a space is a function on its real unitary group; see [the lift on forms](/chapter/theta-lifts-seesaw/#edges-and-arrows). Let $k_1$, $k_2$, $k$ and $k'$ be pairs of types, indexed by $d \in \{\mathrm{false}, \mathrm{true}\}$, on $U_1$, $U_2$, $A$ and $A'$. We write $\neg d$ for the other index.

Let $I$ be an index set. For each $i \in I$ let $a_i$ and $b_i$ be families of characters of $[U(1)]$: they give a character $a_i(p)$ for each finite type $p$, read as the rank of a space. For each $i$ let $\mathfrak{m}_i$ be a modulus, $\nu_i$ a character of $[U(1)]$ and $\chi_i$ a multiplicative character of $O_E/\mathfrak{m}_i$. The lifts $\mathcal{L}$ and $\mathcal{L}^{\mathsf{T}}$ with a function modulo $\mathfrak{m}$ are those of [the seesaw for periods](/chapter/theta-lifts-seesaw/#the-seesaw-for-periods) (`New.Exchange.modLift`, `New.Exchange.modTransposedLift`). The edge families are also defined there. The rank twist is $\operatorname{rankTwist}(\alpha, N) = \alpha\,\upsilon^{|N|/2}$, with $\upsilon$ the splitting character of the Weil data on $[U(1)]$. The number $L_{\mathfrak{m}}(\nu, t)$ is the product $L_*(S, \nu, t)$ of [products of L-values](/chapter/twists-critical-pairs/#products-of-l-values-of-a-twist) for the set $S$ of places of $\mathfrak{m}$. The square law is defined in [Section 2](/chapter/seesaw-squares/#the-square-law).

**Theorem (One square identity).** Assume these conditions.

1. $(b, k_2, k, d, \Phi_2)$, $(a, k_1, k, \neg d, \Phi_1)$, $(a, k', k_2, \neg d, \Phi_2')$ and $(b, k', k_1, d, \Phi_1')$ are edge families for the pairs $(U_2, A)$, $(U_1, A)$, $(A', U_2)$ and $(A', U_1)$.
2. $\sigma \colon n \sqcup n' \simeq n_1 \sqcup n_2$ is a bijection.
3. $\operatorname{neg}(s_1 \oplus s_2) = \operatorname{neg}(s') + \operatorname{neg}(s)$.
4. $|n'| = |n| + 2t$ with $t \in \mathbb{N}$.
5. $2\operatorname{neg}(s_1 \oplus s_2) + 2 \leq |n_1 \sqcup n_2|$.
6. $|n_1 \sqcup n_2| \leq 2\mu_\tau + 2\operatorname{neg}(s_1 \oplus s_2)$ at every infinite place $\tau$.
7. $\nu_i$ is tame for $(\mathfrak{m}_i, \mu, \chi_i)$ for every $i$.
8. If $|p| + |q| = |n_1| + |n_2|$, then $a_i(p)\, b_i(q) = \operatorname{rankTwist}(\nu_i^{-1}, n_1 \sqcup n_2)$.

For $x$ an $n' \times (n_1 \sqcup n_2)$ matrix over $O_E/\mathfrak{m}_i$ with column blocks $x_1$ and $x_2$, and $y$ an $(n_1 \sqcup n_2) \times n$ matrix with row blocks $y_1$ and $y_2$, put
$$\Theta_i(x) = \mathcal{L}^{\mathsf{T}}_{U_2 \to A}(b_i, \Phi_2, \delta_{x_2}) \circ \mathcal{L}_{U_1 \to A}(a_i, \Phi_1, \delta_{x_1}),$$

$$\Theta'_i(y) = \mathcal{L}_{A' \to U_2}(a_i, \Phi_2', \delta_{y_2}) \circ \mathcal{L}^{\mathsf{T}}_{A' \to U_1}(b_i, \Phi_1', \delta_{y_1}).$$
Here $\delta_z$ is the indicator function of $z$, and both maps send forms of type $k_1(\neg d)$ on $U_1$ to forms of type $k_2(\neg d)$ on $U_2$. Then there are $C \in \mathbb{R}$ and $\kappa \in \mathbb{C}$ with this property. For every $i \in I$ there is $c \in \mathbb{C}$ with $c \neq 0$ and $|c|^2 = C\, L_{\mathfrak{m}_i}(\nu_i, t)$, such that for every form $f$ and every linear functional $l$ the functions $x \mapsto l(\Theta_i(x) f)$ and $y \mapsto l(\Theta'_i(y) f)$ satisfy the square law for $\chi_i$ and $\sigma$ with constant $\kappa/c$.

Lean: `New.Exchange.one_square_identity_of_isEdgeFamily` (New/Determinant/Exchange/OneSquare.lean).

This is the statement that [the plan](/chapter/theorem-c-plan/#constants-that-may-vanish) quotes. Section 5 proves it. The statement does not say $\kappa \neq 0$, and Section 5 explains why the proof cannot give it.

### What the chapter uses

The chapter uses these results from earlier chapters. We state each of them in one line where we use it.

1. The exchange identity for data modulo an ideal, `New.Exchange.exchange_identity`, from [the exchange identity, part 2](/chapter/exchange-identity-2/).
2. Matched functions, Jacobi's identity for complementary blocks and the block pair, from [matched functions](/chapter/exchange-identity-1/#matched-functions).
3. Edges, arrows and the lift on forms, from [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows) in Volume 6.
4. Edge families and the lifts with a function modulo $\mathfrak{m}$, from [the seesaw for periods](/chapter/theta-lifts-seesaw/#the-seesaw-for-periods) in Volume 6.
5. The finite Fourier transform of matrices, from [the notation](/chapter/notation/) of the guide.
6. The twisted moduli and the fitting twists, from [twists and critical pairs](/chapter/twists-critical-pairs/), for the grid data of Section 7.

The files of the chapter import `New.Determinant.Exchange.MatchingPartners` (chapter 5), `New.Determinant.Exchange.TheoremForPartners` and `New.OneLift.ComparisonOperator.ExchangeData` (chapter 6), `New.OneLift.Twist.FitTwists` (chapter 2), and `Lib.Weil.Seesaw`, `Lib.Weil.DualPair.Flip` and `Lib.Base` from earlier volumes. No file of this chapter imports a file that the volume puts in a later chapter.

### The plan

1. Section 2 defines the square law and proves its two finite consequences: the law at one point, and the law for a datum $p$ against the datum $\operatorname{nextDatum}(p)$. It also builds a matched partner for a given function.
2. Section 3 takes Fourier transforms. For a primitive character the law for $p$ gives an identity between the transforms, with a constant of known modulus.
3. Section 4 sets up the kernels of a square. It shows that the composite of two lifts is a sum over a product kernel, and it proves the bounds that allow Fubini.
4. Section 5 proves the one square identity and explains why $\kappa$ may vanish.
5. Section 6 defines paths in a grid, pairs of paths and turns, and proves the turn induction.
6. Section 7 defines the data on a grid: the spaces, the characters, the moves along edges, the path data and the period of a pair of paths.
7. Section 8 has exercises and notes.

### A sketch

Apply the exchange identity to the space $W = U_1 \oplus U_2$, with $V = A$ and $V' = A'$. A theta kernel on $W \otimes A$ is a product of a kernel on $U_1 \otimes A$ and a kernel on $U_2 \otimes A$. So the integral over $[U(A)]$ in the exchange identity, paired with forms on $U_1$ and $U_2$, is the pairing of the up path. The same holds on the side of $A'$ with the down path. The real vector on the side of $A$ is not chosen by us: the exchange identity produces it. So the up path is computed with the vector that the identity produces, and our vector is a different one. For a polynomial vector, the integral of the up path is one fixed multiple of the path we want, for all indices, matrices and forms at once. A density argument passes this to the produced vector. So the produced integral is a multiple $\kappa$ of the path we want. Nothing forces this multiple to be nonzero. This is the constant $\kappa$ of the theorem.
