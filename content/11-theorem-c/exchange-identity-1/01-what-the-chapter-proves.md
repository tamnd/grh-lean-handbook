---
title: What the chapter proves
lean:
  - New/Determinant/Exchange/MatchingPartners.lean
  - New/Determinant/Exchange/ConeImage.lean
  - New/Determinant/Exchange/NegativeIndices.lean
  - New/Determinant/Exchange/EquivariantDifference.lean
  - New/Determinant/Exchange/StableSpacesStandardData.lean
  - New/Determinant/Exchange/LargeTriple.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the first half of the exchange identity. The exchange identity compares two theta integrals on one group $U(X)$. The first integral is over a large group $U(V)$, with a datum that is read from rows. The second integral is over a smaller group $U(V')$, with a datum that is read from columns. The identity says that, on standard data at the ramified places, the first integral is a constant $c$ times the second integral, and that $|c|^2$ is a product of $L$-values times a fixed ratio. The chain of lifts of [the plan of the volume](/chapter/theorem-c-plan/) uses the identity at each step: it compares the lifts for two orders of the chain. The general plan of the book is in [the theorem and the plan](/chapter/theorem-and-plan/).

This chapter does four things. It defines *matched functions*, the local objects that the two sides of the identity use at the ramified places. It shows that the difference of the two sides is an *equivariant lift*, and that an equivariant lift that vanishes at a few special data vanishes on all matched data. It proves two vanishing results for Fourier coefficients: one at the indices that are not negative definite, and one at the self-dual lattices. Then it proves the identity for the *large triple* $V = V' \oplus W_1$, under the hypothesis that a period identity holds over $U(W_1)$. The [second part](/chapter/exchange-identity-2/) proves the period identity, removes hyperbolic planes, and proves the general case.

### Why an exchange identity

A theta integral of a pair $(X, V)$ of hermitian spaces is a function on $U(X)$ that integrates the theta kernel over $[U(V)]$. If $V = V' \oplus W_1$, the group $U(V') \times U(W_1)$ sits in $U(V)$, and the theta kernel of $(X, V)$ is the product of the theta kernels of $(X, V')$ and $(X, W_1)$. This is the classical *seesaw* of Kudla. If we integrate over $U(W_1)$ first, we get the theta integral of $(X, W_1)$, which the Siegel-Weil formula identifies. The source does not use the seesaw in this form. It compares the integral over the whole group $U(V)$ with an integral over $U(V')$ alone, and the comparison depends on the data at the ramified places.

At a ramified place the data are not the vacuum. The large side has a datum $\Phi$ on $a \times n$ matrices, where $a$ is the frame of $V$ and $n$ the frame of $X$. The small side has a datum $\Psi$ on $n \times b$ matrices, where $b$ is the frame of $V'$. The two data must fit together, and the condition is that they are *matched*: $\Phi$ lives on the last rows of the inverses of integral matrices $k$, $\Psi$ lives on the first columns of the same $k$, and their values there differ by $\chi(\det k)$. The model of a matched pair comes from Jacobi's identity for complementary minors (Section 2).

### What the chapter uses

The chapter uses the theta integral and the Weil representation of [Volume 6](/chapter/weil-representation/), the singular forms and their centre coefficients of [the inner product formula](/chapter/rallis-inner-product/), and the tower of [the same chapter](/chapter/rallis-inner-product/#the-tower): constant terms along an isotropic line, cone integrals, and the products $L_*(e)$ of $L$-values. It uses split tame characters, defined in [characters and twists](/chapter/fields-places-twists/). It uses the theorem of Witt and weak approximation for unitary groups from [Volume 4](/chapter/adeles-hermitian-spaces/). No file of this chapter imports a file of a later chapter of this volume.

### The plan

The argument runs in this order.

1. Section 2 defines matched functions and proves that block determinant functions are matched.
2. Section 3 defines the sections of a function over the cosets of $GL_b(O)$ and the *same-section pairs*. It proves that matched pairs are same-section pairs, and that a functional that is equivariant in $\Phi$ depends only on $\Psi$.
3. Section 4 uses Section 3 to write the difference $\mathcal{D}(\Psi) = \Theta_{\mathrm{large}}(\Phi) - c\, \Theta_{\mathrm{small}}(\Psi)$ as one linear map of $\Psi$ with the laws of an equivariant lift.
4. Section 5 proves that an equivariant lift that vanishes at the self-dual lattices of a frame vanishes on every matched datum.
5. Section 6 proves that a Fourier coefficient of a theta integral vanishes at an index that is not negative definite at some real place.
6. Section 7 proves that a cone integral at the real places changes the theta integrals of standard data only by a positive analytic factor. It then puts these results together for the large triple, and reduces the exchange identity for $V = V' \oplus W_1$ to a period identity over $[U(W_1)]$.
7. Section 8 has the exercises and the notes.

The logic of the end of Section 7 is short. Let $\mathcal{D}$ be the difference of the two sides for a constant $c$. By Section 4 it is an equivariant lift, and by Section 5 it vanishes on matched data if its Fourier coefficients vanish at the self-dual lattices. There are two kinds of such coefficients. At the indices that are not negative definite, both sides vanish by Section 6, or by a hypothesis on the real data. At the one remaining index, $T = J$, both sides are periods, and the period identity over $[U(W_1)]$ fixes $c$ so that the two periods agree.

The source states the results of this chapter for every split tame character at once. The constants that the proofs produce do not depend on the character. The chain of the plan uses this property, because it applies the identity to many characters with one constant.
