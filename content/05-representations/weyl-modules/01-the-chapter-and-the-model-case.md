---
title: The chapter and the model case
lean:
  - Lib/GLn/SchurModule/Basic.lean
  - Lib/GLn/SchurModule/GramMatrix.lean
  - Lib/GLn/SchurModule/SchurNorm.lean
  - Lib/GLn/Branching/IntegralMap.lean
  - Lib/GLn/Dual.lean
decls:
  - New.hookNumber_one_row
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and the model case

This chapter is about the polynomial representations of a product of general linear groups $\prod_\tau GL_{n_\tau}$. The source needs three things from them that a textbook does not give: a lattice in each representation with an integer Gram matrix, explicit norm bounds for the representation matrices and for the maps between representations, and these maps as integer matrices that work over every field of characteristic $0$ at once. The chapter constructs these objects from products of minors, as the source does. The overview of the argument is in [the theorem and the plan](/chapter/theorem-and-plan/).

### Where the chapter is used

The three main theorems use the chapter. Theorem A uses the norm bound for Schur matrices (`New.weylNormSq_schur_le`) and the branching matrix (`New.exists_branching_matrix`). Theorem B uses the formula for the diagonal matrix coefficient (`New.weylRep_coeff_eq_prod_weightMinors`). Theorem C uses the branching matrix, the dual pairing (`New.exists_isDualPairing_of_isHCParam`), the bound for the hook number and the mixed Cartan embedding. The plans are in [the plan of Theorem A](/chapter/theorem-a-plan/), [the plan of Theorem B](/chapter/theorem-b-plan/) and [the plan of Theorem C](/chapter/theorem-c-plan/).

In each use the representation is a coefficient system for automorphic forms on a unitary group, with one factor $GL_n(\mathbb C)$ for each infinite place $\tau$ of a CM field. The arguments need a norm on $V$ that comes from an integer Gram matrix, is invariant under $\prod_\tau U(n)$, and gives explicit norm bounds for the maps of the argument. This chapter supplies that norm.

### The model case: symmetric powers of the standard representation of $GL_2$

Before the general case we work out the smallest case in the language of the source. Take one place, two rows and the weight of $\operatorname{Sym}^k$. Here every object of the chapter can be computed by hand.

The source works with polynomials in an array of variables $X(a, i)$, with a row $a$ and a column $i \in \mathbb N$. For $GL_2$ the rows are $a \in \{1, 2\}$. A *weight* counts columns: $\kappa(h)$ is the number of columns of height $h$, for $0 < h < 2$. So the weight is one number $\kappa(1) = k$, the diagram of one row with $k$ boxes. The polynomials of this weight are the homogeneous polynomials of degree $k$ in $x_1 = X(1, 0)$ and $x_2 = X(2, 0)$.

The basis of the source consists of products of minors, one minor for each column of the diagram. A column of height $1$ gives a $1 \times 1$ minor, which is one variable. So the basis is the set of monomials

$$b_a = x_1^a x_2^{k - a}, \qquad 0 \le a \le k.$$

The group acts on polynomials by substitution of the rows: $g$ sends $f(x)$ to $f(gx)$. The *Schur matrix* $S(g)$ is the matrix of this substitution in the basis $b_a$. For $\operatorname{Sym}^k$ it is the classical matrix of the symmetric power. The Weyl module of the source is the space of coordinate vectors $\xi = (\xi_a)$, and $S(g)$ acts on it.

The next object is the *kernel*. Let $f = x_1^k$ be the product of the leading minors, one for each column. For a second array $y$ the kernel is $f(y^{\mathsf T} x)$, that is,

$$(y_1 x_1 + y_2 x_2)^k = \sum_{a = 0}^{k} \binom{k}{a} (y_1 x_1)^a (y_2 x_2)^{k - a} = \sum_{a} \binom{k}{a} b_a(x) b_a(y).$$

The *Gram matrix* $G$ of the source has as entries the integer coefficients of the kernel in the products $b_a(x) b_{a'}(y)$. Here it is the diagonal matrix with entries $\binom{k}{a}$. The squared norm of a complex vector is $\xi^* G \xi = \sum_a \binom{k}{a} |\xi_a|^2$.

There is a second way to find this form, through tensors. The basis tensors of $(\mathbb C^2)^{\otimes k}$ are the words $T = (T_1, \dots, T_k)$ in the letters $1, 2$. The product $x_{T_1} \cdots x_{T_k}$ is $b_a$, with $a$ the number of letters $1$. Let $F$ be the $0$-$1$ matrix with row $T$ equal to the coordinates of this product. Then $(F^{\mathsf T} F)_{a a}$ counts the words with $a$ letters $1$, so $F^{\mathsf T} F = G$. So $G$ is the restriction of the form on tensors for which the basis tensors are orthonormal. The matrix $F$ has an integer left inverse, so $\mathbb Z^{k+1}$ is a direct summand of the integral tensors.

The third object is the *Fock pairing* $\langle p, q \rangle = p(\partial) q(0)$ of polynomials. For monomials it gives $\langle x^d, x^{d'} \rangle = d!$ if $d = d'$ and $0$ otherwise. So the matrix $H$ of the pairings of the basis is diagonal with entries $a!(k - a)!$. Then

$$G H = \operatorname{diag}\Big(\binom{k}{a} a! (k - a)!\Big) = k! \cdot 1.$$

The number $k!$ is $\langle f, f \rangle$ for $f = x_1^k$. The source calls $\langle f, f\rangle$ the *hook number*. The identity $GH = \langle f, f \rangle \cdot 1$ holds for every weight, by Schur's lemma (Section 5). So $G^{-1} = \langle f, f\rangle^{-1} H$, and the hook number times $G^{-1}$ is an integer matrix. For a weight with one row at each place the source computes it.

**Lemma.** Let $\Phi$ be a finite set, and let $N_\tau > 1$ for every $\tau$. Let $\kappa_\tau(h) = 0$ for $1 < h < N_\tau$. Then the hook number of $\kappa$ is $\prod_\tau \kappa_\tau(1)!$.

Lean: `New.hookNumber_one_row` (Lib/GLn/SchurModule/GramMatrix.lean).

The name comes from the product of the hook lengths of the diagram. For one row of length $k$ that product is $k!$. The source does not prove a closed formula for the hook number in general. It uses only the bound of Section 5: the hook number is positive, and it is at most $(L^L)^3$ if the diagrams have at most $L$ boxes.

The fourth object is the norm bound. Let $z$ be a complex $2 \times 2$ matrix and let $\rho_0$ be the largest eigenvalue of $z^* z$. Then $\xi^* S(z)^* G S(z) \xi \le \rho_0^k \cdot \xi^* G \xi$, because $\operatorname{Sym}^k$ is a subspace of the tensor power with the restricted form, and $z^{\otimes k}$ has operator norm $\rho_0^{k/2}$. Section 6 gives the general form.

The last object is branching. Restrict $\operatorname{Sym}^k$ to the matrices $\operatorname{diag}(g, s)$ with $g, s \in GL_1$. The monomial $b_a$ is an eigenvector with eigenvalue $g^a s^{k - a}$, so the representation splits into $k + 1$ characters, each once. The branching map onto $g^a s^{k - a}$ is the coordinate $\xi \mapsto \xi_a$, an integer matrix. Section 7 gives the general case.

### What the chapter proves

The chapter proves the following, for products of general linear groups and for weights given by counts of columns.

1. The standard basis theorem in an existence form: some set of products of minors is a basis of the semi-invariants over every commutative ring, and its weights give the Weyl character formula (Section 3).
2. The Schur matrices are integer polynomial matrices with $S(gz) = S(g)S(z)$, and the Weyl module is an integral direct summand of the tensors (Section 4).
3. The Gram matrix is $F^{\mathsf T} F$, it is positive definite, and its product with the Fock matrix is the hook number times the identity. The hook number is at most $(L^L)^3$ (Section 5).
4. The Schur matrix of $z$ has a norm bound in terms of the singular values of $z$. The norm is submultiplicative under products of polynomials. Schur's lemma and Schur orthogonality hold for the compact group (Section 6).
5. The branching map to $GL_{n-1} \times GL_1$ is an integer matrix, equivariant over every field of characteristic $0$, with squared norm at most $((L^L)^3)^2$, and every unitarily equivariant map is a multiple of it. The dual of a Weyl module is a Weyl module by a unimodular isometric integer matrix (Section 7).

Section 8 has exercises and the notes.

### A remark on the method

The source does not use Lie algebras, Young symmetrizers or the symmetric group. Everything is a statement about polynomials: products of minors, substitution of rows, and the Fock pairing. The price is that the basis is chosen by `Classical.epsilon` (Section 3). The gain is that all matrices are integer matrices, and their properties hold over every commutative ring or every field of characteristic $0$, as stated.
