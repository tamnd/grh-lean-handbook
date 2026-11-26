---
title: Schur matrices and the tensor model
lean:
  - Lib/GLn/SchurModule/Basic.lean
  - Lib/GLn/SchurModule/SchurMatrix.lean
  - Lib/GLn/SchurModule/TensorModel.lean
decls:
  - New.FitsRanks
  - New.schurDetExp
  - New.detPow
  - New.schur
  - New.sum_schur_smul_nablaBasis
  - New.schur_mul_left
  - New.schur_mul_right
  - New.schur_one
  - New.schur_smul
  - New.weylEval
  - New.schur_mulVec_weylEval
  - New.tableauWeight
  - New.schur_diagonal
  - New.sum_tableauWeight_le
  - New.weyl_character
  - New.weylRep
  - New.symPowMatrix
  - New.exists_equiv_schur_one_row_eq_symPowMatrix
  - New.ColumnFilling
  - New.fillingPoly
  - New.minorsMatrix
  - New.fillingMatrix
  - New.fillingMatrixOver_mul_schur
  - New.span_fillingPoly
  - New.exists_fillingMatrix_leftInverse
  - New.range_fillingMatrixOver_eq_span
  - New.exists_fillingMatrix_mulVec_eq_iff_mem_span
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Schur matrices and the tensor model

The basis of Section 3 gives the action of a matrix on the semi-invariants as a matrix of coordinates. This section defines that matrix, the Schur matrix, and proves that it is multiplicative. It then puts the Weyl module inside a tensor space with an integral basis, and shows that the Weyl lattice is a direct summand there. The tensor model is the source of the Gram matrix in Section 5.

### The setting

At each place $\tau$ of a finite set $\Phi$ there is a finite set $n_\tau$ of rows. The weight is $\kappa_\tau(h)$, the number of columns of height $h$, for $h < |n_\tau|$. Columns of the full height $|n_\tau|$ are not counted in $\kappa$. The source accounts for them by a power $e_\tau$ of the determinant in `New.weylRep` below.

In the textbook language, the pair $(\kappa, e)$ is the dominant weight $\mu_\tau = (\mu_{\tau,1} \ge \dots \ge \mu_{\tau, |n_\tau|})$ with $\kappa_\tau(h) = \mu_{\tau,h} - \mu_{\tau, h+1}$ for $0 < h < |n_\tau|$ and $e_\tau = \mu_{\tau, |n_\tau|}$. Every dominant integral weight of $\prod_\tau GL_{n_\tau}$ has this form, with $e_\tau \in \mathbb Z$.

### The Schur matrix

Let $z_\tau$ be a matrix of size $n'_\tau \times n_\tau$ over a commutative ring $R$, for every $\tau$. The substitution $f \mapsto f(zy)$ sends a polynomial in the rows $n'$ to a polynomial in the rows $n$. Here $(zy)_{(\tau, b), k} = \sum_a z_\tau(b, a)\, y_{(\tau, a), k}$, so $z$ acts on the rows from the left, as in Section 2.

**Definition.** The family of sizes *fits* $\kappa$ if $|n_\tau| \le |n'_\tau|$ and $\kappa_\tau(h) = 0$ for $|n_\tau| < h < |n'_\tau|$, at every place. The *determinant exponent* $d_\tau$ is $\kappa_\tau(|n_\tau|)$ if $|n_\tau| < |n'_\tau|$, and $0$ otherwise. The polynomial $D_d$ is $\prod_\tau \det(y_\tau)^{d_\tau}$, where $y_\tau$ is the square block of the rows of $\tau$ and the first $|n_\tau|$ columns.

Lean: `New.FitsRanks`, `New.schurDetExp`, `New.detPow` (Lib/GLn/SchurModule/Basic.lean).

The condition says that the diagram of $\kappa$ for the rank $|n'_\tau|$ has at most $|n_\tau|$ rows. Then the substitution of an $|n'_\tau| \times |n_\tau|$ matrix keeps the minors of height below $|n_\tau|$ semi-invariant, and it turns a minor of height $|n_\tau|$ into a minor of $z$ times $\det(y_\tau)$. So $b'_i(zy)$ lies in $\nabla(\kappa) \cdot D_d$, where $\nabla(\kappa)$ is the module of semi-invariants for the rows $n$.

**Definition.** Let $b$ and $b'$ be the bases of Section 3 for the rows $n$ and $n'$. The *Schur matrix* $S(z) = S_\kappa(z)$ is the matrix with rows indexed by the Weyl indices for $n'$ and columns by those for $n$, whose row $i$ is a family of coefficients $(S_{ij})_j$ with
$$b'_i(zy) = \sum_j S_{ij}\, b_j(y)\, D_d(y),$$
chosen by `Function.invFun`.

Lean: `New.schur` (Lib/GLn/SchurModule/Basic.lean).

**Lemma.** If the sizes fit $\kappa$, then the expansion above holds for every $i$:
$$\sum_j S(z)_{ij}\, b_j D_d = b'_i(zy).$$

Lean: `New.sum_schur_smul_nablaBasis` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* The polynomial $b'_i(zy)$ is a semi-invariant of the weight of $\kappa$ plus $d_\tau$ full columns at each $\tau$, by the discussion after the definition. By Section 3 (`New.nabla_le_span_nablaBasis_mul_detPow`), it is a combination of the $b_j D_d$. So the coefficients exist, and `Function.invFun` picks coefficients that work. $\square$

**Remark (Formalization).** The Schur matrix is a total function of $z$. If the sizes do not fit $\kappa$, row $i$ is the value of `Function.invFun` outside its range, an unspecified vector. All the lemmas below assume `New.FitsRanks`, and then the coefficients are unique, because the $b_j D_d$ are linearly independent (`New.GL.linearIndependent_nablaBasis_mul_detPow`). So in every case that is used, the matrix does not depend on the choice.

**Theorem.** Let the sizes fit $\kappa$. Let $z_\tau$ be of size $n'_\tau \times n_\tau$.

1. For square $g_\tau$ of size $n'_\tau$, $S(gz) = S(g) S(z)$.
2. For square $g_\tau$ of size $n_\tau$, $S(zg) = \prod_\tau \det(g_\tau)^{d_\tau} \cdot S(z) S(g)$.
3. $S(1) = 1$.
4. For scalars $t_\tau$, $S(tz) = \prod_\tau t_\tau^{|\kappa_\tau|} S(z)$, where $|\kappa_\tau| = \sum_{h < |n'_\tau|} h\, \kappa_\tau(h)$ is the number of boxes at $\tau$.

Lean: `New.schur_mul_left`, `New.schur_mul_right`, `New.schur_one`, `New.schur_smul` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* (1) Expand $b'_i(gy') = \sum_k S(g)_{ik} b'_k(y')$, put $y' = zy$, and expand each $b'_k(zy)$ by the lemma. This gives $\sum_j (S(g) S(z))_{ij}\, b_j D_d$, and the coefficients are unique by the independence of the $b_j D_d$. (2) is the same computation in the other order. (3) The substitution of $1$ is the identity. (4) follows from the diagonal case below and (1). $\square$

**Definition.** For an array $y$ over $R$ with rows $n$, the *evaluation vector* is $\operatorname{ev}_y = (b_i(y))_i$.

Lean: `New.weylEval` (Lib/GLn/SchurModule/Basic.lean).

**Lemma.** Let the sizes fit $\kappa$. Then $D_d(y) \cdot S(z)\, \operatorname{ev}_y = \operatorname{ev}_{zy}$.

Lean: `New.schur_mulVec_weylEval` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* Evaluate the expansion of the lemma at $y$. $\square$

So a vector $\xi$ of coordinates is a linear form on $\nabla(\kappa)$, through $b_i \mapsto \xi_i$, and $\operatorname{ev}_y$ is the form $f \mapsto f(y)$. The module of vectors $\xi$ with the action $\xi \mapsto S(g)\xi$ is the dual of the module of semi-invariants. This is how Jantzen, *Representations of Algebraic Groups*, 2nd ed., 2003, Part II, 2.13, defines a Weyl module. The source does not state the identification, and the chapter does not use it.

### Weights and the character

**Definition.** For a Weyl index $i$, a place $\tau$ and a row $a \in n_\tau$, the number $w_i(\tau, a)$ is the number of entries equal to $a$ in the filling $i_\tau$.

Lean: `New.tableauWeight` (Lib/GLn/SchurModule/Basic.lean).

**Lemma.** For diagonal matrices $\operatorname{diag}(x_\tau)$, the Schur matrix is diagonal with entry $\prod_\tau \prod_{a} x_\tau(a)^{w_i(\tau, a)}$ at $i$.

Lean: `New.schur_diagonal` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* The substitution of a diagonal matrix multiplies row $a$ by $x_\tau(a)$. A minor with the rows $I$ is multiplied by $\prod_{a \in I} x_\tau(a)$. $\square$

So the $b_i$ are weight vectors, and $w_i$ is the weight of $b_i$. The weights are dominated by the highest weight in the dominance order.

**Lemma.** Let $\lambda(\tau, k) = \sum_{k < h < |n_\tau|} \kappa_\tau(h)$ be the partition of $\kappa$. For a Weyl index $i$, a place $\tau$ and a set $A$ of rows:

1. $\sum_{a \in A} w_i(\tau, a) \le \sum_{k < |A|} \lambda(\tau, k)$;
2. if equality holds, then every entry of $i_\tau$ in a column of height at most $|A|$ lies in $A$.

Lean: `New.sum_tableauWeight_le` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* The entries of a column are distinct (`New.tableau_col_injective`), since a minor with two equal rows is $0$ and the $b_i$ are independent. So a column of height $h$ has at most $\min(h, |A|)$ entries in $A$. The sum of $\min(h, |A|)$ over the columns is $\sum_{k < |A|} \lambda(\tau, k)$. Equality forces each column of height at most $|A|$ to lie in $A$. $\square$

**Theorem (Weyl character formula).** Let $e_\tau : \{0, \dots, a_\tau - 1\} \to n_\tau$ be bijections and $x_\tau : n_\tau \to \mathbb C$. Then
$$\operatorname{tr} S(\operatorname{diag}(x)) \cdot \prod_\tau \det V(x_\tau \circ e_\tau) = \prod_\tau \det\Big(x_\tau(e_\tau(i))^{\lambda(\tau, a_\tau - 1 - j) + j}\Big)_{i, j},$$
where $V$ is the Vandermonde matrix $(x_i^{\,j})$.

Lean: `New.weyl_character` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* By the diagonal lemma, the trace is a product over $\tau$ of the sums $\sum_T x^T$ over the standard fillings. At each place the character property (b) of `New.IsTableauBasis` gives the identity, since $a_0$ is the Vandermonde determinant $\det V$ and $\lambda(\tau, \cdot)$ is the weight $i \mapsto \sum_{i < h < N} k(h)$ of that property. $\square$

The textbook form is $\operatorname{tr} \pi_\lambda(\operatorname{diag}(x)) = a_{\lambda + \delta}(x) / a_\delta(x)$ (Fulton and Harris, *Representation Theory*, 1991, Theorem 6.3, with the denominator cleared).

### The representation and the model case

**Definition.** For $\kappa$ and $e : \Phi \to \mathbb Z$, the *Weyl representation* of $\prod_\tau GL_{n_\tau}(R)$ is
$$\operatorname{weylRep}_{\kappa, e}(g) = \prod_\tau \det(g_\tau)^{e_\tau} \cdot S_\kappa(g).$$

Lean: `New.weylRep` (Lib/GLn/SchurModule/SchurMatrix.lean).

It is a monoid homomorphism by (1) and (3) of the theorem. For $e_\tau \ge 0$ it is the Schur matrix of the diagram with $e_\tau$ more columns of full height, but the source never needs this identification: the factor $\det^{e}$ is carried as a scalar in all later statements.

The model case of Section 1 is a theorem of the source.

**Definition.** For a square matrix $A$ over $\sigma$, the *symmetric power* $\operatorname{Sym}^a(A)$ is the matrix, in the monomial basis of the forms of degree $a$ in $\sigma$, of the linear substitution by $A$.

Lean: `New.symPowMatrix` (Lib/GLn/SchurModule/Basic.lean).

**Proposition.** Let $|m| > 1$, let $k(1) = a$ and $k(h) = 0$ for $1 < h < |m|$, and let $q : \sigma \to m$ be a bijection. Then there is a bijection $\varphi$ from the Weyl indices onto the monomials of degree $a$ in $\sigma$ such that for every $c \in \mathbb C$ and every square complex $z$,
$$c^a\, S_k(z)_{ij} = \operatorname{Sym}^a\big(c \cdot z^{\mathsf T}_{q, q}\big)_{\varphi(j), \varphi(i)}.$$

Lean: `New.exists_equiv_schur_one_row_eq_symPowMatrix` (Lib/GLn/SchurModule/SchurMatrix.lean).

The transposes in the formula come from the two conventions. The Schur matrix has the coordinates of $b_i(zy)$ in its row $i$, and $\operatorname{Sym}^a$ has the coordinates of the image of a basis vector in its column. The factor $c^a$ shows that the identity is linear in $z^{\otimes a}$. The source uses it in `New/UpperBound/Divisibility/HeckeEdges.lean` and `New/Spanning/Unfolding/FillingAdmissible.lean` for diagrams with one row.

### The tensor model

Over $\mathbb Q$ a Weyl module is a summand of a tensor product of exterior powers, one for each column. The source proves the integral form of this.

**Definition.** A *column filling* $T$ gives each column of the diagram, of height $h$ at the place $\tau$, a strictly increasing sequence of $h$ row numbers in $\{0, \dots, |n_\tau| - 1\}$. Its *minor product* is $f_T = \prod$ over the columns of the minor with these rows, read through the numbering of $n_\tau$. For square $z_\tau$, the matrix $\operatorname{Min}(z)$ has the entry $\prod_{\text{columns}} \det\big(z_\tau[T_{\text{col}}, T'_{\text{col}}]\big)$ at $(T, T')$. The *filling matrix* $F$ has as row $T$ the integer coordinates of $f_T$ in the basis $b$, chosen by `Function.invFun`.

Lean: `New.ColumnFilling`, `New.fillingPoly`, `New.minorsMatrix`, `New.fillingMatrix` (Lib/GLn/SchurModule/TensorModel.lean).

The column fillings index the standard basis of $\bigotimes_{\text{columns}} \Lambda^h R^{n_\tau}$, and $\operatorname{Min}(z)$ is the matrix of $\bigotimes \Lambda^h z$ in this basis. The coordinates in the definition of $F$ exist and are unique, by Sections 2 and 3. So the choice by `Function.invFun` is harmless here.

**Theorem.**

1. For square $z_\tau$, $F\, S(z) = \operatorname{Min}(z)\, F$ over every commutative ring.
2. The $f_T$ span $\nabla(\kappa)$ over every commutative ring.
3. There is an integer matrix $Q$ with $Q F = 1$.
4. Over an infinite field $K$, the image of $F$ is the span of the vectors $(f_T(y))_T$ for the arrays $y$ over $K$.
5. An integer vector $v$ is $F \xi$ for an integer vector $\xi$ if and only if $v$ lies in the $\mathbb Q$-span of the vectors $(f_T(y))_T$ for rational arrays $y$.

Lean: `New.fillingMatrixOver_mul_schur`, `New.span_fillingPoly`, `New.exists_fillingMatrix_leftInverse`, `New.range_fillingMatrixOver_eq_span`, `New.exists_fillingMatrix_mulVec_eq_iff_mem_span` (Lib/GLn/SchurModule/TensorModel.lean).

*Proof.* (1) Row $T$ of $F$ is the coordinate vector of $f_T$. Compare the two sides as polynomials through $\xi \mapsto \sum \xi_i b_i$, which is injective. Row $T$ of $F S(z)$ gives $f_T(zy)$. By the Cauchy-Binet formula for each minor, $f_T(zy) = \sum_{T'} \operatorname{Min}(z)_{T T'} f_{T'}(y)$ (`New.rowSubst_fillingPoly`), and this is row $T$ of $\operatorname{Min}(z) F$.

(2) Each $f_T$ is a semi-invariant. Conversely, a basis element $b_i$ is a minor product whose rows need not be increasing. Substitute the identity matrix and apply Cauchy-Binet: $b_i = \sum_T c_T f_T$, where $c_T$ is a product of minors of the identity matrix.

(3) By (2) over $\mathbb Z$, for each $i$ there is an integer vector $v_i$ with $\sum_T v_i(T) f_T = b_i$. Let $Q$ have the rows $v_i$. Then $(QF)_i$ is the coordinate vector of $\sum_T v_i(T) f_T = b_i$, which is the unit vector at $i$.

(4) The image of $F$ contains $F \operatorname{ev}_y = (f_T(y))_T$. Conversely, a linear form $c$ that vanishes on all $(f_T(y))_T$ gives the polynomial $\sum_T c_T f_T$, which vanishes on all of $K^{\text{array}}$. A polynomial over an infinite field that vanishes everywhere is $0$. So $F^{\mathsf T} c = 0$, and $c$ vanishes on the image of $F$.

(5) One direction is clear. For the other, (4) over $\mathbb Q$ gives a rational $\eta$ with $F \eta = v$. Then $\eta = Q F \eta = Q v$ is an integer vector. $\square$

The textbook statement of (3) is that the Weyl module over $\mathbb Z$ is a direct summand of a tensor product of exterior powers as a $\mathbb Z$-module. The source cites Akin, Buchsbaum and Weyman, Adv. Math. 44 (1982), for it.

**Remark (Formalization).** The direct summand in (3) is a summand of $\mathbb Z$-modules only. The left inverse $Q$ is not equivariant, and no statement says it is. The source uses $Q$ to show that some vectors are integral, as in (5), and never to move the group action.

