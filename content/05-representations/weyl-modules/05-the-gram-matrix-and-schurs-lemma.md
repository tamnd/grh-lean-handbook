---
title: The Gram matrix and Schur's lemma
lean:
  - Lib/GLn/SchurModule/Basic.lean
  - Lib/GLn/SchurModule/WeylKernel.lean
  - Lib/GLn/SchurModule/GramMatrix.lean
decls:
  - New.highestPoly
  - New.weylKernel
  - New.weylGram
  - New.weylGramOver
  - New.toPoly
  - New.toPoly_weylEval
  - New.weylKernel_eq_sum_fillingPoly
  - New.fillingMatrix_transpose_mul_self
  - New.weylGram_isSymm
  - New.weylGramOver_posDef
  - New.weylGramOver_mul_schur
  - New.toPoly_schur
  - New.toPoly_injective
  - New.range_toPoly
  - New.GL.zariski_dense_unitary
  - New.mem_range_scalar_of_commute_schur
  - New.hookNumber
  - New.weylGram_mul_fockPairing
  - New.fockPairing_toPoly_nablaBasis
  - New.fockPairing_toPoly_toPoly
  - New.exists_weylGram_mulVec_eq_hookNumber_smul
  - New.hookNumber_pos
  - New.hookNumber_le
  - New.weylNormSq
  - New.weylNormSq_nonneg
  - New.GL.weylNormSq_weylEval_permArray
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Gram matrix and Schur's lemma

This section defines the integer Gram matrix $G$ of the Weyl module and proves its three properties: it is $F^{\mathsf T} F$, it is positive definite, and it is invariant. It then proves Schur's lemma for the unitary group, and uses it to show that $G$ times the matrix of Fock pairings is the hook number times the identity. The section ends with the bound for the hook number. These are the constants that the later volumes use.

### The kernel and the Gram matrix

The idea is the reproducing kernel. In the model case of Section 1 the kernel is $(y_1 x_1 + y_2 x_2)^k$. In general it is the product of leading minors, translated by $y^{\mathsf T}$.

**Definition.** Let $f = \prod_\tau \prod_{h < |n_\tau|} \Delta_{\{1, \dots, h\}}^{\kappa_\tau(h)}$ be the product of the leading principal minors, one for each column of the diagram. For an array $y$ over $R$, the *kernel* is the polynomial $K_y(x) = f(y^{\mathsf T} x)$, where block $\tau$ of $y$ is read on its first $|n_\tau|$ columns.

Lean: `New.highestPoly` (Lib/GLn/SchurModule/Basic.lean), `New.weylKernel` (Lib/GLn/SchurModule/Basic.lean).

The kernel $K_y$ is a semi-invariant of weight $\kappa$ in $x$. If $y$ is also a variable array, it is a semi-invariant in $y$ too. So it has an expansion $K_y(x) = \sum_{i, j} G_{ij}\, b_i(x)\, b_j(y)$ with integer $G_{ij}$.

**Definition.** The *Gram matrix* $G$ is the integer matrix of the coefficients of the generic kernel in the products $b_i(x) b_j(y)$. It is defined in two steps by `Function.invFun`: first the coefficients of $K_y$ in the $b_i(x)$, which are polynomials in $y$, and then the coefficients of these in the $b_j(y)$. The matrix `New.weylGramOver` is $G$ with its entries mapped into $R$. The *polynomial of a vector* $\xi$ is $\hat\xi = \sum_i (G\xi)_i\, b_i$.

Lean: `New.weylGram`, `New.weylGramOver`, `New.toPoly` (Lib/GLn/SchurModule/Basic.lean).

**Remark (Formalization).** Both choices by `Function.invFun` are at points of the range, and both expansions are unique by the independence of the $b_i$ over every commutative ring (Section 3). So $G$ has no junk entries. The source records this as `New.sum_weylGram_smul_eq_weylKernel_of_exists`.

**Lemma.** For every array $y$ over $R$, $\widehat{\operatorname{ev}_y} = K_y$.

Lean: `New.toPoly_weylEval` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* Specialise the generic expansion $K_Y(x) = \sum_i \big(\sum_j G_{ij} b_j(Y)\big) b_i(x)$ at $Y = y$. The coefficient of $b_i$ is $\sum_j G_{ij}\, b_j(y) = (G \operatorname{ev}_y)_i$. $\square$

So $G$ is the matrix of the map from point evaluations to kernels. Over $\mathbb C$, for every $\hat\xi$, the value $\hat\xi(y)$ is $\operatorname{ev}_y^{\mathsf T} G \xi$ (`New.GL.eval_toPoly`).

### The Gram matrix is restricted from tensors

**Theorem.** Let $F$ be the filling matrix of Section 4.

1. $K_y = \sum_T f_T(y)\, f_T$, the sum over the column fillings.
2. $F^{\mathsf T} F = G$. In particular $G$ is symmetric.
3. Over $\mathbb C$, $G$ is positive definite.
4. For square matrices $g_\tau$ over $R$, $G\, S(g) = S(g^{\mathsf T})^{\mathsf T}\, G$.

Lean: `New.weylKernel_eq_sum_fillingPoly`, `New.fillingMatrix_transpose_mul_self`, `New.weylGram_isSymm`, `New.weylGramOver_posDef`, `New.weylGramOver_mul_schur` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* (1) Each factor of $K_y$ is a leading minor of $y^{\mathsf T} x$. By the Cauchy-Binet formula, the leading $h \times h$ minor of $y^{\mathsf T} x$ is $\sum_I \Delta_I(y) \Delta_I(x)$ over the increasing $h$-tuples $I$ of rows. Multiply out over the columns. A choice of $I$ for every column is a column filling $T$, and the product is $f_T(y) f_T(x)$.

(2) Apply $\xi \mapsto \sum_i \xi_i b_i$ to $G \operatorname{ev}_y$ and to $F^{\mathsf T} F \operatorname{ev}_y$. The first gives $K_y$ by the lemma. Since row $T$ of $F$ holds the coordinates of $f_T$, the second gives $\sum_T f_T(y) f_T = K_y$ by (1). The evaluation vectors span over an infinite domain (`New.GL.ext_weylEval`), so $G = F^{\mathsf T} F$.

(3) $F$ is real, so $F^{\mathsf T} = F^*$ and $\xi^* G \xi = \|F \xi\|^2$. It is positive for $\xi \ne 0$, because $F$ has the left inverse $Q$ of Section 4.

(4) By Section 4, $F S(g) = \operatorname{Min}(g) F$. The matrix of minors satisfies $\operatorname{Min}(g^{\mathsf T}) = \operatorname{Min}(g)^{\mathsf T}$, since a minor of $g^{\mathsf T}$ is the transposed minor of $g$. So $G S(g) = F^{\mathsf T} \operatorname{Min}(g) F = (\operatorname{Min}(g^{\mathsf T}) F)^{\mathsf T} F = (F S(g^{\mathsf T}))^{\mathsf T} F = S(g^{\mathsf T})^{\mathsf T} G$. $\square$

By (4), for a unitary $g$ over $\mathbb C$ the matrices $S(g)$ and $S(g^{\mathsf T})$ are adjoint for the bilinear form of $G$. Section 6 turns this into the unitarity of $S(g)$ for the Hermitian form $\xi^* G \eta$.

**Lemma.** Let $R$ be a domain of characteristic $0$, and let the sizes fit $\kappa$. Then:

1. $\widehat{S(z)\xi} = \big(\hat\xi \cdot D_d\big)(z^{\mathsf T} x)$ for $z_\tau$ of size $n'_\tau \times n_\tau$;
2. the map $\xi \mapsto \hat\xi$ is injective;
3. over $\mathbb C$, its image is exactly $\nabla(\kappa)$.

Lean: `New.toPoly_schur`, `New.toPoly_injective`, `New.range_toPoly` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* (1) Both sides are linear in $\xi$, so it is enough to take $\xi = \operatorname{ev}_y$ with $D_d(y) \ne 0$. Then $D_d(y) S(z) \operatorname{ev}_y = \operatorname{ev}_{zy}$ (Section 4), and both sides reduce to $K_{zy}$, because $(zy)^{\mathsf T} x = y^{\mathsf T}(z^{\mathsf T} x)$. (2) The integer $\det G$ is positive, so it is not zero in $R$. (3) $G$ is invertible over $\mathbb C$, and the image of $\xi \mapsto \sum \xi_i b_i$ is $\nabla(\kappa)$ (Section 3). $\square$

### Schur's lemma for the unitary group

The scalar in the Fock identity of the model case came from a computation. In general it comes from Schur's lemma. The source proves Schur's lemma directly, from the highest weight vector and the density of the unitary group.

**Lemma (Zariski density).** Let $P$ be a complex polynomial in the entries of a family of square matrices $g_\tau$. If $P$ vanishes at every family of unitary matrices, then $P$ vanishes everywhere.

Lean: `New.GL.zariski_dense_unitary` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* Write $y = \operatorname{Re} y + i \operatorname{Im} y$ with Hermitian parts. The function $s \mapsto P(\exp(i(-s \operatorname{Re} y + \operatorname{Im} y)))$ is entire, and it vanishes for real $s$, where the exponential is unitary. So it vanishes at $s = i$, where the exponent is $y$. So $P \circ \exp = 0$. The exponential is a local diffeomorphism at $0$, so $P$ vanishes near $1$, and $P = 0$. $\square$

**Theorem (Schur's lemma).** Let $T$ be a complex square matrix on the Weyl module with $T\, S(g) = S(g)\, T$ for every family $g$ of unitary matrices. Then $T$ is a scalar matrix.

Lean: `New.mem_range_scalar_of_commute_schur` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* Let $w$ be the *frame array*: the entry at the row $(\tau, a)$ and the column $k$ is $1$ if $k$ is the number of $a$ in a fixed numbering of $n_\tau$, and $0$ otherwise. So $w$ is the identity matrix in each block. Let $v = \operatorname{ev}_w$. By the theorem $K_w = f$, so $v$ is the vector of the highest weight polynomial.

Step 1. The entries of $S(g) T v - T S(g) v$ are polynomials in $g$. They vanish on the unitary families, so by Zariski density they vanish for every $g$.

Step 2. Let $D$ be the diagonal family with $2$ at the row $(\tau, a)$ and $1$ elsewhere. Then $S(D) v = 2^m v$, where $m = \lambda(\tau, \text{number of } a)$ is the highest weight at that row. By Step 1, $S(D) (Tv) = 2^m (Tv)$. Since $S(D)$ is diagonal with entry $2^{w_i(\tau, a)}$ at $i$, every $i$ with $(Tv)_i \ne 0$ has $w_i(\tau, a) = m$. So $Tv$ lies in the highest weight space.

Step 3. A linear form $\varphi$ on polynomials that sees only basis vectors of highest weight is determined by its value at the kernel: $\varphi(b_i) = \varphi(K_w)\, b_i(w)$ (`New.map_nablaBasis_eq_map_weylKernel_mul_weylEval`). Apply this to the form $b_i \mapsto (Tv)_i$. It gives $Tv = c\, v$ for a number $c$.

Step 4. By Step 1, $T S(g) v = S(g) T v = c\, S(g) v$ for all $g$. The vectors $S(g) v = \operatorname{ev}_{g w}$, for $g$ invertible, span the Weyl module (`New.GL.ext_schur_weylEval`). So $T = c \cdot 1$. $\square$

The textbook route is the irreducibility of the Weyl module over $\mathbb C$ (Fulton and Harris, *Representation Theory*, 1991, Theorem 6.3), followed by Schur's lemma (same book, Lemma 1.7). The source proves only the commutant statement for unitary families, which is what it uses.

### The Fock identity

**Definition.** The *hook number* is $h_\kappa = \langle f, f \rangle = f(\partial) f(0)$, the Fock pairing of the highest weight polynomial with itself, computed over $\mathbb Z$.

Lean: `New.hookNumber` (Lib/GLn/SchurModule/Basic.lean).

**Theorem.** Let $H = (\langle b_i, b_j \rangle)_{i, j}$ be the integer matrix of the Fock pairings of the basis. Then
$$G H = h_\kappa \cdot 1.$$

Lean: `New.weylGram_mul_fockPairing` (Lib/GLn/SchurModule/GramMatrix.lean).

*Proof.* Over $\mathbb C$, let $T = H^{\mathsf T} G$, so that $(T\xi)_k = \langle \hat\xi, b_k \rangle$. By (1) of the last lemma, $\widehat{S(g)\xi} = \hat\xi(g^{\mathsf T} x)$. The adjoint property $\langle p(g^{\mathsf T} x), q \rangle = \langle p, q(g x) \rangle$ (`New.fockPairing_rowSubst`) and $b_k(gx) = \sum_j S(g)_{kj} b_j$ give $T S(g) = S(g) T$. By Schur's lemma $T = c \cdot 1$.

To find $c$, take $v = \operatorname{ev}_w$ for the frame $w$ of the proof of Schur's lemma. Then $\langle K_w, K_w \rangle = h_\kappa$ (`New.fockPairing_weylKernel_permArray_self`), and $\langle \hat v, \hat v \rangle = c\, v^{\mathsf T} G v = c\, K_w(w) = c$. So $c = h_\kappa$, over $\mathbb C$ and hence over $\mathbb Z$. Transpose, and use that $G$ and $H$ are symmetric. $\square$

**Corollary.** For vectors $\xi, \eta$ over any commutative ring $R$ and every index $k$:

1. $\langle \hat\xi, b_k \rangle = h_\kappa\, \xi_k$;
2. $\langle \hat\xi, \hat\eta \rangle = h_\kappa\, \xi^{\mathsf T} G \eta$;
3. for every integer tensor $v$, there is an integer vector $\eta$ with $G \eta = h_\kappa\, F^{\mathsf T} v$.

Lean: `New.fockPairing_toPoly_nablaBasis`, `New.fockPairing_toPoly_toPoly`, `New.exists_weylGram_mulVec_eq_hookNumber_smul` (Lib/GLn/SchurModule/GramMatrix.lean).

*Proof.* (1) and (2) are the theorem written out. For (3), take $\eta = H F^{\mathsf T} v$. $\square$

Statement (3) says that $h_\kappa$ times the orthogonal projection of an integral tensor to the Weyl module is integral. So $h_\kappa$ is the denominator of the projection, and $h_\kappa G^{-1} = H$ is an integer matrix.

### The size of the hook number

**Theorem.** Let $N_\tau$ be any ranks, and let $\kappa$ have at most $L$ boxes: $\sum_\tau \sum_{h < N_\tau} h\, \kappa_\tau(h) \le L$. Then
$$0 < h_\kappa \le (L^L)^3.$$

Lean: `New.hookNumber_pos`, `New.hookNumber_le` (Lib/GLn/SchurModule/WeylKernel.lean).

*Proof.* Positivity. The polynomial $f$ is not zero, since $f$ at the identity array is $1$. The Fock pairing of a nonzero integer polynomial with itself is $\sum_\alpha \alpha!\, c_\alpha^2 > 0$ (Section 2).

Upper bound. Let $d \le L$ be the degree of $f$. Expand each minor over permutations. Then $f$ is a sum of $|S| \le d!$ signed monomials, since a product of factorials divides the factorial of the sum. The Fock pairing of two such monomials is at most $d!$. So
$$h_\kappa \le |S| \cdot |S| \cdot d! \le (d!)^3 \le (L^L)^3,$$
with $d! \le d^d \le L^L$. $\square$

**Remark (Formalization).** The bound $(L^L)^3$ is far from sharp. For one row and for the diagram $(2, 1)$ the hook number is the product of the hook lengths (Section 1 and Exercise 1 of Section 8), which is at most $L!$. The source uses only that the constant is explicit and depends on $L$ alone.

### The norm

**Definition.** The squared norm of a complex vector $\xi$ is $\|\xi\|_G^2 = \operatorname{Re}(\xi^* G \xi)$.

Lean: `New.weylNormSq` (Lib/GLn/SchurModule/GramMatrix.lean).

The real part is a formality: $\xi^* G \xi$ is real because $G$ is positive definite (`New.GL.coe_weylNormSq`).

**Lemma.**

1. $\|\xi\|_G^2 \ge 0$.
2. For every numbering $e$ of the rows, the evaluation vector at the permutation array of $e$ has norm $1$.

Lean: `New.weylNormSq_nonneg`, `New.GL.weylNormSq_weylEval_permArray` (Lib/GLn/SchurModule/GramMatrix.lean).

*Proof.* (1) is positive definiteness. (2) The array $y$ is real, so $\overline{\operatorname{ev}_y} = \operatorname{ev}_y$ and $\|\operatorname{ev}_y\|^2_G = \operatorname{ev}_y^{\mathsf T} G \operatorname{ev}_y = K_y(y)$. This is $f$ at the matrix $y^{\mathsf T} y = 1$ in each block, which is $1$. $\square$
