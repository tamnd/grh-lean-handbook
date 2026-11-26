---
title: Norms, invariance and orthogonality
lean:
  - Lib/GLn/SchurModule/SchurNorm.lean
  - Lib/GLn/SchurModule/GramMatrix.lean
  - Lib/GLn/SchurModule/SchurOrthogonality.lean
  - Lib/GLn/SchurModule/Polarisation.lean
  - Lib/General/LinearAlgebra/MatrixNormBounds.lean
decls:
  - New.GL.schur_conjTranspose_weylGram_schur
  - New.weylNormSq_schur_le
  - New.gramForm
  - New.conjWeylMatrix
  - New.conjWeylRep
  - New.gramForm_conjWeylRep
  - New.GL.comulMatrix
  - New.GL.comulMatrix_mulVec_weylEval
  - New.GL.vecMul_comulMatrix_eq_iff
  - New.GL.comulMatrix_isometry
  - New.GL.comulMatrix_equivariant
  - New.GL.hasLeftInv_comulMatrix
  - New.weylNormSq_le_mul_of_toPoly_eq
  - New.sqrt_weylNormSq_le_of_dual
  - New.sqrt_weylNormSq_sum_le
  - New.decreasingPosition
  - New.highestVector
  - New.hcParameter
  - New.IsHCParam
  - New.gramForm_highestVector_self
  - New.weightMinors
  - New.weylRep_coeff_eq_prod_weightMinors
  - New.schur_orthogonality
  - New.span_conjWeylRep_eq_top
  - New.pairedDetProd
  - New.exists_pairedDetProd_eq_sum_unitary
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Norms, invariance and orthogonality

Section 5 gave the Gram matrix $G$ and the squared norm $\|\xi\|^2 = \operatorname{Re}(\xi^* G \xi)$ on complex coordinate vectors. This section proves the properties of this norm that the source uses. The Schur matrix $S(z)$ of an arbitrary complex matrix $z$ has an explicit norm bound. The norm is submultiplicative under products of polynomials. The form is invariant under the compact group, and Schur orthogonality holds for it. The diagonal matrix coefficient of a highest vector is a product of principal minors.

### The adjoint of a Schur matrix

The first step is a formula for the adjoint of $S(z)$ for the form $G$. Fix two families of index types $n$ and $n'$, and a weight $\kappa$ that fits both ranks (the condition `New.FitsRanks` of Section 4).

**Lemma (adjoint formula).** Let $w$ and $z$ be families of complex $n' \times n$ matrices. Let $G$ and $G'$ be the Gram matrices of $\kappa$ for $n$ and for $n'$. Then
$$S(w)^* \, G' \, S(z) = \Big( \prod_\tau \det(w_\tau^* z_\tau)^{d_\tau} \Big) \cdot G \, S(w^* z),$$
where $d_\tau$ is the number of columns of $\kappa_\tau$ of the full height, as in Section 4.

Lean: `New.GL.schur_conjTranspose_weylGram_schur` (Lib/GLn/SchurModule/SchurNorm.lean).

*Proof.* Both sides are matrices of coefficients of a kernel. By Section 5 the entries of $G$ are the coefficients of the kernel $f(y^{\mathsf T} x)$ in the products $b_i(x) b_j(y)$. Substitution of $z$ in $x$ and of the conjugate of $w$ in $y$ gives $f((\bar w y)^{\mathsf T} z x) = f(y^{\mathsf T} w^* z x)$. On the left this is the substitution applied to the kernel, so its coefficients are the entries of $S(w)^* G' S(z)$. On the right it is the kernel for $n$ after the substitution of $w^* z$, and the full columns give the factor of determinants. Compare the coefficients. $\square$

### The norm bound for Schur matrices

The bound of the source is in terms of numbers that control the eigenvalues of $z_\tau^* z_\tau$.

**Theorem (norm bound).** Let $z$ be a family of complex $n'_\tau \times n_\tau$ matrices, and let $\kappa$ fit the ranks. There are numbers $\rho_\tau(i) \ge 0$, for $i < |n_\tau|$, such that:

1. $\sum_{i < |n_\tau|} \rho_\tau(i) \le \sum_{a, b} |z_\tau(a, b)|^2$ for every $\tau$;
2. for every complex vector $\xi$,
$$\|S(z)\xi\|^2 \le \Big( \prod_\tau \prod_{i < |n_\tau|} \rho_\tau(i)^{\mu_\tau(i)} \Big) \|\xi\|^2,$$
where $\mu_\tau(i)$ is the diagram weight `New.diagramWeight` of $\kappa$ at $(\tau, i)$ for the ranks of $n'$, that is, the number of boxes of the diagram in row $i$.

Lean: `New.weylNormSq_schur_le` (Lib/GLn/SchurModule/SchurNorm.lean).

In the proof the numbers $\rho_\tau(i)$ are the eigenvalues of $z_\tau^* z_\tau$ in decreasing order. Then item 1 is the statement that the trace of $z_\tau^* z_\tau$ is the sum of the squares of the entries. Item 2 bounds $\|S(z)\|^2$ by the value of the highest weight at these eigenvalues. The statement does not say that the $\rho_\tau(i)$ are the eigenvalues.

*Proof.* By the spectral theorem write $z_\tau^* z_\tau = U_\tau D_\tau U_\tau^*$, with $U_\tau$ unitary and $D_\tau$ diagonal with entries $d_\tau(a) \ge 0$. The sum of the $d_\tau(a)$ is the trace of $z_\tau^* z_\tau$, which is $\sum_{a,b} |z_\tau(a,b)|^2$.

Choose an enumeration of the $d_\tau(a)$ such that for every set $A$ of $h$ indices, $\prod_{a \in A} d_\tau(a) \le \rho_\tau(0) \cdots \rho_\tau(h - 1)$. The lemma `exists_enum_prod_le` of the file gives this: take the values in decreasing order. Then item 1 holds.

By the adjoint formula, $\|S(z)\xi\|^2 = c \cdot \eta^* G S(D) \eta$, where $\eta = S(U^*)\xi$ and $c = \prod_\tau \det(z_\tau^* z_\tau)^{d_\tau}$ is the factor of the full columns. Since $U$ is unitary, $\|\eta\| = \|\xi\|$, again by the adjoint formula.

The lemma `New.dotProduct_weylGram_schur_diagonal_le` bounds $\eta^* G S(D) \eta$. It uses the tensor model of Section 4. The form $G$ is $F^{\mathsf T} F$, and on tensors a diagonal matrix acts diagonally in the orthonormal basis of minors. The basis tensor of a column of height $h$ has distinct rows, so its eigenvalue is a product of $h$ distinct entries $d_\tau(a)$. By the choice of $\rho$ this is at most $\rho_\tau(0) \cdots \rho_\tau(h - 1)$. So $\eta^* G S(D) \eta \le N \|\eta\|^2$, where $N = \prod_\tau \prod_h (\rho_\tau(0) \cdots \rho_\tau(h-1))^{\kappa_\tau(h)}$.

The factor $c$ is a product of determinants of full size. Each one is a product of all $d_\tau(a)$, so it is at most $\rho_\tau(0) \cdots \rho_\tau(|n_\tau| - 1)$. The lemma `New.prod_pow_diagramWeight_eq` rewrites the product of these bounds with $N$ as $\prod_\tau \prod_i \rho_\tau(i)^{\mu_\tau(i)}$: a box in row $i$ belongs to a column of height more than $i$. This gives item 2. $\square$

**Remark (Formalization).** The numbers $\rho_\tau(i)$ come from an existential statement, and the source uses them through `choose`. They are the sorted eigenvalues in the proof, but the statement does not say so. Every use in the source needs only items 1 and 2. In particular a user can bound each $\rho_\tau(i)$ by $\sum_{a,b} |z_\tau(a,b)|^2$, and so get a bound for $\|S(z)\|^2$ by a power of the Frobenius norm of $z$ with exponent the number of boxes.

The source cites the standard theory of the norm on Weyl modules: Jantzen, *Representations of Algebraic Groups*, 2nd ed., 2003, Part II, and Goodman and Wallach, *Symmetry, Representations, and Invariants*, 2009, Chapter 5.

### The invariant form

The *Gram form* `New.gramForm` is $(\xi, \eta) \mapsto \xi^* G \eta$, conjugate linear in $\xi$. The compact group acts on coordinate vectors through `New.conjWeylMatrix` and `New.conjWeylRep`: an element $x = (x_\tau)$ of $\prod_\tau U(n_\tau)$ acts by the Weyl representation of weight $(\kappa, e)$ at the entrywise conjugate $\bar x$. In the source, $U(n)$ is the group `New.USign 1` of matrices that preserve the Hermitian form of signature given by the signs $1$.

Lean: `New.gramForm`, `New.conjWeylMatrix`, `New.conjWeylRep` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

**Lemma.** For $x \in \prod_\tau U(n_\tau)$ and all $\xi, \eta$, the Gram form of $x\xi$ and $x\eta$ equals the Gram form of $\xi$ and $\eta$.

Lean: `New.gramForm_conjWeylRep` (Lib/GLn/SchurModule/SchurNorm.lean).

*Proof.* Put $g_\tau = \bar x_\tau$. Then $g_\tau^* g_\tau = 1$ and $|\det g_\tau| = 1$, so the determinant factor $\prod_\tau \det(g_\tau)^{e_\tau}$ has absolute value $1$. By the adjoint formula with $w = z = g$, $S(g)^* G S(g) = G S(g^* g) = G S(1) = G$, by `New.schur_one`. $\square$

**Remark (Formalization).** The action is through the conjugate $\bar x$ and not through $x$. The reason is the convention of the source for the coefficient system of automorphic forms, in which the place $\tau$ acts through its complex conjugate (compare `New.stdSpace_weightRep_apply`). For the invariance of the form this makes no difference, since $\bar x$ is unitary when $x$ is.

### Products of polynomials

The second property is submultiplicativity. It uses a coproduct matrix, which is the integer matrix of the multiplication of polynomials.

**Definition.** Let $\kappa$ and $\kappa'$ be two weights. The matrix `New.GL.comulMatrix` $C$ has a row for each pair $(p, q)$ of basis indices of $\kappa$ and $\kappa'$. Row $(p, q)$ holds the integer coordinates of the product $b_p b_q$ in the basis of the weight $\kappa + \kappa'$.

Lean: `New.GL.comulMatrix` (Lib/GLn/SchurModule/GramMatrix.lean).

The product $b_p b_q$ is a semi-invariant of weight $\kappa + \kappa'$, so these coordinates exist. The source reads them off with `Function.invFun` of the injective map of Section 3, which gives the zero vector outside its range. Here the argument is always in the range.

**Lemma.** The coproduct matrix has these properties.

1. $C \operatorname{ev}_y = \operatorname{ev}_y \otimes \operatorname{ev}_y$ for every array $y$, where $\operatorname{ev}_y$ is the evaluation vector `New.weylEval` of Section 4 (`New.GL.comulMatrix_mulVec_weylEval`);
2. for coordinate vectors $\alpha$ and $\beta$ of weights $\kappa$ and $\kappa'$, $(\alpha \otimes \beta) C = x$ if and only if $\big(\sum_p \alpha_p b_p\big)\big(\sum_q \beta_q b'_q\big) = \sum_k x_k b''_k$, where $b$, $b'$, $b''$ are the bases of $\kappa$, $\kappa'$, $\kappa + \kappa'$ (`New.GL.vecMul_comulMatrix_eq_iff`);
3. $C^{\mathsf T} (G_\kappa \otimes G_{\kappa'}) C = G_{\kappa + \kappa'}$ (`New.GL.comulMatrix_isometry`);
4. $(S_\kappa(g) \otimes S_{\kappa'}(g)) C = C S_{\kappa + \kappa'}(g)$ (`New.GL.comulMatrix_equivariant`);
5. $C$ has an integer left inverse (`New.GL.hasLeftInv_comulMatrix`).

Item 1 holds over every commutative ring. The other items need an infinite domain.

Lean: `New.GL.comulMatrix_mulVec_weylEval`, `New.GL.vecMul_comulMatrix_eq_iff`, `New.GL.comulMatrix_isometry`, `New.GL.comulMatrix_equivariant`, `New.GL.hasLeftInv_comulMatrix` (Lib/GLn/SchurModule/GramMatrix.lean).

*Proof.* Item 1 is the identity $b_i(y) b_j(y) = \sum_k C_{(i,j), k} b_k(y)$ read through the evaluation vectors. Item 3 holds because the kernel is multiplicative: the kernel of $\kappa + \kappa'$ is the product of the kernels of $\kappa$ and $\kappa'$, as the product of the leading minors is. Compare the coefficients of both sides in the basis products. Item 4 holds because substitution of rows is a ring homomorphism. For item 5, split each tableau of $\kappa + \kappa'$ into its first columns, which form a tableau of $\kappa$, and its last columns, which form a tableau of $\kappa'$. The product of the two minor products is the original one. The infinite domain is needed because the identities are proved through evaluations at all arrays. $\square$

**Theorem (submultiplicativity).** Let $\xi$, $\eta$ and $\zeta$ be complex vectors of weights $\kappa$, $\kappa'$ and $\kappa + \kappa'$. If $\operatorname{toPoly}(\zeta) = \operatorname{toPoly}(\xi) \cdot \operatorname{toPoly}(\eta)$, then $\|\zeta\|^2 \le \|\xi\|^2 \|\eta\|^2$.

Lean: `New.weylNormSq_le_mul_of_toPoly_eq` (Lib/GLn/SchurModule/GramMatrix.lean).

Recall from Section 5 that $\operatorname{toPoly}(\xi) = \sum_i (G\xi)_i b_i$. The map toPoly is injective, so the hypothesis determines $\zeta$.

*Proof.* Let $B = G_\kappa \otimes G_{\kappa'}$ and $v = \xi \otimes \eta$. By item 2 of the lemma the hypothesis says $(G_\kappa \xi \otimes G_{\kappa'} \eta) C = G_{\kappa+\kappa'} \zeta$. The matrix $C$ has integer entries, so $C^* = C^{\mathsf T}$. So the pairing $(C\zeta)^* B v$ is $\zeta^* G_{\kappa+\kappa'} \zeta = \|\zeta\|^2$. By item 3, $(C\zeta)^* B (C\zeta) = \|\zeta\|^2$. Also $v^* B v = \|\xi\|^2 \|\eta\|^2$. The Cauchy-Schwarz inequality for the positive definite form $B$ (`New.GL.posDef_cauchy_schwarz`) gives $\|\zeta\|^4 \le \|\zeta\|^2 \cdot \|\xi\|^2 \|\eta\|^2$. Divide by $\|\zeta\|^2$ if it is not $0$. $\square$

### Duality and the triangle inequality

The file `Lib/General/LinearAlgebra/MatrixNormBounds.lean` gives two general facts. Fix a field automorphism $\sigma$ of $\mathbb C$, which is applied to the coordinates.

**Lemma (duality).** Let $v$ be a complex vector and $C \in \mathbb R$. Assume that $|\sigma(c \cdot v)| \le C$ for every vector $c$ with $|\sigma(c \cdot w)| \le \|\sigma(w)\|$ for all $w$. Then $\|\sigma(v)\| \le C$.

Lean: `New.sqrt_weylNormSq_le_of_dual` (Lib/General/LinearAlgebra/MatrixNormBounds.lean).

*Proof.* Test with $c = \sigma^{-1}\big(N^{-1} \sigma(v)^* G\big)$, with $N = \|\sigma(v)\|$. Cauchy-Schwarz for $G$ shows that $c$ satisfies the hypothesis, and $|\sigma(c \cdot v)| = N$. If $N = 0$ there is nothing to prove. $\square$

**Lemma (triangle inequality).** For a finite family $f_a$ of vectors, $\|\sigma(\sum_a f_a)\| \le \sum_a \|\sigma(f_a)\|$.

Lean: `New.sqrt_weylNormSq_sum_le` (Lib/General/LinearAlgebra/MatrixNormBounds.lean).

*Proof.* Apply duality. For $c$ as in the hypothesis, $|\sigma(c \cdot \sum_a f_a)| \le \sum_a |\sigma(c \cdot f_a)| \le \sum_a \|\sigma(f_a)\|$. $\square$

### Highest vectors and the Harish-Chandra parameter

For an integer vector $l$ on $n$ and an index $i$, the number `New.decreasingPosition` of $i$ is the number of $j$ with $l_j > l_i$. If $l$ is injective, this is a bijection from $n$ to $\{0, \dots, |n| - 1\}$, and it sorts $l$ in decreasing order.

Lean: `New.decreasingPosition` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

**Definition.** For a family $l_\tau$ of integer vectors, the *highest vector* `New.highestVector` is the evaluation vector at the permutation array with entry $1$ in row $a$ of block $\tau$ exactly in column $\operatorname{decreasingPosition}(l_\tau)(a)$, and $0$ elsewhere.

Lean: `New.highestVector` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

**Definition.** The integer `New.hcParameter` at the place $w$ and the position $p$ is
$$2\big(e_w + \mu_w(p)\big) + N - 1 - 2p,$$
where $\mu_w(p) = \sum_{p < h < N} \kappa_w(h)$ is the diagram weight in rank $N$. The predicate `New.IsHCParam` says that each $l_w$ is injective and that each value of $l_w$ is the number `New.hcParameter` for some position $p < |n|$.

Lean: `New.hcParameter`, `New.IsHCParam` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

In the textbook language, $\mu_w + e_w$ is the highest weight at $w$, $\rho = ((N - 1)/2 - p)_p$ is half the sum of the positive roots, and $l_w$ lists twice the Harish-Chandra parameter $\mu + \rho$ in some order. The parameter is strictly decreasing in $p$, so the position of $i$ is its decreasing position.

**Lemma.** If every $l_w$ is injective, the Gram form of the highest vector with itself is $1$.

Lean: `New.gramForm_highestVector_self` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

*Proof.* The highest vector is an evaluation vector at a permutation array. By `New.GL.weylNormSq_weylEval_permArray` of Section 5 these vectors have norm $1$. $\square$

The diagonal coefficient of the representation at such a vector is a product of principal minors. For a complex matrix $g$ and an integer vector $l$, the function `New.weightMinors` is
$$\prod_{t \in \mathbb Z} \frac{\operatorname{pm}(g, \{ i : t \le l_i \})}{\det g \text{ if } t \le 0, \text{ else } 1},$$
where $\operatorname{pm}(g, P)$ is the principal minor of $g$ on the set $P$.

Lean: `New.weightMinors` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

**Remark (Formalization).** The product is a `finprod`, which is $1$ by convention when infinitely many factors differ from $1$. For invertible $g$ this does not happen: for large $t$ the set is empty and the factor is $1$, and for small $t$ the set is everything and the factor is $\det g / \det g = 1$. For a non-invertible $g$ the factors for small $t$ are $0/0 = 0$ in the source convention, so infinitely many factors differ from $1$, and the value is the junk value $1$. The source applies the function only to invertible $g$.

**Theorem (diagonal coefficient).** Let $p_\tau : n_\tau \simeq \{0, \dots, |n_\tau| - 1\}$ be bijections, and let $v$ be the evaluation vector at the permutation array of the $p_\tau$. For $g \in \prod_\tau GL_{n_\tau}(\mathbb C)$,
$$v^{\mathsf T} G \, \rho_{\kappa, e}(g) \, v = \prod_\tau \operatorname{weightMinors}\big(i \mapsto e_\tau + \mu_\tau(p_\tau(i))\big)(g_\tau).$$

Lean: `New.weylRep_coeff_eq_prod_weightMinors` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

*Proof.* The coefficient is the factor $\prod_\tau \det(g_\tau)^{e_\tau}$ times the value of the kernel at $g$ and the permutation array. By Section 5 this is the value of the highest polynomial, the product of the powers $\kappa_\tau(h)$ of the leading $h \times h$ minors, at $g$ read in the orderings $p_\tau$. After transposition the leading $h \times h$ minor is the principal minor of $g_\tau$ on $\{i : p_\tau(i) < h\}$. The right side has the same form by an induction on the heights. $\square$

The form here is the bilinear form $v^{\mathsf T} G w$, without conjugation. The vector $v$ has real entries, so this is also the Hermitian form. The theorem is used in `New/Spanning/Bessel/FillingData.lean`, where the matrix coefficient of the coefficient system enters the archimedean integrals.

### Schur orthogonality

Let $dx$ be the Haar measure of total mass $1$ on $\prod_\tau U(n_\tau)$, and write $\rho$ for `New.conjWeylRep` of weight $(\kappa, e)$. Write $\dim \rho$ for the number of basis indices.

**Theorem (Schur orthogonality).** For every linear form $f$ and all vectors $a$, $b$, $c$,
$$\int f(\rho(x) c) \, \langle a, \rho(x^{-1}) b \rangle \, dx = (\dim \rho)^{-1} \langle a, c \rangle f(b),$$
where $\langle \cdot, \cdot \rangle$ is the Gram form.

Lean: `New.schur_orthogonality` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

This is the orthogonality relation for the matrix coefficients of an irreducible representation of a compact group.

*Proof.* Average the rank one map $v \mapsto \langle a, v \rangle c$ over the group: $B = \int \rho(x) (\langle a, \cdot \rangle c) \rho(x^{-1}) \, dx$. Then $B$ commutes with $\rho(x)$ for every $x$ (`New.exists_intertwining_mean`). For a unitary family $g$ the conjugate $\bar g$ is unitary, and $\rho(\bar g)$ is a unit times $S(g)$. So $B$ commutes with $S(g)$ for every unitary $g$. By Schur's lemma for the unitary group of Section 5 (`New.mem_range_scalar_of_commute_schur`), $B$ is a scalar $z$. The trace of $B$ is the trace of the rank one map, which is $\langle a, c \rangle$, so $z = (\dim \rho)^{-1} \langle a, c \rangle$. Apply $f$ to $B b$. $\square$

**Corollary.** For $v \neq 0$, the translates $\rho(x) v$ with $x \in \prod_\tau U(n_\tau)$ span all coordinate vectors.

Lean: `New.span_conjWeylRep_eq_top` (Lib/GLn/SchurModule/Polarisation.lean).

*Proof.* Assume $w$ is not in the span. Choose a linear form $f$ that kills all translates of $v$ with $f(w) \neq 0$. Apply Schur orthogonality with $a = c = v$ and $b = w$. The left side is $0$. The right side is $(\dim \rho)^{-1} \langle v, v \rangle f(w)$, which is not $0$ because $G$ is positive definite. $\square$

### Polarisation

The last result of the section uses the spanning property. For families of matrices $Y_\tau$ of size $n \times p$ over a $\mathbb C$-algebra $S$ and complex $p \times n$ matrices $\eta_{\tau k}$, the element `New.pairedDetProd` is
$$\prod_\tau \prod_k \det(\eta_{\tau k} Y_\tau).$$

Lean: `New.pairedDetProd` (Lib/GLn/SchurModule/GramMatrix.lean).

**Theorem (polarisation).** Let $|p| < |n|$, and let $\eta_0$ be the $p \times n$ matrix whose row $k$ is the standard basis vector at $r(k)$, for an injective map $r$. For all complex $p \times n$ matrices $\eta_{\tau k}$ there is a finitely supported function $c$ on $\prod_\tau U(n)$ such that, for every $\mathbb C$-algebra $S$ and all $Y$,
$$\prod_\tau \prod_k \det(\eta_{\tau k} Y_\tau) = \sum_u c(u) \prod_\tau \prod_k \det(\eta_0 u_\tau^{\mathsf T} Y_\tau).$$

Lean: `New.exists_pairedDetProd_eq_sum_unitary` (Lib/GLn/SchurModule/Polarisation.lean).

*Proof.* Take $Y$ to be a matrix of variables. Then both sides are semi-invariants, of the weight with $|k|$ columns of height $|p|$ at each $\tau$. Up to the conventions of the action, the term on the right for $u$ is the image of the term for $u = 1$ under $u$. The term for $u = 1$ is a product of minors and is not $0$. By the corollary its translates span the module, which contains the left side. The coefficients $c(u)$ are then independent of $Y$. For a general $S$, substitute $Y$ for the variables. $\square$

The condition $|p| < |n|$ makes the columns of height $|p|$ part of the diagram and not full columns.
