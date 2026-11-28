---
title: Split places and the transfer of Hecke polynomials
lean:
  - Lib/Weil/Unramified/SplitHecke.lean
  - Lib/Weil/Unramified/HeckeTransfer.lean
  - Lib/Weil/Unramified/HeckeGL.lean
  - Lib/General/Combinatorics.lean
decls:
  - New.maxCompactAt
  - New.sphericalAt
  - New.heckeSplit
  - New.mem_sphericalAt_iff
  - New.heckeSplit_star
  - New.heckeSplit_dual
  - New.heckeSplit_adjoint
  - New.heckeSplit_comm
  - New.IsUnitary.le_span_joint_eigenvectors
  - New.heckePolyEval
  - New.heckePolyOp
  - New.HasHeckePolynomial
  - New.hasHeckePolynomial_of_heckeSplit
  - New.exists_heckeSplit_eq_smul
  - New.SiegelWeil.qPochhammer
  - New.SiegelWeil.hasHeckePolynomial_qPochhammer
  - New.SiegelWeil.hasHeckePolynomial_of_apply_eq_smul_det
  - New.AutChar.frobValue
  - New.SiegelWeil.heckePolyOp_pairWeilTarget
  - New.SiegelWeil.hasHeckePolynomial_formLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Split places and the transfer of Hecke polynomials

The source does not use representations of $\mathrm{GL}_N(F)$ alone. It uses automorphic forms on a unitary group $G$ over a totally real field, attached to a CM field $E$. At a finite place $w$ of $E$ that is split, that is, $\bar w \neq w$, the local group of $G$ is a general linear group, and the results of this chapter apply. This section sets up the Hecke operators at split places, proves a spectral theorem for them, and states how Hecke polynomials pass through a theta lift.

**Remark (Formalization).** All results of this section are for split places only. At a place $w = \bar w$ the local group is a unitary group, not $\mathrm{GL}_N$, and the source does not use Hecke operators there in this form.

### Hecke operators at a split place

Let $G_f$ be the finite adelic unitary group of rank $n$, as in [Automorphic forms on unitary groups](/chapter/automorphic-forms/). Let $w$ be a split place. The map that sends $g \in \mathrm{GL}_n(E_w)$ to the element of $G_f$ that is $g$ at $w$ and $1$ off $w$ and $\bar w$ is an embedding (Lean: `New.ofSplitPlace`). Its component at $\bar w$ is determined by $g$, since the element is unitary.

**Definition.** Let $\pi$ be a representation of $G_f$. Let $K_w$ be the subgroup of the standard maximal compact subgroup of $G_f$ of the elements with component $1$ away from $w$ and $\bar w$. A vector is spherical at $w$ if $K_w$ fixes it. The Hecke operator $T_{w,j}$ is the operator $T_j$ of section 4 for the representation $\pi$ composed with the embedding of $\mathrm{GL}_n(E_w)$.

Lean: `New.maxCompactAt`, `New.sphericalAt`, `New.heckeSplit`, `New.mem_sphericalAt_iff` (Lib/Weil/Unramified/SplitHecke.lean).

A vector is spherical at $w$ if and only if it is fixed by $\mathrm{GL}_n(\mathcal{O}_w)$ through the embedding (Lean: `New.mem_sphericalAt_iff`). So all results of sections 2 to 6 apply to $\pi$ composed with the embedding.

The operators at $w$ and at $\bar w$ are related.

**Theorem.** Let $v$ be spherical at the split place $w$.

1. $T_{\bar w,j}\,v$ is the operator at $w$ of the indicator function of the inverse of the double coset of $T_{w,j}$.
2. If $n = i + j$ and $\varpi$ is a uniformiser of $E_w$, then $\pi(\varpi)\,T_{\bar w,i}\,v = T_{w,j}\,v$, where $\varpi$ is the scalar matrix embedded at $w$.
3. Let $B$ be a pairing of $\pi$ with $\pi'$, semilinear in the first variable and invariant under $G_f$, and let $v'$ be spherical at $w$ for $\pi'$. Then $B(T_{w,j}v, v') = B(v, T_{\bar w,j}v')$.

Lean: `New.heckeSplit_star`, `New.heckeSplit_dual`, `New.heckeSplit_adjoint` (Lib/Weil/Unramified/SplitHecke.lean).

*Proof.* The map from $\mathrm{GL}_n(E_{\bar w})$ to $G_f$ and then to the component at $w$ is the conjugate transpose inverse. It carries the double coset of $\operatorname{diag}(\varpi 1_j, 1)$ at $\bar w$ to the inverse of the double coset at $w$, up to the transpose, and the transpose does not change a double coset of $\mathrm{GL}_n(\mathcal{O}_w)$. This is part 1. Part 2 follows from part 1 and the duality of lattices of section 4 (Lean: `New.heckeGL_dual`). For part 3, the adjoint of the operator of a function $f$ for an invariant pairing is the operator of $g \mapsto f(g^{-1})$, and part 1 identifies it. $\square$

**Theorem.** Let $w$ and $u$ be split places and let $v$ be spherical at both. Then $T_{w,i}\,T_{u,j}\,v = T_{u,j}\,T_{w,i}\,v$.

Lean: `New.heckeSplit_comm` (Lib/Weil/Unramified/SplitHecke.lean).

*Proof.* If $u = w$, this is the commutativity of the spherical Hecke algebra, which follows from Gelfand's trick: the transpose is an anti-automorphism that fixes each double coset. If $u = \bar w$, part 1 of the previous theorem moves $T_{\bar w,j}$ to an operator at $w$ of a bi-invariant function, and Gelfand's trick applies again. Otherwise the elements supported at $u$ and $\bar u$ commute with those supported at $w$ and $\bar w$. $\square$

### A spectral theorem

**Theorem (Joint eigenvectors).** Let $\pi$ be unitary for a form $B$, and let $S$ be a set of split places that is stable under $w \mapsto \bar w$. Let $U$ be a subspace of finite dimension that is spherical at each $w \in S$ and stable under each $T_{w,j}$ with $w \in S$. Then $U$ is spanned by its vectors that are eigenvectors of all the $T_{w,j}$, $w \in S$, at the same time.

Lean: `New.IsUnitary.le_span_joint_eigenvectors` (Lib/Weil/Unramified/SplitHecke.lean).

*Proof.* The operators $T_{\bar w,j}$, $w \in S$, commute on $U$. Suppose the span of the joint eigenvectors is a proper subspace. Then the commuting operators $T_{\bar w,j}$ have a joint generalised eigenspace that is not contained in the span. Let $x$ be in this space, with $(T_{\bar w,j} - c)^k x = 0$. The operator $T_{\bar w,j}$ is adjoint to $T_{w,j}$ on $U$ and commutes with it. For such a pair, a vector killed by a power of $T' - c$ is killed by $T' - c$ and by $T - \bar c$. The reason is that $y = (T - \bar c)\,x$ is killed by $T' - c$ by induction on $k$, and so $B(y, y) = B(x, (T' - c)\,y) = 0$. So $x$ is a joint eigenvector of the $T_{w,j}$ with eigenvalues $\bar c$, a contradiction. $\square$

The operators $T_{w,j}$ need not be normal on $V$ as a whole. The proof uses only the finite-dimensional space $U$ and the adjoint relation on it.

### The Hecke polynomial at a split place

**Definition.** For a sequence $t_0, t_1, \ldots$ and $X \in \mathbb{C}$ put
$$H_w(t)(X) = \sum_{i=0}^{n} (-X)^i\, q^{i(i-1)/2}\, t_i,$$
where $q$ is the norm of $w$. The Hecke polynomial operator $H_w(X)$ is this sum with $t_i = T_{w,i}$. A vector $y$ has Hecke polynomial $p : \mathbb{C} \to \mathbb{C}$ at $w$ if $y$ is spherical at $w$ and $H_w(X)\,y = p(X)\,y$ for all $X \in \mathbb{C}$.

Lean: `New.heckePolyEval`, `New.heckePolyOp`, `New.HasHeckePolynomial` (Lib/Weil/Unramified/SplitHecke.lean).

The sum $H_w(t)$ is the reversed form of the Hecke polynomial $P$ of section 4: $H_w(t)(X) = X^n P(1/X)$. So if $P = \prod_i (X - y_i)$, then $H_w(t)(X) = \prod_i (1 - y_i X)$. This is the form of a local $L$-factor. The roots of $P$ are the inverses of the zeros of $H_w(t)$.

**Remark (Formalization).** The eigenvalue $p$ in `New.HasHeckePolynomial` is a function $\mathbb{C} \to \mathbb{C}$, not a polynomial. The operator $H_w(X)$ is defined pointwise for each complex number $X$. Since $H_w(X)\,y$ is a polynomial in $X$ of degree at most $n$ with vector coefficients, the function $p$ is then a polynomial function when $y \neq 0$.

**Theorem.** Let $y$ be spherical at $w$ with $T_{w,i}\,y = t_i\,y$ for all $i$. Then $y$ has the Hecke polynomial $H_w(t)$ at $w$. Conversely, for each function $p$ there is a sequence $t$ such that every $y$ with Hecke polynomial $p$ at $w$ has $T_{w,i}\,y = t_i\,y$ for all $i$.

Lean: `New.hasHeckePolynomial_of_heckeSplit`, `New.exists_heckeSplit_eq_smul` (Lib/Weil/Unramified/SplitHecke.lean).

*Proof.* The first part is a computation term by term. For the second part, the operators that act by one scalar on all vectors with Hecke polynomial $p$ form a subspace of the endomorphisms. It contains $H_w(X)$ for each $X$. Since $H_w(X)$ is a polynomial in $X$ of degree $n$ whose coefficients are multiples of the $T_{w,i}$, the values at $n + 1$ distinct points determine the coefficients by interpolation. So the subspace contains each $T_{w,i}$, for $i \leq n$. For $i > n$ the double coset is empty and $T_{w,i} = 0$. $\square$

**Example (Fixed vectors).** Let $v$ be fixed by all of $G_f$. Then $v$ is spherical at each split $w$, and its Hecke polynomial is
$$X \mapsto \prod_{l<n}(1 - q^l X).$$
Lean: `New.SiegelWeil.qPochhammer`, `New.SiegelWeil.hasHeckePolynomial_qPochhammer`, `New.SiegelWeil.hasHeckePolynomial_of_apply_eq_smul_det` (Lib/Weil/Unramified/HeckeTransfer.lean).

This agrees with section 4: the trivial representation of $\mathrm{GL}_n(E_w)$ has the roots $1, q, \ldots, q^{n-1}$. The proof in Lean is a direct count. The operator $H_w(X)$ is a sum over the subspaces $U$ of $k^n$, with the coefficient $(-X)^{\dim U}q^{\dim U(\dim U - 1)/2}$, and the $q$-binomial theorem evaluates the sum.

More generally, if $G_f$ acts on $v$ by $g \mapsto \chi(\det g)$ for a character $\chi$ of $[\mathrm{U}(1)]$ whose base change is unramified at $w$, with value $c$ at the uniformiser, then the Hecke polynomial of $v$ is $X \mapsto \prod_{l<n}(1 - q^l c X)$ (Lean: `New.SiegelWeil.hasHeckePolynomial_of_apply_eq_smul_det`).

### The transfer through a theta lift

Let $S$ and $T$ be Hermitian spaces of ranks $n$ and $n + k$, and let $a$ and $b$ be characters of $[\mathrm{U}(1)]$ whose base changes are unramified at the split place $w$. For a character $c$ and a rank $N$, let
$$\alpha_N(c) = \chi(\varpi_w)\, q^{N/2}, \qquad \chi(x) = c(x/\bar x)\,\upsilon(x)^{-N},$$
where $\upsilon$ is the splitting character of the Weil data (Lean: `New.AutChar.frobValue`). Write $\alpha = \alpha_n(a)$ and $\beta = \alpha_{n+k}(b)$.

**Theorem (Transfer on the vacuum).** Let $f$ be a Schwartz function on $\mathrm{Hom}(S, T)$ that is fixed by the averaging over integral vectors at $w$ and $\bar w$. Then $f$ is spherical at $w$ for both unitary groups in the twisted Weil representation, and
$$H^T_w(X/\alpha)\, f = \prod_{l<k}(1 - q^l X)\cdot H^S_{\bar w}\bigl(q^k X/\beta\bigr)\, f$$
for every $X \in \mathbb{C}$.

Lean: `New.SiegelWeil.heckePolyOp_pairWeilTarget`, `New.AutChar.frobValue` (Lib/Weil/Unramified/HeckeTransfer.lean).

The proof counts lattices. On the vacuum, the Hecke operators of $S$ and of $T$ become sums over the subspaces of the kernels of an integral matrix and of its transpose modulo $w$, and the $q$-binomial theorem relates the two sums. The source names the unramified theta correspondence as the known form of this result, with references to Howe (Corvallis 1979), Rallis (Amer. J. Math. 104, 1982) and Kudla (Invent. Math. 83, 1986).

**Theorem (Hecke polynomial of a theta lift).** In this setting, let $y$ be an automorphic form on the unitary group of $S$ with Hecke polynomial $p$ at $w$, and let $f$ also be an arrow for the theta kernel (Lean: `New.IsArrow`), so that the theta lift by $f$ is equivariant. Theta lifts are the subject of [Theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). Then the theta lift of $y$ by $f$ has the Hecke polynomial
$$X \mapsto \prod_{l<k}(1 - q^l \alpha X)\cdot p\bigl(q^k \alpha \beta^{-1} X\bigr)$$
at $w$.

Lean: `New.SiegelWeil.hasHeckePolynomial_formLift` (Lib/Weil/Unramified/HeckeTransfer.lean).

In terms of roots: if $p(X) = \prod_i (1 - y_i X)$, the lift has the roots $q^l\alpha$ for $l < k$ and the roots $q^k\alpha\beta^{-1} y_i$. The first $k$ roots form a chain of length $k$ in the sense of section 6.
