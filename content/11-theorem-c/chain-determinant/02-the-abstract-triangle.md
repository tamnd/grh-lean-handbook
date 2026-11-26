---
title: The abstract triangle
lean:
  - New/Determinant/Chain/TriangleNorms.lean
decls:
  - New.Exchange.SquareCommutes
  - New.Exchange.SquareAdjoint
  - New.Exchange.IsTriangle
  - New.Exchange.HasSquareModuli
  - New.Exchange.weightedChain
  - New.Exchange.weightedChain_succ_apply
  - New.Exchange.ChainCommutes
  - New.Exchange.ChainAdjoint
  - New.Exchange.ChainCommutes.succ
  - New.Exchange.ChainAdjoint.succ
  - New.Exchange.chainCommutes_zero
  - New.Exchange.IsTriangle.exists_chainCommutes
  - New.Exchange.IsTriangle.exists_chainAdjoint
  - New.Exchange.HasSquareModuli.exists_chainCommutes
  - New.Exchange.IsTriangle.exists_chainCommutes_and_chainAdjoint
  - New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero
  - New.Exchange.IsTriangle.ne_zero_of_chainCommutes
  - New.Exchange.IsTriangle.inner_weightedChain_succ
  - New.Exchange.IsTriangle.exists_inner_weightedChain_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The abstract triangle

This section contains no theta lifts. It proves three results on a triangle of inner product spaces with arrows that commute up to scalars. Chains along a row are injective. The scalars of the chain relations have no zero. The Gram form of a chain is a product of the scalars of the squares, times the Gram form of the first arrows. Section 5 shows that the theta lifts form such a triangle.

Inner products are linear in the second argument and conjugate linear in the first, as in Mathlib. All statements hold for each value of a parameter $t$ in a set $I$. In the application $t$ is an $m$-fold twist. We write the dependence on $t$ only where it matters.

### The data of a triangle

The data are complex inner product spaces $F_{i,n}$ for $i, n \in \mathbb{N}$ and three families of maps:

- arrows $a_{i,n} \colon F_{i,n} \to F_{i,n+1}$ along the row $i$;
- descents $d_{i,n} \colon F_{i,n+1} \to F_{i+1,n}$ from the row $i$ to the row $i + 1$;
- isometries $j_i \colon V \to F_{i,0}$ from one fixed inner product space $V$.

There are also weights $w_n = w_t(n)$, natural numbers that are not $0$. A descent goes down one row and removes one step. The spaces $F_{i,n+1}$ and $F_{i+1,n}$ have the same index sum $i + n + 1$. The weighted chain of row $i$ is the composite of the first arrows of the row, each times its weight.

**Definition (Weighted chain).** The $n$-chain $X_{i,n} \colon F_{i,0} \to F_{i,n}$ of row $i$ is the identity for $n = 0$, and $X_{i,n+1} = w_n\,a_{i,n} \circ X_{i,n}$.

Lean: `New.Exchange.weightedChain` (New/Determinant/Chain/TriangleNorms.lean).

**Lemma (One more arrow).** For $y \in F_{i,0}$, $X_{i,n+1}\,y = w_n\,a_{i,n}(X_{i,n}\,y)$.

Lean: `New.Exchange.weightedChain_succ_apply` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* This is the definition. $\square$

### Squares

The square at $(i, n)$ has the corners $F_{i,n+1}$, $F_{i+1,n}$, $F_{i,n+2}$ and $F_{i+1,n+1}$. Its two paths from $F_{i,n+1}$ to $F_{i+1,n+1}$ are $a_{i+1,n} \circ d_{i,n}$ and $d_{i,n+1} \circ a_{i,n+1}$.

**Definition (A square commutes up to $\beta$).** Let $\beta$ be a complex function of $t$. The square at $(i, n)$ commutes up to $\beta$ if for every $t$ and every $y \in F_{i,n+1}$
$$w_n\,a_{i+1,n}(d_{i,n}\,y) = \frac{w_{n+2}}{\overline{\beta(t)}}\,d_{i,n+1}(a_{i,n+1}\,y).$$

Lean: `New.Exchange.SquareCommutes` (New/Determinant/Chain/TriangleNorms.lean).

**Definition (Adjoint law of a square).** Let $\kappa$ be a complex function of $t$. The square at $(i, n)$ obeys the adjoint law with $\kappa$ if every $z \in F_{i,n+2}$ has a vector $x \in F_{i,n+1}$ with
$$\langle a_{i,n+1}\,y, z\rangle = \langle y, x\rangle \quad (y \in F_{i,n+1}), \qquad \langle d_{i,n}\,x, y'\rangle = \kappa(t)\,\langle d_{i,n+1}\,z, a_{i+1,n}\,y'\rangle \quad (y' \in F_{i+1,n}).$$

Lean: `New.Exchange.SquareAdjoint` (New/Determinant/Chain/TriangleNorms.lean).

The vector $x$ is the value at $z$ of the adjoint of $a_{i,n+1}$. The spaces of forms in the application are finite dimensional, but the definition does not need this. It asks only for the adjoint vector at each $z$. In words, the adjoint law says $d_{i,n}\,a_{i,n+1}^* = \kappa\,a_{i+1,n}^*\,d_{i,n+1}$.

**Remark (Formalization).** In Lean $x/0 = 0$. So where $\beta(t) = 0$, the commutation law says only $w_n\,a(d\,y) = 0$, and it relates the two paths in no other way. The source never assumes $\beta \neq 0$. It proves $\beta \neq 0$ for the chain relations below, from injectivity.

**Definition (Triangle).** The data form a triangle of size $m$ if they have four properties.

1. For $i + (n + 1) < m$ the square at $(i, n)$ commutes up to some $\beta$.
2. For $i < m$, $z \in F_{i,1}$ and $y \in V$, $\langle z, a_{i,0}(j_i\,y)\rangle = \langle d_{i,0}\,z, j_{i+1}\,y\rangle$.
3. For $i < m$ and $y \in V$, $d_{i,0}(a_{i,0}(j_i\,y))$ is in the image of $j_{i+1}$.
4. For $i < m$ and $y \in V$, if $d_{i,0}(a_{i,0}(j_i\,y)) = 0$, then $y = 0$.

Lean: `New.Exchange.IsTriangle` (New/Determinant/Chain/TriangleNorms.lean).

Property 2 says that the first arrow of each row is adjoint to the first descent on the copies of $V$. Properties 3 and 4 say that $d \circ a$ maps the copy $j_i(V)$ injectively into the copy $j_{i+1}(V)$.

For the Gram forms we also need the sizes of the constants. Let $M(c, f)$ be a relation between complex functions $c$ and real functions $f$ of $t$. Read it as "$c$ has modulus $f$". Let $L_{r,k}$ be real functions of $t$.

**Definition (Moduli of the squares).** The triangle has square moduli $L$ for $M$ if:

1. $M(1, 1)$;
2. $M(c, f)$ and $M(c', f')$ imply $M(cc', ff')$;
3. for $i + (n+1) < m$ the square at $(i, n)$ commutes up to some $\beta$ with $M(\beta, L_{i+1,\,i+n+2})$;
4. for $i + (n+1) < m$ the square at $(i, n)$ obeys the adjoint law with some $\kappa$ with $M(\kappa, 1)$.

Lean: `New.Exchange.HasSquareModuli` (New/Determinant/Chain/TriangleNorms.lean).

The square at $(i, n)$ removes the block $i + 1$ and adds the block $i + n + 2$. The index $L_{i+1,\,i+n+2}$ records these two blocks. In Section 5, $M(c, f)$ is "$|c|^2$ is a constant times a power of $\mathrm{Nm}\,Q$ times $f^2$", and $L_{r,k}$ is the quotient ratio $\rho_{rk}$.

### Chain relations

The squares of a row combine to a relation for a whole chain.

**Definition (Chain commutation).** The chain relation at $(i, n)$ holds with $\beta$ if for every $t$ and $y \in F_{i,0}$
$$X_{i+1,n}\big(d_{i,0}(a_{i,0}\,y)\big) = \frac{w_{n+1}}{w_1\,w_0\,\overline{\beta(t)}}\,d_{i,n}\big(X_{i,n+1}\,y\big).$$

Lean: `New.Exchange.ChainCommutes` (New/Determinant/Chain/TriangleNorms.lean).

**Definition (Chain adjoint law).** The chain adjoint law at $(i, n)$ holds with $\kappa$ if for every $t$, $y \in V$ and $z \in F_{i,n+1}$
$$\big\langle z, a_{i,n}\big(X_{i,n}(j_i\,y)\big)\big\rangle = \kappa(t)\,\big\langle d_{i,n}\,z, X_{i+1,n}(j_{i+1}\,y)\big\rangle.$$

Lean: `New.Exchange.ChainAdjoint` (New/Determinant/Chain/TriangleNorms.lean).

**Lemma (The empty chain).** The chain relation at $(i, 0)$ holds with $\beta = 1$.

Lean: `New.Exchange.chainCommutes_zero` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* The left side is $d(a\,y)$. On the right, $X_{i,1}\,y = w_0\,a\,y$, and $\frac{w_1}{w_1 w_0}\,w_0 = 1$, since the weights are not $0$. $\square$

**Lemma (A chain relation grows by a square).** If the chain relation at $(i, n)$ holds with $\beta$ and the square at $(i, n)$ commutes up to $\beta'$, then the chain relation at $(i, n+1)$ holds with $\beta\beta'$.

Lean: `New.Exchange.ChainCommutes.succ` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Fix $t$ and $y$. Put $Y = X_{i,n+1}\,y$ and $c = w_{n+1}/(w_1 w_0 \bar\beta)$. By the lemma on one more arrow and the chain relation,
$$X_{i+1,n+1}(d\,a\,y) = w_n\,a_{i+1,n}\big(X_{i+1,n}(d\,a\,y)\big) = c\,w_n\,a_{i+1,n}(d_{i,n}\,Y).$$
The square turns this into $c\,(w_{n+2}/\bar\beta')\,d_{i,n+1}(a_{i,n+1}\,Y)$. Again by the lemma on one more arrow, $a_{i,n+1}\,Y = w_{n+1}^{-1}\,X_{i,n+2}\,y$. So the scalar in front of $d_{i,n+1}(X_{i,n+2}\,y)$ is
$$\frac{w_{n+1}}{w_1 w_0 \bar\beta}\cdot\frac{w_{n+2}}{\bar\beta'}\cdot\frac{1}{w_{n+1}} = \frac{w_{n+2}}{w_1 w_0\,\overline{\beta\beta'}}.$$
This is the claim. $\square$

The identity of scalars holds in Lean also where $\beta$ or $\beta'$ is $0$, since $(uv)^{-1} = u^{-1}v^{-1}$ for all $u$, $v$ when $0^{-1} = 0$.

**Lemma (A chain adjoint law grows by a square).** If the chain adjoint law at $(i, n)$ holds with $\kappa$ and the square at $(i, n)$ obeys the adjoint law with $\kappa'$, then the chain adjoint law at $(i, n+1)$ holds with $\kappa\kappa'$.

Lean: `New.Exchange.ChainAdjoint.succ` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Fix $t$, $y$ and $z \in F_{i,n+2}$. Let $x$ be the adjoint vector of $z$ from the adjoint law of the square. Put $X = X_{i,n}(j_i\,y)$ and $Y = X_{i+1,n}(j_{i+1}\,y)$. Then
$$\langle z, a_{i,n+1}(w_n\,a_{i,n}X)\rangle = w_n\,\langle x, a_{i,n}X\rangle = w_n\,\kappa\,\langle d_{i,n}\,x, Y\rangle = w_n\,\kappa\kappa'\,\langle d_{i,n+1}\,z, a_{i+1,n}\,Y\rangle.$$
The first step is the defining property of $x$, read with the conjugate symmetry of the inner product. The second is the chain adjoint law at $(i, n)$, and the third is the adjoint law of the square. The last term is $\kappa\kappa'\,\langle d\,z, X_{i+1,n+1}(j_{i+1}\,y)\rangle$, by the lemma on one more arrow. $\square$

**Proposition (Chain relations exist).** Let the data form a triangle of size $m$, and let $i + n < m$.

1. The chain relation at $(i, n)$ holds with some $\beta$.
2. If the triangle has square moduli $L$, then $\beta$ can be chosen with $M\big(\beta, \prod_{i+1 < k \leq i+1+n} L_{i+1,k}\big)$, and the chain adjoint law at $(i, n)$ holds with some $\kappa$ with $M(\kappa, 1)$.

Lean: `New.Exchange.IsTriangle.exists_chainCommutes`, `New.Exchange.HasSquareModuli.exists_chainCommutes`, `New.Exchange.IsTriangle.exists_chainAdjoint` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Induction on $n$. For $n = 0$ take $\beta = 1$ by the lemma on the empty chain, with $M(1, 1)$ and the empty product $1$. Take $\kappa = 1$: the chain adjoint law at $(i, 0)$ is property 2 of the triangle, since $X_{i,0}$ and $X_{i+1,0}$ are identities. For $n + 1$ with $i + n + 1 < m$, the hypothesis of induction gives $\beta$ and $\kappa$ at $(i, n)$. The square at $(i, n)$ exists since $i + (n + 1) < m$. It commutes up to some $\beta'$, with $M(\beta', L_{i+1,\,i+1+n+1})$ in the second case, and it obeys the adjoint law with some $\kappa'$ of modulus $1$. The two growth lemmas give $\beta\beta'$ and $\kappa\kappa'$. The moduli multiply, and the product over $i + 1 < k \leq i + 1 + n$ gains the factor $k = i + n + 2$. $\square$

**Corollary (Both laws together).** For $i + n < m$ there are $\beta$ and $\kappa$ such that the chain relation at $(i, n)$ holds with $\beta$, and, if the triangle has square moduli $L$, then $M\big(\kappa\beta, \prod_{i+1 < k \leq i+1+n} L_{i+1,k}\big)$ and the chain adjoint law at $(i, n)$ holds with $\kappa$.

Lean: `New.Exchange.IsTriangle.exists_chainCommutes_and_chainAdjoint` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* If the triangle has square moduli, take $\beta$ and $\kappa$ from the proposition and multiply the moduli, $1$ and the product. If not, take $\beta$ from part 1 of the proposition and $\kappa = 1$. The implication then holds since its hypothesis fails. $\square$

**Remark (Formalization).** In the second case of the corollary, $\kappa = 1$ is a junk value. Nothing uses it.

### Chains are injective

**Theorem (Chains are injective).** Let the data form a triangle of size $m$. Let $i + n \leq m$, $y \in V$ and $X_{i,n}(j_i\,y) = 0$. Then $y = 0$.

Lean: `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Induction on $n$, for all $i$ and $y$ at once. For $n = 0$ the chain is the identity, and $j_i$ is an isometry, so it is injective. Let $i + n + 1 \leq m$ and $X_{i,n+1}(j_i\,y) = 0$. Then $i < m$ and $i + n < m$. By property 3 there is $x \in V$ with $j_{i+1}\,x = d_{i,0}(a_{i,0}(j_i\,y))$. The chain relation at $(i, n)$ holds with some $\beta$. So
$$X_{i+1,n}(j_{i+1}\,x) = X_{i+1,n}\big(d(a(j_i\,y))\big) = \frac{w_{n+1}}{w_1 w_0\bar\beta}\,d_{i,n}\big(X_{i,n+1}(j_i\,y)\big) = 0.$$
Since $(i+1) + n \leq m$, the hypothesis of induction gives $x = 0$. So $d(a(j_i\,y)) = j_{i+1}(0) = 0$, and $y = 0$ by property 4. $\square$

The proof uses the chain relation in one direction only. It does not need $\beta \neq 0$.

**Theorem (The chain scalars are not zero).** Let the data form a triangle of size $m$, let $V \neq 0$ and $i + n < m$. If the chain relation at $(i, n)$ holds with $\beta$, then $\beta(t) \neq 0$ for every $t$.

Lean: `New.Exchange.IsTriangle.ne_zero_of_chainCommutes` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Suppose $\beta(t) = 0$. Take $y \neq 0$ in $V$ and $x$ with $j_{i+1}\,x = d(a(j_i\,y))$. The scalar of the chain relation is a quotient by $0$, so it is $0$. So $X_{i+1,n}(j_{i+1}\,x) = 0$. Since $(i+1) + n \leq m$, the theorem on injectivity gives $x = 0$. Then $d(a(j_i\,y)) = 0$, and $y = 0$ by property 4. This is a contradiction. $\square$

**Remark (Formalization).** The proof uses the convention $x/0 = 0$ in an essential way. A relation "up to $\beta$" with $\beta(t) = 0$ forces the chain to vanish, and injectivity excludes this. So the nonvanishing of $\beta$ comes from the injectivity of the chain, not from a computation of $\beta$. The source has the same lemma for one square, `New.Exchange.IsTriangle.ne_zero_of_squareCommutes`, proved from the chain form with $\beta\beta'$. It is not applied anywhere in the source ([constants that may vanish](/chapter/theorem-c-plan/#constants-that-may-vanish), finding F-121). The proof below uses only the chain form.

### The Gram form of a chain

**Lemma (One row down).** Let the data form a triangle of size $m$ and let $i + n < m$. Let the chain relation at $(i, n)$ hold with $\beta$ and the chain adjoint law with $\kappa$. Let $x, x', z \in V$ with $j_{i+1}\,x' = d_{i,0}(a_{i,0}(j_i\,x))$. Then
$$\big\langle X_{i,n+1}(j_i x), X_{i,n+1}(j_i z)\big\rangle = \kappa\beta\,\frac{w_0 w_1 w_n}{w_{n+1}}\,\big\langle X_{i+1,n}(j_{i+1}x'), X_{i+1,n}(j_{i+1}z)\big\rangle.$$

Lean: `New.Exchange.IsTriangle.inner_weightedChain_succ` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* If $V = 0$, then $z = 0$, and both sides are $0$. Let $V \neq 0$. Then $\beta(t) \neq 0$ by the last theorem. Put $X = X_{i,n+1}(j_i x)$, $X' = X_{i+1,n}(j_{i+1}x')$ and $Y = X_{i+1,n}(j_{i+1}z)$. By the choice of $x'$ and the chain relation, $X' = \frac{w_{n+1}}{w_1 w_0\bar\beta}\,d_{i,n}X$. The inner product is conjugate linear in the first argument, so
$$\langle X', Y\rangle = \frac{w_{n+1}}{w_1 w_0\beta}\,\langle d_{i,n}X, Y\rangle.$$
On the other side, the lemma on one more arrow and the chain adjoint law at $(i, n)$, with $X$ in the place of $z$, give
$$\langle X, X_{i,n+1}(j_i z)\rangle = w_n\,\langle X, a_{i,n}X_{i,n}(j_i z)\rangle = w_n\,\kappa\,\langle d_{i,n}X, Y\rangle.$$
Since $\beta \neq 0$ and the weights are not $0$, $\langle d_{i,n}X, Y\rangle = \frac{w_1 w_0\beta}{w_{n+1}}\langle X', Y\rangle$. Insert this. $\square$

Here $\beta \neq 0$ is needed: the step divides by the scalar of the chain relation.

**Theorem (Gram form of a chain).** Let the data form a triangle of size $m$ with square moduli $L$. Let $U$ be a complex vector space, $s \colon U \to V$ a map, $S_{t,i}$ endomorphisms of $U$ and $C_i$ complex functions of $t$ with $M(C_i, 1)$. Suppose that for $i < m$, all $t$, $x \in V$ and $y \in U$
$$w_0\,\big\langle a_{i,0}(j_i\,x), a_{i,0}(j_i\,s(y))\big\rangle = C_i(t)\,\big\langle x, s(S_{t,i}\,y)\big\rangle.$$
Let $i + n = m$. Then there is $\kappa$ with $M\big(\kappa, \prod_{i < r \leq m}\prod_{r < k \leq m} L_{r,k}\big)$ such that for all $t$, $x$, $y$
$$\big\langle X_{i,n}(j_i x), X_{i,n}(j_i\,s(y))\big\rangle = \kappa(t)\,\frac{w_0\,w_1^n}{w_n}\,\big\langle x, s(S_{t,i}S_{t,i+1}\cdots S_{t,m-1}\,y)\big\rangle.$$

Lean: `New.Exchange.IsTriangle.exists_inner_weightedChain_eq` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Induction on $n$, for all $i$ at once. For $n = 0$ we have $i = m$. Take $\kappa = 1$. The double product is empty, the chain is the identity, $j_m$ is an isometry, $w_0 w_1^0/w_0 = 1$ and the product of the $S$ is empty.

Let $i + n + 1 = m$. Then $i + n < m$ and $(i + 1) + n = m$. Put $T = S_{t,i+1}\cdots S_{t,m-1}$. The hypothesis of induction for row $i + 1$ gives $\kappa_1$ with modulus $\prod_{i+1 < r \leq m}\prod_{r < k \leq m} L_{r,k}$ and
$$\big\langle X_{i+1,n}(j_{i+1}x'), X_{i+1,n}(j_{i+1}\,s(y))\big\rangle = \kappa_1\,\frac{w_0 w_1^n}{w_n}\,\langle x', s(T y)\rangle$$
for all $x'$ and $y$. The proposition on chain relations gives $\beta$ with modulus $\prod_{i+1 < k \leq m} L_{i+1,k}$ and $\kappa'$ with modulus $1$ at $(i, n)$. Take $x'$ with $j_{i+1}\,x' = d(a(j_i\,x))$. Then, by the isometry $j_{i+1}$, property 2 of the triangle and the hypothesis on row $i$,
$$w_0\,\langle x', s(Ty)\rangle = w_0\,\big\langle d(a(j_i x)), j_{i+1}\,s(Ty)\big\rangle = w_0\,\big\langle a(j_i x), a(j_i\,s(Ty))\big\rangle = C_i\,\langle x, s(S_{t,i}\,T y)\rangle.$$
The lemma one row down, with $z = s(y)$, and the hypothesis of induction give
$$\big\langle X_{i,n+1}(j_i x), X_{i,n+1}(j_i\,s(y))\big\rangle = \kappa'\beta\,\frac{w_0 w_1 w_n}{w_{n+1}}\cdot\kappa_1\,\frac{w_0 w_1^n}{w_n}\,\langle x', s(Ty)\rangle = \kappa'\beta\kappa_1\,\frac{w_0 w_1^{n+1}}{w_{n+1}}\cdot w_0\langle x', s(Ty)\rangle.$$
Insert the last display. The constant is $\kappa = \kappa'\beta\kappa_1 C_i$. Its modulus is $1 \cdot \prod_{i+1<k\leq m} L_{i+1,k} \cdot \prod_{i+1<r\leq m}\prod_{r<k\leq m} L_{r,k} \cdot 1$, which is the double product over $i < r \leq m$. $\square$

The double product has one factor $L_{r,k}$ for each pair $i < r < k \leq m$. Each row $r$ of the triangle contributes the pairs $(r, k)$, one for each square of that row on the path of the chain. For $i = 0$ the pairs are $0 < r < k \leq m$, which is the index set of the main theorem.

**Example (Two rows).** Let $m = 2$, $i = 0$ and $n = 2$. The theorem has the factors $C_0$ and $C_1$ of the first arrows of rows $0$ and $1$, the factor $\beta$ of the square at $(0, 0)$, and the factor $\kappa'$ of its adjoint law. The double product has the one factor $L_{1,2}$. The weights give $w_0 w_1^2/w_2$.
