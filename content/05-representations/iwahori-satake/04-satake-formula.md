---
title: Satake's formula through partial Hecke sums
lean:
  - Lib/Adelic/Unitary/Defs.lean
  - Lib/Adelic/Hecke/Basic.lean
  - Lib/Weil/Unramified/HeckeGL.lean
  - Lib/LocalGL/Iwahori/HeckeDegrees.lean
  - Lib/GaloisRep/Main/Defs.lean
decls:
  - New.basicDoubleCoset
  - New.heckeGL
  - New.heckeFun
  - New.basicCosetRep
  - New.heckeGL_eq_sum
  - New.heckePoly
  - New.partialCosets
  - New.partialHecke
  - New.partialHecke_zero_eq_heckeGL
  - New.partialHecke_mem_levelSpace
  - New.card_echelonRows_mem_residueKer
  - New.partialHecke_hyperplane_count_of_invariant
  - New.IsExponent.apply_partialHecke
  - New.iwahoriDegree
  - New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul
  - New.heckeCoset_mulSingle_zero_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Satake's formula through partial Hecke sums

This section proves Satake's formula for $\mathrm{GL}_N$ in the language of exponents. The proof does not compute the Satake transform of a Hecke function. It splits each Hecke operator $T_j$ into partial sums over lattices, and it relates the partial sums by a count of hyperplanes. The count turns into the recursion for elementary symmetric functions.

From now on $F = E_w$ is the completion of a number field at a finite place $w$, with residue field $k$ of order $q$, and $\varpi$ is a uniformiser. Let $K = \mathrm{GL}_N(\mathcal{O})$.

### Hecke operators and lattices

**Definition.** For $j \in \mathbb{N}$, let $D_j$ be the set of $g \in \mathrm{GL}_N(F)$ such that $g$ and $\varpi g^{-1}$ are integral and $v(\det g) = \exp(-j)$. The $j$-th Hecke operator is
$$T_j = \sum_{gK \subseteq D_j} \rho(g),$$
the sum over representatives of the cosets $gK$ in $D_j$.

Lean: `New.basicDoubleCoset`, `New.heckeGL`, `New.heckeFun` (Lib/Adelic/Unitary/Defs.lean, Lib/Adelic/Hecke/Basic.lean).

For $j \leq N$ the set $D_j$ is the double coset $K \operatorname{diag}(\varpi 1_j, 1_{N-j}) K$. For $j > N$ it is empty, since $\det g$ has valuation at least that of $\varpi^N$ when $\varpi g^{-1}$ is integral. The coset $gK$ is determined by the lattice $L = g\mathcal{O}^N$. The conditions say $\varpi\mathcal{O}^N \subseteq L \subseteq \mathcal{O}^N$ and $[\mathcal{O}^N : L] = q^j$. So $T_j x$ is a sum over the subspaces $L/\varpi\mathcal{O}^N$ of $k^N$ of codimension $j$.

**Theorem.** Let $x$ be fixed by $K$. Then
$$T_j x = \sum_{U} \rho(\gamma_U^{\mathsf{T}})\, x,$$
where $U$ runs over the subspaces of $k^N$ of dimension $j$, and $\gamma_U \in D_j$ is a chosen element whose reduction modulo $\varpi$ has kernel $U$.

Lean: `New.heckeGL_eq_sum`, `New.basicCosetRep` (Lib/Weil/Unramified/HeckeGL.lean).

*Proof.* The cosets $Kg$ in $D_j$ correspond to the kernels of the reductions of $g$, which are the subspaces of dimension $j$ of $k^N$. Twist $\rho$ by the inverse transpose, which keeps $K$ and $D_j$, to pass from the cosets $Kg$ to the cosets $gK$. On a $K$-fixed vector the choice of representatives does not matter. $\square$

**Remark (Formalization).** The operator `New.heckeFun` of a function $f$ is defined as the sum of $f(g)\rho(g)$ over chosen representatives $g$ of all cosets in $G/K$, as a finite sum in the sense of `finsum`. If infinitely many terms are not zero, the value is $0$ by convention. For the indicator of $D_j$ the number of cosets is finite, so the convention does not occur. The representatives $\gamma_U$ are chosen with `choose` (Lean: `New.basicCosetRep`). The value of $T_j x$ does not depend on the choice, because $x$ is fixed by $K$. The normalisation is that $K$ has volume $1$.

**Definition.** For a sequence $t_0, t_1, \ldots$ the Hecke polynomial of degree $N$ is
$$P(X) = \sum_{j=0}^{N} (-1)^j q^{j(j-1)/2}\, t_j\, X^{N-j}.$$

Lean: `New.heckePoly` (Lib/GaloisRep/Main/Defs.lean).

If $x$ is a spherical eigenvector with $T_j x = t_j x$, then $t_0 = 1$, and $P$ is monic.

### Partial Hecke sums

**Definition.** For $r, j \in \mathbb{N}$ let $D_{r,j}$ be the set of $g \in D_j$ whose lattice $g\mathcal{O}^N$ contains the first $r$ basis vectors $e_0, \ldots, e_{r-1}$. Equivalently, the first $r$ columns of $g^{-1}$ are integral. The partial Hecke sum is
$$T_{r,j} = \sum_{gK \subseteq D_{r,j}} \rho(g).$$

Lean: `New.partialCosets`, `New.partialHecke` (Lib/LocalGL/Iwahori/HeckeDegrees.lean).

Let $x$ be fixed by $K$. Then:

1. $T_{0,j}x = T_j x$, since every lattice contains the empty set of vectors (Lean: `New.partialHecke_zero_eq_heckeGL`).
2. $T_{r,0}x = x$, since the only lattice of colength $0$ is $\mathcal{O}^N$.
3. $T_{N,j+1} = 0$, since a lattice that contains all basis vectors is $\mathcal{O}^N$.
4. $T_{r,j}x$ is fixed by the parahoric subgroup with one block of size $r$ followed by blocks of size $1$: the level function is $i \mapsto i + 1 - r$, cut off at $0$ (Lean: `New.partialHecke_mem_levelSpace`). The reason is that this group keeps the span of $e_0, \ldots, e_{r-1}$ and is contained in $K$.

### The count of hyperplanes

Let $b_r$ be the diagonal matrix with $\varpi$ at the index $r$ and $1$ elsewhere. For a row vector $u$ over $k$ of the form $(0, \ldots, 0, 1, *, \ldots, *)$, with the entry $1$ at the index $r$, there are $q^{N-1-r}$ choices of $u$.

**Lemma.** Let $g \in D_{r,j+1}$. The number of such rows $u$ that lie in the kernel of the transpose of the reduction of $g$ is $0$ if $g \in D_{r+1,j+1}$, and $q^j$ otherwise.

Lean: `New.card_echelonRows_mem_residueKer` (Lib/LocalGL/Iwahori/HeckeDegrees.lean).

*Proof.* The kernel of the transpose of the reduction $\bar g$ has dimension $j + 1$. It is the space of linear forms on $k^N$ that vanish on the image $\bar L$ of $L = g\mathcal{O}^N$. Such a form vanishes at $e_0, \ldots, e_{r-1}$, because these lie in $L$. So its first $r$ entries are $0$. A form of the shape of $u$ is one with value $1$ at $e_r$. If $e_r \in \bar L$ there is none. If not, the forms in the kernel with first $r$ entries $0$ form a space of dimension $j + 1$, the value at $e_r$ is a nonzero linear function on it, and the forms with value $1$ form an affine hyperplane with $q^j$ points. The case $e_r \in \bar L$ is the case $g \in D_{r+1,j+1}$, since $\varpi e_r \in L$ always. $\square$

**Theorem (Count of hyperplanes).** Let $x$ be fixed by $K$, let $r < N$, and let $\psi$ be a linear map that is invariant under every $k \in I_1$ whose off-diagonal entries vanish outside row $r$. Then
$$q^{N-1-r}\, \psi\bigl(\rho(b_r)\, T_{r+1,j}\, x\bigr) = \psi\bigl(q^j\,(T_{r,j+1}x - T_{r+1,j+1}x)\bigr).$$

Lean: `New.partialHecke_hyperplane_count_of_invariant` (Lib/LocalGL/Iwahori/HeckeDegrees.lean).

*Proof.* For each row $u$ as above, let $n_u \in I_1$ be the matrix whose row $r$ lifts $u$ and whose other rows are those of the identity. By the invariance of $\psi$,
$$q^{N-1-r}\,\psi\bigl(\rho(b_r)y\bigr) = \sum_u \psi\bigl(\rho(n_u^{-1}b_r)\,y\bigr)$$
for every $y$. Apply this to $y = T_{r+1,j}x$, which is a sum of $\rho(h)x$ over the cosets $hK$ in $D_{r+1,j}$. The products $n_u^{-1}b_r h$ lie in $D_{r,j+1}$. Conversely, a coset $gK$ in $D_{r,j+1}$ occurs once for each $u$ that kills the reduction of $g$, in the sense of the lemma. By the lemma it occurs $q^j$ times if $g \notin D_{r+1,j+1}$, and not at all if $g \in D_{r+1,j+1}$. So the sum is $q^j$ times the sum of $\psi(\rho(g)x)$ over $D_{r,j+1} \setminus D_{r+1,j+1}$, which is the right side. $\square$

The library also has the form `New.partialHecke_hyperplane_count`, with the invariance hypothesis on $k^{-1}$. Section 6 uses a second count, the same identity read in the dual representation $g \mapsto \rho((g^{\mathsf{T}})^{-1})$.

### Satake's formula

**Theorem (Satake's formula, in stages).** Let $x$ be fixed by $K$, let $\theta = (\theta_0, \ldots, \theta_{N-1})$ be a family of characters of $F^\times$, and let $l$ be an exponent of $\rho$ for $\xi_\theta$. Put $y_i = \theta_i(\varpi)$. Then for $r \leq N$ and every $j$,
$$l(T_{r,j}\,x) = \frac{e_j(y_r, y_{r+1}, \ldots, y_{N-1})}{q^{j(j-1)/2}}\; l(x).$$
For $r = 0$ this is $l(T_j x) = e_j(y_0, \ldots, y_{N-1})\, q^{-j(j-1)/2}\, l(x)$.

Lean: `New.IsExponent.apply_partialHecke`, `New.partialHecke_zero_eq_heckeGL`, `New.partialHecke_mem_levelSpace` (Lib/LocalGL/Iwahori/HeckeDegrees.lean).

*Proof.* Descending induction on $r$, from $r = N$. For $r = N$ both sides are $l(x)$ if $j = 0$, by item 2, and $0$ if $j > 0$, by item 3 and $e_j(\varnothing) = 0$. Let $r < N$ and assume the formula for $r + 1$ and all $j$. For $j = 0$ both sides are $l(x)$.

First, the vector $T_{r+1,j}x$ is fixed by the parahoric with a first block of size $r + 1$. The lemma on monomial translates of section 3 applies to it with $\sigma = 1$ and $t = b_r$. The only pairs $b < a$ with $v(t_b) > v(t_a)$ are $a = r$ and $b < r$, and these lie in the first block. So
$$l\bigl(\rho(b_r)\,T_{r+1,j}x\bigr) = \xi_\theta(b_r)\, l(T_{r+1,j}x) = \frac{y_r}{q^{N-1-r}}\, l(T_{r+1,j}x),$$
since $\xi_\theta(b_r) = \theta_r(\varpi)\,|\varpi|^{N-1-r}$.

Second, $l$ is invariant under $I_1$, so the count of hyperplanes applies with $\psi = l$. With the first step it gives
$$y_r\, l(T_{r+1,j}x) = q^j\bigl(l(T_{r,j+1}x) - l(T_{r+1,j+1}x)\bigr).$$
So $l(T_{r,j+1}x) = l(T_{r+1,j+1}x) + y_r q^{-j}\, l(T_{r+1,j}x)$. By the induction hypothesis the right side is
$$\frac{e_{j+1}(y_{r+1}, \ldots)}{q^{(j+1)j/2}}\, l(x) + \frac{y_r\, e_j(y_{r+1}, \ldots)}{q^{j}\, q^{j(j-1)/2}}\, l(x).$$
Since $(j+1)j/2 = j(j-1)/2 + j$ and $e_{j+1}(y_r, y_{r+1}, \ldots) = e_{j+1}(y_{r+1}, \ldots) + y_r\, e_j(y_{r+1}, \ldots)$, this is the formula for $r$ and $j + 1$. $\square$

Suppose now that $x$ is a spherical eigenvector, $T_j x = t_j x$, and that $l(x) \neq 0$. Then $t_j = e_j(y)\,q^{-j(j-1)/2}$ for every $j$. So the Hecke polynomial is
$$P(X) = \sum_{j=0}^{N} (-1)^j e_j(y)\, X^{N-j} = \prod_{i=0}^{N-1} (X - \theta_i(\varpi)).$$
The roots of $P$ are the numbers $\theta_i(\varpi)$. The source uses this in the comparison with Galois representations: the theorem `New.IsIwahoriEigen.exists_hasHeckePolyAt` passes from an Iwahori eigenform with unramified sorted $\theta$ to a spherical eigenform with Hecke polynomial $\prod_i (X - \theta_i(\varpi))$, with the results of this section and the next.

**Example.** Let $\rho$ be trivial. Section 2 found the exponent $l = \mathrm{id}$ with $y_i = q^{N-1-i}$. The formula gives
$$t_j = \frac{e_j(1, q, \ldots, q^{N-1})}{q^{j(j-1)/2}}.$$
By the $q$-binomial theorem $e_j(1, q, \ldots, q^{N-1}) = q^{j(j-1)/2}\binom{N}{j}_q$. So $t_j = \binom{N}{j}_q$, the number of subspaces of codimension $j$ of $k^N$, as it must be for the trivial representation.

### The degree of an Iwahori double coset

The operators $U_t$ of section 2 are means, not sums over cosets. The Hecke operator of the double coset $I_1 t I_1$ differs from $U_t$ by the number of cosets.

**Theorem.** Let $t$ be dominant and let $x$ be fixed by $I_1$. The Hecke operator of the indicator of $I_1 t I_1$, for the group $I_1$, sends $x$ to
$$\deg(t)\, \bar m\bigl(\rho(t)x\bigr), \qquad \deg(t) = \prod_{i<j} \left|\frac{t_j}{t_i}\right|.$$
The number $\deg(t)$ is the number of cosets in $I_1 t I_1 / I_1$.

Lean: `New.iwahoriDegree`, `New.heckeFun_iwahoriDoubleCoset_eq_iwahoriDegree_smul`, `New.heckeCoset_mulSingle_zero_eq` (Lib/LocalGL/Iwahori/HeckeDegrees.lean).

*Proof.* The cosets in $I_1 t I_1 / I_1$ are those of $r t$, where $r$ runs over the upper unitriangular matrices whose entry $(i, j)$, for $i < j$, runs over representatives of $\mathcal{O} / (t_i/t_j)\mathcal{O}$. There are $|t_j / t_i|$ choices for the entry $(i, j)$. Each $\rho(rt)x$ has the same mean over $I_1$ as $\rho(t)x$, and the sum of the means is the mean of the sum. $\square$

**Example.** For $t = \operatorname{diag}(\varpi, 1, \ldots, 1)$ only the pairs $(0, j)$ with $j > 0$ contribute, each with the factor $|\varpi^{-1}| = q$. So the Hecke operator of $I_1 t I_1$ is $q^{N-1}\,\bar m \circ \rho(t)$ on $V^{I_1}$ (Lean: `New.heckeCoset_mulSingle_zero_eq`). Section 6 uses this operator.
