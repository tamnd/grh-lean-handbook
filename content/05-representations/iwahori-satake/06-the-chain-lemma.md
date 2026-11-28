---
title: The unitary chain lemma
lean:
  - Lib/Adelic/Hecke/ClassSums.lean
  - Lib/LocalGL/SphericalChainLemma.lean
decls:
  - New.IsUnitary
  - New.IsUnitary.adjoint_eq_inv
  - New.Patching.HasRootChain
  - New.Patching.partialHecke_hyperplane_count_dual
  - New.Patching.chain_lemma_of_adjoint
  - New.Patching.aeval_cofactor_eq_zero
  - New.Patching.aeval_conj_eq_zero
  - New.Patching.adjoint_aeval_map_starRingEnd
  - New.Patching.chain_lemma
  - New.Patching.le_norm_sq_of_isRoot_of_not_isRoot_mul
  - New.Patching.isRoot_chain_of_norm
  - New.Patching.pairing_aeval_heckeCoset_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The unitary chain lemma

This section proves the main result of the chapter. Let $\rho$ be a smooth unitary representation of $\mathrm{GL}_N(F)$, and let $x \neq 0$ be a spherical eigenvector with Hecke polynomial $P$. The chain lemma says that the roots of $P$ come in chains $c, cq, \ldots, cq^{k-1}$, that the top root of a chain is not small, and that an operator at the level $I_1$ sees only the top root of a chain. The proof uses the partial Hecke sums of section 4 with $r = 1$, an operator $U$ at the level $I_1$ and its adjoint $U'$. It does not use the classification of the unitary dual.

Throughout, $F = E_w$, $q$ is the norm of $w$, $\varpi$ is a uniformiser, $N = n + 1 \geq 1$, and $t_j$ are the Hecke eigenvalues of $x$, so that $P(X) = \sum_{j \leq N} (-1)^j q^{j(j-1)/2} t_j X^{N-j}$.

### Unitary representations

**Definition.** A sesquilinear form $B$ on $V$ makes $\rho$ unitary if $B(x, x)$ is a positive real number for each $x \neq 0$, and $B(\rho(g)x, \rho(g)y) = B(x, y)$ for all $g$, $x$, $y$.

Lean: `New.IsUnitary`, `New.IsUnitary.adjoint_eq_inv` (Lib/Adelic/Hecke/ClassSums.lean).

Then the adjoint of $\rho(g)$ is $\rho(g^{-1})$ (Lean: `New.IsUnitary.adjoint_eq_inv`), and the adjoint of the mean over a compact open subgroup is the same mean.

**Remark (Formalization).** The definition is algebraic. It asks for a positive definite invariant form on $V$ itself. There is no completion to a Hilbert space and no condition of admissibility. Every argument in this section is a computation with finitely many vectors, so a Hilbert space is not needed.

### The operators and their relations

Let $b = \operatorname{diag}(\varpi, 1, \ldots, 1)$ and let $\bar m$ be the mean over $I_1$. Put
$$U = q^n\, \bar m\, \rho(b)\, \bar m, \qquad U' = q^n\, \bar m\, \rho(b^{-1})\, \bar m.$$
By section 4, $U$ is the Hecke operator of the double coset $I_1 b I_1$ on $V^{I_1}$. Since $\rho$ is unitary, $U'$ is the adjoint of $U$ for $B$. Let
$$T_j = T_{1,j}\, x$$
be the partial Hecke sum over the lattices of colength $j$ that contain $e_0$. Then $T_0 = x$, and each $T_j$ is fixed by $I_1$.

The count of hyperplanes of section 4 with $r = 0$ and $\psi = \bar m$ gives
$$U\,T_j = q^j\,(t_{j+1}\,x - T_{j+1}) \quad \text{for all } j.$$
The same count read in the dual representation $g \mapsto \rho((g^{\mathsf{T}})^{-1})$ gives the relations for $U'$.

**Theorem (Dual count).** Let $x$ be fixed by $K$ and let $a = \rho(b)^{-1}$. Then:

1. if $1 + (i + 1 + j) = N$, then $q^{N-1}\,\bar m(a\, T_{1,i+1}x) = q^j\,\bigl(\bar m(a\,T_{0,i+1}x) - T_{1,i}x\bigr)$;
2. $a\,T_{0,N}x = T_{1,N-1}x$;
3. if $T_{0,N}x = 0$, then $x = 0$.

Lean: `New.Patching.partialHecke_hyperplane_count_dual` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* The dual representation turns lattices of colength $j$ into lattices of colength $N - j$, up to the scalar $\varpi$ (Lean: `New.partialHecke_dual`). The count of section 4 in the dual representation, with $\psi = \bar m \circ \rho(\operatorname{diag}(1, \varpi, \ldots, \varpi))$, translates into part 1. The group in the hypothesis of the count is conjugated into $I_1$ by this diagonal matrix. For parts 2 and 3, $x$ is the translate by $\operatorname{diag}(\varpi^{-1}, \ldots, \varpi^{-1})$ of $T_{0,N}x$, since the only lattice of colength $N$ is $\varpi\mathcal{O}^N$, and also the translate by $\operatorname{diag}(1, \varpi^{-1}, \ldots, \varpi^{-1})$ of $T_{1,N-1}x$. $\square$

Since $T_{0,i}x = t_i\,x$, the theorem gives, for $i < n$,
$$U'\,T_{i+1} = q^{n-i-1}\Bigl(\frac{t_{i+1}}{q^n}\, U'x - T_i\Bigr), \qquad U'x = q^n\, t_N^{-1}\, T_n, \qquad U\,T_n = q^n\, t_N\, x,$$
and $t_N \neq 0$ by part 3. The relation for $U$ at $j = n$ then gives $T_N = 0$.

### The linear algebra

The rest of the proof uses only these relations.

**Theorem (Chain lemma, linear form).** Let $B$ be positive definite, and let $U$ and $U'$ be adjoint to each other for $B$. Let $q > 1$, and let $T_0, T_1, \ldots$ be vectors with $T_0 \neq 0$ that satisfy the relations above, with $t_0 = 1$ and $t_N \neq 0$. Let $P$ be the Hecke polynomial of the $t_j$. Then:

1. every root $c$ of $P$ such that $qc$ is not a root has $|c|^2 \geq q^{N-2}$;
2. if $d \neq 0$, $q^k/d$ is a root of $P$, and $P = \prod_{i<k}(dX - q^i) \cdot R$, then $\bar R(U')\,T_0 = 0$, where $\bar R$ is $R$ with complex conjugate coefficients.

Lean: `New.Patching.chain_lemma_of_adjoint` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* Write $x = T_0$, and let $p_m$ be the Hecke polynomial of degree $m$, that is, the sum up to $j = m$. By induction on $m$, with the relation for $U$,
$$p_m(U)\,x = (-1)^m\, q^{m(m-1)/2}\, T_m.$$
Since $P = p_N$ and $T_N = 0$, we get $P(U)x = 0$.

Let $c$ be a root of $P$, write $P = (X - c)\,D$, and put $z = D(U)\,x$. Then $(U - c)z = P(U)x = 0$, so $U z = c z$. The relations for $U'$ give, by a computation with the polynomials $p_m$,
$$c\, U'z = \frac{P(qc)}{q^N}\, U'x + q^{N-2}\, z.$$
Pair this with $U'x$. Since $B(U'x, U'y) = B(x, U U'x)$ and $U U' x = q^{2n} x$, and since $B(U'x, z) = B(x, Uz) = c\,B(x, z)$, one gets
$$c\, B(x, z)\,(q^N - 1) = P(qc)\, B(x, x).$$
Now pair the same formula with $z$. The left side gives $\bar c\,B(U'z, z) = \bar c\,B(z, Uz) = |c|^2 B(z, z)$. With the last identity this gives
$$\bigl(|c|^2 - q^{N-2}\bigr)\, B(z, z) = \frac{|P(qc)|^2\, B(x, x)}{q^N\,(q^N - 1)}.$$

For part 1, let $P(qc) \neq 0$. Then $B(x, z) \neq 0$, so $z \neq 0$ and $B(z, z) > 0$. The right side is positive, so $|c|^2 > q^{N-2}$.

For part 2, first let $c \neq 0$ be a root with $P(qc) = 0$. Then $U'z = c^{-1}q^{N-2}\, z$, and $B(x, z) = 0$. So $B(G(U)x, z) = 0$ for every polynomial $G$, by induction on $G$, since $B(Ux', z) = B(x', U'z)$ is a multiple of $B(x', z)$. In particular $B(z, z) = 0$, and $z = D(U)x = 0$. So the factor $X - c$ can be cancelled from $P(U)x = 0$ when $c \neq 0$ and $qc$ are both roots. Two lemmas finish the proof. $\square$

**Lemma (Cancelling a chain).** Let $P(U)y = 0$, and assume that $(P/(X - c))(U)y = 0$ for every root $c \neq 0$ of $P$ such that $qc$ is also a root. Let $P = \prod_{i<k}(dX - q^i) \cdot R$ with $d \neq 0$, $q > 1$, and let $q^k/d$ be a root of $P$. Then $R(U)\,y = 0$.

Lean: `New.Patching.aeval_cofactor_eq_zero` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* Induction on $k$. For $k = 0$ it is the hypothesis $P(U)y = 0$. For the step, the induction hypothesis for the factorisation with $k$ factors and the cofactor $(dX - q^k)R$ says that $U$ acts on $R(U)y$ by $q^k/d$. The roots $q^k/d$ and $q^{k+1}/d$ are both roots of $P$, so the hypothesis cancels the factor $X - q^k/d$. What remains is $Q(U)\,R(U)\,y = 0$ with $Q = \prod_{i<k}(dX - q^i)$. Since $U$ acts on $R(U)y$ by $q^k/d$, this is $Q(q^k/d)\,R(U)y = 0$, and $Q(q^k/d) \neq 0$ because $q^k \neq q^i$ for $i < k$. $\square$

**Lemma (Conjugation).** Let $R(U)$ kill every $T_j$, and let $U'$ keep the span of $T_0, \ldots, T_n$ by the relations above. Then $\bar R(U')\,T_0 = 0$.

Lean: `New.Patching.aeval_conj_eq_zero`, `New.Patching.adjoint_aeval_map_starRingEnd` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* By the relations, $G(U')\,T_j$ lies in the span of $T_0, \ldots, T_n$ for every polynomial $G$, so $R(U)$ kills it. The adjoint of $R(U)$ is $\bar R(U')$ (Lean: `New.Patching.adjoint_aeval_map_starRingEnd`). So the vector $v = \bar R(U')T_0$ has $B(v, v) = B(T_0, R(U)\,G(U')T_0) = 0$ for $G = \bar R$, and $v = 0$. $\square$

In the proof of the theorem, the first lemma gives $R(U)x = 0$. Since $T_j$ is a multiple of $p_j(U)x$ and $R(U)$ commutes with $p_j(U)$, $R(U)$ kills every $T_j$. The second lemma gives part 2.

### The chain lemma

**Definition.** Let $P$, $e$ be polynomials, $q, d \in \mathbb{C}$ and $t \in \mathbb{N}$. Then $P$ has a root chain of length $t$ at $d$ with cofactor dividing $e$ if
$$P(dX) = (X - 1)(X - q)\cdots(X - q^{t-1})\cdot S \quad \text{for some } S \text{ with } S \mid e.$$

Lean: `New.Patching.HasRootChain` (Lib/LocalGL/SphericalChainLemma.lean).

So the roots $d, dq, \ldots, dq^{t-1}$ of $P$ form a chain.

**Theorem (Chain lemma).** Let $B$ make $\rho$ unitary, let $x \neq 0$ be fixed by $K$ with $T_j x = t_j x$ for all $j$, and let $P$ be its Hecke polynomial. Then:

1. if $P(c) = 0$ and $P(qc) \neq 0$, then $|c|^2 \geq q^N/q^2$;
2. let $d \neq 0$, and let $P$ have a root chain of length $k + 1$ at $d^{-1}$ with cofactor dividing $R$. Let $H$ be the Hecke operator of $I_1 b I_1$, and let $\tilde G(X) = (dX - q^k)\,R(dX)$. Then $B(x, \tilde G(H)\,y) = 0$ for every $y$ fixed by $I_1$.

Lean: `New.Patching.chain_lemma` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* Apply the linear form to $U$, $U'$ and $T_j = T_{1,j}x$, with the relations proved above. Part 1 is part 1 of the linear form. For part 2, write $P(X) = \prod_{i \leq k}(dX - q^i)\cdot S(dX)$ with $S \mid R$, and let $G = (dX - q^k)\,S(dX)$. Then $q^k/d$ is a root of $P$, and $P = \prod_{i<k}(dX - q^i)\cdot G$. Part 2 of the linear form gives $\bar G(U')\,x = 0$. On $V^{I_1}$ the operator $H$ is $U$, and its adjoint is $U'$. The polynomial in the statement is a multiple of $G$, so its value at $H$ is $F(H)\,G(H)$ for a polynomial $F$, and $B(x, F(H)G(H)y) = B(\bar G(U')x, F(H)y) = 0$. $\square$

**Remark (Formalization).** Lean writes the bound $q^{N-2}$ as $q^N / q^2$, to avoid a subtraction of natural numbers when $N = 1$.

The two parts are also stated alone.

**Theorem (Top root of a chain).** In the setting of the chain lemma, if $P(c) = 0$ and $P(qc) \neq 0$, then $|c|^2 \geq q^{N-2}$.

Lean: `New.Patching.le_norm_sq_of_isRoot_of_not_isRoot_mul` (Lib/LocalGL/SphericalChainLemma.lean).

**Theorem (Orthogonality).** In the setting of the chain lemma, if $d \neq 0$ and $P$ has a root chain of length $k + 1$ at $d^{-1}$ with cofactor dividing $R$, then $x$ is orthogonal to $\bigl((dX - q^k)R(dX)\bigr)(H)\,y$ for every $y$ fixed by $I_1$.

Lean: `New.Patching.pairing_aeval_heckeCoset_eq_zero` (Lib/LocalGL/SphericalChainLemma.lean).

The source uses the orthogonality in the argument on congruences, where an Iwahori level eigenform must be compared with a spherical one. See [Auxiliary primes and first-order deformations](/chapter/first-order-deformations/).

### Chains of roots

**Theorem (Chains).** In the setting of the chain lemma, let $P(c) = 0$ and $|c|^2 q^k = q^N$. Then $c, cq, \ldots, cq^{k-1}$ are all roots of $P$.

Lean: `New.Patching.isRoot_chain_of_norm` (Lib/LocalGL/SphericalChainLemma.lean).

The proof uses a symmetry of the roots.

**Lemma (Symmetry).** If $y'$ is a root of $P$ and $\bar y\, y'\, q = q^N$, then $y$ is a root of $P$. So the roots are stable under $y \mapsto q^{N-1}/\bar y$.

Lean: a step in the proof of `New.Patching.isRoot_chain_of_norm` (Lib/LocalGL/SphericalChainLemma.lean).

*Proof.* Let $\zeta = B(\rho(\varpi)x, x)$, where $\varpi$ acts as a scalar matrix. For $d + b = N$, the adjoint of $T_d$ is the Hecke operator of the inverse double coset, which is $\rho(\varpi)^{-1} T_b$ (Lean: `New.heckeGL_dual`). So
$$\overline{t_d}\, B(x, x) = B(T_d x, x) = B(\rho(\varpi)x, T_b x) = t_b\,\zeta.$$
Compare $\overline{P(y)}$ and $P(y')$ term by term, with the term $d$ on one side and the term $N - d$ on the other. With $\bar y\,y'\,q = q^N$ and the identity $\binom{N}{2} + \binom{d}{2} + d = \binom{b}{2} + Nd$, this gives
$$\overline{P(y)}\; B(x, x)\; q^{N(N-1)/2} = (-\bar y)^N\, \zeta\, P(y').$$
Since $B(x, x) \neq 0$, $P(y') = 0$ implies $P(y) = 0$. $\square$

*Proof of the theorem.* Strong induction on $i < k$. Write $k = i + 1 + j$. If $j < i$, then $cq^j$ is a root by induction, and $\overline{cq^i}\cdot cq^j \cdot q = |c|^2 q^{k} = q^N$. So $cq^i$ is a root by the symmetry. Let $i \leq j$. For $i = 0$ the claim is $P(c) = 0$. Let $i = i' + 1$, and suppose that $cq^{i}$ is not a root. By induction $cq^{i'}$ is a root, so the bound on top roots gives $|c|^2 q^{2i'} \geq q^{N-2}$. Multiply by $q^k$ and use $|c|^2 q^k = q^N$: this gives $q^{N+2i'} \geq q^{N - 2 + k}$, so $k \leq 2i' + 2$, that is, $j \leq i'$. This contradicts $i \leq j$. $\square$

The source uses this theorem in the argument on congruences, in the same chapter as the orthogonality.

### Examples

**Example (Trivial representation).** The roots are $1, q, \ldots, q^{N-1}$. The top root $c = q^{N-1}$ has $|c|^2 = q^{2N-2} \geq q^{N-2}$. The root $c = 1$ has $|c|^2 q^N = q^N$, so the theorem on chains with $k = N$ gives the chain $1, q, \ldots, q^{N-1}$. The symmetry sends $q^i$ to $q^{N-1-i}$.

**Example (Tempered representations).** If $y_i = q^{(N-1)/2}\alpha_i$ with $|\alpha_i| = 1$, then $|y_i|^2 = q^{N-1} \geq q^{N-2}$, and the bound holds for every root. The theorem on chains, with $k = 1$, says only that $c$ is a root. The symmetry sends $y_i$ to $q^{(N-1)/2}/\bar\alpha_i = q^{(N-1)/2}\alpha_i$, so it fixes each root.

**Example (Complementary series of $\mathrm{GL}_2$).** Let $N = 2$ and $\alpha = q^{\pm s}$ with $s > 0$ real. The roots are $c_\pm = q^{1/2 \pm s}$. For $s \neq 1/2$, the number $q\,c_-$ is not a root, so the bound applies to $c_-$ and gives $q^{1 - 2s} \geq q^0$, that is, $s \leq 1/2$. The unitary complementary series of $\mathrm{GL}_2$ is the range $0 < s < 1/2$, so the bound is sharp for $N = 2$. At $s = 1/2$ the roots are $1$ and $q$, the roots of the trivial representation, and they form a chain. The symmetry $y \mapsto q/\bar y$ exchanges $c_+$ and $c_-$.

**Remark (Formalization).** The bound of the chain lemma is weaker than what Tadić's classification of the unitary dual gives for $N \geq 3$. The classification describes the unitary unramified representations as products of segments, and for chains of length at least $2$ it gives a lower bound for the top root that grows with the length of the chain. The Lean proof gives only $|c|^2 \geq q^{N-2}$, which is the bound that the source needs.
