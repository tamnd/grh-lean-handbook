---
title: The pro-p Iwahori subgroup and the operators U_t
lean:
  - Lib/LocalGL/Iwahori/ParahoricStructure.lean
decls:
  - New.proIwahori
  - New.blockParahoric
  - New.dominantTorus
  - New.exists_iwasawa_bruhat
  - New.exists_unipotent_conj_mem_proIwahori
  - New.compactMean_diagGL_compactMean_diagGL
  - New.iwahoriHeckeHom
  - New.IsExponent
  - New.IsIwahoriEigen
  - New.normAbsChar
  - New.torusChar
  - New.exists_inv_mul_mul_map_eq_diagGL_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The pro-p Iwahori subgroup and the operators U_t

This section defines the compact subgroups and the operators of the chapter. The central object is the pro-$p$ Iwahori subgroup $I_1$. The operators $U_t = \bar m \circ \rho(t)$, where $\bar m$ is the mean over $I_1$, form a commutative monoid indexed by the dominant diagonal matrices. The linear forms that are eigenforms of all $U_t$ at once are the exponents. They take the place of the Jacquet module.

### Parahoric subgroups

Let $F$, $\mathcal{O}$, $\mathfrak{p}$, $k$ and $q$ be as in section 1. Reduction modulo $\mathfrak{p}$ is a homomorphism $\mathrm{GL}_N(\mathcal{O}) \to \mathrm{GL}_N(k)$. The preimage of a subgroup of $\mathrm{GL}_N(k)$ is an open compact subgroup of $\mathrm{GL}_N(F)$.

**Definition.** The pro-$p$ Iwahori subgroup $I_1$ is the set of $g \in \mathrm{GL}_N(\mathcal{O})$ whose reduction is upper triangular with $1$ on the diagonal. In terms of the valuation: all entries are integral, $v(g_{ij}) < 1$ for $j < i$, and $v(g_{ii} - 1) < 1$.

Lean: `New.proIwahori` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

The name comes from the fact that $I_1$ is a pro-$p$ group, where $p$ is the characteristic of $k$. The Iwahori subgroup $I$ is the larger group of the $g \in \mathrm{GL}_N(\mathcal{O})$ whose reduction is upper triangular. The quotient $I / I_1$ is the group of diagonal matrices over $k$, of order $(q - 1)^N$.

**Definition.** Let $b$ be a function from the indices to $\mathbb{N}$. The parahoric subgroup $P_b$ is the set of $g \in \mathrm{GL}_N(\mathcal{O})$ with $v(g_{ij}) < 1$ whenever $b(j) < b(i)$.

Lean: `New.blockParahoric` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

The reduction of an element of $P_b$ is block upper triangular for the blocks on which $b$ is constant, if $b$ does not decrease. Three cases occur in the chapter, with indices $0, \ldots, N - 1$. For $b = \min(N, \cdot)$, that is $b(i) = i$, the group $P_b$ is the Iwahori subgroup $I$. For $b = \min(1, \cdot)$ it is the group whose first column is $0$ below the diagonal modulo $\mathfrak{p}$, the stabiliser of the line through the first basis vector. For $b = 0$ it is $K = \mathrm{GL}_N(\mathcal{O})$. In general $b = \min(m, \cdot)$ gives a chain
$$I = P_{\min(N, \cdot)} \subseteq P_{\min(N - 1, \cdot)} \subseteq \cdots \subseteq P_{\min(1, \cdot)} \subseteq P_{\min(0, \cdot)} = K.$$
Section 5 descends this chain.

### Dominant elements and the decomposition of Iwasawa and Bruhat

**Definition.** A diagonal element $t = (t_0, \ldots, t_{N-1})$ of $(F^\times)^N$ is dominant if $v(t_i) \leq v(t_j)$ for $i \leq j$. The dominant elements form a submonoid.

Lean: `New.dominantTorus` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

With $v(\varpi) = \exp(-1)$, the element $t = \operatorname{diag}(\varpi^{a_0}, \ldots, \varpi^{a_{N-1}})$ is dominant if and only if $a_0 \geq a_1 \geq \cdots \geq a_{N-1}$. For example $\operatorname{diag}(\varpi, 1, \ldots, 1)$ is dominant. If $t$ is dominant, then conjugation $g \mapsto t g t^{-1}$ multiplies the entry $(i, j)$ by $t_i / t_j$. For $i < j$ this factor is integral. So $t$ keeps the upper unitriangular part of $I_1$, and $t^{-1}$ keeps the lower triangular part.

**Theorem (Iwasawa and Bruhat).** For every $g \in \mathrm{GL}_N(F)$ there is an upper unitriangular $u$ over $F$ with the following two properties.

1. There are a diagonal $t$ and a permutation matrix $\sigma$ with $(t\sigma)^{-1} u^{-1} g \in I_1$. So $g = u t \sigma k$ with $k \in I_1$.
2. If $g \in I_1$, then $u \in I_1$ and $u^{-1} g$ is lower triangular.

Lean: `New.exists_iwasawa_bruhat` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

*Proof.* Reduce the rows of $g$ from the last row upwards. For each row $i$ the proof chooses a pivot column $p(i)$: the first column where the entry of the row has the largest valuation. Then it subtracts multiples of row $i$ from the rows above it, so that the column $p(i)$ becomes $0$ above row $i$. These operations multiply $g$ on the left by an upper unitriangular matrix. Call the result $m = u^{-1} g$. Each column $p(i)$ is $0$ above row $i$ and not $0$ in row $i$, so the pivot columns are distinct and $p$ is a permutation. Let $t_i = m_{i, p(i)}$. Divide row $i$ of $m$ by $t_i$ and move it to the place $p(i)$. This gives $(t\sigma)^{-1} m$ for a permutation matrix $\sigma$. Row $p(i)$ of the result has $1$ in column $p(i)$, entries of valuation less than $1$ to the left of column $p(i)$, and integral entries to the right. So the result is integral, it is upper unitriangular modulo $\mathfrak{p}$, and its determinant is a unit. It lies in $I_1$. This proves 1.

For 2, let $g \in I_1$. The row operations subtract integral multiples of a row from the rows above it, so they keep $I_1$, and $m \in I_1$. In row $i$ of $m$ the diagonal entry is a unit, the entries to its left lie in $\mathfrak{p}$, and the entries to its right are integral. So the pivot of row $i$ is the diagonal entry, and $m$ is $0$ above the diagonal. So $u^{-1} g = m$ is lower triangular, and $u = g m^{-1} \in I_1$. $\square$

**Remark (Formalization).** The Lean theorem is an existence statement. It does not say that the double coset $I_1 t \sigma I_1$ determines $t$ and $\sigma$ up to units, and it does not give the disjoint union over the extended affine Weyl group. The chapter uses only part 2, the Iwahori factorisation with the same $u$. The proof chooses the pivots, so $u$ is not unique.

### The operators U_t

Let $\rho$ be a smooth representation of $\mathrm{GL}_N(F)$ and let $\bar m$ be the mean over $I_1$. For dominant $t$ put $U_t = \bar m \circ \rho(\operatorname{diag} t)$ on the space $V^{I_1}$ of $I_1$-fixed vectors.

**Theorem (Product formula).** Let $t$ and $t'$ be dominant, and let $x$ be fixed by $I_1$. Then
$$\bar m\bigl(\rho(t)\, \bar m(\rho(t') x)\bigr) = \bar m\bigl(\rho(tt') x\bigr).$$

Lean: `New.compactMean_diagGL_compactMean_diagGL`, `New.exists_unipotent_conj_mem_proIwahori` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

*Proof.* The left side is the mean over $k \in I_1$ of $\bar m(\rho(t)\rho(k)\rho(t')x)$. It is enough to show that every $k \in I_1$ is a product $k = u k'$ such that $t u t^{-1} \in I_1$ and $k'$ fixes $\rho(t')x$. Then
$$\rho(t)\rho(k)\rho(t')x = \rho(t u t^{-1})\, \rho(tt')\, x,$$
and the outer mean removes the factor $\rho(tut^{-1})$.

By part 2 of the decomposition there is an upper unitriangular $u \in I_1$ such that $k' = u^{-1}k$ is lower triangular. It lies in $I_1$. Since $t$ is dominant, $tut^{-1}$ is upper unitriangular with integral entries, so it lies in $I_1$. Since $t'$ is dominant, $t'^{-1}k't'$ is lower triangular and lies in $I_1$, so it fixes $x$. Then $\rho(k')\rho(t')x = \rho(t')\rho(t'^{-1}k't')x = \rho(t')x$. $\square$

The Lean proof finds $u$ with `New.exists_unipotent_conj_mem_proIwahori`. The theorem says that $t \mapsto U_t$ is a homomorphism of monoids.

**Theorem.** The map $t \mapsto U_t$ is a monoid homomorphism from the dominant diagonal elements to the endomorphisms of $V^{I_1}$.

Lean: `New.iwahoriHeckeHom` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

*Proof.* The product formula gives $U_t U_{t'} = U_{tt'}$ on $V^{I_1}$. For $t = 1$ the operator is $\bar m$, which is the identity on $V^{I_1}$. $\square$

The monoid of dominant elements is commutative. So all $U_t$ commute. This is the analogue, at the level $I_1$, of the commutative part of the Iwahori-Hecke algebra of Iwahori and Matsumoto.

### Exponents and eigenvectors

Let $\xi$ be a character of the diagonal torus $(F^\times)^N$ with values in $\mathbb{C}^\times$.

**Definition.** A linear form $l : V \to \mathbb{C}$ is an exponent of $\rho$ for $\xi$ if
$$l\bigl(\rho(t)\, \bar m(x)\bigr) = \xi(t)\, l(x)$$
for every dominant $t$ and every $x \in V$.

Lean: `New.IsExponent` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

The single equation holds two facts. For $t = 1$ it says $l(\bar m(x)) = l(x)$. So $l$ factors through the mean and is invariant under $I_1$. For $x \in V^{I_1}$ it says $l(\rho(t)x) = \xi(t) l(x)$. So the restriction of $l$ to $V^{I_1}$ is an eigenform of the transposes of all $U_t$, with eigenvalue $\xi(t)$.

**Definition.** A vector $x$ is an Iwahori eigenvector for $\xi$ if $x \neq 0$, $x \in V^{I_1}$, and $U_t x = \xi(t) x$ for every dominant $t$.

Lean: `New.IsIwahoriEigen` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

The characters of the chapter have a normalised form. Let $|\cdot|$ be the normalised absolute value, with $|\varpi| = q^{-1}$ (Lean: `New.normAbsChar`). For a family $\theta = (\theta_0, \ldots, \theta_{N-1})$ of characters of $F^\times$ put
$$\xi_\theta(t) = \prod_{i=0}^{N-1} \theta_i(t_i)\, |t_i|^{N-1-i}.$$

Lean: `New.torusChar`, `New.normAbsChar` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

The map $\theta \mapsto \xi_\theta$ is a bijection onto the characters of the torus. The factor $|t_i|^{N-1-i}$ is a shift by the half sum of positive roots, up to a central character: $\prod_i |t_i|^{N-1-i} = \delta(t)^{1/2} |\det t|^{(N-1)/2}$, where $\delta$ is the modulus of the upper triangular Borel subgroup. With this shift the Hecke polynomial has the roots $\theta_i(\varpi)$ with no further factor. The trivial representation, for example, has the exponent $l = \mathrm{id}$ with $\xi = 1$. Then $\theta_i = |\cdot|^{-(N-1-i)}$ and $\theta_i(\varpi) = q^{N-1-i}$. These are the roots $1, q, \ldots, q^{N-1}$ of section 1.

**Remark (Formalization).** Classically, the exponents of $\rho$ are the characters of the torus that occur in the Jacquet module of $\rho$ for the upper triangular Borel subgroup. The Lean library does not define the Jacquet module. It uses the definition above, which needs only the mean over $I_1$. This choice has a cost. A statement about the Jacquet module, for example that its dimension is finite, becomes a hypothesis on the space of forms. Section 5 shows where such a hypothesis occurs.

### Twisted conjugacy

One more result of the file is used outside this chapter, in the trace formula for Shimura varieties and in base change of Iwahori eigenforms (Volume 8).

**Theorem (Twisted conjugacy).** Let $\sigma$ be a continuous endomorphism of $F$ that keeps $v$ and acts surjectively on $\mathrm{GL}_N(F)$, and let $t$ be diagonal with $v(t_i)$ strictly increasing in $i$. Then for every $g \in I_1 t I_1$ there are $k \in I_1$ and a diagonal $d \in I_1$ with $k^{-1} g\, \sigma(k) = td$.

Lean: `New.exists_inv_mul_mul_map_eq_diagGL_mul` (Lib/LocalGL/Iwahori/ParahoricStructure.lean).

*Proof.* Put $X(k) = t^{-1} k^{-1} g \sigma(k)$ and $H_j = t^{-j} I_1 t^j$. For each finite range of $j$ some $k \in I_1$ has $X(k) \in H_j$ for all $j$ in the range. The proof finds such a $k$ by successive approximation, with the strict increase of $v(t_i)$. Since $I_1$ is compact, a cluster point of these $k$ has $X(k)$ in every $H_j$. The intersection of all $H_j$, for $j \in \mathbb{Z}$, consists of diagonal matrices in $I_1$. $\square$

The source cites Görtz, Haines, Kottwitz and Reuman, *Compositio Math.* 146 (2010), Theorem 1.1.5, for this statement. For $\sigma$ the identity it says that every element of $I_1 t I_1$ is $I_1$-conjugate to an element of $t$ times the diagonal part of $I_1$.
