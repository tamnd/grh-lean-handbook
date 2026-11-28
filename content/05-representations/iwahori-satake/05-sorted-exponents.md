---
title: Sorted exponents and spherical vectors
lean:
  - Lib/LocalGL/Iwahori/SphericalExponents.lean
  - Lib/LocalGL/Iwahori/SortedExponents.lean
  - Lib/General/LinearAlgebra/Eigenvalues.lean
decls:
  - New.exists_compactMean_and_swap_eq_sum
  - New.IsExponent.apply_swap_diagGL_mulSingle
  - New.IsExponent.eq_zero_of_apply_permGL_swap_eq_zero
  - New.IsExponent.eq_zero_of_eq_zero_on_spherical
  - New.IsExponent.exists_sorted
  - New.IsIwahoriEigen.exists_isExponent
  - New.exists_eigenvector_of_functional
  - New.exists_sorted_isIwahoriEigen_of_diagGL_smul
  - New.exists_sorted_of_detChar
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sorted exponents and spherical vectors

Satake's formula of section 4 starts from a spherical vector $x$ and an exponent $l$ with $l(x) \neq 0$. This section goes in the other direction. It starts from an exponent and finds a spherical vector on which the exponent is not zero. The condition is that the characters are unramified and sorted: $|\theta_i(\varpi)|$ does not increase with $i$. The second half of the section shows how to sort an exponent, and how to get exponents from eigenvectors in a unitary representation.

In this section $F$ is a field with a valuation in $\mathbb{Z}^{\times}_{\geq 0}$ with a zero element, with compact ring of integers, uniformiser $\varpi$ and residue field of order $q$. For $0 \leq m \leq N$ let $P_m$ be the parahoric subgroup with level function $i \mapsto \min(i, m)$. So $P_0 = K$, and $P_N$ is the Iwahori subgroup $I$ of the matrices in $K$ that are upper triangular modulo $\mathfrak{p}$. The group $P_m$ is the set of $g \in K$ with $g_{ij} \in \mathfrak{p}$ when $j < i$ and $j < m$: the first $m$ columns are upper triangular modulo $\mathfrak{p}$. Write $(m\,i)$ for the permutation matrix of the transposition of $m$ and $i$.

### The converse to Satake's formula

**Theorem.** Let $l$ be an exponent of $\rho$ for $\xi_\theta$. Assume that each $\theta_i$ is trivial on $\mathcal{O}^\times$, and that $|\theta_i(\varpi)|$ does not increase with $i$. If $l$ vanishes on the spherical vectors, then $l = 0$.

Lean: `New.IsExponent.eq_zero_of_eq_zero_on_spherical` (Lib/LocalGL/Iwahori/SphericalExponents.lean).

The source calls this a form of one direction of the description of spherical representations in the Langlands-Zelevinsky classification: a nonzero sorted unramified exponent forces a spherical vector. The proof goes down a chain of groups,
$$K = P_0 \supseteq P_1 \supseteq \cdots \supseteq P_N = I,$$
and shows that $l$ vanishes on the means over each $P_m$. At $m = N$ the mean over $I$ does not change $l$, so $l$ vanishes everywhere.

The step from $P_m$ to $P_{m+1}$ needs two lemmas. The first one is a computation of orbit sums.

**Lemma (Orbit sums).** Let $\varphi$ be a linear form that is invariant under $I$, let $m < N$, and let $x$ be fixed by the elements of $P_m$ whose column $m$ lies in $\mathfrak{p}$ off the diagonal. Put
$$a_j = (q - 1)\, q^{j}\, \varphi\bigl(\rho((m\,j))\,x\bigr).$$
Then there are vectors $y$ and $z$ such that

1. $\varphi$ of the mean of $y$ over $P_m$ is $\sum_{j \geq m} a_j$;
2. $z$ is fixed by the elements of $P_m$ whose row $m$ lies in $\mathfrak{p}$ off the diagonal, and $\varphi(\rho((m\,i))\,z) = a_i + (1 - q^{-1}) \sum_{j > i} a_j$ for every $i \geq m$.

Lean: `New.exists_compactMean_and_swap_eq_sum` (Lib/LocalGL/Iwahori/SphericalExponents.lean).

*Proof.* For $p \in P_m$ the vector $\rho(p)x$ depends only on column $m$ of $p$ modulo $\mathfrak{p}$, a column $c$ over $k$. The first $m$ columns of $p$ are upper triangular modulo $\mathfrak{p}$ with units on the diagonal, so $c$ is not in the span of $e_0, \ldots, e_{m-1}$. So the last nonzero entry of $c$ has an index $j \geq m$, and there are $(q - 1)q^{j}$ columns with last nonzero entry at $j$. Let $y$ be the sum of the vectors for all columns $c$, and let $z$ be the sum over the columns with $c_m \neq 0$. A column with last nonzero entry at $j$ is moved to $e_j$ by an element of $I$, and $e_j$ is column $m$ of the swap $(m\,j)$. Since $\varphi$ is invariant under $I$, all columns in one class give the value $\varphi(\rho((m\,j))x)$. This gives part 1. For $z$ the condition $c_m \neq 0$ keeps all columns with $j = m$ and a fraction $1 - q^{-1}$ of the columns with $j > m$. This gives part 2 for $i = m$, and the same count after the swap $(m\,i)$ gives it for $i > m$. $\square$

The second lemma is a case of the lemma on monomial translates. Let $b$ be the diagonal matrix with $\varpi^{-1}$ at $m$ and $1$ elsewhere. If $z$ is fixed by the group of the level function $\min(\cdot, m)$ with the value at $m$ changed to $N$, then
$$l\bigl(\rho((m\,i))\,\rho(b)\,z\bigr) = \theta_i(\varpi)^{-1}\, q^{N-1-i}\, l\bigl(\rho((m\,i))\,z\bigr).$$

Lean: `New.IsExponent.apply_swap_diagGL_mulSingle` (Lib/LocalGL/Iwahori/SphericalExponents.lean).

The reason is that $(m\,i)\, b = \operatorname{diag}(\varpi^{-1} \text{ at } i)\,(m\,i)$, and $\xi_\theta$ of this diagonal matrix is $\theta_i(\varpi)^{-1} q^{N-1-i}$.

**Theorem (Descent step).** Let $l$ be an exponent for $\xi_\theta$ with $|\theta_i(\varpi)|$ not increasing, let $l$ be invariant under $I$, and let $l$ vanish on all means over $P_m$. Let $x$ be fixed by the elements of $P_m$ whose column $m$ lies in $\mathfrak{p}$ off the diagonal. Let $0 \leq j \leq N$. If $l(\rho((m\,i))\,x) = 0$ for all $i \geq j$, then $l(x) = 0$.

Lean: `New.IsExponent.eq_zero_of_apply_permGL_swap_eq_zero` (Lib/LocalGL/Iwahori/SphericalExponents.lean).

*Proof.* Induction on $j$, for all $x$ at the same time. For $j = 0$ the hypothesis at $i = m$ says $l(x) = 0$. Assume the statement for $j$, and let the hypothesis hold for all $i \geq j + 1$. Suppose that $l(x) \neq 0$. Then $m \leq j$, since otherwise $i = m$ is in the range of the hypothesis.

Take $y$ and $z$ from the lemma on orbit sums, with $\varphi = l$. Since $l$ vanishes on the means over $P_m$, the sum $\sum_{i \geq m} a_i$ is $0$. So
$$l(z) = a_m + (1 - q^{-1})(-a_m) = a_m / q.$$
Put
$$x' = \theta_j(\varpi)\,\rho(b)\,z - (q - 1)\,q^{N-1}\, x.$$
Conjugation by $b^{-1}$ carries the group that fixes $x$ into the group that fixes $z$. So $x'$ is fixed by the same group as $x$. For $i > j$ the hypothesis kills all terms $a_{i'}$ with $i' \geq i$, and both parts of $l(\rho((m\,i))x')$ are $0$. For $i = j$ the terms beyond $j$ vanish, so $l(\rho((m\,j))z) = a_j$, and the second lemma gives
$$l(\rho((m\,j))\,x') = q^{N-1-j}\, a_j - (q-1)\,q^{N-1}\, l(\rho((m\,j))\,x) = 0.$$
So the induction hypothesis applies to $x'$, and $l(x') = 0$. With the second lemma at $i = m$ and $l(z) = a_m/q$ this reads
$$\theta_j(\varpi)\,\theta_m(\varpi)^{-1}\, q^{N-1-m}\, \frac{(q-1)\,q^m\, l(x)}{q} = (q-1)\,q^{N-1}\, l(x).$$
Since $l(x) \neq 0$, this gives $\theta_j(\varpi) = q\,\theta_m(\varpi)$. But $m \leq j$, so $|\theta_j(\varpi)| \leq |\theta_m(\varpi)| < q\,|\theta_m(\varpi)|$. This is a contradiction. $\square$

*Proof of the theorem.* First, $l$ is invariant under $I$. An element $k$ of $I$ is a diagonal matrix $d$ of units times an element of $I_1$. Since the $\theta_i$ are trivial on units, $\xi_\theta(d) = 1$, and $l$ is invariant under $d$ by the lemma on integral diagonal matrices of section 3. It is invariant under $I_1$ by definition.

Next, by induction on $m$, $l$ vanishes on the means over $P_m$. For $m = 0$ the mean over $P_0 = K$ is spherical, and $l$ vanishes on it by hypothesis. Let $l$ vanish on the means over $P_m$, and let $x$ be the mean of some vector over $P_{m+1}$. The elements of $P_m$ whose column $m$ lies in $\mathfrak{p}$ off the diagonal lie in $P_{m+1}$, so they fix $x$. The descent step with $j = N$ asks for nothing and gives $l(x) = 0$.

At $m = N$ this says that $l$ vanishes on the means over $I$. Since $l$ is invariant under $I$, $l$ of the mean of $x$ is $l(x)$. So $l = 0$. $\square$

**Example.** The case that the descent step excludes is $\theta_j(\varpi) = q\,\theta_m(\varpi)$ with $m < j$. For $\mathrm{GL}_2$ it is the case $y_1 = q\,y_0$, the roots of the trivial representation in the wrong order. The standard theory says that the Steinberg representation of $\mathrm{GL}_2$, which has no spherical vector, has a normalised Jacquet module equal to $\delta_B^{1/2}$. In the normalisation of this chapter its exponent has $(y_0, y_1) = (1, q)$, which is not sorted. So the hypothesis of the theorem cannot be removed.

The source uses the theorem with Satake's formula in the result `New.IsIwahoriEigen.exists_hasHeckePolyAt`. Let $f$ be an automorphic eigenform of the unitary group that is an Iwahori eigenvector at a split place $w$ with character $\xi_\theta$, where the $\theta_i$ are unramified and $|\theta_i(\varpi)|$ does not increase. Then there is an eigenform $g$ for the same Hecke eigenvalues away from $w$ that is spherical at $w$, with Hecke polynomial $\prod_i (X - \theta_i(\varpi))$ at $w$. The form $g$ is the mean over $K$ of a vector $u$ for which $B(u, \cdot)$ is an exponent. It is not zero by the theorem above, and its eigenvalues come from section 4.

### Sorting an exponent

The theorem needs sorted characters. An exponent can be sorted if the vector on which it is not zero has enough symmetry.

**Theorem (Sorting).** Let $x$ be fixed by $I_1$. Let the integral diagonal matrices act on $x$ by a function $\tau$, and let every permutation matrix whose permutation preserves $\tau$ on units act on $x$ by a scalar. Let $l$ be an exponent for $\xi_\theta$ with $l(x) \neq 0$. Then there is a permutation $\sigma$ such that

1. some exponent for $\xi_{\theta \circ \sigma}$ is not zero at $\rho(\sigma^{-1})x$;
2. $|\theta_{\sigma(i)}(\varpi)|$ does not increase with $i$.

Lean: `New.IsExponent.exists_sorted` (Lib/LocalGL/Iwahori/SortedExponents.lean).

*Proof (outline).* By bubble sort it is enough to exchange two neighbours $i$ and $j = i + 1$ whose roots $a = \theta_i(\varpi)$ and $b = \theta_j(\varpi)$ have $|a| < |b|$. Let $w$ be the dominant element whose valuation drops by one between $i$ and $j$ and nowhere else, and let $s$ be the form $l$ after the exchange. On the kernel of $l$, the mean of $s$ is an eigenform for the exchanged character. So $s \circ (U_w - \xi_\theta(w))$ is an exponent for $\xi_{\theta \circ (i\,j)}$. If it were $0$ at the permuted vector, the quadratic relation of section 3 would give $q\,a = q\,b + (q - 1)\,a$ up to a common factor, so $a = q\,b$. This contradicts $|a| < |b|$. The hypothesis on permutations is used to show that the permuted vector is fixed by the transvections at $(i, j)$. $\square$

The source calls this a special case of the results of Bernstein and Zelevinsky on cuspidal exponents.

### Exponents from eigenvectors

An Iwahori eigenvector is a nonzero $y \in V^{I_1}$ with $U_t\,y = \xi(t)\,y$ for all dominant $t$. In a unitary representation it gives an exponent.

**Theorem.** Let $B$ be a positive definite invariant Hermitian form on $V$. Let $x \in V$, and assume that the $I_1$-fixed vectors in the span of the translates $\rho(g)x$ form a space of finite dimension. If this span contains an Iwahori eigenvector $y$ for $\xi$, then it contains a $w \neq 0$ such that $B(w, \cdot)$ is an exponent for $\xi$.

Lean: `New.IsIwahoriEigen.exists_isExponent`, `New.exists_eigenvector_of_functional` (Lib/LocalGL/Iwahori/SortedExponents.lean, Lib/General/LinearAlgebra/Eigenvalues.lean).

*Proof.* Let $W = V^{I_1}$ and let $S$ be the space of the forms $B(w, \cdot)$ on $W$, for $w$ in the $I_1$-fixed part of the span. It has finite dimension. The adjoint of $U_t$ for $B$ is the mean over $I_1$ after $\rho(t^{-1})$, and it keeps the span. So $S$ is stable under the duals of the operators $U_t$, and these duals commute, by the product formula. Evaluation at $y$ is a linear form on $S$. It is not zero on $S$, since $B(y, y) > 0$, and it is an eigenform for the duals with the character $\xi$. A linear algebra lemma (Lean: `New.exists_eigenvector_of_functional`) gives a common eigenvector $B(w, \cdot)$ in $S$ for the character $\xi$. This is the claim. $\square$

**Remark (Formalization).** The Lean definition of a smooth representation does not include admissibility. The theorem has the finite dimension of the $I_1$-fixed part of the span as a hypothesis instead. Where the source uses the theorem, the hypothesis must be supplied for the representation at hand.

Two results put the pieces together. Both assume that $\rho$ is unitary and that the $I_1$-fixed part of each cyclic span has finite dimension.

**Theorem.** Let $x \neq 0$ be fixed by $I_1$, with the hypotheses on $\tau$ and on permutations of the sorting theorem. Then there are characters $\theta$ with $\theta_i(\varepsilon) = \tau(\varepsilon \text{ at } i)$ for units $\varepsilon$, an exponent for $\xi_\theta$ that is not zero at $x$, and a permutation $\sigma$ that sorts $|\theta_i(\varpi)|$, such that the span of the translates of $x$ contains an Iwahori eigenvector for $\xi_{\theta \circ \sigma}$.

Lean: `New.exists_sorted_isIwahoriEigen_of_diagGL_smul` (Lib/LocalGL/Iwahori/SortedExponents.lean).

**Theorem.** Let $\chi_1, \ldots, \chi_r$ be distinct characters of $k^\times$ and $m_1 + \cdots + m_r = N$. Let $x$ be fixed by the integral matrices that reduce to $1$, and assume that the projection of $x$ along the Hall product of the class functions $\chi_a \circ \det$ on $\mathrm{GL}_{m_a}(k)$ is not zero. Then the span of the translates of $x$ contains an Iwahori eigenvector for $\xi_\theta$, where $|\theta_i(\varpi)|$ does not increase with $i$, and where the restriction of each $\theta_i$ to units is $\chi_{c(i)}$ of the residue, for a labelling $c$ that takes each value $a$ exactly $m_a$ times.

Lean: `New.exists_sorted_of_detChar` (Lib/LocalGL/Iwahori/SortedExponents.lean).

The Hall product is the parabolic induction of class functions of finite general linear groups, from [Characters of GL_n over a finite field](/chapter/finite-gln/). The proof cuts the indices into consecutive blocks of sizes $m_a$, finds a nonzero vector in the span on which the parahoric of the blocks acts by $\prod_a \chi_a(\det g_a)$, and applies the previous theorem to it.
