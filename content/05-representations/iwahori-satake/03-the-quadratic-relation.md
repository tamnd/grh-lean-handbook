---
title: The quadratic relation and an injective U_t
lean:
  - Lib/LocalGL/Iwahori/QuadraticRelation.lean
  - Lib/LocalGL/Iwahori/ParahoricStructure.lean
  - Lib/General/LinearAlgebra/Eigenvalues.lean
decls:
  - New.swap_mul_transvectionGL
  - New.exists_swap_conj_mem_proIwahori
  - New.quadratic_relation
  - New.exists_antitone_of_swap
  - New.exists_iwahoriHeckeHom_injective
  - New.IsExponent.apply_proIwahori
  - New.IsExponent.apply_diagGL_unit
  - New.IsExponent.apply_monomial_translate
  - New.eventually_pow_mul_mem_dominantTorus
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The quadratic relation and an injective U_t

In the Iwahori-Hecke algebra, the operator of a simple reflection $s$ satisfies a quadratic relation $(T_s - q)(T_s + 1) = 0$. This section proves a form of this relation for a linear map $\varphi$ that is invariant under $I_1$, and for a vector $x$ that need not be fixed by $I_1$. The relation has two uses. In this section it shows that some $U_t$ with $t$ strictly dominant is injective on $V^{I_1}$. In sections 5 and 6 it moves exponents across simple transpositions.

Throughout, $\rho$ is a smooth representation of $\mathrm{GL}_N(F)$, the ring $\mathcal{O}$ is compact, and $\bar m$ is the mean over $I_1$. For indices $a \neq b$ and $r \in F$ let $E_{ab}$ be the matrix unit, and let $1 + rE_{ab}$ be the transvection. Let $s = s_{ab}$ be the permutation matrix of the transposition of $a$ and $b$.

### A factorisation in GL_2

**Lemma.** Let $u \in F^\times$, and let $d$ be the diagonal matrix with $-u^{-1}$ at $a$, $u$ at $b$ and $1$ elsewhere. Then
$$s\,(1 + uE_{ab}) = (1 + u^{-1}E_{ab})\, d\, (1 + u^{-1}E_{ba}).$$

Lean: `New.swap_mul_transvectionGL` (Lib/LocalGL/Iwahori/QuadraticRelation.lean).

*Proof.* Only the rows and columns $a$ and $b$ take part, so it is an identity in $\mathrm{GL}_2$. With $a$ first and $b$ second, the left side is $\begin{pmatrix} 0 & 1 \\ 1 & u \end{pmatrix}$. On the right,
$$\begin{pmatrix} 1 & u^{-1} \\ 0 & 1 \end{pmatrix}\begin{pmatrix} -u^{-1} & 0 \\ 0 & u \end{pmatrix}\begin{pmatrix} 1 & 0 \\ u^{-1} & 1 \end{pmatrix} = \begin{pmatrix} 1 & u^{-1} \\ 0 & 1 \end{pmatrix}\begin{pmatrix} -u^{-1} & 0 \\ 1 & u \end{pmatrix} = \begin{pmatrix} 0 & 1 \\ 1 & u \end{pmatrix}. \qquad \square$$

If $u$ is a unit, the left factor $1 + u^{-1}E_{ab}$ with $a < b$ lies in $I_1$, the factor $d$ is a diagonal matrix of units, and the right factor is a lower transvection with integral entry.

**Lemma.** Let $b = a + 1$ and $g \in I_1$. There is an integral $z$ such that $s\, g (1 + zE_{ab})\, s^{-1} \in I_1$.

Lean: `New.exists_swap_conj_mem_proIwahori` (Lib/LocalGL/Iwahori/QuadraticRelation.lean).

*Proof.* Put $z = -g_{ab}/g_{aa}$. It is integral, since $g_{aa}$ is a unit. Right multiplication by $1 + zE_{ab}$ adds $z$ times column $a$ to column $b$. So the entry $(a, b)$ of $g' = g(1 + zE_{ab})$ is $0$, and $g' \in I_1$. Conjugation by $s$ exchanges the rows $a, b$ and the columns $a, b$. Since $a$ and $b$ are adjacent, the only entry that it moves from above the diagonal to below the diagonal is the entry $(a, b)$, which is $0$. So $sg's^{-1} \in I_1$. $\square$

### The quadratic relation

**Theorem (Quadratic relation).** Let $b = a + 1$, let $s$ be the transposition of $a$ and $b$, and let $\varphi$ be a linear map on $V$ with $\varphi \circ \rho(k) = \varphi$ for $k \in I_1$. Let $x \in V$ be fixed by $1 + rE_{ba}$ for every integral $r$. Let $c$ be a value such that $\varphi(\rho(d)x) = c$ for every $d$ as in the first lemma with $u$ a unit. Then
$$q\, \varphi\bigl(\rho(s)\, \bar m(x)\bigr) = \varphi\bigl(\rho(s)x\bigr) + (q - 1)\,c.$$

Lean: `New.quadratic_relation` (Lib/LocalGL/Iwahori/QuadraticRelation.lean).

*Proof.* Let $f$ be a set of representatives in $\mathcal{O}$ of the residue field, and put
$$y = \sum_{r \in k} \rho(1 + f(r)E_{ab})\, x.$$
Each transvection $1 + f(r)E_{ab}$ lies in $I_1$, so $\bar m(y) = q\,\bar m(x)$. The theorem follows if
$$\varphi\bigl(\rho(s)\rho(g)y\bigr) = \varphi(\rho(s)x) + (q - 1)c$$
for every $g \in I_1$: take the mean over $g$.

Fix $g \in I_1$. By the second lemma there are an integral $z$ and an $h \in I_1$ with $sg = h\, s\, (1 - zE_{ab})$. By the invariance of $\varphi$,
$$\varphi\bigl(\rho(s)\rho(g)y\bigr) = \sum_{r \in k} \varphi\bigl(\rho(s)\rho(1 + (f(r) - z)E_{ab})\,x\bigr).$$
Exactly one $r$, the residue of $z$, has $v(f(r) - z) < 1$. For this $r$ put $\varepsilon = f(r) - z$. Then $s(1 + \varepsilon E_{ab})s^{-1} = 1 + \varepsilon E_{ba}$ lies in $I_1$, and the term is $\varphi(\rho(s)x)$. For each of the other $q - 1$ values of $r$, the element $u = f(r) - z$ is a unit. By the first lemma,
$$\rho(s)\rho(1 + uE_{ab})x = \rho(1 + u^{-1}E_{ab})\,\rho(d)\,\rho(1 + u^{-1}E_{ba})\,x = \rho(1 + u^{-1}E_{ab})\,\rho(d)\,x.$$
The left factor lies in $I_1$, so the term is $\varphi(\rho(d)x) = c$. $\square$

For $x \in V^{I_1}$ and $\varphi = \bar m$ the relation says $q\,\bar m \rho(s) \bar m = \bar m \rho(s) + (q - 1)c$ on $x$. This is the classical relation in the form used at the Iwahori level, where $c$ is the contribution of the diagonal part.

### An injective U_t

**Theorem.** Let $\varpi$ be a uniformiser and $\rho$ smooth. There is a diagonal $t$ with $v(t_i)$ strictly increasing in $i$ such that $U_t$ is injective on $V^{I_1}$.

Lean: `New.exists_iwahoriHeckeHom_injective`, `New.exists_antitone_of_swap` (Lib/LocalGL/Iwahori/QuadraticRelation.lean, Lib/General/LinearAlgebra/Eigenvalues.lean).

*Proof.* For each index $a$ let $s_a$ be the diagonal element with $\varpi^{-1}$ at the indices $i \geq a$ and $1$ before. It is dominant. The product $t = \prod_a s_a$ has $t_i = \varpi^{-(i+1)}$, so its valuations strictly increase. The operators $U$ with zero kernel are closed under products, and $U_t = \prod_a U_{s_a}$ by the product formula of section 2. So it is enough to show that $U_{s_a} x = 0$ implies $x = 0$ for $x \in V^{I_1}$.

Fix $a$ and $x \in V^{I_1}$ with $\bar m(\rho(s_a)x) = 0$. Let $\gamma$ be the cyclic permutation that shifts the indices by $a$, and put $n = \gamma^{-1} s_a$, a monomial matrix. A computation with valuations shows that $n^{-1} h n \in I_1$ for every $h \in I_1$. So $y = \rho(n)x$ is fixed by $I_1$. For a permutation $\sigma$ let $P(\sigma)$ be the statement
$$\bar m\bigl(\rho(\sigma^{-1})\,y\bigr) = 0.$$
The hypothesis $U_{s_a}x = 0$ says $P(\gamma^{-1})$.

Let $i$ and $j = i + 1$ be adjacent indices with $\sigma(j) < \sigma(i)$, and assume $P(\sigma)$. Put $z = \rho(\sigma^{-1})y$. Since $y$ is fixed by $I_1$ and $\sigma(j) < \sigma(i)$, the vector $z$ is fixed by $1 + rE_{ji}$ for integral $r$. A diagonal matrix of units normalises $I_1$, so $\bar m(\rho(d)z) = \bar m(\rho(d)\bar m(z)) = 0$ for such $d$. The quadratic relation with $\varphi = \bar m$ and $c = 0$ gives
$$q\,\bar m\bigl(\rho(s_{ij})\,\bar m(z)\bigr) = \bar m\bigl(\rho(s_{ij})z\bigr).$$
The left side is $0$ by $P(\sigma)$. So $P(\sigma s_{ij})$ holds.

Each such step removes one inversion of $\sigma$. By bubble sort, a finite number of steps carries $\gamma^{-1}$ to the identity, and $P(1)$ holds. Since $y$ is fixed by $I_1$, $P(1)$ says $y = \bar m(y) = 0$. Since $\rho(n)$ is injective, $x = 0$. $\square$

The bubble sort is a general lemma of the library: if a property of permutations passes from $\sigma$ to $\sigma s_{i,i+1}$ whenever $\sigma(i+1) < \sigma(i)$, then from any starting point it reaches a permutation that sorts a given function (Lean: `New.exists_antitone_of_swap`, in Lib/General/LinearAlgebra/Eigenvalues.lean).

**Remark (Formalization).** The Lean statement is existential, but the proof gives the explicit element $t = \operatorname{diag}(\varpi^{-1}, \varpi^{-2}, \ldots, \varpi^{-N})$. Up to the centre this is $\operatorname{diag}(\varpi^{N-1}, \ldots, \varpi, 1)$. The source calls the theorem a case of the injectivity of fixed vectors into the Jacquet module, due to Moy and Prasad and to Morris. In this chapter the injectivity replaces that result: the Jacquet module is not defined, and an injective $U_t$ is what the proofs need.

### Exponents on monomial translates

The rest of the chapter evaluates exponents on vectors that are not fixed by $I_1$. Four lemmas of the file make this possible. Let $l$ be an exponent for $\xi$.

**Lemma.** For $k \in I_1$ and every $z$, $l(\rho(k)z) = l(z)$.

Lean: `New.IsExponent.apply_proIwahori` (Lib/LocalGL/Iwahori/QuadraticRelation.lean).

*Proof.* The definition at $t = 1$ gives $l = l \circ \bar m$, and $\bar m \circ \rho(k) = \bar m$. $\square$

**Lemma.** Let $t$ be diagonal with unit entries. Then $l(\rho(t)z) = \xi(t)\,l(z)$ for every $z$.

Lean: `New.IsExponent.apply_diagGL_unit` (Lib/LocalGL/Iwahori/QuadraticRelation.lean).

*Proof.* The element $t$ is dominant, since all its valuations are $1$. It normalises $I_1$. So $l(\rho(t)z) = l(\bar m(\rho(t)z)) = l(\bar m(\rho(t)\bar m(z))) = l(\rho(t)\bar m(z))$, and the definition gives $\xi(t)l(z)$. $\square$

The fourth lemma is the one that section 4 applies to partial Hecke sums. It drops the mean in the definition at a monomial translate of a vector with a large fixer.

**Lemma (Monomial translates).** Let $y$ be fixed by every $g$ in the parahoric $P_c$ whose diagonal entries are congruent to $1$. Let $\sigma$ be a permutation and $t$ diagonal, and suppose that for $\sigma(b) < \sigma(a)$ either $v(t_{\sigma(b)}) \leq v(t_{\sigma(a)})$, or $c(a) \leq c(b)$ and $v(t_{\sigma(b)}) \leq v(t_{\sigma(a)})\exp(1)$. Then
$$l\bigl(\rho(t)\rho(\sigma)y\bigr) = \xi(t)\,l\bigl(\rho(\sigma)y\bigr).$$

Lean: `New.IsExponent.apply_monomial_translate`, `New.eventually_pow_mul_mem_dominantTorus` (Lib/LocalGL/Iwahori/QuadraticRelation.lean, Lib/LocalGL/Iwahori/ParahoricStructure.lean).

*Proof.* Here $t$ need not be dominant. Let $t_0 = \operatorname{diag}(1, \varpi^{-1}, \varpi^{-2}, \ldots)$, which is strictly dominant. For large $k$ the product $t_0^k t$ is dominant (Lean: `New.eventually_pow_mul_mem_dominantTorus`). For a dominant $d$ and a vector of the form $\rho(t\sigma)y$, the hypotheses let one drop the mean: for $g \in I_1$, write $g = u(u^{-1}g)$ with $u$ upper unitriangular in $I_1$ and $u^{-1}g$ lower triangular. The conjugate of $u^{-1}g$ by $t\sigma$ lies in the group that fixes $y$, by the hypothesis on valuations, and $dud^{-1} \in I_1$. Apply this twice: to $d = t_0^k$ with the vector $\rho(t\sigma)y$, and to $d = t_0^k t$ with the vector $\rho(\sigma)y$. Both compute $l(\rho(t_0^k t \sigma)y)$. So $\xi(t_0^k)\, l(\rho(t)\rho(\sigma)y) = \xi(t_0^k)\,\xi(t)\, l(\rho(\sigma)y)$. Cancel the factor $\xi(t_0^k)$. $\square$
