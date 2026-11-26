---
title: Sections and same-section pairs
lean:
  - Lib/Adelic/Adeles/LocalFactors.lean
  - New/Determinant/Exchange/MatchingPartners.lean
decls:
  - New.schwartzBruhat
  - New.TameLocalChar
  - New.IsCommonCosetRep
  - New.exists_isCommonCosetRep
  - New.commonCosetSum
  - New.commonCosetRep
  - New.commonCosetSum_eq_sum
  - New.localSection
  - New.localSection_eq_sum
  - New.exists_isPrimitiveMatrix_localSection_eq
  - New.sameSectionPairs
  - New.mem_sameSectionPairs_iff
  - New.sameSectionPairs.translate_mem
  - New.isClopen_setOf_isPrimitiveMatrix
  - New.exists_eq_invLastRows_iff_isPrimitiveMatrix
  - New.sameSectionPairs.exists_linear_factor
  - New.AreMatched.apply_invLastRows_eq_of_isPrimitiveMatrix
  - New.AreMatched.isLocallyConstant_comp_transpose
  - New.AreMatched.mem_sameSectionPairs
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sections and same-section pairs

Matched functions are not stable under $GL_n(F)$, as the condition refers to $GL_n(O)$. The large side of the exchange identity is equivariant under all of $GL_n(F)$ at the ramified places. This section replaces matched pairs by a larger class that is stable under $GL_n(F)$: the *same-section pairs*. It then proves the key property of the class: a functional of $\Phi$ with the right equivariance depends only on $\Psi$.

Throughout, $F$ is a semilocal field with ring $O$ (Section 2), and $e \colon b \sqcup a \to n$ splits the indices.

### Locally constant data and tame characters

**Definition.** For a set $s$ of a topological space, $\mathcal{S}(s)$ is the space of complex functions that are locally constant, have compact support, and vanish off $s$.

Lean: `New.schwartzBruhat` (Lib/Adelic/Adeles/LocalFactors.lean).

**Definition.** A character $\chi$ of $F$ is *tame* if there are a finite ring $R$, a surjective ring map $\pi \colon O \to R$ with kernel $\varpi O$, and a primitive character $\eta$ of $R$, such that $\eta(\pi(t)) = \chi^{-1}_O(t)$ for every $t \in O$. Here $\chi^{-1}_O(t) = \chi(t)^{-1}$ if $t$ is a unit of $O$ and $0$ otherwise.

Lean: `New.TameLocalChar` (Lib/Adelic/Adeles/LocalFactors.lean).

A tame character is constant on the cosets of $1 + \varpi O$ in the units of $O$. So $\chi^{-1}_O$ is locally constant. The characters of a split tame character at its ramified places are tame; see [characters and twists](/chapter/fields-places-twists/).

### Common coset representatives

The group $GL_b(F)$ acts on the right on the $n \times b$ matrices, and $GL_b(O)$ is a compact open subgroup. Write $Q$ for the set of left cosets $g\, GL_b(O)$.

**Definition.** A map $r \colon Q \to GL_b(F)$ is a choice of *common coset representatives* if:

1. $r(q) \in q$ for every coset $q$;
2. for every $n \times b$ matrix $y$ with a left inverse, there is exactly one $q$ with $y\, r(q)$ primitive;
3. for every such $y$, there is exactly one $q$ with $y\, r(q)^{-1}$ primitive.

Lean: `New.IsCommonCosetRep` (New/Determinant/Exchange/MatchingPartners.lean).

**Lemma.** Common coset representatives exist.

Lean: `New.exists_isCommonCosetRep` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Step 1: each coset has a symmetric representative. Let $g \in GL_b(F)$. The valuation pair condition gives a Smith normal form $g = k\, d\, l$ with $k, l \in GL_b(O)$ and $d$ diagonal. Then $g\, (l^{-1} k^{\mathsf{T}}) = k\, d\, k^{\mathsf{T}}$ is symmetric, and $l^{-1} k^{\mathsf{T}} \in GL_b(O)$. So choose for each coset $q$ a symmetric representative $r(q) \in q$.

Step 2: the cosets of primitive translates. Let $y$ have a left inverse. A column reduction of Hermite type, which the valuation pair condition allows, gives $u \in GL_b(F)$ with $y\, u$ primitive. For $h \in GL_b(F)$, the matrix $(y u)\, h$ is primitive exactly when $h \in GL_b(O)$. Indeed, if $L$ is an integral left inverse of $y u$ and $y u h$ is integral, then $h = L\, y u h$ is integral; and an integral left inverse $L'$ of $y u h$ gives the integral inverse $L' y u$ of $h$. The converse is clear. So $y\, g$ is primitive exactly when $u^{-1} g \in GL_b(O)$, that is, when $g$ lies in the coset of $u$. Condition 2 holds, with the coset of $u$.

Step 3: inverses. By Step 2, $y\, r(q)^{-1}$ is primitive exactly when $u^{-1} r(q)^{-1} \in GL_b(O)$. The group $GL_b(O)$ is stable under $h \mapsto (h^{-1})^{\mathsf{T}}$. Applied to $u^{-1} r(q)^{-1}$, this map gives $u^{\mathsf{T}}\, r(q)^{\mathsf{T}} = u^{\mathsf{T}}\, r(q)$, because $r(q)$ is symmetric. So the condition is $u^{\mathsf{T}} r(q) \in GL_b(O)$: the coset $q$ is the coset of $(u^{\mathsf{T}})^{-1}$. Condition 3 holds. $\square$

The symmetry of the representatives is the point of the lemma. Without it, the cosets in conditions 2 and 3 would be left and right cosets, and the two families would not be indexed by the same set.

**Example.** Let $F$ be one local field with uniformizer $\varpi$ and valuation $v$, and let $b = \{1\}$. The cosets $Q = F^\times / O^\times$ have the representatives $\varpi^m$, $m \in \mathbb{Z}$, which are symmetric. A column $y = (y_1, \ldots, y_n)$ has a left inverse exactly when $y \neq 0$, and $y\, \varpi^m$ is primitive exactly when $m = -\min_i v(y_i)$. So $y\, \varpi^{m}$ is primitive for exactly one $m$, and $y\, \varpi^{-m}$ for exactly one $m$.

### The section of a function

**Definition.** The *coset sum* $\Sigma$ is a linear functional on the complex functions on $GL_b(F)$, and $r$ is a choice of common coset representatives, such that $\Sigma(f) = \sum_{q \in t} f(r(q))$ whenever $t$ is a finite set of cosets that contains every $q$ with $f(r(q)) \neq 0$.

Lean: `New.commonCosetSum`, `New.commonCosetRep`, `New.commonCosetSum_eq_sum` (New/Determinant/Exchange/MatchingPartners.lean).

**Definition.** For a character $\chi$ of $F$ and an $n \times b$ matrix $y$, the *section at $y$* is the linear functional
$$\sigma_y(\Psi) = \Sigma\bigl(g \mapsto \chi(\det g)\, \Psi(y g)\bigr)$$
on the functions $\Psi$ of $n \times b$ matrices. When only the cosets of a finite set $t$ contribute,
$$\sigma_y(\Psi) = \sum_{q \in t} \chi(\det r(q))\, \Psi\bigl(y\, r(q)\bigr).$$

Lean: `New.localSection`, `New.localSection_eq_sum` (New/Determinant/Exchange/MatchingPartners.lean).

**Remark (Formalization).** The coset sum and the representatives are chosen together, with the axiom of choice. A linear extension of the finite sum from the finitely supported functions to all functions exists because every subspace has a complement. The values of $\Sigma$ at functions with infinitely many nonzero values at the representatives are not specified, and the source never uses them. Every section that the source evaluates is a finite sum.

For a single local field and $b = \{1\}$, the section is $\sigma_y(\Psi) = \sum_m \chi(\varpi)^m\, \Psi(\varpi^m y)$, a sum of Tate type over the multiples of the line of $y$.

**Lemma (One term).** Let $y$ have a left inverse. There is $g \in GL_b(F)$ with $y g$ primitive such that $\sigma_y(\Psi) = \chi(\det g)\, \Psi(y g)$ for every $\Psi$ that vanishes off the primitive matrices.

Lean: `New.exists_isPrimitiveMatrix_localSection_eq` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* By condition 2 there is exactly one coset $q_0$ with $y\, r(q_0)$ primitive. Put $g = r(q_0)$. For every other $q$ the matrix $y\, r(q)$ is not primitive, so $\Psi(y\, r(q)) = 0$. The sum with $t = \{q_0\}$ gives the claim. $\square$

### Same-section pairs

**Definition.** A pair $(\Phi, \Psi)$, with $\Phi$ a function of $a \times n$ matrices and $\Psi$ a function of $n \times b$ matrices, is a *same-section pair* for $\chi$ and $e$ if:

1. $\Phi \in \mathcal{S}(\{x : x^{\mathsf{T}} \text{ has a left inverse}\})$;
2. $\Psi \in \mathcal{S}(\{y : y \text{ has a left inverse}\})$;
3. for every $k \in GL_n(F)$,
$$\sigma_{x_k^{\mathsf{T}}}\bigl(y \mapsto \Phi(y^{\mathsf{T}})\bigr) = \chi(\det k)\, \sigma_{y_k}(\Psi).$$

The same-section pairs form a complex vector space.

Lean: `New.sameSectionPairs`, `New.mem_sameSectionPairs_iff` (New/Determinant/Exchange/MatchingPartners.lean).

The section on the left is taken over the cosets of $GL_a(O)$, and the one on the right over the cosets of $GL_b(O)$. Condition 3 is the matching condition of Section 2, averaged over these cosets, and now asked for every invertible $k$ and not only for the integral ones.

**Proposition (Translation).** Let $(\Phi, \Psi)$ be a same-section pair and $g \in GL_n(F)$. Then
$$\bigl(x \mapsto \chi(\det g)\, \Phi(x g),\ \ y \mapsto \Psi(g^{-1} y)\bigr)$$
is a same-section pair.

Lean: `New.sameSectionPairs.translate_mem` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Call the new pair $(\Phi', \Psi')$. Right multiplication by $g$ is a homeomorphism of the $a \times n$ matrices, and $x^{\mathsf{T}}$ has a left inverse $L$ exactly when $(x g)^{\mathsf{T}}$ has the left inverse $L\, g^{\mathsf{T}}$. So $\Phi'$ satisfies condition 1. In the same way $\Psi'$ satisfies condition 2, with left inverses $L g^{-1}$. For condition 3, fix $k$. The rows $a$ of $k^{-1} g = (g^{-1} k)^{-1}$ are $x_k\, g$, and the columns $b$ of $g^{-1} k$ are $g^{-1} y_k$. So $x_k g = x_{g^{-1} k}$ and $g^{-1} y_k = y_{g^{-1} k}$. From the definition of the section,
$$\sigma_{x_k^{\mathsf{T}}}\bigl(y \mapsto \Phi'(y^{\mathsf{T}})\bigr) = \chi(\det g)\, \sigma_{x_{g^{-1}k}^{\mathsf{T}}}\bigl(y \mapsto \Phi(y^{\mathsf{T}})\bigr), \qquad \sigma_{y_k}(\Psi') = \sigma_{y_{g^{-1}k}}(\Psi).$$
Condition 3 for the old pair at $g^{-1} k$ says that the left side is $\chi(\det g)\, \chi(\det g^{-1} \det k)\, \sigma_{y_{g^{-1}k}}(\Psi) = \chi(\det k)\, \sigma_{y_k}(\Psi')$. $\square$

### The key property

Two facts on primitive matrices come first.

**Lemma.** The primitive $n \times a$ matrices form a closed and open set. An $a \times n$ matrix $x$ is $x_k$ for some $k \in GL_n(O)$ exactly when $x^{\mathsf{T}}$ is primitive.

Lean: `New.isClopen_setOf_isPrimitiveMatrix`, `New.exists_eq_invLastRows_iff_isPrimitiveMatrix` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* The primitive matrices are the projection of the set of pairs $(y, L)$ of integral matrices with $L y = 1$. This set is compact, as $O$ is compact, so its projection is compact, hence closed. For openness, let $y$ be primitive with integral left inverse $L$. A matrix $z$ near $y$ is integral, because $O$ is open, and $L z$ is near $1$. Its determinant is near $1$ and is therefore a unit of $O$, because $1 + \varpi O$ consists of units of $O$ and the units form an open set. Then $(L z)^{-1} L$ is an integral left inverse of $z$. For the second statement, $x = x_k$ exactly when $x^{\mathsf{T}}$ is the matrix of the columns $a$ of $(k^{-1})^{\mathsf{T}}$, and $k \mapsto (k^{-1})^{\mathsf{T}}$ preserves $GL_n(O)$. A primitive matrix is a block of columns of some $k \in GL_n(O)$ by the valuation pair condition, and conversely. $\square$

**Theorem (Equivariant functionals factor).** Let $\Lambda$ be a linear map from functions of $a \times n$ matrices to functions on a set $X$, with
$$\chi(\det g)\, \Lambda\bigl(x \mapsto \Phi(g x)\bigr) = \Lambda(\Phi)$$
for every $g \in GL_a(F)$ and every $\Phi \in \mathcal{S}(\{x : x^{\mathsf{T}} \text{ has a left inverse}\})$. Then there is a linear map $T$ from functions of $n \times b$ matrices to functions on $X$ with $T(\Psi) = \Lambda(\Phi)$ for every same-section pair $(\Phi, \Psi)$.

Lean: `New.sameSectionPairs.exists_linear_factor` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Write $r$ for the common representatives of the cosets of $GL_a(O)$. For each $x$ with $x^{\mathsf{T}}$ primitive, choose $k(x) \in GL_n(O)$ with $x = x_{k(x)}$, by the lemma. Define the linear map
$$R(\Psi)(x) = \chi(\det k(x))\, \sigma_{y_{k(x)}}(\Psi) \text{ if } x^{\mathsf{T}} \text{ is primitive}, \qquad R(\Psi)(x) = 0 \text{ otherwise},$$
and put $T = \Lambda \circ R$. Now let $(\Phi, \Psi)$ be a same-section pair. We show $\Lambda(R(\Psi)) = \Lambda(\Phi)$.

Cut $\Phi$ into pieces. For each $x$ with $\Phi(x) \neq 0$, condition 3 of the representatives, applied to $x^{\mathsf{T}}$, gives exactly one coset $q$ with $x^{\mathsf{T}} r(q)^{-1}$ primitive. The sets $U_q = \{x : x^{\mathsf{T}} r(q)^{-1} \text{ primitive}\}$ are open and cover the support of $\Phi$, which is compact. So finitely many cosets, a set $t$, suffice. Put $\Phi_q = \Phi \cdot \mathbf{1}_{U_q}$. Each $U_q$ is closed and open, so $\Phi_q$ is locally constant, and $\Phi_q$ is in $\mathcal{S}$. By uniqueness, $\Phi = \sum_{q \in t} \Phi_q$.

Compute $R(\Psi)$. Let $x^{\mathsf{T}}$ be primitive and $k = k(x)$. By condition 3 of the pair,
$$R(\Psi)(x) = \chi(\det k)\, \sigma_{y_k}(\Psi) = \sigma_{x^{\mathsf{T}}}\bigl(y \mapsto \Phi(y^{\mathsf{T}})\bigr) = \sum_{q} \chi(\det r(q))\, \Phi\bigl(r(q)^{\mathsf{T}} x\bigr).$$
A term with $\Phi(r(q)^{\mathsf{T}} x) \neq 0$ has $r(q)^{\mathsf{T}} x \in U_{q'}$ for some $q' \in t$. Then $x^{\mathsf{T}}\, r(q)\, r(q')^{-1}$ is primitive. As $x^{\mathsf{T}}$ is primitive, Step 2 of the proof of the existence of representatives gives $r(q)\, r(q')^{-1} \in GL_a(O)$. Transpose and use the symmetry of $r(q)$ and $r(q')$: $r(q')^{-1} r(q) \in GL_a(O)$, so $q = q'$. So the sum is finite, over $q \in t$, and the term of $q$ is $\chi(\det r(q))\, \Phi_q(r(q)^{\mathsf{T}} x)$. The same computation shows that $\Phi_q(r(q)^{\mathsf{T}} x) \neq 0$ only if $x^{\mathsf{T}}$ is primitive. So, for all $x$,
$$R(\Psi)(x) = \sum_{q \in t} \chi(\det r(q))\, \Phi_q\bigl(r(q)^{\mathsf{T}} x\bigr).$$
Apply $\Lambda$ and the hypothesis with $g = r(q)^{\mathsf{T}}$, whose determinant is $\det r(q)$:
$$\Lambda(R(\Psi)) = \sum_{q \in t} \chi(\det r(q))\, \Lambda\bigl(x \mapsto \Phi_q(r(q)^{\mathsf{T}} x)\bigr) = \sum_{q \in t} \Lambda(\Phi_q) = \Lambda(\Phi). \qquad \square$$

In Section 4, $\Lambda$ is the theta integral over $[U(V)]$. The group $GL_a(F)$ is the Levi factor of $U(V)$ at a split place, and the hypothesis on $\Lambda$ says that the theta integral does not see the action of $U(V)$ on the datum.

### Matched pairs are same-section pairs

**Lemma (Compatibility).** Let $\Phi$ and $\Psi$ be matched for $\chi$ over $O$. Let $i \in GL_n(O)$ and $j \in GL_n(F)$ with $x_j = x_i$ and $y_j$ primitive. Then $\Phi(x_j) = \chi(\det j)\, \Psi(y_j)$.

Lean: `New.AreMatched.apply_invLastRows_eq_of_isPrimitiveMatrix` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Write $u_j$ for the rows $b$ of $j^{-1}$, a left inverse of $y_j$. The columns of $y_i$ and of $y_j$ both span the kernel of the common rows $x = x_i = x_j$. So $y_i = y_j\, g$ with $g = u_j\, y_i$, and $g$ is invertible with inverse $u_i\, y_j$. Both $y_i$ and $y_j$ are primitive, so $g$ and $g^{-1}$ are integral, by Step 2 above. Jacobi's identity with the rows $s = u_j$ gives $\det(u_j; x)\det j = \det(u_j y_j) = 1$ and $\det(u_j; x) \det i = \det(u_j y_i) = \det g$. So $\det g = \det i / \det j$. Now let $i' = i \cdot \operatorname{diag}(g^{-1}, 1)$, in the blocks $b \sqcup a$. It lies in $GL_n(O)$. Its columns $b$ are $y_i g^{-1} = y_j$, and the rows $a$ of $i'^{-1} = \operatorname{diag}(g, 1)\, i^{-1}$ are those of $i^{-1}$, so $x_{i'} = x$. The matching condition at $i'$ gives
$$\Phi(x_j) = \chi(\det i')\, \Psi(y_j) = \chi(\det i / \det g)\, \Psi(y_j) = \chi(\det j)\, \Psi(y_j). \qquad \square$$

**Lemma.** Let $\chi$ be tame, let $\Phi$ and $\Psi$ be matched for $\chi$ over $O$, and let $\Psi$ be locally constant. Then $y \mapsto \Phi(y^{\mathsf{T}})$ is locally constant.

Lean: `New.AreMatched.isLocallyConstant_comp_transpose` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Put $G(k) = \Psi(y_k) / \chi^{-1}_O(\det k)$ for $k \in GL_n(O)$. For such $k$, $\det k$ is a unit of $O$, so $G(k) = \chi(\det k)\Psi(y_k) = \Phi(x_k)$. As $\chi$ is tame, $\chi^{-1}_O$ is locally constant, so $G$ is locally constant on the compact group $GL_n(O)$. The function $\phi(y) = \Phi(y^{\mathsf{T}})$ vanishes off the closed and open set $P$ of primitive matrices, and $P$ is the image of $GL_n(O)$ under $k \mapsto x_k^{\mathsf{T}}$. Let $s$ be a set of values. The set $C = \{x_k^{\mathsf{T}} : k \in GL_n(O),\ G(k) \notin s\}$ is the continuous image of a compact set, so it is closed. A primitive $y$ has $\phi(y) \notin s$ exactly when $y \in C$. So $\phi^{-1}(s)$ is $P \setminus C$ if $0 \notin s$, and $(P \setminus C) \cup P^c$ if $0 \in s$. Both sets are open. $\square$

**Theorem.** Let $\chi$ be tame, let $\Phi$ and $\Psi$ be matched for $\chi$ over $O$, and let $\Psi$ be locally constant. Then $(\Phi, \Psi)$ is a same-section pair.

Lean: `New.AreMatched.mem_sameSectionPairs` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Conditions 1 and 2. Both $y \mapsto \Phi(y^{\mathsf{T}})$ and $\Psi$ are locally constant, by the hypothesis and the lemma, and they vanish off the primitive matrices, by the lemma on $x_k$ and by the valuation pair condition. A locally constant function that vanishes off the compact set of primitive matrices is in $\mathcal{S}$, and primitive matrices have left inverses.

Condition 3. Let $k \in GL_n(F)$. By the lemma on one term there are $g \in GL_a(F)$ with $x_k^{\mathsf{T}} g$ primitive and $u \in GL_b(F)$ with $y_k u$ primitive, with
$$\sigma_{x_k^{\mathsf{T}}}\bigl(y \mapsto \Phi(y^{\mathsf{T}})\bigr) = \chi(\det g)\, \Phi(g^{\mathsf{T}} x_k), \qquad \sigma_{y_k}(\Psi) = \chi(\det u)\, \Psi(y_k u).$$
Let $j = k \cdot \operatorname{diag}(u, (g^{\mathsf{T}})^{-1})$ in the blocks $b \sqcup a$. Then $y_j = y_k u$, $x_j = g^{\mathsf{T}} x_k$, and $\det j \det g = \det k \det u$. The matrix $x_j^{\mathsf{T}} = x_k^{\mathsf{T}} g$ is primitive, so $x_j = x_i$ for some $i \in GL_n(O)$. The compatibility lemma applies, as $y_j$ is primitive:
$$\chi(\det g)\, \Phi(x_j) = \chi(\det g)\chi(\det j)\, \Psi(y_j) = \chi(\det k)\, \chi(\det u)\, \Psi(y_k u) = \chi(\det k)\, \sigma_{y_k}(\Psi). \qquad \square$$

The theorem is the bridge between Section 2 and Section 4. The exchange identity is stated for matched data, which are easy to write down. Its proof needs the stability under $GL_n(F)$, which only the same-section pairs have.
