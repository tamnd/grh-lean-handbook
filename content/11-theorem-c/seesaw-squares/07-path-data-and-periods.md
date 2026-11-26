---
title: Path data and periods
lean:
  - New/Determinant/AuxiliaryForms/PathData.lean
decls:
  - New.Data.gridModulus
  - New.Data.gridModulus_one_ideal
  - New.Data.triangleModulus
  - New.Data.gridModulus_ideal_le_triangleModulus_ideal
  - New.Data.gridSpace
  - New.Data.gridChar
  - New.Data.nodeLevel
  - New.Data.isConjKernelPair_gridKernel
  - New.Data.isEdgeFamily_grid_succ_left
  - New.Data.isEdgeFamily_grid_succ_right
  - New.Data.gridSpace_subdiag
  - New.Data.gridSpace_diag
  - New.Data.transposedChain
  - New.Data.transposedMove
  - New.Data.liftMove
  - New.Data.gridChar_det
  - New.Data.levelIndex_eq_card_GL_untwisted
  - New.IsSumOfRootsOfUnity
  - New.IsSumOfRootsOfUnity.sum
  - New.IsSumOfRootsOfUnity.mul_mem_nsmul
  - New.Data.EdgeTuple
  - New.Data.tupleAction
  - New.Data.edgeCharProd
  - New.Data.IsPathDatum
  - New.Data.sum_tuplesOn_insert
  - New.Data.sum_tuplesOn_tupleAction
  - New.Data.IsPathDatum.sum_tupleAction
  - New.Data.card_tuplesOn_le
  - New.GridPath.formMap
  - New.GridPath.formMap_append
  - New.GridPath.card_edges_le
  - New.Data.card_tuplesOn_edges_le
  - New.Data.gridPeriod
  - New.Data.IsProportional
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Path data and periods

This section puts forms on the paths of the previous section. It defines the moduli, spaces and characters at the nodes, the moves along the edges, the functions of matrices on the edges (the *path data*), and the period of a path. All of it is in [PathData.lean](lean:New/Determinant/AuxiliaryForms/PathData.lean).

### Results used

1. `modLift` and `modTransposedLift` are the theta lift and the transposed lift for the characters $a$, the polynomial $P$ and a function $\Psi$ of matrices modulo $\mathfrak{m}$ ([Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L88), [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows)).
2. `IsEdgeFamily`: conjugate cuspidal kernel pairs, characters of fixed weights with a common tame part, and the Fock vector of $\Phi$ is an edge ([Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L135)).
3. `periodPairing` is the period of a conjugate form and a form along a comparison map ([Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L472), [the seesaw for periods](/chapter/theta-lifts-seesaw/#the-seesaw-for-periods)).
4. An $m$-fold twist $\vartheta$ has places $Q$, and `twistModulus` $\vartheta$ $c$ is $\varpi^c Q$ ([twists and their powers](/chapter/twists-critical-pairs/#twists-and-their-powers), [Rows.lean](lean:New/UpperBound/Objects/Rows.lean#L109)).
5. If $\nu$ has weight $e$ and tame part $\psi$ with $\psi_w = 1$ for $w \nmid \mathfrak{m}$, then $\nu(\det k) = \chi_\psi(\det k \bmod \mathfrak{m})$ for integral $k$ ([TameModulus.lean](lean:Lib/ClassField/HeckeCharacter/TameModulus.lean#L341)).

### Moduli

Let $\varpi$ generate the product of the chosen places, let $b_0 = $ `D.natB` $\geq 1$ and let $\mathfrak{b} = \varpi^{b_0}$.

**Definition.** The *grid modulus* of $\vartheta$ is $\mathfrak{m} = \mathfrak{b} Q$. The *triangle modulus* of grid $z$ is $\varpi Q$ for $z = \mathrm{false}$ and $\mathfrak{b}$ for $z = \mathrm{true}$.

Lean: `New.Data.gridModulus`, `New.Data.triangleModulus` (New/Determinant/AuxiliaryForms/PathData.lean).

**Lemma.** The grid modulus of the trivial twist has ideal $(\mathfrak{b})$. For both $z$, the ideal of the grid modulus lies in the ideal of the triangle modulus.

Lean: `New.Data.gridModulus_one_ideal`, `New.Data.gridModulus_ideal_le_triangleModulus_ideal` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* The trivial twist has no places, so its modulus is the untwisted one, with ideal $(\varpi^{b_0})$. Let $M$ be the product of the chosen places. For $z = \mathrm{false}$, $M^{b_0} Q \subseteq M Q$ since $b_0 \geq 1$. For $z = \mathrm{true}$ the factor of the trivial twist is $1$, and $M^{b_0} Q \subseteq M^{b_0}$. $\square$

### Nodes, spaces and moves

A *node* is a triple $(z, a, b)$. For $z = \mathrm{false}$ it is the space $Y^a_b$, and for $z = \mathrm{true}$ it is $\tilde Y^b_a$.

**Definition.** The space `gridSpace` at the node $(z, a, b)$ is $Y_b$ for $z = \mathrm{false}$ and $a = 0$. It is $Y_0$ plus a line of sign $1$ at $(\mathrm{true}, 0, 0)$. At all other nodes it is the diagonal space of the signs `gridSigns`. The kernel pair `gridKernel` is the pair of kernels of the parameter `gridParam` and its negative, and `GridForm` $z$ $a$ $b$ is the space of forms of the second kernel. For a bit $c$, an index $l$ and an index type $n$, the character is $\mathrm{gridChar} = \mu_{l+1}(\vartheta^{l+1})\, \upsilon^{\lfloor |n|/2 \rfloor}$ if $c$ is true and $\mu_{l+1}(1)\, \upsilon^{\lceil |n|/2 \rceil}$ if $c$ is false. Here $\mu_{l+1}(\xi)$ is `liftChar` $\xi$ $(l+1)$ and $\upsilon$ is the splitting character.

Lean: `New.Data.gridSpace`, `New.Data.gridChar` (New/Determinant/AuxiliaryForms/PathData.lean).

**Definition.** The *level* `nodeLevel` at a node $p$ is a subgroup of $\mathrm{GL}_n(O_E/\mathfrak{m})$. It is trivial at the nodes $(\mathrm{false}, 0, b)$. At all other nodes it is the kernel of reduction modulo $\mathfrak{b}$.

Lean: `New.Data.nodeLevel` (New/Determinant/AuxiliaryForms/PathData.lean).

**Lemma.** For $i, j \leq m$ the kernel pair at $(z, i, j)$ is a pair of conjugate cuspidal kernels. For $i + 1, j \leq m$ and any family of twists $\vartheta_x$, the step from $(i, j)$ to $(i + 1, j)$ of grid $z$, with the characters $\mathrm{gridChar}(\vartheta_x, z, i)$, is an edge family with $d = \mathrm{true}$. For $i, j + 1 \leq m$, the step from $(i, j)$ to $(i, j + 1)$, with the characters $\mathrm{gridChar}(\vartheta_x, \lnot z, j)$, is an edge family with $d = \mathrm{false}$. The polynomial is `gridHarmonic` in both cases.

Lean: `New.Data.isConjKernelPair_gridKernel`, `New.Data.isEdgeFamily_grid_succ_left`, `New.Data.isEdgeFamily_grid_succ_right` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* The parameter has the gap `D.gap`. The rank at the node is at most $2 n_m$, and the log bound of the data puts the gap above the threshold for that rank. So `isConjKernelPair_kernelPair` applies. For the edges, each character has the weight `gridWeight` and the tame part `gridTamePart` at both ends. The parameters of the two nodes correspond (`paramsCorrespond_grid_succ_left` and `_right`). Then `isEdgeFamily_of_paramsCorrespond` gives the edge family. $\square$

**Lemma.** For every $j$ there is a bijection $\tau$ from the basis of $\tilde Y^{j+1}_j$ to that of $Y^{j+1}_j$ that keeps the signs, and $\tilde Y^{j+1}_j$ is $Y^{j+1}_j$ relabelled along $\tau^{-1}$. For $j \leq m$, $\tilde Y^j_j$ is $Y^j_j$ plus a line of sign $(-1)^j$, relabelled by `gridDiagEquiv`.

Lean: `New.Data.gridSpace_subdiag`, `New.Data.gridSpace_diag` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* The two index sets have the same size, since $t$ is odd, and the same number of signs $-1$. So a bijection keeps the signs. Both spaces are diagonal spaces of their signs. The diagonal case is the same computation for $j \geq 1$ and holds by definition for $j = 0$. $\square$

**Definition.** For a matrix $y$ modulo $\mathfrak{m}$, `transposedMove` $y$ is the transposed lift from forms at $(a, b + 1)$ to forms at $(a, b)$, with the characters $\mathrm{gridChar}(\vartheta, \lnot z, b)$, the polynomial `gridHarmonic` and $\Psi = \delta_y$. The map `liftMove` $y$ is the lift from $(a, b)$ to $(a + 1, b)$, with $\mathrm{gridChar}(\vartheta, z, a)$ and $\Psi = \delta_y$. The *transposed chain* from $(0, m)$ to $(0, b)$ is the identity for $b = m$, the composite $L_b \circ \mathrm{chain}(b + 1)$ for $b < m$, and $0$ for $b > m$. Here $L_b$ is the transposed lift with the inclusion matrix, times the order of $\mathrm{GL}$ modulo the triangle modulus.

Lean: `New.Data.transposedMove`, `New.Data.liftMove`, `New.Data.transposedChain` (New/Determinant/AuxiliaryForms/PathData.lean).

**Remark (Formalization).** The value $0$ of the chain for $b > m$ is a junk value.

**Lemma.** Let $k$ be an integral point of a unitary group of index type $n'$. Then $\mathrm{gridChar}(\vartheta, c, l, n)(\det(1, k)) = \chi(\det k \bmod \mathfrak{m})$, where $\chi$ is the character modulo $\mathfrak{m}$ of the tame part `gridTamePart`. If $z$ is true or $a \neq 0$, the index of the level at $(z, a, b)$ is the order of $\mathrm{GL}_n(O_E/\mathfrak{b})$.

Lean: `New.Data.gridChar_det`, `New.Data.levelIndex_eq_card_GL_untwisted` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* For the first claim use background item 5. We must show $\psi_w = 1$ for $w \nmid \mathfrak{m}$. Such a $w$ is not a chosen place and is not in $Q$. The tame part is $\omega^{l+1}$, times the tame part of $\vartheta^{l+1}$ if $c$ is true. The family $\omega$ is trivial outside the chosen places, and $\vartheta$ is tame outside $Q$. For the second claim, the level is the kernel of reduction from $\mathfrak{m}$ to $\mathfrak{b}$. Reduction of integral points is onto, so this map of groups is onto. The index of its kernel is the order of its image. $\square$

### Sums of roots of unity

**Definition.** A complex number $z$ is a *sum of at most $N$ roots of unity* if $z = \sum_{c \in s} c$ for a multiset $s$ of at most $N$ elements of finite order.

Lean: `New.IsSumOfRootsOfUnity` (New/Determinant/AuxiliaryForms/PathData.lean).

**Lemma.** $0$ is such a sum for every $N$, and a root of unity is such a sum for $N = 1$. The property is monotone in $N$ and stable under multiplication by a root of unity. If each $f(x)$, $x \in X$, is a sum of at most $N$ roots of unity, then $\sum_x f(x)$ is a sum of at most $|X| N$. If $z$ is a sum of at most $N$ roots of unity, $0 \in A$ and $c a \in A$ for every root of unity $c$, then $z a \in N \cdot A$, the set of sums of $N$ elements of $A$.

Lean: `New.IsSumOfRootsOfUnity.sum`, `New.IsSumOfRootsOfUnity.mul_mem_nsmul` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* Take $s = \emptyset$ for $0$ and $s = \{u\}$ for $u$. Monotonicity is clear. For $u z$ take the image of $s$ under $c \mapsto u c$; a product of elements of finite order has finite order. For the sum, choose $s_x$ for each $x$ and take their sum, which has size at most $|X| N$. For the last claim, induction on $s$ gives $(\sum s)\, a \in |s| \cdot A$: the empty sum gives $0$, and the step adds $c a \in A$. Since $0 \in A$, $|s| \cdot A \subseteq N \cdot A$. $\square$

### Edge tuples and path data

**Definition.** An *edge tuple* $S$ is a matrix $S(p, q)$ modulo $\mathfrak{m}$ for each pair of nodes, of size $|q| \times |p|$. A *node family* $g$ is an element $g(p) \in \mathrm{GL}(O_E/\mathfrak{m})$ for each node. It acts by $(g \cdot S)(p, q) = g(q)^{-1} S(p, q)\, g(p)$. It is *admissible* if $g(z, 0, m)$ is in the level of $(z, 0, m)$ for both $z$, and $g(\mathrm{true}, a, a) = g(\mathrm{false}, a, a) \oplus 1$ for all $a$. An edge from $p$ to $q$ is *vertical* if $p_1$ holds exactly when the first index changes. Its character `edgeChar` is the character modulo $\mathfrak{m}$ of `gridTamePart`, with the twist exactly when the edge is vertical. For a set $w$ of edges, $\mathrm{tuples}(w)$ is the set of tuples that vanish outside $w$, and $\varepsilon(g, w) = \prod_{(p, q) \in w} \chi_{(p,q)}(\det g(q) / \det g(p))$.

Lean: `New.Data.EdgeTuple`, `New.Data.tupleAction`, `New.Data.edgeCharProd` (New/Determinant/AuxiliaryForms/PathData.lean).

**Definition.** $\Psi$ is a *path datum* for $N$ and $w$ if:

1. $\Psi(S)$ depends only on the $S(e)$ with $e \in w$;
2. $\varepsilon(g, w)\, \Psi(g \cdot S) = \Psi(S)$ for every admissible $g$ and every $S$;
3. if $\Psi(S) \neq 0$, then $S(e)$ has a left inverse for every vertical $e \in w$;
4. every $\Psi(S)$ is a sum of at most $N$ roots of unity.

Lean: `New.Data.IsPathDatum` (New/Determinant/AuxiliaryForms/PathData.lean).

**Lemma.** Let $e \notin w$. Then $\sum_{S \in \mathrm{tuples}(w \cup \{e\})} F(S) = \sum_{S \in \mathrm{tuples}(w)} \sum_y F(S[e \mapsto y])$, where $y$ runs over all matrices at $e$. For every node family $g$, $\sum_{S \in \mathrm{tuples}(w)} F(g \cdot S) = \sum_{S \in \mathrm{tuples}(w)} F(S)$. If $\Psi$ is a path datum for $w$ and $g$ is admissible, then $\sum_S \Psi(S) f(g \cdot S) = \varepsilon(g, w) \sum_S \Psi(S) f(S)$.

Lean: `New.Data.sum_tuplesOn_insert`, `New.Data.sum_tuplesOn_tupleAction`, `New.Data.IsPathDatum.sum_tupleAction` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* The map $S \mapsto (S[e \mapsto 0], S(e))$ is a bijection from $\mathrm{tuples}(w \cup \{e\})$ to $\mathrm{tuples}(w) \times \{y\}$, with inverse $(S, y) \mapsto S[e \mapsto y]$. This gives the first claim. The action is a right action: $(g g') \cdot S = g' \cdot (g \cdot S)$ and $1 \cdot S = S$, by associativity of the matrix product. It keeps $\mathrm{tuples}(w)$, since $g(q)^{-1}\, 0\, g(p) = 0$. So $S \mapsto g \cdot S$ is a bijection of $\mathrm{tuples}(w)$ with inverse $S \mapsto g^{-1} \cdot S$. For the last claim, the second claim moves $S$ to $g \cdot S$ in $\Psi(S) f(g \cdot S)$. Condition 2 gives $\Psi(S) = \varepsilon(g, w) \Psi(g \cdot S)$. $\square$

**Lemma.** If both ends of every edge in $w$ have indices at most $(m, m)$, then $|\mathrm{tuples}(w)| \leq B^{|w|}$, with $B = |O_E/\mathfrak{m}|^{(2 n_m)^2}$.

Lean: `New.Data.card_tuplesOn_le` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* $\mathrm{tuples}(w)$ is the image of the product over $e \in w$ of the matrices at $e$. A node with indices at most $m$ has rank at most $2 n_m$, so there are at most $B$ matrices at each edge. $\square$

### Paths, maps and periods

**Definition.** The *edges* of a grid path in grid $z$ are defined by recursion: $\mathrm{nil}$ has none; $p.\mathrm{down}$ to $(a, b)$ adds the edge from $(z, a, b)$ to $(z, a, b + 1)$; $p.\mathrm{right}$ from $(a, b)$ adds the edge from $(z, a, b)$ to $(z, a + 1, b)$. For an edge tuple $S$, the *form map* is the identity on $\mathrm{nil}$, $\mathrm{transposedMove}(S(e)) \circ \mathrm{formMap}(p)$ on $p.\mathrm{down}$, and $\mathrm{liftMove}(S(e)) \circ \mathrm{formMap}(p)$ on $p.\mathrm{right}$, where $e$ is the added edge. The edges of a two-grid path $\Gamma$ are the union of the edges of its two halves.

Lean: `New.GridPath.formMap` (New/Determinant/AuxiliaryForms/PathData.lean).

**Lemma.** The edges and the form map of $p \cdot q$ are the union of the edges and the composite $\mathrm{formMap}(q) \circ \mathrm{formMap}(p)$. The form map depends only on $S$ on the edges of the path. Every edge $(u, v)$ of a path from $(a_0, b_0)$ to $(a, b)$ in grid $z$ has $u_1 = v_1 = z$ and $(a_0, b) \leq u_2 \leq v_2 \leq (a, b_0)$. The path has at most $(a - a_0) + (b_0 - b)$ edges. A two-grid path of size $m$ has at most $B^{2m}$ tuples on its edges.

Lean: `New.GridPath.formMap_append`, `New.GridPath.card_edges_le`, `New.Data.card_tuplesOn_edges_le` (New/Determinant/AuxiliaryForms/PathData.lean).

*Proof.* The first four claims hold by induction on the path. For the bounds of an edge, the last step is bounded by `GridPath.le_and_le`, and an earlier edge by the claim for the shorter path. For the last claim, each half goes from $(0, m)$ to $(l, l)$ and so has at most $l + (m - l) = m$ edges. The union has at most $2m$. Every edge of a half has ends at most $(l, m) \leq (m, m)$, so the previous lemma applies. $\square$

**Definition.** Let $\Gamma$ have diagonal index $l$ and let $g$ be a real point of $U(\tilde Y^l_l)$. The diagonal pairing takes a conjugate form $y$ on $Y^l_l$ and a form $\varphi$ on $\tilde Y^l_l$ to the period pairing along $x \mapsto (x, 1, \sigma^l)$, after translation by $g$. Here $\sigma$ is `flipScalar`, the finite idele $\bar u / u$. A *period triple* is a twist $\vartheta$, a conjugate form $y'$ on $Y_m$ and a form $\varphi$ on $\tilde Y^m_0$. For a family $\Psi_\vartheta$ of functions on edge tuples, the *period* is

$$I(\Psi; g)(\vartheta, y', \varphi) = \sum_{S \in \mathrm{tuples}(\Gamma)} \Psi_\vartheta(S)\, \langle \mathrm{formMap}_{\mathrm{false}}(S)\, y', \mathrm{formMap}_{\mathrm{true}}(S)\, \varphi \rangle_g.$$

$\Psi$ is *proportional* to $\Xi$ on $\Gamma$ if for every $g$ there is $\beta \in \mathbb{C}$ with $I(\Psi; g)(x) = \beta\, \Xi(x)$ for every period triple $x$.

Lean: `New.Data.gridPeriod`, `New.Data.IsProportional` (New/Determinant/AuxiliaryForms/PathData.lean).

**Remark (Formalization).** The constant $\beta$ may be $0$, and it may depend on $g$. So $\Psi \propto \Xi$ holds for $\Psi = 0$ and every $\Xi$. The levels of $y'$ and $\varphi$ are not fixed in a period triple.
