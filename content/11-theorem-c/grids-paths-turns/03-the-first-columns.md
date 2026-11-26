---
title: The first columns
lean:
  - New/Determinant/AuxiliaryForms/GridFirstColumns.lean
decls:
  - New.Data.finMean_isUnit_indicator
  - New.Data.disjoint_edges_column
  - New.Data.exists_triangleGLCard_eq_mul_levelIndex
  - New.Data.diagonalPeriodForm_formRep
  - New.Data.formRep_block_one_eq_self
  - New.Data.gridKernel_zero_true_eq_star
  - New.Data.exists_petersson_eq_diagonalPeriodForm
  - New.Data.formRep_formMap_column_tupleAction
  - New.Data.diagonalPeriodForm_tupleAction
  - New.Data.sum_tuplesOn_union
  - New.Data.edges_column
  - New.Data.mem_edges_first
  - New.Data.edgePointDatum
  - New.Data.columnPointDatum
  - New.Data.firstPointDatum
  - New.Data.columnPointDatum_congr
  - New.Data.isSumOfRootsOfUnity_firstPointDatum
  - New.Data.hasLeftInv_of_edgePointDatum_ne_zero
  - New.Data.pointTransposedLift_eq_sum
  - New.Data.transposedChain_eq_sum
  - New.Data.transposedChain_one_true_eq_transposedChain
  - New.Data.pairing_transposedChain_eq_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---

## The first columns

The first path goes down the column $a = 0$ of both grids. Its spaces are $Y_m, \ldots, Y_0$ and $\tilde Y^m_0, \ldots, \tilde Y^0_0 = Y_0 \oplus E\tilde e_0$. A conjugate form $y'$ on $Y_m$ and a form $\varphi$ on $\tilde Y^m_0$ move down the columns by the transposed chains and meet on $\tilde Y^0_0$. This section writes their period as a constant times the period $I(\Psi^0)$ of one path datum $\Psi^0$. All results are in [GridFirstColumns.lean](lean:New/Determinant/AuxiliaryForms/GridFirstColumns.lean), in the namespace `New.Data`.

```text
  grid of the Y (conj. forms)      grid of the Ytilde (forms)
  Y_m     y'                       Ytilde^m_0     phi
   |  L_{m-1}, twist theta           |  L_{m-1}, twist 1
   v                                 v
  ...                               ...
   |  L_0                            |  L_0
   v                                 v
  Y_0  ------ diagonal period -----> Ytilde^0_0 = Y_0 + line
```

### Results used

1. The transposed lift $L_b$ from $(z, 0, b + 1)$ to $(z, 0, b)$ is `pointTransposedLift`: the transposed lift with the indicator of the inclusion matrix modulo the triangle modulus $\mathfrak{t}_z$, times $n_z(b) = $ `triangleGLCard` $z$ $\vartheta$ $b$, the order of $\mathrm{GL}$ of the node modulo $\mathfrak{t}_z$. Here $\mathfrak{t}_{\mathrm{false}} = \mathfrak{m}_0 = \varpi Q$ and $\mathfrak{t}_{\mathrm{true}} = \mathfrak{b}$. The chain $\mathrm{chain}_z(b)$ composes them ([path data and periods](/chapter/seesaw-squares/#path-data-and-periods)).
2. The period $I(\Psi; g)$ of a path, the moves `transposedMove`, the edge tuples, the action of node families, the characters $\varepsilon(g, w)$ and the path data are in the same section. The diagonal pairing at the index $0$ is `diagonalPeriodForm`.
3. The Weil representation moves translations from the datum of a transposed lift to its two forms: for $k$ and $u$ integral with reductions $\bar k$, $\bar u$, translating the image of $\mathrm{transposedMove}(\bar k^{-1} y \bar u)$ by $k$ gives the character of the edge at $\det \bar u / \det \bar k$ times $\mathrm{transposedMove}(y)$ of the translate by $u$ (`New.IsArrow.formRep_formLift_of_eq_smul`, [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows)).
4. The integral over $\Gamma \backslash G$ of a continuous left $\Gamma$-invariant function does not change under right translation by a finite point (`New.Space.integral_comp_mul_right`). The spaces of cusp forms of a fixed level are finite dimensional ([cuspidality and finite dimension](/chapter/automorphic-forms/#cuspidality-and-finite-dimension)).

### Two counting facts

**Lemma.** For a finite commutative ring $R$, the mean over the $n \times n$ matrices of the indicator of the invertible ones is $|\mathrm{GL}_n(R)| / |R|^{n^2}$.

Lean: `New.Data.finMean_isUnit_indicator` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* There are $|R|^{n^2}$ matrices, and the invertible ones are in bijection with $\mathrm{GL}_n(R)$. $\square$

**Lemma.** Reduction from $O_E/\mathfrak{m}$ to $O_E/\mathfrak{m}_0$ is a local homomorphism. For each $j$ there is $C_j \in \mathbb{C}$, the same for all twists, with
$$n_{\mathrm{false}}(j) = C_j \cdot [\mathrm{GL}(Y_j) : \mathrm{nodeLevel}(\mathrm{false}, 0, j)].$$

Lean: `New.Data.exists_triangleGLCard_eq_mul_levelIndex` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* The two moduli $\mathfrak{m} = \varpi^{b_0} Q$ and $\mathfrak{m}_0 = \varpi Q$ have the same primes. An element that is a unit modulo an ideal $I$ is a unit modulo $I^{b_0}$, and $\mathfrak{m} \supseteq \mathfrak{m}_0^{b_0}$. So an element is a unit modulo $\mathfrak{m}$ if its reduction modulo $\mathfrak{m}_0$ is a unit. This is the local property. Let $r$ be the rank of $Y_j$, $R = O_E/\mathfrak{m}$ and $R_0 = O_E/\mathfrak{m}_0$. The level at $(\mathrm{false}, 0, j)$ is trivial, so its index is $|\mathrm{GL}_r(R)|$. Reduction $\pi \colon M_r(R) \to M_r(R_0)$ is onto, and every fiber has the same size. A matrix is invertible if and only if its determinant is a unit. Since the reduction is local, $x$ is invertible exactly when $\pi(x)$ is. So the mean of the indicator of invertibility over $M_r(R)$ equals that over $M_r(R_0)$. By the previous lemma,
$$\frac{n_{\mathrm{false}}(j)}{|R_0|^{r^2}} = \frac{|\mathrm{GL}_r(R)|}{|R|^{r^2}}.$$
The norms are multiplicative, so $|R_0| / |R| = |O_E/\varpi| / |O_E/\varpi^{b_0}|$, and the factor $\mathrm{Nm}\, Q$ cancels. Put $C_j = (|O_E/\varpi| / |O_E/\varpi^{b_0}|)^{r^2}$. $\square$

### Translations of the period on the diagonal

**Lemma.** Let $u$ be a finite adelic point of $U(Y^j_j)$. Translate a conjugate form $y$ on $Y^j_j$ by $u$ and a form $\varphi$ on $\tilde Y^j_j$ by the block matrix $\mathrm{diag}(u, 1)$. The diagonal pairing at the real point $g$ does not change.

Lean: `New.Data.diagonalPeriodForm_formRep` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* Let $\iota(x) = (x, 1, \sigma^j)$ be the comparison map, with $\sigma$ the flip scalar. The pairing is the integral over $\Gamma \backslash U(Y^j_j)$ of $F(x) = y(x)\,\varphi(\iota(x) g)$. If $\gamma$ is rational, then $\iota(\gamma x) = \gamma'\iota(x)$ with $\gamma' = \gamma \oplus 1$ rational, so $F$ is left $\Gamma$-invariant. It is continuous. Also $\iota(x u) = \iota(x) \cdot \mathrm{diag}(u, 1)$ at the finite places. So after the two translations the integrand is $x \mapsto F(x u)$. By item 4 its integral is that of $F$. $\square$

**Lemma.** A form $\varphi$ on $\tilde Y^0_0$ of principal level $\mathfrak{b}$ is fixed by $\mathrm{diag}(u, 1)$ for every $u$ on $Y_0$ of principal level $\mathfrak{b}$. The kernel of the conjugate forms on $Y^0_0$ is the complex conjugate of the kernel of the forms on $Y^0_0$.

Lean: `New.Data.formRep_block_one_eq_self`, `New.Data.gridKernel_zero_true_eq_star` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* The block matrix is in the standard level, and its entries are those of $u$ on the block of $Y_0$ and those of the identity elsewhere. So it is congruent to $1$ modulo $\mathfrak{b}$. The second claim is part of the conjugate kernel pair of item 2. $\square$

**Proposition.** Let $g$ be a real point of $U(\tilde Y^0_0)$. There is a linear map $R_g$ from the forms on $\tilde Y^0_0$ of level $\mathfrak{b}$ to the forms on $Y_0$ of level $J_M$ (the chosen level), such that for every twist $\vartheta$, every $\varphi$ and every form $y$ on $Y_0$ of level $\mathfrak{m}_0$,
$$\langle y, R_g \varphi \rangle_{\mathrm{Pet}} = \mathrm{diag}_g(\bar y, \varphi).$$

Lean: `New.Data.exists_petersson_eq_diagonalPeriodForm` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* The space $V$ of forms on $Y_0$ of level $J_M$ is finite dimensional (item 4), since the kernel is cuspidal. For fixed $\varphi$ the map $y \mapsto \overline{\mathrm{diag}_g(\bar y, \varphi)}$ (at the trivial twist) is linear on $V$. Let $R_g \varphi$ be its Riesz representative, the value at $1$ of its adjoint. Then $\langle R_g\varphi, y\rangle = \overline{\mathrm{diag}_g(\bar y, \varphi)}$ for $y \in V$. Now let $y$ have level $\mathfrak{m}_0$ and let $\bar y_J$ be its mean over $J_M$, which lies in $V$. Both sides of the claim are constant on the $J_M$-translates of $y$. For the left side: $R_g\varphi$ is fixed by $J_M$, and the Petersson product is invariant. For the right side: take $u \in J_M$. Choose $v$ supported at the places of $\mathfrak{b}$ and their conjugates with $u v \equiv 1$ modulo $\mathfrak{b}$. Then $v \in J_M$, and $v$ is trivial at the places of $\vartheta$, so $v$ has level $\mathfrak{m}_0$ and fixes $y$. So the translate of $y$ by $u$ equals the translate by $u v$. The previous lemmas move $u v$ to $\mathrm{diag}(uv, 1)$ on $\varphi$, which fixes $\varphi$. So both sides at $y$ equal those at $\bar y_J$, where they agree. The diagonal pairing at $j = 0$ has the flip scalar to the power $0$, so it does not depend on the twist. $\square$

The next chapter uses this proposition.

**Lemma.** Let $g$ be a node family with $g(z, 0, m) = 1$. Let $k$ be an integral lift of $g(z, 0, b)$, with $k = 1$ if $b = m$. Then for every tuple $S$ and form $F$ at $(z, 0, m)$,
$$\rho(k)\, \mathrm{formMap}_{\mathrm{col}(b)}(g \cdot S)\, F = \varepsilon(g, \mathrm{edges}_z(\mathrm{col}(b)))\ \mathrm{formMap}_{\mathrm{col}(b)}(S)\, F.$$
If also $g(z, 0, m) = 1$ for both $z$ and $g(\mathrm{true}, 0, 0) = g(\mathrm{false}, 0, 0) \oplus 1$, then for the diagonal pairing at every real point $g_\infty$,
$$\mathrm{diag}\big(\mathrm{formMap}(g \cdot S)\,y', \mathrm{formMap}(g \cdot S)\,\varphi\big) = \varepsilon(g, \mathrm{first})\ \mathrm{diag}\big(\mathrm{formMap}(S)\,y', \mathrm{formMap}(S)\,\varphi\big).$$

Lean: `New.Data.formRep_formMap_column_tupleAction`, `New.Data.diagonalPeriodForm_tupleAction`, `New.Data.disjoint_edges_column` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* The first claim is a descending induction on $b$. For $b = m$ both sides are $F$. For $b < m$, let $u$ be an integral lift of $g(z, 0, b + 1)$, with $u = 1$ if $b + 1 = m$. The edge $e$ from $(0, b)$ to $(0, b + 1)$ carries $(g \cdot S)(e) = g(0, b+1)^{-1} S(e)\, g(0, b)$. By item 3, $\rho(k) \circ \mathrm{transposedMove}((g\cdot S)(e))$ is $\chi_e(\det g(0, b+1)/\det g(0, b))$ times $\mathrm{transposedMove}(S(e)) \circ \rho(u)$. The induction hypothesis for $b + 1$ handles $\rho(u)$ on the rest of the column. The edge $e$ is not an edge of the shorter column, so the characters multiply to $\varepsilon$ over the longer column. For the second claim, let $u$ lift $g(\mathrm{false}, 0, 0)$. Then $\mathrm{diag}(u, 1)$ lifts $g(\mathrm{true}, 0, 0)$. Translate the two images by $u$ and $\mathrm{diag}(u, 1)$; the pairing does not change. The first claim gives the two products $\varepsilon$ over the two columns. The columns have disjoint edges, since an edge of grid $z$ starts at a node of grid $z$. So the product is $\varepsilon$ over the first path. Here $m \neq 0$, since $m = 2\varrho + 2$. $\square$

### The point data

**Definition.** The *point datum* $P_z(b)$ of the edge from $(z, 0, b)$ to $(z, 0, b + 1)$ is the function of matrices $y$ modulo $\mathfrak{m}$ that is $1$ if $y$ reduces modulo $\mathfrak{t}_z$ to the inclusion matrix and $0$ otherwise. For a tuple $S$, $P_z(b, S) = \prod_{b \leq i < m} P_z(i)(S(e_{z,i}))$, where $e_{z,i}$ is the edge from $(z, 0, i)$ to $(z, 0, i + 1)$. The *first point datum* is $\Psi^1(S) = P_{\mathrm{false}}(0, S)\, P_{\mathrm{true}}(0, S)$.

Lean: `New.Data.edgePointDatum`, `New.Data.columnPointDatum`, `New.Data.firstPointDatum` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

**Lemma.**

1. The edges of $\mathrm{col}(b)$ in grid $z$ are the $e_{z,i}$ with $b \leq i < m$. An edge is on the first path if and only if it is some $e_{z,i}$ with $i < m$.
2. A sum over $\mathrm{tuples}(w \cup w')$ for disjoint $w$, $w'$ is the double sum over $S \in \mathrm{tuples}(w)$ and $S' \in \mathrm{tuples}(w')$ of the value at the tuple equal to $S$ on $w$ and $S'$ off $w$.
3. $P_z(b, S)$ depends only on the $S(e_{z,i})$ with $b \leq i < m$. Every value of $\Psi^1$ is $0$ or $1$, so it is a sum of at most one root of unity.
4. If $P_{\mathrm{false}}(b)(y) \neq 0$, then $y$ has a left inverse modulo $\mathfrak{m}$.

Lean: `New.Data.edges_column`, `New.Data.mem_edges_first`, `New.Data.sum_tuplesOn_union`, `New.Data.columnPointDatum_congr`, `New.Data.isSumOfRootsOfUnity_firstPointDatum`, `New.Data.hasLeftInv_of_edgePointDatum_ne_zero` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* Claim 1 is a descending induction on $b$: the step adds the edge $e_{z,b}$. For claim 2, cutting a tuple into its parts on $w$ and off $w$ is a bijection with the pairs, and gluing is its inverse. For claim 4, let $J$ be the inclusion matrix modulo $\mathfrak{m}$. Then $J^T y$ reduces to $J^T J = 1$ modulo $\mathfrak{m}_0$. Since the reduction is local, $J^T y$ is invertible modulo $\mathfrak{m}$, and $(J^T y)^{-1} J^T$ is a left inverse of $y$. $\square$

**Proposition.** For $b \leq m$,
$$L_b = n_z(b) \sum_y P_z(b)(y)\ \mathrm{transposedMove}(y), \qquad \mathrm{chain}_z(b) = \Big(\prod_{b \leq i < m} n_z(i)\Big) \sum_{S \in \mathrm{tuples}(\mathrm{col}(b))} P_z(b, S)\ \mathrm{formMap}_{\mathrm{col}(b)}(S).$$
The chain in the grid of the $\tilde Y$ does not depend on the twist.

Lean: `New.Data.pointTransposedLift_eq_sum`, `New.Data.transposedChain_eq_sum`, `New.Data.transposedChain_one_true_eq_transposedChain` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* The datum of $L_b$ is the indicator of the inclusion matrix modulo $\mathfrak{t}_z$. Pulled back along the reduction from $\mathfrak{m}$, it is the function $P_z(b)$, and $P_z(b) = \sum_y P_z(b)(y)\,\delta_y$. The transposed lift is linear in its datum, and with the datum $\delta_y$ it is $\mathrm{transposedMove}(y)$. This is the first identity. The second is a descending induction on $b$. For $b = m$ both sides are the identity. For $b < m$, $\mathrm{chain}_z(b) = L_b \circ \mathrm{chain}_z(b + 1)$. Insert the first identity and the induction hypothesis. The edge $e_{z,b}$ is not in $\mathrm{col}(b + 1)$. Updating $S$ at $e_{z,b}$ multiplies $P_z(b + 1, S)$ by $P_z(b)(y)$ and does not change the form map of $\mathrm{col}(b + 1)$. The sum over $\mathrm{tuples}(\mathrm{col}(b + 1))$ and $y$ is the sum over $\mathrm{tuples}(\mathrm{col}(b))$ (`New.Data.sum_tuplesOn_insert` of [path data and periods](/chapter/seesaw-squares/#path-data-and-periods)). For the last claim: in the grid of the $\tilde Y$ the modulus $\mathfrak{t}_{\mathrm{true}} = \mathfrak{b}$ and the character $\mathrm{gridChar}(\vartheta, \mathrm{false}, b)$ do not contain $\vartheta$. So $L_b$ is the same map for all twists. $\square$

**Theorem.** Let $B$ be a bilinear form on conjugate forms on $Y_0$ and forms on $\tilde Y^0_0$. Then
$$B\big(\mathrm{chain}^{\vartheta}_{\mathrm{false}}(0)\, y', \mathrm{chain}^{1}_{\mathrm{true}}(0)\, \varphi\big) = \prod_{i < m} n_{\mathrm{false}}(i)\, n_{\mathrm{true}}(i) \sum_{S \in \mathrm{tuples}(\mathrm{first})} \Psi^1(S)\, B\big(\mathrm{formMap}(S)\, y', \mathrm{formMap}(S)\, \varphi\big).$$

Lean: `New.Data.pairing_transposedChain_eq_sum` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* Replace the chain at the trivial twist by the chain at $\vartheta$. Expand both chains by the proposition. The edges of the first path are the disjoint union of the two columns, so by item 2 of the lemma the sum over the first path is the double sum over the two columns. A glued tuple has $P_{\mathrm{false}}$ and the form map of the $Y$ from its part on the column of the $Y$, and $P_{\mathrm{true}}$ and the form map of the $\tilde Y$ from the other part. Bilinearity of $B$ gives the claim. $\square$
