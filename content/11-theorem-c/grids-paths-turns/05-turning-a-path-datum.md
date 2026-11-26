---
title: Turning a path datum
lean:
  - New/Determinant/AuxiliaryForms/Turns.lean
decls:
  - New.Data.Corner
  - New.Data.Corner.oldEdges
  - New.Data.Corner.newEdges
  - New.Data.Corner.char
  - New.Data.Corner.IsTurn
  - New.Data.Corner.oldMatrix
  - New.Data.Corner.oldColumn
  - New.Data.Corner.newMatrix
  - New.Data.Corner.newRow
  - New.Data.Corner.oldTuple
  - New.Data.Corner.newTuple
  - New.Data.Corner.columnFourier
  - New.Data.Corner.turned
  - New.Data.Corner.IsTurn.sum_tuplesOn_oldEdges
  - New.Data.Corner.IsTurn.sum_tuplesOn_newEdges
  - New.Data.Corner.IsTurn.columnFourier_congr
  - New.Data.Corner.IsTurn.columnFourier_tupleAction
  - New.Data.Corner.IsTurn.hasLeftInv_of_columnFourier_ne_zero
  - New.Data.Corner.IsTurn.newRow_tupleAction
  - New.Data.Corner.IsTurn.newMatrix_tupleAction
  - New.Data.Corner.IsTurn.areMatched_columnFourier
  - New.Data.Corner.IsTurn.turned_tupleAction
  - New.Data.Corner.IsTurn.exists_turned_eq
  - New.Data.Corner.IsTurn.hasLeftInv_of_turned_ne_zero
  - New.Data.Corner.IsTurn.isSumOfRootsOfUnity_turned
  - New.Data.Corner.IsTurn.exists_isPathDatum
  - New.Data.Corner.IsTurn.sum_eq_of_squareLaw
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Turning a path datum

A turn of a path replaces two sides of a square by the two other sides. This section is pure finite algebra. It takes a path datum $\Psi'$ on the old path and makes a path datum $\Psi$ on the new path, matched with $\Psi'$ in the sense of the square law. It then turns a sum over the old path into a sum over the new path. The same construction serves the inner turns of Section 6 and the diagonal turns of Section 7.

We use edge tuples, node families, admissible families, the characters $\varepsilon(g, w)$ and path data from [path data and periods](/chapter/seesaw-squares/#path-data-and-periods), and the square law, $\operatorname{matchOf}$ and matched functions from [the square law](/chapter/seesaw-squares/#the-square-law). All matrices are over the residue ring $R = O_E/\mathfrak{m}$, with $\mathfrak{m}$ = `gridModulus` $\vartheta$, and "matched" means matched over all of $R$.

### Corners

```text
   old path:  V' -> W1      Ṽ' -> W2
   new path:  W1 -> V       W2 -> Ṽ

        V' ---------> W1
        :              |
        :   square     |
        v              v
        W2 ---------> V

   Ṽ' = V' ⊕ T   and   Ṽ = V ⊕ T
   off the diagonal T is empty; on it T is one line
```

**Definition (Corner).** A *corner* with types $B$ and $T$ is six nodes $V'$ (`low`), $\tilde V'$ (`lowExt`), $W_1$ (`fst`), $W_2$ (`snd`), $V$ (`high`), $\tilde V$ (`highExt`), with bijections $B \simeq W_2$, $V' \sqcup T \simeq \tilde V'$ and $V \sqcup T \simeq \tilde V$ of index sets. For a set $w$ of edges, the old edges are $w \cup \{(V', W_1), (\tilde V', W_2)\}$ and the new edges are $w \cup \{(W_1, V), (W_2, \tilde V)\}$. The character of the corner is $\chi = (\chi_{(V', W_1)}\, \chi_{(\tilde V', W_2)})^{-1}$, a character of $R$.

Lean: `New.Data.Corner`, `New.Data.Corner.oldEdges`, `New.Data.Corner.newEdges`, `New.Data.Corner.char` (New/Determinant/AuxiliaryForms/Turns.lean).

**Definition (Turn).** The corner is a *turn* for $\vartheta$ and $w$ if:

1. $W_1 \neq W_2$, and $V'$, $\tilde V'$ are not among $W_1, W_2, V, \tilde V$;
2. no edge of $w$ starts at $V'$ or $\tilde V'$, and no edge of $w$ ends at $V'$, $\tilde V'$, $V$ or $\tilde V$;
3. $(V', W_1)$ is vertical and $(W_1, V)$ is not, or $(\tilde V', W_2)$ is vertical and $(W_2, \tilde V)$ is not;
4. opposite edges have the same character: $\chi_{(W_1, V)} = \chi_{(\tilde V', W_2)}$ and $\chi_{(W_2, \tilde V)} = \chi_{(V', W_1)}$;
5. for every admissible $g$, $g(\tilde V) = g(V) \oplus 1$;
6. for every admissible $g$ and every $k \in \mathrm{GL}(V')$ there is an admissible $g'$ with $g'(V') = k$, $g'(\tilde V') = k \oplus 1$, and $g' = g$ at every other node.

Lean: `New.Data.Corner.IsTurn` (New/Determinant/AuxiliaryForms/Turns.lean).

Condition 6 says that $V'$ is an inner node: the level does not restrict it. Condition 5 says that only the group of $V$ acts at $\tilde V$.

### Reading a tuple at the square

**Definition.** For an edge tuple $S$:

- $y = \mathrm{oldMatrix}(S)$ is the $(W_1 \sqcup B) \times V'$ matrix with rows $S(V', W_1)$ and the $V'$ columns of $S(\tilde V', W_2)$;
- $v = \mathrm{oldColumn}(S)$ is the $B \times T$ block of the $T$ columns of $S(\tilde V', W_2)$;
- $x = \mathrm{newMatrix}(S)$ is the $V \times (W_1 \sqcup B)$ matrix with columns $S(W_1, V)$ and the $V$ rows of $S(W_2, \tilde V)$;
- $v' = \mathrm{newRow}(S)$ is the $T \times B$ block of the $T$ rows of $S(W_2, \tilde V)$.

Conversely, $\mathrm{oldTuple}(S, y, v)$ writes $y$ and $v$ on the two old edges of the square and keeps $S$ elsewhere, and $\mathrm{newTuple}(S, x, v')$ writes $x$ and $v'$ on the two new edges.

Lean: `New.Data.Corner.oldMatrix`, `New.Data.Corner.oldColumn`, `New.Data.Corner.newMatrix`, `New.Data.Corner.newRow`, `New.Data.Corner.oldTuple`, `New.Data.Corner.newTuple` (New/Determinant/AuxiliaryForms/Turns.lean).

The two maps are inverse to each other on the square. By condition 2 they keep $S$ on $w$. Then a sum over tuples splits.

**Lemma.** For a turn and any $F$,
$$\sum_{S \in \mathrm{tuples}(\mathrm{old})} F(S) = \sum_{S \in \mathrm{tuples}(w)} \sum_y \sum_v F(\mathrm{oldTuple}(S, y, v)),$$
$$\sum_{S \in \mathrm{tuples}(\mathrm{new})} F(S) = \sum_{S \in \mathrm{tuples}(w)} \sum_{v'} \sum_x F(\mathrm{newTuple}(S, x, v')).$$

Lean: `New.Data.Corner.IsTurn.sum_tuplesOn_oldEdges`, `New.Data.Corner.IsTurn.sum_tuplesOn_newEdges` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Neither old edge is in $w$ by condition 2, and the two old edges differ since $W_1 \neq W_2$. Apply the insertion lemma of [path data and periods](/chapter/seesaw-squares/#path-data-and-periods) twice. The sum over the matrix on $(V', W_1)$ and the matrix on $(\tilde V', W_2)$ is a sum over $y_1$, then over the two column blocks $(y_2, v)$ of the second matrix after the bijections. Join $y_1$ and $y_2$ into $y$. The new edges are the same with rows and columns exchanged. $\square$

### The column Fourier transform and the turned datum

Let $\psi$ be an additive character of $R$.

**Definition.** The *column Fourier transform* of $\Psi'$ is
$$\hat\Psi'(S, v', y) = \sum_{v \in R^{B \times T}} \psi(\operatorname{tr}(v' v))\ \Psi'(\mathrm{oldTuple}(S, y, v)).$$
For $\varepsilon \colon V' \sqcup V \simeq W_1 \sqcup B$, the *turned datum* is
$$\mathrm{turned}(\Psi')(S) = \operatorname{matchOf}\bigl(\chi, \varepsilon, \hat\Psi'(S, \mathrm{newRow}(S), \cdot)\bigr)(\mathrm{newMatrix}(S)).$$

Lean: `New.Data.Corner.columnFourier`, `New.Data.Corner.turned` (New/Determinant/AuxiliaryForms/Turns.lean).

Off the diagonal $T$ is empty, so $v$ and $v'$ are empty matrices, $\psi(\operatorname{tr}) = 1$, and $\hat\Psi'(S, \cdot, y) = \Psi'(\mathrm{oldTuple}(S, y))$. Then $\mathrm{turned}$ is just the match of $\Psi'$ across the square. In the rest of the section let the corner be a turn and let $\Psi'$ be a path datum for $N$ on the old edges.

**Lemma.** $\hat\Psi'(S, \cdot, \cdot)$ depends only on $S$ on $w$. If $\hat\Psi'(S, v', y) \neq 0$, then the $W_1$ rows of $y$ have a left inverse if $(V', W_1)$ is vertical, the $B$ rows of $y$ have one if $(\tilde V', W_2)$ is vertical, and $S(e)$ has one for every vertical $e \in w$.

Lean: `New.Data.Corner.IsTurn.columnFourier_congr`, `New.Data.Corner.IsTurn.hasLeftInv_of_columnFourier_ne_zero` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* If $S = S'$ on $w$, then $\mathrm{oldTuple}(S, y, v)$ and $\mathrm{oldTuple}(S', y, v)$ agree on all old edges, and $\Psi'$ depends only on those. If the sum is not $0$, some term $\Psi'(\mathrm{oldTuple}(S, y, v)) \neq 0$. Condition 3 of a path datum gives left inverses on the vertical old edges. On $(\tilde V', W_2)$ the matrix is $(y_2\ v)$; a left inverse $L$ of it gives $L y_2 = 1$ on the $V'$ block, after we restrict $L$ to those rows. $\square$

**Lemma (Equivariance).** Let $g$ be admissible and $k \in \mathrm{GL}(V')$. Write $g_2$ for $g(W_2)$ in the basis $B$ and $\gamma_g = g(W_1) \oplus g_2$. Then
$$\chi(\det k)\, \chi_{(V', W_1)}(\det g(W_1))\, \chi_{(\tilde V', W_2)}(\det g(W_2))\, \varepsilon(g, w)\ \hat\Psi'(g \cdot S, v' g_2, \gamma_g^{-1} y k) = \hat\Psi'(S, v', y).$$

Lean: `New.Data.Corner.IsTurn.columnFourier_tupleAction` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Condition 6 gives an admissible $g'$ equal to $k$ at $V'$, to $k \oplus 1$ at $\tilde V'$ and to $g$ elsewhere. On the old edges, $\varepsilon(g', \mathrm{old})$ is the product of the four factors on the left, by the definition of $\chi$ and since the old edges have no other end at $V'$ or $\tilde V'$. A direct block computation gives $g' \cdot \mathrm{oldTuple}(S, y, v) = \mathrm{oldTuple}(g \cdot S, \gamma_g^{-1} y k, g_2^{-1} v)$ on the old edges. Substitute $v \mapsto g_2^{-1} v$ in the sum, a bijection. Then $\operatorname{tr}(v' g_2 g_2^{-1} v) = \operatorname{tr}(v' v)$, and the invariance of $\Psi'$ under $g'$ gives the claim. $\square$

**Lemma.** For admissible $g$, $\mathrm{newRow}(g \cdot S) = \mathrm{newRow}(S)\, g_2$ and $\mathrm{newMatrix}(g \cdot S) = g(V)^{-1}\, \mathrm{newMatrix}(S)\, \gamma_g$. The functions $\operatorname{matchOf}(\chi, \varepsilon, \hat\Psi'(S, v', \cdot))$ and $\hat\Psi'(S, v', \cdot)$ are matched for $\chi$.

Lean: `New.Data.Corner.IsTurn.newRow_tupleAction`, `New.Data.Corner.IsTurn.newMatrix_tupleAction`, `New.Data.Corner.IsTurn.areMatched_columnFourier` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* The first two claims are block computations with $g(\tilde V) = g(V) \oplus 1$ from condition 5. For the third claim, use the criterion `areMatched_matchOf` of [the square law](/chapter/seesaw-squares/#the-square-law). Its support condition: if $\hat\Psi'(S, v', y) \neq 0$, then by condition 3 of a turn and the previous lemma one row block of $y$ has a left inverse, so $y$ is the first columns of an invertible matrix (`exists_eq_firstCols`). Its character condition is the equivariance lemma with $g = 1$. $\square$

**Lemma.** For admissible $g$, $\varepsilon(g, \mathrm{new})\ \mathrm{turned}(\Psi')(g \cdot S) = \mathrm{turned}(\Psi')(S)$.

Lean: `New.Data.Corner.IsTurn.turned_tupleAction` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Let $H = \hat\Psi'(g \cdot S, \mathrm{newRow}(S) g_2, \cdot)$ and $\Phi = \operatorname{matchOf}(\chi, \varepsilon, H)$. Let $a = \chi_{(V', W_1)}(\det g(W_1))\, \chi_{(\tilde V', W_2)}(\det g(W_2))\, \varepsilon(g, w)$. The equivariance lemma with $k = 1$ gives $\hat\Psi'(S, \mathrm{newRow}(S), y) = a\, H(\gamma_g^{-1} y)$. A translate of a matched pair is matched, so $x \mapsto a\, \chi(\det \gamma_g)\, \Phi(x \gamma_g)$ is matched with $\hat\Psi'(S, \mathrm{newRow}(S), \cdot)$. A match is unique, so $\mathrm{turned}(\Psi')(S) = a\, \chi(\det\gamma_g)\, \Phi(\mathrm{newMatrix}(S) \gamma_g)$. On the other side, the previous lemma and left translation by $g(V)$ give $\mathrm{turned}(\Psi')(g \cdot S) = \chi(\det g(V))\, \Phi(\mathrm{newMatrix}(S) \gamma_g)$. It remains to show $\varepsilon(g, \mathrm{new})\, \chi(\det g(V)) = a\, \chi(\det \gamma_g)$. Expand both sides. Condition 4 identifies the characters of opposite edges, and condition 5 gives $\det g(\tilde V) = \det g(V)$. The two sides are then equal. $\square$

**Lemma.** If $\mathrm{turned}(\Psi')(S) \neq 0$, there is an invertible $\gamma$ with $\mathrm{newMatrix}(S) = x_\gamma$ and $\mathrm{turned}(\Psi')(S) = \chi(\det\gamma)\, \hat\Psi'(S, \mathrm{newRow}(S), y_\gamma)$. In this case $S(e)$ has a left inverse for every vertical new edge $e$. Every value of $\mathrm{turned}(\Psi')$ is a sum of at most $|R^{B \times T}|\, N$ roots of unity.

Lean: `New.Data.Corner.IsTurn.exists_turned_eq`, `New.Data.Corner.IsTurn.hasLeftInv_of_turned_ne_zero`, `New.Data.Corner.IsTurn.isSumOfRootsOfUnity_turned` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* The first claim is the support of a matched pair. For the second, $\hat\Psi'(S, \mathrm{newRow}(S), y_\gamma) \neq 0$, so the earlier lemma gives left inverses for the row blocks of $y_\gamma$ on vertical old edges and for $S$ on $w$. A row block of $y_\gamma$ has a left inverse exactly when the complementary column block of $x_\gamma$ has one (`hasLeftInv_toCols_of_hasLeftInv_toRows`). By condition 3 a vertical new edge is opposite to a vertical old edge. On $(W_2, \tilde V)$ the matrix is $(x_2; v')$, and a left inverse of $x_2$ padded by $0$ is a left inverse of it. For the third claim, $\chi(\det\gamma)$ and every $\psi(r)$ have finite order in a finite ring, and $\hat\Psi'$ is a sum of $|R^{B \times T}|$ terms, each a root of unity times a sum of at most $N$ roots of unity. $\square$

**Theorem (Turning a path datum).** Let the corner be a turn for $\vartheta$ and $w$, let $\Psi'$ be a path datum for $N$ on the old edges, and fix $\varepsilon$ and $\psi$. There is a path datum $\Psi$ for $|R^{B \times T}|\, N$ on the new edges such that for all $S$ and $v'$ the functions $x \mapsto \Psi(\mathrm{newTuple}(S, x, v'))$ and $\hat\Psi'(S, v', \cdot)$ are matched for $\chi$ and $\varepsilon$.

Lean: `New.Data.Corner.IsTurn.exists_isPathDatum` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Take $\Psi = \mathrm{turned}(\Psi')$. It depends only on the new edges: $\mathrm{newRow}$ and $\mathrm{newMatrix}$ read only the new edges of the square, and $\hat\Psi'$ depends only on $w$. The three lemmas above give conditions 2, 3 and 4 of a path datum. For the match, $\mathrm{newRow}(\mathrm{newTuple}(S, x, v')) = v'$, $\mathrm{newMatrix}(\mathrm{newTuple}(S, x, v')) = x$, and $\mathrm{newTuple}$ keeps $S$ on $w$. So $x \mapsto \Psi(\mathrm{newTuple}(S, x, v'))$ is $\operatorname{matchOf}(\chi, \varepsilon, \hat\Psi'(S, v', \cdot))$, which is matched with $\hat\Psi'(S, v', \cdot)$. $\square$

**Remark (Formalization).** $\operatorname{matchOf}$ uses a choice of $\gamma$ through `Function.extend`. The lemmas above show that the value does not depend on it. The bound $|R^{B \times T}|\, N$ is $N$ off the diagonal, where $T$ is empty.

### The sum over a square

**Theorem.** Let the corner be a turn, let $\Psi'$ be a path datum on the old edges, and let $\Psi$ satisfy the match of the theorem. Let $(L_i, L'_i)_{i \in J}$ satisfy the square law for $\chi$ and $\varepsilon$ with one constant $C$. Let $f(S, v') \in J$ depend only on $S$ on $w$. Then
$$\sum_{S \in \mathrm{tuples}(\mathrm{old})} \Psi'(S) \sum_{v'} \psi(\operatorname{tr}(v'\, \mathrm{oldColumn}(S)))\, L'_{f(S, v')}(\mathrm{oldMatrix}(S)) = C \sum_{S \in \mathrm{tuples}(\mathrm{new})} \Psi(S)\, L_{f(S, \mathrm{newRow}(S))}(\mathrm{newMatrix}(S)).$$

Lean: `New.Data.Corner.IsTurn.sum_eq_of_squareLaw` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Split both sums with the first lemma of the section. Fix $S$ on $w$. Since $f$ sees only $w$, $f(\mathrm{oldTuple}(S, y, v), v') = f(S, v')$, and the same holds for $\mathrm{newTuple}$. On the left the sums over $y$, $v$ and $v'$ commute; the sum over $v$ is $\hat\Psi'(S, v', y)$. So the left side is $\sum_{v'} \sum_y \hat\Psi'(S, v', y)\, L'_{f(S, v')}(y)$. For each $v'$ the square law, applied to the matched pair, turns $\sum_y$ into $C \sum_x \Psi(\mathrm{newTuple}(S, x, v'))\, L_{f(S, v')}(x)$. This is the right side for this $S$. $\square$

The left side is a period on the old path after the line is moved by $\psi$. The right side is a period on the new path. Sections 6 and 7 make the functions $L_i$, $L'_i$ from the two sides of a grid square.
