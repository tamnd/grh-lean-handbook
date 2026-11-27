---
title: Grid paths and turns
lean:
  - New/Determinant/AuxiliaryForms/GridPaths.lean
decls:
  - New.GridPath
  - New.GridPath.append
  - New.GridPath.column
  - New.GridPath.row
  - New.GridPath.squares
  - New.GridPath.le_and_le
  - New.GridPath.eq_row
  - New.GridPath.squares_append
  - New.GridPath.bounds_of_mem_squares
  - New.GridPath.squares_row
  - New.GridPath.notMem_squares_down_right_append
  - New.GridPath.squares_right_down_append
  - New.GridPath.exists_corner_or_eq_down_or_eq
  - New.TwoGridPath
  - New.TwoGridPath.first
  - New.TwoGridPath.last
  - New.TwoGridPath.Turn
  - New.TwoGridPath.squares
  - New.TwoGridPath.mem_squares
  - New.TwoGridPath.squares_subset
  - New.TwoGridPath.squares_first
  - New.TwoGridPath.squares_last
  - New.TwoGridPath.Turn.squares_eq
  - New.TwoGridPath.Turn.mem_product
  - New.TwoGridPath.Turn.exists_corner_of_lt
  - New.TwoGridPath.Turn.exists_half_true_eq_of_gt
  - New.TwoGridPath.Turn.exists_eq_down_and_eq_right
  - New.TwoGridPath.exists_turn
  - New.TwoGridPath.turn_induction
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Grid paths and turns

Later chapters move forms through two square grids of unitary groups, the grid of the spaces $Y^i_j$ and the grid of the spaces $\tilde Y^i_j$. This section has only the indices. It is pure combinatorics, and all proofs are inductions on paths.

A path goes from $(m, 0)$ to $(0, m)$ by steps up ($j$ grows) or left ($i$ falls). It meets the diagonal once, at a node $(l, l)$. Its first half lies in the grid of the $\tilde Y$ and its second half in the grid of the $Y$. The source records both halves in one shape: as paths from $(0, m)$ to $(l, l)$ by steps down or right. The half in the grid of the $Y$ is read backwards. The half in the grid of the $\tilde Y$ is read forwards with the two indices exchanged, so a step left is a step down and a step up is a step right.

### Paths in one grid

**Definition.** A *grid path* from $(a_0, b_0)$ to $(a, b)$ is one of these: the empty path $\mathrm{nil}$ from $(a_0, b_0)$ to itself; a path $p$ to $(a, b + 1)$ followed by a step down, written $p.\mathrm{down}$, to $(a, b)$; a path $p$ to $(a, b)$ followed by a step right, written $p.\mathrm{right}$, to $(a + 1, b)$. The concatenation $p \cdot q$ of a path $p$ to $(a, b)$ and a path $q$ from $(a, b)$ is defined by recursion on $q$. The *column* is the path from $(0, m)$ down to $(0, b)$ for $b \leq m$. The *row* $\mathrm{row}(m, a)$ is the path from $(0, m)$ right to $(a, m)$.

Lean: `New.GridPath`, `New.GridPath.append`, `New.GridPath.column`, `New.GridPath.row` (New/Determinant/AuxiliaryForms/GridPaths.lean).

The column to $(0, m)$ is $\mathrm{nil}$, and for $b < m$ the column to $(0, b)$ is the column to $(0, b + 1)$ followed by a step down (`column_self`, `column_of_lt`). Both hold by the defining equations of the decreasing induction.

**Definition.** The *squares* of a grid path are the unit squares between the first column and the steps down of the path. A square is named by its corner with the least indices. A step down from $(a, b + 1)$ to $(a, b)$ contributes the squares $(i, b)$ with $i < a$. A step right contributes nothing.

Lean: `New.GridPath.squares` (New/Determinant/AuxiliaryForms/GridPaths.lean).

**Lemma.** Let $p$ be a grid path from $(a_0, b_0)$ to $(a, b)$.

1. $a_0 \leq a$ and $b \leq b_0$.
2. If $a_0 = 0$ and $b = b_0 = m$, then $p = \mathrm{row}(m, a)$.
3. The squares of $p \cdot q$ are the union of those of $p$ and those of $q$.
4. A square $(i, j)$ of $p$ satisfies $i < a$, $b \leq j$ and $j < b_0$.
5. The row has no squares.

Lean: `New.GridPath.le_and_le`, `New.GridPath.eq_row`, `New.GridPath.squares_append`, `New.GridPath.bounds_of_mem_squares`, `New.GridPath.squares_row` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* Claims 1, 3, 4 and 5 hold by induction on the path; each step changes one index by one. For claim 2, a path from $(0, m)$ to a node $(k, m + 1)$ cannot exist by claim 1. So $p$ has no step down. Induction on $a$: for $a = 0$ the path is $\mathrm{nil}$, and for $a + 1$ it is $q.\mathrm{right}$ with $q = \mathrm{row}(m, a)$ by induction. $\square$

**Lemma (Corners).** Let $q$ be a path to $(i, j + 1)$ and $r$ a path from $(i + 1, j)$.

1. $(i, j)$ is not a square of $q.\mathrm{down}.\mathrm{right} \cdot r$.
2. The squares of $q.\mathrm{right}.\mathrm{down} \cdot r$ are those of $q.\mathrm{down}.\mathrm{right} \cdot r$ with $(i, j)$ added.

Lean: `New.GridPath.notMem_squares_down_right_append`, `New.GridPath.squares_right_down_append` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* By claim 4 of the previous lemma, a square of $q$ has first index less than $i$, and a square of $r$ has second index less than $j$. Neither is $(i, j)$. The step down from $(i, j + 1)$ gives the squares $(k, j)$ with $k < i$, and the step right gives none. This proves claim 1. In the second path the step down starts at $(i + 1, j + 1)$ and gives the squares $(k, j)$ with $k < i + 1$. That is one more square, $(i, j)$. $\square$

**Lemma.** A grid path $p$ from $(a_0, b_0)$ to $(a, b)$ has a *corner*, that is $p = q.\mathrm{down}.\mathrm{right} \cdot r$ for some $i$, $j$, $q$ to $(i, j + 1)$ and $r$ from $(i + 1, j)$; or it ends with a step down; or $b = b_0$.

Lean: `New.GridPath.exists_corner_or_eq_down_or_eq` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* Induction on $p$. The empty path has $b = b_0$. A path that ends with a step down is the second case. For $p.\mathrm{right}$, use the claim for $p$. A corner of $p$ is a corner of $p.\mathrm{right}$, with $r$ extended by the step. If $p = q.\mathrm{down}$, then $p.\mathrm{right}$ has a corner with $r = \mathrm{nil}$. If $b = b_0$, this stays true. $\square$

### Paths through two grids

**Definition.** A *two-grid path* of size $m$ is a number $l$, the *diagonal index*, and two grid paths $\mathrm{half}(z)$ from $(0, m)$ to $(l, l)$, for $z \in \{\mathrm{false}, \mathrm{true}\}$. Here $\mathrm{half}(\mathrm{false})$ is the half in the grid of the $Y$, where $(a, b)$ is $Y^a_b$. The half $\mathrm{half}(\mathrm{true})$ lies in the grid of the $\tilde Y$, where $(a, b)$ is $\tilde Y^b_a$. The *first* path has $l = 0$ and both halves equal to the column. The *last* path has $l = m$ and both halves equal to $\mathrm{row}(m, m)$.

Lean: `New.TwoGridPath`, `New.TwoGridPath.first`, `New.TwoGridPath.last` (New/Determinant/AuxiliaryForms/GridPaths.lean).

**Definition (Turn).** A *turn* at $s$ from $\Gamma$ to $\Gamma'$ is one of these.

1. *Inner turn.* For some $z$, $\mathrm{half}_\Gamma(z) = q.\mathrm{down}.\mathrm{right} \cdot r$ with $q$ to $(a, b + 1)$ and $r$ from $(a + 1, b)$. Then $\Gamma'$ has the same diagonal index, the same other half, and $\mathrm{half}_{\Gamma'}(z) = q.\mathrm{right}.\mathrm{down} \cdot r$. The node is $s = (a, b)$ if $z = \mathrm{false}$ and $s = (b, a)$ if $z = \mathrm{true}$.
2. *Diagonal turn.* $\Gamma$ has diagonal index $j$ and halves $q(z).\mathrm{down}$ with $q(z)$ to $(j, j + 1)$. Then $\Gamma'$ has diagonal index $j + 1$ and halves $q(z).\mathrm{right}$. The node is $s = (j, j)$.

In both cases the node $(i, j)$ of the path is replaced by $(i + 1, j + 1)$.

Lean: `New.TwoGridPath.Turn` (New/Determinant/AuxiliaryForms/GridPaths.lean).

**Definition.** The *squares* of a two-grid path $\Gamma$ with diagonal index $l$ are the pairs $(i, j)$ with $i, j < l$, the squares of $\mathrm{half}(\mathrm{false})$, and the mirror images $(j, i)$ of the squares $(i, j)$ of $\mathrm{half}(\mathrm{true})$. So $s$ is a square of $\Gamma$ if and only if $s_1, s_2 < l$, or $s$ is a square of $\mathrm{half}(\mathrm{false})$, or its mirror image is a square of $\mathrm{half}(\mathrm{true})$.

Lean: `New.TwoGridPath.squares`, `New.TwoGridPath.mem_squares` (New/Determinant/AuxiliaryForms/GridPaths.lean).

**Lemma.** Let $\Gamma$ be a two-grid path of size $m$.

1. Its diagonal index is at most $m$, and its squares lie in $\{0, \ldots, m - 1\}^2$.
2. The first path has no squares. The squares of the last path are all of $\{0, \ldots, m - 1\}^2$.

Lean: `New.TwoGridPath.squares_subset`, `New.TwoGridPath.squares_first`, `New.TwoGridPath.squares_last` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* The bound $l \leq m$ is claim 1 of the first lemma for $\mathrm{half}(\mathrm{false})$. The bounds of claim 4 of that lemma give the rest of claim 1. The first path has $l = 0$, and its halves have squares with first index below $0$, so none. The last path has $l = m$, and the rows have no squares. $\square$

**Lemma.** Let $\Gamma$ turn at $s$ into $\Gamma'$.

1. $s$ is not a square of $\Gamma$, and the squares of $\Gamma'$ are those of $\Gamma$ with $s$ added. So $s \in \{0, \ldots, m - 1\}^2$.
2. If $s = (i, j)$ with $i < j$, the turn is inner in $\mathrm{half}(\mathrm{false})$: $\mathrm{half}_\Gamma(\mathrm{false}) = q.\mathrm{down}.\mathrm{right} \cdot r$ with $q$ to $(i, j + 1)$, and $\Gamma'$ has this half replaced by $q.\mathrm{right}.\mathrm{down} \cdot r$.
3. If $j < i$, the turn is inner in $\mathrm{half}(\mathrm{true})$, in the same form with $q$ to $(j, i + 1)$.
4. If $s = (j, j)$, the turn is diagonal.

Lean: `New.TwoGridPath.Turn.squares_eq`, `New.TwoGridPath.Turn.mem_product`, `New.TwoGridPath.Turn.exists_corner_of_lt`, `New.TwoGridPath.Turn.exists_half_true_eq_of_gt`, `New.TwoGridPath.Turn.exists_eq_down_and_eq_right` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* For an inner turn at the corner $(a, b)$ of $\mathrm{half}(z)$, the path $r$ goes from $(a + 1, b)$ to $(l, l)$, so $a < l \leq b$. By the corner lemma, $(a, b)$ is not a square of $\mathrm{half}(z)$, and the new half gains exactly this square. The pair $(a, b)$ is not a square of the other half and not in the block $l \times l$, since $b \geq l$. Mirror images give the case $z = \mathrm{true}$. For a diagonal turn, a square of $q(z).\mathrm{down}$ has first index less than $j$, so $(j, j)$ is not one. The new block $(j + 1) \times (j + 1)$ is the old block, the strip $(k, j)$ for $k < j$, its mirror image, and $(j, j)$. The step down of each old half gave exactly these strips. So the squares gain $(j, j)$. The last part of claim 1 follows from the previous lemma applied to $\Gamma'$.

For claims 2 to 4: an inner turn has $a < l \leq b$, so the node is $(a, b)$ with $a < b$ for $z = \mathrm{false}$ and $(b, a)$ with $b > a$ for $z = \mathrm{true}$. A diagonal turn has node $(j, j)$. So the order of the two indices of $s$ fixes the kind of the turn. $\square$

**Lemma.** Every two-grid path $\Gamma$ other than the last one has a turn.

Lean: `New.TwoGridPath.exists_turn` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* If some half has a corner, there is an inner turn. Assume that neither half has a corner. If $l = m$, then both halves go from $(0, m)$ to $(m, m)$, so both are $\mathrm{row}(m, m)$ by claim 2 of the first lemma, and $\Gamma$ is the last path. Otherwise $l \neq m$. By the corner lemma each half ends with a step down: $\mathrm{half}(z) = q(z).\mathrm{down}$. Then there is a diagonal turn at $(l, l)$. $\square$

**Remark (Formalization).** The proof picks the paths $q(z)$ with `choose`. This choice is only used to build the turn. The statement is an existence statement.

**Theorem (Turn induction).** Let $M(\Gamma, T)$ be a property of a two-grid path $\Gamma$ and a finite set $T$ of pairs. Assume that $M(\mathrm{last}, \emptyset)$ holds. Assume that for every turn at $s$ from $\Gamma$ to $\Gamma'$ and every $T$ with $s \notin T$, $M(\Gamma', T)$ implies $M(\Gamma, T \cup \{s\})$. Then $M(\mathrm{first}, \{0, \ldots, m - 1\}^2)$ holds.

Lean: `New.TwoGridPath.turn_induction` (New/Determinant/AuxiliaryForms/GridPaths.lean).

*Proof.* Let $Q = \{0, \ldots, m - 1\}^2$. We prove $M(\Gamma, Q \setminus \mathrm{sq}(\Gamma))$ for every $\Gamma$, by strong induction on $k = |Q \setminus \mathrm{sq}(\Gamma)|$. The case of the first path is the claim, since it has no squares. If $\Gamma$ is the last path, then $Q \setminus \mathrm{sq}(\Gamma) = \emptyset$, and this is the first hypothesis. Otherwise take a turn at $s$ from $\Gamma$ to $\Gamma'$. Then $s \in Q$, $s \notin \mathrm{sq}(\Gamma)$, and $\mathrm{sq}(\Gamma') = \mathrm{sq}(\Gamma) \cup \{s\}$. So $Q \setminus \mathrm{sq}(\Gamma) = (Q \setminus \mathrm{sq}(\Gamma')) \cup \{s\}$, and $s \notin Q \setminus \mathrm{sq}(\Gamma')$. The set for $\Gamma'$ has $k - 1$ elements. Induction gives $M(\Gamma', Q \setminus \mathrm{sq}(\Gamma'))$, and the second hypothesis gives $M(\Gamma, Q \setminus \mathrm{sq}(\Gamma))$. $\square$

In the source, [DiagonalTurns.lean](lean:New/Determinant/AuxiliaryForms/DiagonalTurns.lean#L663) applies this induction. There $M(\Gamma, T)$ says that periods transfer from $\Gamma$ to the last path with the product over $T$ of the constants of single turns. The chapter [grids, columns and turns](/chapter/grids-paths-turns/) gives the details.

**Remark (Formalization).** Here, as in GridPaths.lean, a turn goes from the old path $\Gamma$ to the new path $\Gamma'$. Turns.lean and DiagonalTurns.lean write `Γ'.Turn s Γ`, with $\Gamma'$ the old path.
