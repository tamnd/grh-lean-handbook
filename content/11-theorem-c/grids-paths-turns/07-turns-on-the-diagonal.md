---
title: Turns on the diagonal
lean:
  - New/Determinant/AuxiliaryForms/DiagonalTurns.lean
decls:
  - New.Data.subdiagEquiv
  - New.Data.gridSigns_subdiagEquiv
  - New.Data.gridSpace_subdiagEquiv
  - New.Data.subdiagMap
  - New.Data.reindex_subdiagMap
  - New.Data.height_subdiagMap
  - New.Data.subdiagWeight
  - New.Data.columnLineKernel
  - New.Data.columnLineKernel_weightFn
  - New.Data.rowLineKernel
  - New.Data.rowLineKernel_weightFn
  - New.Data.diagonalCorner
  - New.Data.downPath
  - New.Data.rightPath
  - New.Data.edges_downPath
  - New.Data.edges_rightPath
  - New.Data.columnPeriod
  - New.Data.rowPeriod
  - New.Data.gridChar_subdiag
  - New.Data.modKernel_eq_columnLineKernel_mul
  - New.Data.rowLineKernel_mul_modKernel
  - New.Data.isProportional_of_columnPeriod
  - New.Data.IsProportional.exists_rowPeriod_eq_mul
  - New.Data.modKernel_eq_sum_single
  - New.Data.exists_columnLineKernel_eq
  - New.Data.isTurn_diagonalCorner
  - New.Data.char_diagonalCorner
  - New.Data.card_column_le_vectorCountBound
  - New.Data.periodPairing_columnLineKernel_eq
  - New.Data.columnPeriod_eq_mul_rowPeriod
  - New.Data.exists_transfersPeriods_diagonal
  - New.Data.exists_transfersPeriods_of_turn
  - New.Data.exists_transfersPeriods_first_last
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Turns on the diagonal

A diagonal turn at $j < m$ replaces the node $(j, j)$ of both halves by $(j + 1, j + 1)$. The two grids meet on the diagonal: $\tilde Y^j_j = Y^j_j \oplus E\tilde e_j$. So the square has a line on one side, and the turn of Section 5 runs with $T$ = `Unit`. The period does not pass across the square directly. A seesaw moves it to the space $S = \tilde Y^{j+1}_j = Y^{j+1}_j$ common to both paths. There the line is reversed, the square is crossed, and a second seesaw moves the period on. The section ends with the composite of all $m^2$ turns.

We use [the seesaw for periods](/chapter/theta-lifts-seesaw/#the-seesaw-for-periods) and the theta kernels `modKernel` of [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows).

```text
  removed: V' = Y^j_j          Ṽ' = Ỹ^j_j = V' ⊕ E ẽ_j
  kept:    W1 = Y^j_(j+1)      W2 = Ỹ^(j+1)_j
  added:   V  = Y^(j+1)_(j+1)  Ṽ  = V ⊕ E ẽ_(j+1)

  old: q(false), then down;   q(true), then down
  new: q(false), then right;  q(true), then right

  common space: S = Y^(j+1)_j, the renumbering of W2
```

### The common space

**Definition.** `subdiagEquiv` is a bijection of the index sets of $\tilde Y^{j+1}_j$ and $Y^{j+1}_j$ that carries the signs of one to the signs of the other and makes $\tilde Y^{j+1}_j$ the renumbering of $Y^{j+1}_j$. The map `subdiagMap` is the induced map of groups. It is a right inverse of the renumbering and keeps heights. For a function $\theta$ of moderate growth on the group of $S$, `subdiagWeight` $\theta$ is the moderate weight $\theta \circ$ `subdiagMap` with comparison map `subdiagMap`.

Lean: `New.Data.subdiagEquiv`, `New.Data.gridSigns_subdiagEquiv`, `New.Data.gridSpace_subdiagEquiv`, `New.Data.subdiagMap`, `New.Data.reindex_subdiagMap`, `New.Data.height_subdiagMap`, `New.Data.subdiagWeight` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

**Remark (Formalization).** The bijection is taken with `choose` from `gridSpace_subdiag`. Any bijection with these properties gives the same results.

**Definition (Kernels of the line).** Let $u$ = `flipScalar` of $\mathfrak{m}$. For a column $v \in R^{S \times 1}$ and a polynomial $p$, $\theta^j_{v, p}$ (`columnLineKernel`) is the weight from the theta kernel of the pair from the line $E\tilde e_j$, of sign $(-1)^j$, to $S$. It has the point mass at $v$, the character `gridChar` $\vartheta$ false $j$ on $S$, and is taken at $u^j$ on the line. For a row $v' \in R^{1 \times S}$, $\theta^{j+1}_{v', p}$ (`rowLineKernel`) is the weight from the kernel of the pair from $S$ to the line $E\tilde e_{j+1}$, with character `gridChar` $\vartheta$ true $j$ and $\upsilon$ on the line, taken at $u^{j+1}$. Their weight functions at $g$ are these kernels at `subdiagMap` $g$.

Lean: `New.Data.columnLineKernel`, `New.Data.columnLineKernel_weightFn`, `New.Data.rowLineKernel`, `New.Data.rowLineKernel_weightFn` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

**Definition.** The *diagonal corner* has $V' = (\mathrm{false}, j, j)$, $\tilde V' = (\mathrm{true}, j, j)$, $W_1 = (\mathrm{false}, j, j + 1)$, $W_2 = (\mathrm{true}, j, j + 1)$, $V = (\mathrm{false}, j + 1, j + 1)$, $\tilde V = (\mathrm{true}, j + 1, j + 1)$, $T$ = `Unit`, $B$ the index set of $Y^{j+1}_j$, and the bijections `subdiagEquiv` and `gridDiagEquiv`. For halves $q(z)$ from $(0, m)$ to $(j, j + 1)$, `downPath` $q$ has diagonal index $j$ and halves $q(z).\mathrm{down}$, and `rightPath` $q$ has index $j + 1$ and halves $q(z).\mathrm{right}$. Their edges are the old and new edges of the diagonal corner for $w = $ the edges of $q(\mathrm{false})$ and $q(\mathrm{true})$.

Lean: `New.Data.diagonalCorner`, `New.Data.downPath`, `New.Data.rightPath`, `New.Data.edges_downPath`, `New.Data.edges_rightPath` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

### Periods on the common space

**Definition.** For $z$ in the archimedean group of $S$ and a triple $x = (\vartheta, y', \varphi)$,
$$I^S_{\mathrm{col}}(\Psi; z, p)(x) = \sum_{S \in \mathrm{tuples}(\mathrm{down})} \Psi_\vartheta(S)\ P_z\bigl(\theta^j_{\mathrm{oldColumn}(S), p};\ \mathrm{formMap}_{q(\mathrm{true})}(S)\varphi,\ \mathcal{L}(y_2)\mathcal{L}^{\mathsf T}(y_1)\, \mathrm{formMap}_{q(\mathrm{false})}(S) y'\bigr),$$
with $y = \mathrm{oldMatrix}(S)$ and $P_z$ = `periodPairing`, the integral over the group of $\tilde Y^{j+1}_j$ of the weight times the two forms, translated by $z$. $I^S_{\mathrm{row}}(\Psi; z, p)$ is the same on `rightPath` with $\theta^{j+1}_{\mathrm{newRow}(S), p}$ and $\mathcal{L}^{\mathsf T}(x_2)\mathcal{L}(x_1)$, $x = \mathrm{newMatrix}(S)$.

Lean: `New.Data.columnPeriod`, `New.Data.rowPeriod` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

**Lemma (Splitting the kernels).** The characters `gridChar` agree at $\tilde Y^{j+1}_j$ and $Y^{j+1}_j$. Since $t$ is odd:

1. The kernel of the edge $\tilde Y^j_j \to \tilde Y^{j+1}_j$ for the point mass at $X$ and the polynomial $A \cdot B$, at $(h \oplus u^j, g)$, is $\theta^j_{X_2, B}(g)$ times the kernel of the edge $Y^j_j \to S$ for $X_1$ and $A$ at $(h, \mathrm{subdiagMap}\, g)$. Here $X_1$, $X_2$ are the column blocks of $X$.
2. $\theta^{j+1}_{X_2, B}(g)$ times the kernel of the edge $S \to Y^{j+1}_{j+1}$ for $X_1$ and $A$ is the kernel of the edge $\tilde Y^{j+1}_j \to \tilde Y^{j+1}_{j+1}$ for $X$ and the product polynomial, at $(g, h \oplus u^{j+1})$. Here $X_1$, $X_2$ are the row blocks.

Lean: `New.Data.gridChar_subdiag`, `New.Data.modKernel_eq_columnLineKernel_mul`, `New.Data.rowLineKernel_mul_modKernel` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* The ranks are equal, so the characters agree. A theta kernel of an orthogonal sum is the product of the kernels (`modKernel_reindex`, `gridSpace_diag`). The point mass at $X$ is the product of the point masses at its blocks. The splitting characters of the two sides differ by the character of the line. Since $t$ is odd, the rounded half ranks give the trivial character in claim 1 and $\upsilon$ in claim 2. $\square$

**Lemma (Two seesaws).**

1. If for all $z$ and $p$ there is $\beta$ with $I^S_{\mathrm{col}}(\Psi; z, p) = \beta\, \Xi$, then $\Psi \propto \Xi$ on `downPath` $q$.
2. If $\Psi \propto \Xi$ on `rightPath` $q$, then for all $z$ and $p$ there is $\beta$ with $I^S_{\mathrm{row}}(\Psi; z, p) = \beta\, \Xi$.

Lean: `New.Data.isProportional_of_columnPeriod`, `New.Data.IsProportional.exists_rowPeriod_eq_mul` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Both are `seesaw_periods`. In claim 1 the pairs are the edge $Y^j_j \to S$ (a lift) and the edge $\tilde Y^j_j \to \tilde Y^{j+1}_j$ (a transposed lift), with the edge families `isEdgeFamily_grid_succ_left` and `_succ_right`. The theorem needs that the matched polynomials span. The variables of the second edge split into the two column blocks, and these cover all variables, so the products $A \cdot B$ span (`mem_rename_range_mul`). A product $A \cdot B$ is matched: take $A$ on the edge from $Y^j_j$, the point mass at $y_2$, and the weight $\theta^j_{\mathrm{oldColumn}(S), B}$. Claim 1 of the splitting lemma gives the matched kernels. The hypothesis gives the proportional periods. The weight of the period on the path is $1$. In claim 2 the pairs are the two edges into the diagonal node. Fix $p$. Every $A$ is matched with $A \cdot p$, the point mass at the row edge matrix, and the weight $\theta^{j+1}$, by claim 2 of the splitting lemma. The proportional periods are the hypothesis. $\square$

### Reversing the line

**Lemma.** The theta kernel is linear in its datum: for a function $\Psi$ on matrices, the kernel of $\Psi$ is $\sum_v \Psi(v)$ times the kernel of the point mass at $v$.

Lean: `New.Data.modKernel_eq_sum_single` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Write $\Psi = \sum_v \Psi(v)\, \delta_v$. The kernel is linear in the datum. $\square$

**Lemma (Reversing the line).** There are a map $\tau$ of polynomials, additive characters $\psi_\vartheta$ and units $c_{\mathrm{line}}(\vartheta)$ with $|c_{\mathrm{line}}(\vartheta)|^2\, |R^S| = 1$ such that
$$\theta^j_{v, p}(g) = c_{\mathrm{line}}(\vartheta) \sum_{v'} \psi_\vartheta(\operatorname{tr}(v' v))\ \theta^{j+1}_{v', \tau(p)}(g).$$
The map $\tau$ does not depend on $\vartheta$.

Lean: `New.Data.exists_columnLineKernel_eq` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Take $\tau$ = `flipPoly`. For each $\vartheta$ the flip of a line (`exists_modKernel_flip_line`, in [Flip.lean](lean:Lib/Weil/DualPair/Flip.lean#L579)) gives $\psi$ and $c$ with the norm condition. It says that the kernel from the line for $f$ is $c$ times the kernel to the line for the matrix Fourier transform of $f$ and $\tau(p)$. Choose these for every $\vartheta$. For $f = \delta_v$ the Fourier transform at $v'$ is $\psi(\operatorname{tr}(v' v))$. Expand with the previous lemma. $\square$

### One diagonal turn

**Lemma.** For $j < m$:

1. The diagonal corner is a turn for every $\vartheta$ and $w$.
2. Its character is $(\chi_{\mathrm{col}}\chi_{\mathrm{row}})^{-1}$ for the column and row edges at $(\mathrm{false}, j, j)$.
3. The number of columns $|R^{S \times 1}|$ is at most `vectorCountBound` $\vartheta = |O/\mathfrak{m}|^{2n_m}$.
4. If $\theta^j_{v, p} = c \sum_{v'} \psi(\operatorname{tr}(v'v))\, \theta^{j+1}_{v', p'}$, then the same identity holds for their period pairings with any $\varphi$, $y$ and $z$.

Lean: `New.Data.isTurn_diagonalCorner`, `New.Data.char_diagonalCorner`, `New.Data.card_column_le_vectorCountBound`, `New.Data.periodPairing_columnLineKernel_eq` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* 1. The edges of $q$ lie in the rectangle from $(0, m)$ to $(j, j + 1)$, so they avoid the removed nodes and do not end at the added ones. The edge $\tilde Y^j_j \to \tilde Y^{j+1}_j$ is vertical and $Y^j_j \to Y^j_{j+1}$ is not, and opposite edges have equal characters. An admissible family is $g \oplus 1$ on the diagonal, which gives condition 5. For condition 6, put $k$ at $Y^j_j$ and $k \oplus 1$ at $\tilde Y^j_j$; these are not start nodes since $j < m$. 2. The edge from $\tilde Y^j_j$ has the character of the row edge. 3. The rank of $S$ is at most $2n_m$. 4. The integrand is a finite sum. Each term is integrable by the integrability of period pairings, so the integral commutes with the sum. Both weights have the comparison map `subdiagMap`. $\square$

**Lemma.** For one triple $x$, let $\theta^j_{v, p} = c \sum_{v'} \psi(\operatorname{tr}(v' v))\, \theta^{j+1}_{v', p'}$ for every $v$. Let the square law hold for the diagonal corner with constant $C$, for every $f$ and $l$. Let $\Psi$ be matched with the column Fourier transform of $\Psi'$ for $\psi$. Then $I^S_{\mathrm{col}}(\Psi'; z, p)(x) = c\, C\, I^S_{\mathrm{row}}(\Psi; z, p')(x)$.

Lean: `New.Data.columnPeriod_eq_mul_rowPeriod` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Claim 4 above expands each column period pairing into $c \sum_{v'} \psi(\operatorname{tr}(v'\, \mathrm{oldColumn}(S)))$ times row period pairings. Take the index $f(S, v')$ = (the form $\mathrm{formMap}_{q(\mathrm{false})}(S) y'$, the functional $P_z(\theta^{j+1}_{v', p'}; \mathrm{formMap}_{q(\mathrm{true})}(S)\varphi, \cdot)$). It depends only on $S$ on $w$. The theorem on the sum over a square of Section 5 gives the factor $C$ and the row period. $\square$

**Theorem (Diagonal turns).** For $j < m$ there are units $c(\vartheta)$ with absolute value $\mathrm{turnRatio}_{jj}$ up to a norm power such that `downPath` $q$ transfers periods to `rightPath` $q$ with bound `vectorCountBound` and constant $c$, for all $q$.

Lean: `New.Data.exists_transfersPeriods_diagonal` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Take $\kappa$, $\sigma$, $c_{\mathrm{sq}}$ from the grid square theorem of Section 6 for grid false at $(j, j)$, and $\tau$, $\psi$, $c_{\mathrm{line}}$ from the reversal lemma. Put $c = c_{\mathrm{sq}}/c_{\mathrm{line}}$. Since $|c_{\mathrm{line}}^{-1}|^2 = |R^S| = (\mathrm{Nm}\,\mathfrak{m})^{|S|}$, the function $c_{\mathrm{line}}^{-1}$ has absolute value $1$ up to a norm power (`of_norm_sq_eq_mul_card_zpow`). Products keep this property, so $c$ has absolute value $\mathrm{turnRatio}_{jj}$ up to a norm power.

Given path data $\Psi'$ on `downPath`, Section 5 gives path data $\Psi$ on `rightPath` with bound $|R^{S \times 1}|\, N \leq$ `vectorCountBound` $\cdot N$, matched for $\psi_\vartheta$. Choose them for each $\vartheta$. Let $\Psi \propto \Xi$. By the second seesaw, $I^S_{\mathrm{row}}(\Psi; z, \tau(p)) = \beta\, \Xi$. The previous lemma gives $I^S_{\mathrm{col}}(\Psi'; z, p)(x) = c_{\mathrm{line}}\, (\kappa/c_{\mathrm{sq}})\, \beta\, \Xi(x) = \kappa\beta\, \Xi(x)/c(\vartheta)$. The first seesaw gives $\Psi' \propto \Xi/c$. $\square$

**Theorem (One turn).** For $i, j < m$ there are units $c(\vartheta)$ with absolute value $\mathrm{turnRatio}_{ij}$ up to a norm power such that every turn at $(i, j)$ from $\Gamma'$ to $\Gamma$ transfers periods with bound `vectorCountBound` and constant $c$.

Lean: `New.Data.exists_transfersPeriods_of_turn` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* Split into $i < j$, $i = j$ and $i > j$. If $i < j$, the turn is inner in grid false (`Turn.exists_corner_of_lt`); use Section 6 with $z$ false and enlarge the bound from $1$, since $1 \leq$ `vectorCountBound`. If $i = j$, the turn is diagonal, with $\Gamma'$ = `downPath` $q$ and $\Gamma$ = `rightPath` $q$; use the previous theorem. If $i > j$, the turn is inner in grid true at $(j, i)$; Section 6 with $z$ true gives $\mathrm{turnRatio}_{ij}$. $\square$

**Theorem (First path to last path).** There are units $c(\vartheta)$ with absolute value $\prod_{i, j < m} \mathrm{turnRatio}_{ij}$ up to a norm power such that the first path transfers periods to the last path with bound $\text{vectorCountBound}^{m^2}$ and constant $c$.

Lean: `New.Data.exists_transfersPeriods_first_last` (New/Determinant/AuxiliaryForms/DiagonalTurns.lean).

*Proof.* For each $s \in \{0, \ldots, m-1\}^2$ choose $c_s$ by the previous theorem, and put $c = \prod_s c_s$. A product of functions with absolute values $f_s$ up to norm powers has absolute value $\prod f_s$ up to a norm power (`HasAbsUpToNormPower.prod`). Apply [turn induction](/chapter/seesaw-squares/#grid-paths-and-turns) with $M(\Gamma, T)$: $\Gamma$ transfers periods to the last path with bound $\text{vectorCountBound}^{|T|}$ and constant $\prod_{s \in T} c_s$. For the last path and $T = \emptyset$ this is reflexivity. For a turn at $s \notin T$ from $\Gamma'$ to $\Gamma$, compose the transfer of the turn with $M(\Gamma, T)$; bounds and constants multiply. At the first path $|T| = m^2$. $\square$

**Remark (Formalization).** In chapter 7 the turn induction is stated with the opposite names of the two paths; the source here writes `Γ'.Turn s Γ` with $\Gamma'$ the old path. The constants $c_s$ come from `choose!`. Each transfer carries a factor $\kappa\beta$ that may be $0$. So the result gives no lower bound for periods on the first path.
