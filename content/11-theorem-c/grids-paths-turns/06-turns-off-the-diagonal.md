---
title: Turns off the diagonal
lean:
  - New/Determinant/AuxiliaryForms/Turns.lean
decls:
  - New.Data.turnRatio
  - New.Data.squarePair
  - New.Data.isRamified_squarePair
  - New.Data.isRamifiedRatio_turnRatio
  - New.Data.isRamifiedRatio_turnRatio_of_mem
  - New.Data.card_gridIndex_square
  - New.Data.charOfTamePart_gridModulus_mul
  - New.Data.edgeChar_columnEdge_mul_rowEdge
  - New.Data.gridChar_mul_gridChar_eq_rankTwist
  - New.Data.card_gridIndex_square_le
  - New.Data.exists_squareLaw_grid_hasAbsUpToNormPower
  - New.Data.TransfersPeriods
  - New.Data.TransfersPeriods.refl
  - New.Data.TransfersPeriods.mono
  - New.Data.TransfersPeriods.trans
  - New.Data.innerCorner
  - New.Data.isTurn_innerCorner
  - New.Data.edges_eq_oldEdges_innerCorner
  - New.Data.edges_update_eq_newEdges_innerCorner
  - New.Data.sum_formMap_eq_of_squareLaw
  - New.Data.exists_transfersPeriods_off_diagonal
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Turns off the diagonal

This section applies the one square identity to a square of a grid. It defines the transfer of periods and proves it for every turn off the diagonal. The constant of the transfer has, up to a norm power, the absolute value of a ratio of Hecke values.

We use the one square identity of [the one square identity](/chapter/seesaw-squares/#the-one-square-identity), the critical pairs of [twists, critical pairs and regular families](/chapter/twists-critical-pairs/), and the ratios $\Lambda$, the ramified ratios and "absolute value up to a norm power" of [moduli and ratios of Hecke values](/chapter/chain-determinant/#moduli-and-ratios-of-hecke-values). Write $\chi_j$ for `untwistedLiftChar` $j$ and $w_j$ for `liftWeight` $j$.

### The ratio of a turn

**Definition.** For $i, j \in \mathbb{N}$ the *turn ratio* is $\mathrm{turnRatio}_{ij}(\vartheta) = \Lambda(\chi_{i+1}\chi_{j+1}, t, \vartheta^{j+1})$. For $a, b < m$ the *pair of the square* $(a, b)$ is the critical pair with character $\chi_{a+1}\chi_{b+1}$, minus weight $w_{b+1} + w_{a+1}$, tame part $\omega^{a+b+2}$ (with $\omega$ = `chiMLocal`) and $z = t$.

Lean: `New.Data.turnRatio`, `New.Data.squarePair` (New/Determinant/AuxiliaryForms/Turns.lean).

The pair is a critical pair: the weights of the two characters add and their tame parts multiply, and $t \leq w_{a+1} + w_{b+1} \leq 4b$ at every infinite place, by the bounds on `liftWeight`.

**Lemma.** For $a, b < m$ the pair of the square is ramified. For $i, j < m$, $\mathrm{turnRatio}_{ij}$ is a ramified ratio, and so is $\mathrm{turnRatio}_{s_1 s_2}$ for every $s \in \{0, \ldots, m - 1\}^2$.

Lean: `New.Data.isRamified_squarePair`, `New.Data.isRamifiedRatio_turnRatio`, `New.Data.isRamifiedRatio_turnRatio_of_mem` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* The tame part $\omega^k$ with $k = a + b + 2$ is not $1$ exactly at the chosen places, since $1 \leq k \leq 2m$ (`chiMLocal_zpow_ne_one_iff_isChosen`). For the ratio take the pair of the square $(i, j)$ and $n = j + 1$, with $1 \leq n \leq m$. $\square$

### The square of a grid

```text
  grid z, square s = (a, b), a, b < m

   (a, b+1) --- x1 ---> (a+1, b+1)
      |                     |
      y1                    x2
      v                     v
   (a, b)   --- y2 ---> (a+1, b)

  old half: q, down (y1), right (y2), r
  new half: q, right (x1), down (x2), r
```

A step down uses a transposed lift by the matrix on a column edge; a step right uses a lift by the matrix on a row edge. The column edge at $(a, b)$ goes from $(z, a, b)$ to $(z, a, b + 1)$ and the row edge from $(z, a, b)$ to $(z, a + 1, b)$.

**Lemma.** In grid $z$:

1. $|(a, b)| + |(a + 1, b + 1)| = |(a, b + 1)| + |(a + 1, b)|$ for the ranks of the corners.
2. The character of the residue ring with tame parts $\psi\psi'$ is the product of the characters with tame parts $\psi$ and $\psi'$.
3. For $a, b < m$, the product of the characters of the column edge and the row edge at $(a, b)$ is the character with tame parts $\omega^{a+b+2}\, \vartheta^n$, where $n = a + 1$ if $z$ is true and $n = b + 1$ otherwise.
4. For $a, b < m$ and types $p$, $q$ with $|p| + |q| = |(a, b + 1)| + |(a + 1, b)|$, $\mathrm{gridChar}(\vartheta, z, a, p) \cdot \mathrm{gridChar}(\vartheta, \neg z, b, q) = \operatorname{rankTwist}(\chi_{a+1}\chi_{b+1}\vartheta^n, (a, b + 1) \sqcup (a + 1, b))$.
5. For $a, b < m$ and every infinite place $\tau$, $|(a, b + 1) \sqcup (a + 1, b)| \leq 2(w_{a+1} + w_{b+1})(\tau) + 2\operatorname{neg}$, where $\operatorname{neg}$ counts the negative signs on the two kept corners.

Lean: `New.Data.card_gridIndex_square`, `New.Data.charOfTamePart_gridModulus_mul`, `New.Data.edgeChar_columnEdge_mul_rowEdge`, `New.Data.gridChar_mul_gridChar_eq_rankTwist`, `New.Data.card_gridIndex_square_le` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Claim 1 follows from the rank formula `card_gridIndex`, which is affine in each index. Claim 2: the character is a finite product over places of local characters, and a finite product of products splits. Claim 3: one of the two edges is vertical and carries $\vartheta^n$; the other carries the trivial twist. The untwisted tame parts give $\omega^{a+1}\omega^{b+1}$. Claim 4: the sum of the two ranks is even, so the rounded halves of $|p| + (\neg z)$ and $|q| + z$ add up to half the total rank. Then both sides are the same product of powers of the characters. Claim 5: each rank is at most $2n_m$, $n_m \leq$ `halfGap` by the log bound, and both weights are at least `halfGap`. $\square$

### The one square identity on a grid square

The source applies the one square identity to a grid square at [Turns.lean](lean:New/Determinant/AuxiliaryForms/Turns.lean#L769).

**Theorem.** Let $a, b < m$ and $z \in \{\mathrm{false}, \mathrm{true}\}$. There are $\kappa \in \mathbb{C}$, a bijection $\sigma \colon (a, b) \sqcup (a + 1, b + 1) \simeq (a, b + 1) \sqcup (a + 1, b)$ of index sets, and units $c(\vartheta)$ with these properties.

1. $\vartheta \mapsto c(\vartheta)$ has absolute value $\mathrm{turnRatio}_{ab}$ up to a norm power if $z$ is false, and $\mathrm{turnRatio}_{ba}$ if $z$ is true.
2. For every twist $\vartheta$, every form $f$ at $(a, b + 1)$ and every functional $l$ on the forms at $(a + 1, b)$, the functions
$$L(x) = l\bigl(\mathcal{L}^{\mathsf T}(x_2)\, \mathcal{L}(x_1)\, f\bigr), \qquad L'(y) = l\bigl(\mathcal{L}(y_2)\, \mathcal{L}^{\mathsf T}(y_1)\, f\bigr)$$
satisfy the square law for $(\chi_{\mathrm{col}}\chi_{\mathrm{row}})^{-1}$ and $\sigma$ with constant $\kappa / c(\vartheta)$. Here $\chi_{\mathrm{col}}$, $\chi_{\mathrm{row}}$ are the characters of the column edge and the row edge at $(a, b)$, $\mathcal{L}$ is `liftMove`, $\mathcal{L}^{\mathsf T}$ is `transposedMove`, and $x_1, x_2$, $y_1, y_2$ are the blocks of the figure.

Lean: `New.Data.exists_squareLaw_grid_hasAbsUpToNormPower` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Let $p$ be the pair of the square and $n$ as in claim 3 of the lemma. We check the conditions of the one square identity for the four grid spaces at the corners. The edge families come from `isEdgeFamily_grid_succ_right` and `isEdgeFamily_grid_succ_left` of [path data and periods](/chapter/seesaw-squares/#path-data-and-periods). Take $\sigma$ = `equivOfCardEq`, which exists by claim 1. The sign count condition holds by `negCount_gridSigns`. The rank of $(a + 1, b + 1)$ is the rank of $(a, b)$ plus $2t$, from the rank formula. On the two kept corners at least two more signs are positive than negative, again from the rank formula. The weight bound is claim 5. Tameness of $(\nu\vartheta^n)^{-1}$ is `CriticalPair.isTameFor_inv_mul_pow` for the ramified pair $p$. The character condition is claim 4.

The identity gives $C \in \mathbb{R}$, $\kappa$, and for each $\vartheta$ a $c \neq 0$ with $|c|^2 = C\, L_*(\text{places of } \mathfrak{m}, (\nu\vartheta^n)^{-1}, t)$ and the square law with constant $\kappa / c$, for the character with tame parts $(\omega^{a+b+2}\vartheta^n)^{-1}$. Choose these $c(\vartheta)$. The proposition `CriticalPair.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd` turns the formula for $|c|^2$ into claim 1, since $\Lambda(\nu, t, \vartheta^n)$ is the turn ratio named in the claim. Claim 3 of the lemma rewrites the character as $(\chi_{\mathrm{col}}\chi_{\mathrm{row}})^{-1}$. $\square$

**Remark (Formalization).** The constant $\kappa$ may be $0$; the one square identity does not exclude it. The numbers $c(\vartheta)$ come from `choose` and are units. The bijection $\sigma$ is any bijection of the right size; the identity holds for each one.

### Transfer of periods

The period $I(\Psi; g)$ and proportionality $\Psi \propto \Xi$ on a path are those of [path data and periods](/chapter/seesaw-squares/#path-data-and-periods).

**Definition (Transfer of periods).** Let $\Gamma'$ and $\Gamma$ be two-grid paths, $k$ a function from twists to $\mathbb{N}$ and $c$ a function from twists to units. Then $\Gamma'$ *transfers periods to* $\Gamma$ with bound $k$ and constant $c$ if for every $N$ and every family $\Psi'_\vartheta$ of path data for $N(\vartheta)$ on $\Gamma'$ there is a family $\Psi_\vartheta$ of path data for $k(\vartheta) N(\vartheta)$ on $\Gamma$ such that, for every $\Xi$, $\Psi \propto \Xi$ on $\Gamma$ implies $\Psi' \propto \Xi / c$ on $\Gamma'$. Here $(\Xi / c)(\vartheta, y', \varphi) = \Xi(\vartheta, y', \varphi) / c(\vartheta)$.

Lean: `New.Data.TransfersPeriods` (New/Determinant/AuxiliaryForms/Turns.lean).

Path data pass forward from $\Gamma'$ to $\Gamma$. Proportionality passes backward from $\Gamma$ to $\Gamma'$.

**Lemma.** Every path transfers periods to itself with bound $1$ and constant $1$. A transfer with bound $k$ is a transfer with every bound $k' \geq k$. If $\Gamma_1$ transfers to $\Gamma_2$ with $(k, c)$ and $\Gamma_2$ to $\Gamma_3$ with $(k', c')$, then $\Gamma_1$ transfers to $\Gamma_3$ with $(k k', c c')$.

Lean: `New.Data.TransfersPeriods.refl`, `New.Data.TransfersPeriods.mono`, `New.Data.TransfersPeriods.trans` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* For the first claim take $\Psi = \Psi'$. For the second, a path datum for $N$ is one for every larger bound. For the third, apply the first transfer to $\Psi_1$ and get $\Psi_2$ for $k N$. Apply the second to $\Psi_2$ and get $\Psi_3$ for $k'(kN) = (kk')N$. If $\Psi_3 \propto \Xi$, then $\Psi_2 \propto \Xi / c'$, so $\Psi_1 \propto (\Xi/c')/c = \Xi / (cc')$. $\square$

### The inner corner

**Definition.** The *inner corner* at $(z, a, b)$ has $V' = \tilde V' = (z, a, b)$, $W_1 = (z, a, b + 1)$, $W_2 = (z, a + 1, b)$, $V = \tilde V = (z, a + 1, b + 1)$, $B$ the index set of $W_2$ and $T$ empty.

Lean: `New.Data.innerCorner` (New/Determinant/AuxiliaryForms/Turns.lean).

**Lemma.** Let $a < b < m$, and let no edge of $w$ start or end at $(z, a, b)$ or end at $(z, a + 1, b + 1)$. Then the inner corner is a turn for every $\vartheta$ and $w$.

Lean: `New.Data.isTurn_innerCorner` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Conditions 1 and 2 hold by the choice of nodes and the hypothesis on $w$. For condition 3, the column edge at $(a, b)$ is vertical in grid false and the row edge in grid true, and the opposite new edges are not. For condition 4, opposite sides of the square have the same kind and the same twist, so the same character. Condition 5 holds since $T$ is empty. For condition 6, set $g' = g$ with the value at $(z, a, b)$ replaced by $k$. This is admissible: $(z, a, b)$ is not a start node $(z, 0, m)$ since $b < m$, and not a diagonal node since $a < b$. $\square$

**Lemma.** Let the half of $\Gamma'$ in grid $z$ be $q \cdot \mathrm{down} \cdot \mathrm{right} \cdot r$, with $q$ from $(0, m)$ to $(a, b + 1)$ and $r$ from $(a + 1, b)$ to the diagonal node $(l, l)$. Let $w$ be the union of the edges of $q$, of $r$ and of the other half. Then the edges of $\Gamma'$ are the old edges of the inner corner for $w$. If the half is replaced by $q \cdot \mathrm{right} \cdot \mathrm{down} \cdot r$, the edges of the new path are the new edges.

Lean: `New.Data.edges_eq_oldEdges_innerCorner`, `New.Data.edges_update_eq_newEdges_innerCorner` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Unfold the edges of a concatenation: they are the union of the edges of the parts. The step down from $(a, b + 1)$ adds the column edge at $(a, b)$, and the step right from $(a, b)$ adds the row edge at $(a, b)$. The new steps add the row edge at $(a, b + 1)$ and the column edge at $(a + 1, b)$. $\square$

**Lemma.** Let the inner corner be a turn for $\vartheta$ and $w$, with the edges of $q$ and $r$ in $w$. Let $\Psi$ be matched with the column Fourier transform of $\Psi'$, for $\psi = 1$ and $\sigma$. Let the square law hold for every $f$ and $l$, as in the theorem, with constant $C$. Let $F$ be a form at $(0, m)$ and let the functionals $l_S$ at $(k, k)$ depend only on $S$ on $w$. Then
$$\sum_{S \in \mathrm{tuples}(\mathrm{old})} \Psi'(S)\, l_S\bigl(\mathrm{formMap}_{q\,\mathrm{down}\,\mathrm{right}\,r}(S)\, F\bigr) = C \sum_{S \in \mathrm{tuples}(\mathrm{new})} \Psi(S)\, l_S\bigl(\mathrm{formMap}_{q\,\mathrm{right}\,\mathrm{down}\,r}(S)\, F\bigr).$$

Lean: `New.Data.sum_formMap_eq_of_squareLaw` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* The form map of a concatenation is the composite of the form maps. So the left term is $l_S \circ \mathrm{formMap}_r$ applied to $\mathcal{L}(y_2)\mathcal{L}^{\mathsf T}(y_1)$ of $\mathrm{formMap}_q(S) F$, with $y = \mathrm{oldMatrix}(S)$. The right term is the same with $\mathcal{L}^{\mathsf T}(x_2)\mathcal{L}(x_1)$ and $x = \mathrm{newMatrix}(S)$. The pair $(\mathrm{formMap}_q(S) F,\ l_S \circ \mathrm{formMap}_r(S))$ depends only on $S$ on $w$. Take it as the index $f(S, v')$ in the theorem on the sum over a square of Section 5, with the family of square laws indexed by such pairs. Since $T$ is empty there is one row $v'$, and $\psi(\operatorname{tr}(v' v)) = 1$. $\square$

### The transfer

**Theorem (Turns off the diagonal).** Let $a < b < m$ and $z \in \{\mathrm{false}, \mathrm{true}\}$. There are units $c(\vartheta)$ with absolute value $\mathrm{turnRatio}_{ab}$ up to a norm power ($\mathrm{turnRatio}_{ba}$ if $z$ is true) such that the following holds. If the half of $\Gamma'$ in grid $z$ is $q \cdot \mathrm{down} \cdot \mathrm{right} \cdot r$, then $\Gamma'$ transfers periods with bound $1$ and constant $c$ to the path $\Gamma$ whose half in grid $z$ is $q \cdot \mathrm{right} \cdot \mathrm{down} \cdot r$.

Lean: `New.Data.exists_transfersPeriods_off_diagonal` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Take $\kappa$, $\sigma$ and $c$ from the theorem on a grid square, for $(a, b)$. Let $\Psi'$ be path data for $N$ on $\Gamma'$. Let $w$ be as in the edge lemma. The edges of $w$ avoid $(z, a, b)$ and do not end at $(z, a + 1, b + 1)$: every edge of a grid path from $(0, m)$ to $(a, b + 1)$, or from $(a + 1, b)$ to $(l, l)$, has its ends in the boxes given by `GridPath.eq_and_le_of_mem_edges`, and the other half lies in the other grid. So the inner corner is a turn. Section 5 gives path data $\Psi_\vartheta$ on $\Gamma$, matched with $\Psi'_\vartheta$, with bound $|R^{B \times \emptyset}| N = N$. These are chosen for each $\vartheta$.

Let $\Psi \propto \Xi$ on $\Gamma$, so $I(\Psi; g)(x) = \beta\, \Xi(x)$. Fix $g$ and a triple $x = (\vartheta, y', \varphi)$. The form of the triple that starts in grid $z$ crosses the square. The other half, followed by the diagonal pairing, gives the functional $l_S$; it depends only on the edges of the other half. The previous lemma gives $I(\Psi'; g)(x) = (\kappa / c(\vartheta))\, I(\Psi; g)(x) = \kappa\beta\, \Xi(x) / c(\vartheta)$. So $\Psi' \propto \Xi / c$ with the number $\kappa\beta$. $\square$

**Remark (Formalization).** The number $\kappa\beta$ may be $0$ if $\kappa = 0$. Proportionality allows the number $0$, so the transfer still holds, but then it carries no information. The constants $c(\vartheta)$ are units. Only their absolute value is controlled.
