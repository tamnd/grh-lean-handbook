---
title: Line coordinates
lean:
  - New/OneLift/ComparisonOperator/LineCoordinates.lean
decls:
  - New.HasWeightNormSqLe
  - New.HasWeightNormSqLe.mul
  - New.HasWeightNormSqLe.prod
  - New.HasWeightNormSqLeIf
  - New.HasWeightNormSqLeIf.prod
  - New.exists_toPoly_eq_det_and_weylNormSq_le
  - New.Data.AddedIndex
  - New.Data.posEquiv
  - New.Data.constantRows
  - New.Data.stackedDetProdCoords
  - New.Data.addedDatum
  - New.Data.leftSideSeries
  - New.Data.card_detIndex_le
  - New.Data.prod_sum_norm_sq_le_M_pow
  - New.Data.IsSmallSpecialization
  - New.Data.hasWeightNormSqLeIf_stackedDet
  - New.Data.weylNormSq_comp_eval_stackedDetProdCoords_le
  - New.Data.toPoly_stackedDetProdCoords
  - New.Data.aeval_smul_X_stackedDetProdCoords
  - New.Data.IsHomogeneousOverEntries
  - New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Line coordinates

The left side of the comparison is a series $\Upsilon$ of theta kernels on definite spaces. Its polynomial is a product $P_V$ of determinants. This section writes $P_V$ as the polynomial of a vector $\zeta$ in a Weyl module, and bounds the norm, the degree and the denominator of $\zeta$. The Weyl modules, the map `toPoly` from coordinates to polynomials and the squared norm `weylNormSq` for the Gram matrix are in [Weyl modules](/chapter/weyl-modules/). The products of stacked determinants and their coordinates `firstColsCoord` are in [the exchange identity, part 2](/chapter/exchange-identity-2/).

### Notation

Fix admissible data $D$, a tame character $\vartheta$ and $1 \leq j \leq m$. Put $k = D.k$, $m = D.m$, $M = D.M$ and $r_+ = k + j - 1$ (`D.posRank j`). The space $V''$ is on `FirstFactorIndex j`, with $N = \#V''$ rows of variables. The space $W^{\mathrm{add}} = E^{3m-j} \oplus W^\flat \oplus E^{3m}$, with $W^\flat = E^{6m+1}$, is on `AddedIndex j`. The diagram $\mu^+$ has $\kappa(\tau, h)$ columns of height $h$ at the place $\tau$ (`(untwistedDescentPair j).colsPlus`). The set `DetIndex j τ` has one element for each column of $\mu^+$ at $\tau$. Its columns of height $r_+$ number $\Delta' = $ `D.reducedHalfGap`.

### Weights with a norm bound

**Definition.** $F$ *has weight $\kappa$ and squared norm at most $b$* if $F = \mathrm{toPoly}(\xi)$ for a coordinate vector $\xi$ of weight $\kappa$ with $\mathrm{weylNormSq}(\xi) \leq b$. The conditional form for a proposition $p$ asks $\mathrm{weylNormSq}(\xi) \leq b$ only under $p$.

Lean: `New.HasWeightNormSqLe`, `New.HasWeightNormSqLeIf` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Lemma (Products).** If $F$ has weight $\kappa$ and bound $b$, and $G$ has weight $\kappa'$ and bound $c$, then $FG$ has weight $\kappa + \kappa'$ and bound $bc$. For a finite product the weights add and the bounds multiply, also in the conditional form.

Lean: `New.HasWeightNormSqLe.mul`, `New.HasWeightNormSqLe.prod`, `New.HasWeightNormSqLeIf.prod` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* Products of semi-invariants of weights $\kappa$ and $\kappa'$ are semi-invariants of weight $\kappa + \kappa'$, so $FG = \mathrm{toPoly}(\zeta)$ for some $\zeta$. The norm of the Weyl module is submultiplicative on products: $\mathrm{weylNormSq}(\zeta) \leq \mathrm{weylNormSq}(\xi)\,\mathrm{weylNormSq}(\eta)$ ([Weyl modules](/chapter/weyl-modules/)). Finite products follow by induction from the empty product $1$, which has weight $0$ and bound $1$. In the conditional form, choose an unconditional bound $c_i$ for each factor with $c_i \leq b_i$ under $p$. The product of the $c_i$ is a bound, and under $p$ it is at most $\prod b_i$ since the $c_i$ are nonnegative. $\square$

**Lemma (One column).** Let $h < \#N$, and let $e : a \sqcup N \simeq \mathrm{Fin}\,h \sqcup c$ match rows and columns. For a complex matrix $Z$ with rows $a \sqcup N$ and columns $c$ there is a vector $\xi$ of weight "one column of height $h$ at $\tau$" with
$$\mathrm{toPoly}(\xi)(x) = \det\Bigl(\bigl(\begin{smallmatrix}0\\ X\end{smallmatrix}\ \big|\ Z\bigr)\circ e\Bigr), \qquad \mathrm{weylNormSq}(\xi) \leq \prod_{b \in c}\sum_x|Z_{xb}|^2.$$
Here $X$ is the $N \times h$ matrix of variables at $\tau$.

Lean: `New.exists_toPoly_eq_det_and_weylNormSq_le` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* Expand the determinant along the first $h$ columns (Laplace). The result is a sum over $h$-subsets $S$ of $N$ of the minor of $X$ on $S$ times a complementary minor of $Z$, up to sign. The minors of $X$ are the basis products of the Weyl module for one column of height $h$. So the determinant is $\mathrm{toPoly}(\xi)$ with coordinates given by the complementary minors. Their squared moduli sum, by the Cauchy-Binet formula, to the Gram determinant of the columns of $Z$, and Hadamard's inequality bounds this by the product of the squared column lengths. $\square$

**Example.** Take $h = 0$. The weight is trivial, $\xi$ is a number, and the lemma reads $|\det Z|^2 \leq \prod_b \sum_x|Z_{xb}|^2$. This is Hadamard's inequality.

### The constant rows and the series

**Definition (Constant rows).** The map `posEquiv j` is a bijection $\mathrm{Fin}(2m) \sqcup V'' \simeq \mathrm{Fin}(r_+) \sqcup W^{\mathrm{add}}$. For the place $\tau$, a row choice $i$ and $Y \in M_{W^\flat}(E)$, the matrix $\mathsf{c}$ has $2m$ rows for each column $l$ of $\mu^+$. For a column of height $h < r_+$, row $a$ is the basis vector at the positive index $h + a$ of $W_j$ if $h + a < r_+$, and basis vector number $a$ of $E^{3m-j}$ otherwise. For the $l$-th column of height $r_+$, the rows are the rows `i.rows τ l` of $\tau(Y)$, placed in the columns of $W^\flat$.

Lean: `New.Data.AddedIndex`, `New.Data.posEquiv`, `New.Data.constantRows` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Definition (The map $\zeta$).** $P_V$ is the product over $\tau$ and over the columns $l$ of the determinants $\det(\mathsf{c}_l;\ X\,z)$: the $2m$ constant rows over the $N$ rows of variables. Read $P_V$ as a polynomial in the variables $X$ of the first $r_+$ columns with coefficients polynomials in the variables $z$ of the columns of $W^{\mathrm{add}}$. Then $\zeta = $ `stackedDetProdCoords j i Y` is its vector of coordinates of weight $\mu^+$.

Lean: `New.Data.stackedDetProdCoords` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Definition (Datum and series).** The datum $\Psi^{\mathrm{add}}$ for a matrix $\Lambda$ modulo $\varpi^2$ is $0$ unless the columns of $z$ on $E^{3m-j}$ and $W^\flat$ are those of the identity matrix. In that case it is $\sum_{g \in GL_{3m}(\mathcal{O}_E/\varpi^2)}\psi(\mathrm{tr}(z'g\Lambda))$, with $z'$ the columns on $E^{3m}$ reduced modulo $\varpi^2$. The series $\Upsilon$ at $h$ has coordinate $l$ equal to a kernel of $((E^j)^-, V'')$ at $(1, h)$ times a class sum over $h' \in U(E^{3m})$ of $\mathsf{a}(h')\chi'(h')\,\mathsf{K}[\zeta_l]((1, h^\flat, h'), h)$. Here $\mathsf{K}$ is the kernel of $(W^{\mathrm{add}}, V'')$ with datum $\Psi^{\mathrm{add}}$ and $\chi' = \chi^j\vartheta$.

Lean: `New.Data.addedDatum`, `New.Data.leftSideSeries` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Remark (Formalization).** The representative $h^\flat$ of the class in a choice is `Quotient.out`, a choice by the library. The bijection `posEquiv` comes from `Fintype.equivOfCardEq` and is also a choice. The value $0$ of $\Psi^{\mathrm{add}}$ off the identity columns is part of the definition, not a junk value.

### Norm

**Lemma (Number of determinants).** $\#\mathrm{DetIndex}(j, \tau) \leq b_{\mathbb{N}} + w_{\mathrm{off}} + \Delta + m\Delta$, with $\Delta = $ `D.gap`.

Lean: `New.Data.card_detIndex_le` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* The number of columns plus the exponent of the first factor character is the lift weight at $\tau$, which is at most $b_{\mathbb{N}} + w_{\mathrm{off}} + \Delta + j\Delta$. Use $j \leq m$. $\square$

**Lemma (Column lengths).** Let $r_+ - h \leq j$ and let $Z$ have rows $\mathrm{Fin}(2m) \sqcup V''$, columns $\mathrm{Fin}(r_+ - h) \sqcup W^{\mathrm{add}}$, and entries of modulus at most $M^4$. Then $\prod_b\sum_a|Z_{ab}|^2 \leq (M^9)^{12m+1}$.

Lean: `New.Data.prod_sum_norm_sq_le_M_pow` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* There are $r + 11m + 1$ rows, so each column has squared length at most $(r + 11m + 1)M^8 \leq M^9$, as $M$ is large. There are $(r_+ - h) + (3m - j) + (6m + 1) + 3m \leq 12m + 1$ columns, and $M^9 \geq 1$. $\square$

**Definition.** A specialisation by values $z$ and a ring map $\varphi : \mathbb{C} \to \mathbb{C}$ is *small* if $|\varphi(\tau(Y_{ab}))| \leq M^4$ and $|\varphi(z_x)| \leq M^4$ for all entries and values.

Lean: `New.Data.IsSmallSpecialization` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Lemma (One determinant).** Let $l$ be a column of $\mu^+$ of height $h$ at $\tau$. The determinant $\det(\mathsf{c}_l; X\,z)$, read in the first $r_+$ columns and specialised by $z$ and $\varphi$, has weight "one column of height $h$ at $\tau$" and, if the specialisation is small, squared norm at most $(M^9)^{12m+1}$.

Lean: `New.Data.hasWeightNormSqLeIf_stackedDet` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* The heights of $\mu^+$ satisfy $r_+ - j \leq h \leq r_+$, and $h < N$. For $h < r_+$ the constant rows contain the unit vectors at the positive indices $h, \ldots, r_+ - 1$. Adding multiples of these rows to the rows of variables clears the variables in those columns. This is a unipotent row operation, so the determinant does not change. The cleared matrix has the form $((0; X) \mid Z)$, with $X$ the first $h$ columns. Each entry of $Z$ is $0$, $1$, a conjugate of an entry of $Y$ or a value of $z$. After $\varphi$ these have modulus at most $M^4$ when the specialisation is small. Apply the lemma on one column and the lemma on column lengths. $\square$

**Theorem (Norm of $\zeta$).** If the specialisation by $z$ and $\varphi$ is small, then
$$\mathrm{weylNormSq}(\varphi \circ \mathrm{eval}_z \circ \zeta) \leq (M^9)^{(12m+1)\sum_\tau\#\mathrm{DetIndex}(j,\tau)}.$$

Lean: `New.Data.weylNormSq_comp_eval_stackedDetProdCoords_le` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* By the lemma on products, the specialised $P_V$ is $\mathrm{toPoly}(\xi)$ for a $\xi$ of weight $\mu^+$ whose squared norm is at most the stated power under smallness. A vector is determined by its polynomial, and the specialised $P_V$ is also the polynomial of $\varphi \circ \mathrm{eval}_z \circ \zeta$. So the two vectors agree. $\square$

**Lemma.** $\mathrm{toPoly}(\zeta) = P_V$, read in the first $r_+$ columns.

Lean: `New.Data.toPoly_stackedDetProdCoords` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* Compare the coefficients at every point $z$, using the specialised identity with $\varphi = \mathrm{id}$. $\square$

### Degree and denominator

**Lemma (Homogeneity).** For $c \neq 0$, replacing every variable $z_x$ by $cz_x$ multiplies each coordinate $\zeta_l$ by $c^d$, where $d = \sum_\tau\sum_{h<N}(N - h)\kappa(\tau, h)$.

Lean: `New.Data.aeval_smul_X_stackedDetProdCoords` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* Scaling all $N$ rows of variables by $c$ multiplies $P_V$ by $c^{N\sum\kappa}$. In the $X$ variables the same scaling acts on the Weyl module by the Schur matrix of $c\cdot 1$, the scalar $c^{\sum h\kappa(h)}$. The coordinates of $P_V$ therefore scale by the quotient $c^d$. Cancel the nonzero power. $\square$

**Definition.** A polynomial $Q$ in the variables $z$ is *homogeneous of degree $d$ over the entries of $Y$* if $Q(cz) = c^dQ(z)$ for $c \neq 0$ and $Q$ has its coefficients in every subring $A \subseteq \mathbb{C}$ that contains all $\tau(Y_{ab})$.

Lean: `New.Data.IsHomogeneousOverEntries` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

**Theorem (Degree and denominator of $\zeta$).** There are $d \leq (10m+1)\sum_\tau\#\mathrm{DetIndex}(j,\tau)$ and an integer $0 < H \leq (d^d)^3$, independent of $i$ and $Y$, such that every $H\zeta_l$ is homogeneous of degree $d$ over the entries of $Y$.

Lean: `New.Data.exists_isHomogeneousOverEntries_smul_stackedDetProdCoords` (New/OneLift/ComparisonOperator/LineCoordinates.lean).

*Proof.* Take $d$ as in the lemma on homogeneity. When $\kappa(\tau, h) \neq 0$ we have $N - h \leq 10m + 1$, so $d \leq (10m+1)\sum_{\tau,h}\kappa(\tau, h)$, and $\sum_h\kappa(\tau, h) = \#\mathrm{DetIndex}(j,\tau)$. Let $H$ be the hook number of the complementary diagram $h \mapsto \kappa(\tau, N - h)$. It is positive. Reversing the order of summation shows that the complementary diagram has at most $d$ boxes at each place in total, which gives $H \leq (d^d)^3$. Homogeneity of $H\zeta_l$ is the lemma above. For integrality, each entry of each determinant is $0$, $1$, a variable or some $\tau(Y_{ab})$, so $P_V$ has coefficients in $A$. Then the Gram matrix applied to $\zeta$ has coordinates $c$ in $A[z]$, as these are coefficients of $P_V$ in the basis of products of minors. The hook number times the corresponding combination of products of minors is $\mathrm{toPoly}$ of a vector $\zeta'$ over $A[z]$ ([Weyl modules](/chapter/weyl-modules/)). A vector is determined by its polynomial, so $\zeta'$ maps to $H\zeta$. $\square$

**Remark (Formalization).** The degree $d$ and the number $H$ are given by `∃`, but the proof fixes them explicitly as above. The theorem holds for every $Y$, also when $Y$ is not the short basis.
