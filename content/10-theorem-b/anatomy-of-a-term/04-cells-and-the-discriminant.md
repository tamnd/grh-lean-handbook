---
title: Cells and the discriminant
lean:
  - New/Spanning/Unfolding/Terms.lean
  - New/Spanning/Unfolding/Link.lean
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/RemainingTerms/BorderedDeterminant.lean
  - New/Spanning/RemainingTerms/Data.lean
decls:
  - New.PairOccursAt
  - New.NormOnePairOccursFrom
  - New.Filling.HasCellRank
  - New.Filling.frameProducts_mulVec_of_frameImage_eq
  - New.Filling.hasCellRank_last
  - New.Filling.HasCellRank.unique
  - New.Filling.cellRank
  - New.Filling.HasCellRank.hasCellRank_cellRank
  - New.Filling.HasCellRank.cellRank_eq
  - New.Filling.CharsAgree
  - New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU
  - New.Filling.IsStable
  - New.NormOnePairOccursFrom.besselU_mul
  - New.NormOnePairOccursFrom.inv
  - New.Filling.isStable_hasCellRank
  - New.Filling.exists_frameImage_eq_of_normOnePairOccursFrom
  - New.Filling.frameImage_mulVec_eq_zero_iff
  - New.Filling.termDisc_eq_zero_iff_exists
  - New.Filling.termDisc_eq_zero_iff
  - New.Filling.frameDisc_weylElem_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cells and the discriminant

The Bruhat decomposition sorts the elements of a classical group by the relative position of a flag and its image. This section does the same for a term $\gamma$, with the flag $\mathfrak{f}_0 \subset \langle\mathfrak{f}_0, \mathfrak{f}_1\rangle \subset \cdots$ of the frame. The cell rank $j$ of $\gamma$ is the first index from which the flags of $\mathfrak{f}$ and $\gamma\mathfrak{f}$ share a vector at each step. The main results are these. A term has at most one cell rank. The cell rank, the leading minors and the discriminant do not change under $\gamma \mapsto u^{-1}\gamma u'$ with $u, u' \in \mathsf{U}$. The discriminant vanishes exactly when the spans of $\mathfrak{f}$ and $\gamma\mathfrak{f}$ meet. On the big cell the discriminant has a closed form.

### Shared vectors and the cell rank

Write $\mathfrak{f}\cdot x = \sum_a x_a\mathfrak{f}_a$ for $x \in E^{\varrho+1}$, as in [the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block).

**Definition (Shared vectors at an index).** Let $\gamma$ be an isometry, $c, c'$ scalars and $0 \leq a \leq \varrho$. A pair occurs at $a$ with the coefficients $c, c'$ if there are $x, y$ with $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$, $x_a = c$, $y_a = c'$ and $x_b = y_b = 0$ for all $b > a$. A norm one pair occurs from $j$ if there is one $c$ with $c\bar{c} = 1$ such that a pair occurs at $a$ with the coefficients $c, 1$ for every $a \geq j$.

Lean: `New.PairOccursAt` (New/Spanning/Unfolding/Terms.lean). Lean: `New.NormOnePairOccursFrom` (New/Spanning/Unfolding/Terms.lean).

**Definition (Cell rank).** Let $0 \leq j \leq \varrho + 1$. A rational $\gamma$ has the cell rank $j$ if three conditions hold: a norm one pair occurs from $j$; the leading minor $D_j(\gamma)$ is not $0$; and $\varrho < j$ if and only if $\mathsf{g}(\gamma) \neq 0$.

Lean: `New.Filling.HasCellRank` (New/Spanning/Unfolding/Terms.lean).

So the cell rank $\varrho + 1$ is the main case and the cell ranks $j \leq \varrho$ are the remaining cases. The condition "from $\varrho + 1$" is empty, since no index $a \leq \varrho$ satisfies $a \geq \varrho + 1$.

A shared vector has a simple image under $Z(\gamma)$.

**Lemma (Products of a shared vector).** If $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$, then $Z(\gamma)y = (0, \dots, 0, -Nx_\varrho)$.

Lean: `New.Filling.frameProducts_mulVec_of_frameImage_eq` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The entry $a$ of $Z(\gamma)y$ is $h(\mathfrak{f}_a, \gamma\mathfrak{f}\cdot y) = h(\mathfrak{f}_a, \mathfrak{f}\cdot x)$. The frame vectors are orthogonal to each other, $e_a$ is isotropic and $h(z, z) = -N$. So this is $0$ for $a < \varrho$ and $-Nx_\varrho$ for $a = \varrho$. $\square$

**Lemma (The top cell).** If $\mathsf{g}(\gamma) \neq 0$, then $\gamma$ has the cell rank $\varrho + 1$.

Lean: `New.Filling.hasCellRank_last` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The pair condition from $\varrho + 1$ is empty, with $c = 1$. The third condition holds since $\varrho < \varrho + 1$ and $\mathsf{g}(\gamma) \neq 0$. For the second, $D_{\varrho+1} = \det Z(\gamma)$. If it were $0$, then $\mathsf{g}(\gamma) = -N^2|D_\varrho|^2$. At a place $v$ the image is $-N^2|\Phi_v(D_\varrho)|^2 \leq 0$. By [Lemma](/decl/New.Filling.map_termDisc_eq_norm/) the image is also at least $0$, so it is $0$, and $\mathsf{g}(\gamma) = 0$. This is a contradiction. $\square$

**Lemma (A term has at most one cell rank).** If $\gamma$ has the cell ranks $j$ and $j'$, then $j = j'$.

Lean: `New.Filling.HasCellRank.unique` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

*Proof.* Suppose $j < j'$. The other case is symmetric. First, $j' \leq \varrho$. Indeed, if $j' > \varrho$, then $\mathsf{g}(\gamma) \neq 0$ by the third condition for $j'$, and so $j > \varrho$ by the third condition for $j$. This is impossible, since $j < j' \leq \varrho + 1$.

Put $i = j' - 1$. Then $j \leq i \leq \varrho - 1$. Since a norm one pair occurs from $j$, a pair occurs at $i$: there are $x, y$ with $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$, $y_i = 1$ and $x_b = y_b = 0$ for $b > i$. By the previous lemma $Z(\gamma)y = (0, \dots, 0, -Nx_\varrho)$. Let $y'$ be the vector of the first $j'$ entries of $y$. It is not $0$, since $y'_i = y_i = 1$. The entries of $y$ outside the first $j'$ vanish, so for $a < j'$,

$$(Z_{j'}y')_a = (Z(\gamma)y)_a = 0,$$

where $Z_{j'}$ is the leading block of order $j'$. The last step uses $a < j' \leq \varrho$. So $Z_{j'}$ has a nonzero kernel vector, and $D_{j'} = \det Z_{j'} = 0$. This contradicts the second condition for $j'$. $\square$

**Definition (The cell rank of a term).** The cell rank of $\gamma$ is an index $j$ with the cell rank $j$, chosen by Hilbert's epsilon operator.

Lean: `New.Filling.cellRank` (New/Spanning/RemainingTerms/Data.lean).

**Lemma (The chosen cell rank).** If $\gamma$ has the cell rank $j$, then $\gamma$ has the cell rank $\operatorname{cellRank}(\gamma)$, and $\operatorname{cellRank}(\gamma) = j$.

Lean: `New.Filling.HasCellRank.hasCellRank_cellRank` (New/Spanning/RemainingTerms/Data.lean). Lean: `New.Filling.HasCellRank.cellRank_eq` (New/Spanning/RemainingTerms/Data.lean).

*Proof.* The epsilon operator returns an element with the property when one exists. Uniqueness then gives the equality. $\square$

**Remark (Formalization).** If $\gamma$ has no cell rank, then $\operatorname{cellRank}(\gamma)$ is an unspecified index. The later chapters use $\operatorname{cellRank}(\gamma)$ only for terms that have a cell rank. By the lemma on the top cell, every term with $\mathsf{g}(\gamma) \neq 0$ has one. For the terms with $\mathsf{g}(\gamma) = 0$ the source needs a hypothesis on characters.

**Definition (Agreeing characters).** The characters of $\gamma$ agree if $\chi(u) = \chi(u')$ for all rational $u, u' \in \mathsf{U}$ with $u\gamma = \gamma u'$.

Lean: `New.Filling.CharsAgree` (New/Spanning/Unfolding/Terms.lean).

[The chapter on Poincaré series](/chapter/poincare-series/) proves that if the characters of $\gamma$ agree and $\mathsf{g}(\gamma) = 0$, then $\gamma$ has a cell rank ([Lemma](/decl/New.Filling.CharsAgree.exists_hasCellRank/)). The terms whose characters do not agree contribute $0$ to the amplitude sums.

### Invariance under the unipotent group

This subsection proves the result that [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/) uses in its bound on the open cell. The proof works over any commutative ring $F$ with an involution, for any form $T$ on $V$ of the shape of this volume. For an isometry $g$ let $\mathcal{Z}(g)$ be the matrix of the products $h(\mathfrak{f}_a, g\mathfrak{f}_b)$, so that $Z(\gamma) = \mathcal{Z}(\gamma)$ for the rational form.

**Lemma (Discriminant invariance under the unipotent group).** Let $F$ be a commutative ring with an involution, let $T$ be a form over $F$, let $\gamma, u, u'$ be isometries of $T$ with $u, u' \in \mathsf{U}$, and let $N \in F$. Then

$$\det\mathcal{Z} \cdot \overline{\det\mathcal{Z}} - N^2 D_\varrho(\mathcal{Z})\overline{D_\varrho(\mathcal{Z})}$$

has the same value for $\mathcal{Z} = \mathcal{Z}(u^{-1}\gamma u')$ and for $\mathcal{Z} = \mathcal{Z}(\gamma)$. In particular $\mathsf{g}(u^{-1}\gamma u') = \mathsf{g}(\gamma)$ for rational $\gamma$ and rational $u, u' \in \mathsf{U}$.

Lean: `New.Filling.frameDisc_frameGram_inv_mul_mul_of_mem_besselU` (New/Spanning/Unfolding/Link.lean).

*Proof.* We prove the stronger claim that every leading minor $D_l$, $0 \leq l \leq \varrho + 1$, is unchanged. The claim of the lemma follows, since its expression involves only $D_{\varrho+1} = \det\mathcal{Z}$ and $D_\varrho$.

*Step 1: $u$ acts on the frame by an upper unitriangular matrix.* By definition, $u \in \mathsf{U}$ means $u_{ij} = \delta_{ij}$ for all basis indices $i, j$ with $\operatorname{level}(j) \leq \operatorname{level}(i)$. The level of $\mathfrak{f}_b$ is $b$. Look at the column of $u$ at $\mathfrak{f}_b$. Its entries at the rows of level at least $b$ are those of the identity. So

$$u\mathfrak{f}_b = \mathfrak{f}_b + \sum_{\operatorname{level}(i) < b} u_{i\mathfrak{f}_b}\, i.$$

The basis vectors of level less than $b$ are $e_0, \dots, e_{b-1}$, and these are the frame vectors $\mathfrak{f}_0, \dots, \mathfrak{f}_{b-1}$. So $u\mathfrak{f}_b = \sum_a U_{ab}\mathfrak{f}_a$, where $U = (u_{\mathfrak{f}_a\mathfrak{f}_b})_{a,b}$ is the frame block of $u$, and $U$ is upper triangular with $1$ on the diagonal. The same holds for $u'$, with the matrix $U'$.

*Step 2: the frame products transform by $U$ and $U'$.* Since $u$ is an isometry, $h(x, u^{-1}y) = h(ux, uu^{-1}y) = h(ux, y)$. So

$$\mathcal{Z}(u^{-1}\gamma u')_{ab} = h(u\mathfrak{f}_a, \gamma u'\mathfrak{f}_b) = \sum_{c, d}\overline{U_{ca}}\, h(\mathfrak{f}_c, \gamma\mathfrak{f}_d)\, U'_{db}.$$

The form is conjugate linear in the first argument. In matrix form, $\mathcal{Z}(u^{-1}\gamma u') = U^*\mathcal{Z}(\gamma)U'$, where $U^* = \bar{U}^{\mathrm{T}}$.

*Step 3: leading blocks.* Let $l \leq \varrho + 1$ and let $a, b < l$. In the sum of Step 2, $U_{ca} = 0$ unless $c \leq a$, and $U'_{db} = 0$ unless $d \leq b$. So only $c, d < l$ contribute, and the leading block of order $l$ satisfies

$$\mathcal{Z}(u^{-1}\gamma u')_l = (U_l)^*\, \mathcal{Z}(\gamma)_l\, U'_l,$$

where $U_l$ and $U'_l$ are the leading blocks of $U$ and $U'$. These blocks are upper unitriangular, so $\det U'_l = 1$ and $\det (U_l)^* = \overline{\det U_l} = 1$. The determinant is multiplicative over a commutative ring. So $D_l(\mathcal{Z}(u^{-1}\gamma u')) = D_l(\mathcal{Z}(\gamma))$. $\square$

**Remark (Formalization).** The source proves the invariance of the minors as [Lemma](/decl/New.Filling.leadingMinor_frameGram_besselU_mul/) of [the chapter on Bessel subgroups](/chapter/bessel-bruhat/). It derives it from a more general lemma on the groups $Q_l$ of partially unitriangular isometries ([Lemma](/decl/New.Floors.FloorGroups.leadingMinor_frameGram_partialUnitriangularGroup_mul/)): the minors of order $j \leq l$ do not change under $Q_l$, and $\mathsf{U} \subset Q_l$ for every $l$. The proof above is the case $l = \varrho + 1$ of that lemma. The function `frameDisc` is applied to $\mathcal{Z}(u^{-1}\gamma u')$, which the source writes as `T.frameGram (u⁻¹ * γ * u').val`.

**Definition (Stable sets).** A set $\mathcal{T}$ of rational isometries is stable if $u^{-1}\gamma u' \in \mathcal{T} \iff \gamma \in \mathcal{T}$ for all rational $u, u' \in \mathsf{U}$ and all $\gamma$.

Lean: `New.Filling.IsStable` (New/Spanning/Unfolding/Setup.lean).

The pair condition is the other part of the cell rank. It needs two lemmas.

**Lemma (Pairs under the unipotent group).** Let $u \in \mathsf{U}$. If a norm one pair occurs from $j$ for $\gamma$, then it occurs from $j$ for $u\gamma$.

Lean: `New.NormOnePairOccursFrom.besselU_mul` (New/Spanning/Unfolding/Link.lean).

*Proof.* Keep the same $c$. Let $a \geq j$, and let $x, y$ give the pair at $a$ for $\gamma$. Apply $u$ to $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$. By Step 1 of the previous proof, $u(\mathfrak{f}\cdot x) = \mathfrak{f}\cdot(Ux)$, and the right side becomes $(u\gamma)\mathfrak{f}\cdot y$. For $b \geq a$,

$$(Ux)_b = \sum_i U_{bi}x_i = x_b,$$

since $U_{bi} = \delta_{bi}$ for $i \leq b$, and $x_i = 0$ for $i > b \geq a$. So $Ux$ vanishes above $a$ and $(Ux)_a = c$. The pair $(Ux, y)$ occurs at $a$ for $u\gamma$. $\square$

**Lemma (Pairs under inversion).** If a norm one pair occurs from $j$ for $\gamma$, then it occurs from $j$ for $\gamma^{-1}$.

Lean: `New.NormOnePairOccursFrom.inv` (New/Spanning/Unfolding/Link.lean).

*Proof.* Use the constant $\bar{c}$, which has $\bar{c}c = 1$. Apply $\gamma^{-1}$ to $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$. This gives $\mathfrak{f}\cdot y = \gamma^{-1}\mathfrak{f}\cdot x$, and so $\mathfrak{f}\cdot(\bar{c}y) = \gamma^{-1}\mathfrak{f}\cdot(\bar{c}x)$. The vectors $\bar{c}y$ and $\bar{c}x$ vanish above $a$, with the entries $\bar{c}$ and $\bar{c}c = 1$ at $a$. $\square$

**Lemma (Cells are stable).** For each $j$, the set of rational $\gamma$ with the cell rank $j$ is stable.

Lean: `New.Filling.isStable_hasCellRank` (New/Spanning/Unfolding/Link.lean).

*Proof.* Let $u, u' \in \mathsf{U}$. Suppose a norm one pair occurs from $j$ for $\gamma$. Apply the two lemmas in turn: it occurs for $u^{-1}\gamma$, for $(u^{-1}\gamma)^{-1} = \gamma^{-1}u$, for $u'^{-1}\gamma^{-1}u$, and for its inverse $u^{-1}\gamma u'$. The converse is the same argument with $u^{-1}, u'^{-1}$ and $u^{-1}\gamma u'$ in place of $u, u'$ and $\gamma$. The leading minors and the discriminant do not change, by the proof of the invariance lemma. So all three conditions of the cell rank hold for $u^{-1}\gamma u'$ if and only if they hold for $\gamma$. $\square$

The pair condition from $j$ gives shared vectors with any prescribed coefficients from $j$ on.

**Lemma (Shared vectors with prescribed tails).** Suppose a norm one pair occurs from $j$ for $\gamma$. Then for every $y$ there are $x, y'$ with $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y'$ and $y'_a = y_a$ for all $a \geq j$.

Lean: `New.Filling.exists_frameImage_eq_of_normOnePairOccursFrom` (New/Spanning/Unfolding/Link.lean).

*Proof.* By descending induction on $j$. For $j = \varrho + 1$ take $x = y' = 0$. Suppose the claim holds for $j + 1$, with $x, w$: so $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot w$ and $w_a = y_a$ for $a > j$. Let $X, Y$ give the pair at $j$, so $Y_j = 1$ and $X, Y$ vanish above $j$. Put $\lambda = y_j - w_j$. Then $x + \lambda X$ and $w + \lambda Y$ give a shared vector. Its coefficient at $j$ is $w_j + \lambda = y_j$, and at $a > j$ it is $w_a = y_a$. $\square$

### When the discriminant vanishes

**Lemma (The image frame is independent).** For a rational $\gamma$, $\gamma\mathfrak{f}\cdot y = 0$ only if $y = 0$.

Lean: `New.Filling.frameImage_mulVec_eq_zero_iff` (New/Spanning/Unfolding/Link.lean).

*Proof.* The matrix $\gamma$ is invertible, so $\mathfrak{f}\cdot y = 0$, and the frame vectors are distinct basis vectors. $\square$

**Lemma (Vanishing discriminant and shared vectors).** For a rational $\gamma$, $\mathsf{g}(\gamma) = 0$ if and only if there are $x$ and $y \neq 0$ with $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$.

Lean: `New.Filling.termDisc_eq_zero_iff_exists` (New/Spanning/Unfolding/Link.lean).

*Proof.* Write $Z = Z(\gamma)$.

*Case $\det Z = 0$.* Then $\mathsf{g}(\gamma) = -N^2|D_\varrho|^2$. By [Theorem](/decl/New.Filling.termDisc_pos_or_eq_zero/), $\mathsf{g}(\gamma) \neq 0$ would force $\det Z \neq 0$. So $\mathsf{g}(\gamma) = 0$. Take $y \neq 0$ with $Zy = 0$ and put $t = \gamma\mathfrak{f}\cdot y$. The norm identity ([Lemma](/decl/New.Filling.norm_sq_middle_part_eq/)) with $D = 0$ gives $N\sum_i|\Phi_v(t_{x_i})|^2 = -N^2|\Phi_v(y_\varrho)|^2 \leq 0$. Its part 4 gives $x$ with $\mathfrak{f}\cdot x = t$. So both sides of the claim hold.

*Case $\det Z \neq 0$.* Let $c$ be the last column of the adjugate of $Z$, so $Zc = (0, \dots, 0, \det Z)$ and $c_\varrho = D_\varrho$. Put $t = \gamma\mathfrak{f}\cdot c$. Part 3 of the norm identity gives $N\sum_i|\Phi_v(t_{x_i})|^2 = \Phi_v(\mathsf{g}(\gamma))$. So $\mathsf{g}(\gamma) = 0$ if and only if the $X_0$-part $t_0$ of $t$ vanishes. If $t_0 = 0$, then $t$ has no $e^*$-part and no $X_0$-part, so $t = \mathfrak{f}\cdot x$ for some $x$, and $c \neq 0$ since $Zc \neq 0$. Conversely, let $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$ with $y \neq 0$. By the lemma on products of a shared vector, $Zy = (0, \dots, 0, -Nx_\varrho)$. Since $Z$ is invertible, $y = \lambda c$ with $\lambda = -Nx_\varrho/\det Z$, and $\lambda \neq 0$ since $y \neq 0$. The vector $\gamma\mathfrak{f}\cdot y = \lambda t$ lies in the frame span, so its $X_0$-part $\lambda t_0$ is $0$. So $t_0 = 0$. $\square$

**Remark (Formalization).** The source proves the two facts on $t_0$ that this proof takes from the norm identity through the link isometry of [the next section](/chapter/anatomy-of-a-term/#the-link). It uses [Lemma](/decl/New.Filling.exists_frameImage_eq_of_frameProducts_mulVec_eq_zero/) and [Theorem](/decl/New.Filling.mul_dotProduct_comp_indexX₀_eq_sub/). The two routes compute the same quantity.

**Theorem (Vanishing discriminant).** For a rational $\gamma$, $\mathsf{g}(\gamma) = 0$ if and only if the spans of $\mathfrak{f}$ and of $\gamma\mathfrak{f}$ have a nonzero intersection.

Lean: `New.Filling.termDisc_eq_zero_iff` (New/Spanning/Unfolding/Link.lean).

*Proof.* A nonzero vector in both spans is $\mathfrak{f}\cdot x = \gamma\mathfrak{f}\cdot y$ with $\gamma\mathfrak{f}\cdot y \neq 0$, that is, with $y \neq 0$ by the independence lemma. Apply the previous lemma. $\square$

So a term of cell rank $j \leq \varrho$ has $\mathsf{g}(\gamma) = 0$, and its frame span meets the image span. A term of the top cell rank has $\mathsf{g}(\gamma) \neq 0$, and the two spans are in general position.

### The big cell

Let $p = (p_0, p_1, \dots)$ be units, and let $w_p$ be [the Weyl element](/decl/New.Floors.FloorGroups.weylElem/) with $e_a \mapsto p_ae^*_a$ and $e^*_a \mapsto \bar{p}_a^{-1}e_a$ for $a < \varrho$, fixing the middle vectors. Let $\sigma$ lie in [the floor group](/decl/New.Shape.Form.floorGroup/) of level $\varrho$, the isometries that fix every $e_a$ and $e^*_a$. The elements $w_p\sigma$ form the big cell of the Bruhat decomposition of [the chapter on Bessel subgroups](/chapter/bessel-bruhat/).

**Theorem (The discriminant on the big cell).** Let $A$ be a field with an involution and let $T$ be a form over $A$ with a hermitian invertible Gram matrix. Let $\sigma$ lie in the floor group of level $\varrho$, let $t = h(z, \sigma z)$ and $d = \prod_{a < \varrho} p_a$. Then

$$\det\mathcal{Z}(w_p\sigma)\,\overline{\det\mathcal{Z}(w_p\sigma)} - N^2 D_\varrho\overline{D_\varrho} = d\bar{d}\,(t\bar{t} - N^2).$$

Lean: `New.Filling.frameDisc_weylElem_mul` (New/Spanning/Unfolding/Link.lean).

*Proof.* By [Theorem](/decl/New.Filling.frameGram_weylElem_mul/) of the chapter on Bessel subgroups, $\mathcal{Z}(w_p\sigma)$ is diagonal with the entries $p_0, \dots, p_{\varrho-1}, t$. Indeed $h(e_a, w_p\sigma e_b) = h(e_a, p_be^*_b) = p_b\delta_{ab}$, and $w_p\sigma z = \sigma z$ is a middle vector. So $\det = dt$ and $D_\varrho = d$. Then $dt\,\overline{dt} - N^2d\bar{d} = d\bar{d}(t\bar{t} - N^2)$. $\square$

**Example.** Take $\sigma = 1$. Then $t = h(z, z) = -N$, so $t\bar{t} - N^2 = 0$, and the discriminant of $w_p$ vanishes. This agrees with the theorem on vanishing: $w_p z = z$, so $z$ is a shared vector. If $\sigma$ moves $z$ to a vector $\sigma z$ with $|h(z, \sigma z)| \neq N$, the discriminant is not zero. Over $E$ the theorem on positivity says more: $\Phi_v(t\bar{t}) \geq N^2$ at every place, with equality at one place only if $\mathsf{g} = 0$. This is the reverse Cauchy-Schwarz inequality for the vectors $z$ and $\sigma z$ of norm $-N$ in the space $X_0 \perp Ez$ of signature $(k, 1)$ at each place.
