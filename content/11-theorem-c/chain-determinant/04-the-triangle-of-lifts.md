---
title: The triangle of lifts
lean:
  - New/Determinant/Chain/TriangleLifts.lean
decls:
  - New.formNegEquiv
  - New.formNegEquiv_formRep
  - New.Exchange.IsEdgeFamily.exists_inner_modLift_eq_inner_modTransposedLift
  - New.Data.TriangleForm
  - New.Data.triangleLift
  - New.Data.triangleNegEquiv
  - New.Data.triangleBaseLevel
  - New.Data.triangleBase
  - New.Data.triangleNegEquiv_triangleRep
  - New.Data.hasLevel_triangleNegEquiv
  - New.Data.exists_triangleRep_triangleLift_eq_smul
  - New.Data.isSharp_pointDatum
  - New.Data.triangleFirstLift
  - New.Data.two_mul_card_gridIndex_zero_lt
  - New.Data.mem_triangleBase_of_inner_eq_inner_triangleFirstLift
  - New.Data.eq_zero_of_triangleFirstLift_eq_zero
  - New.Data.exists_hasSum_inner_triangleFirstLift
  - New.Data.leftPairChar
  - New.Data.IsLeftPair
  - New.Data.IsReversedPair
  - New.Data.triangleTransposedLift
  - New.Data.triangleReversedLift
  - New.Data.isEdgeFamily_triangleKernel
  - New.Data.exists_isLeftPair
  - New.Data.exists_isReversedPair
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The triangle of lifts

This section builds the spaces and the lifts of the triangle, and it proves the norm formula for the first lift of each row. That formula is the hypothesis on the first lift in the theorem on weighted chains of Section 2.

### The spaces of the triangle

The source has two grids of hermitian spaces, selected by a flag $z$ ([parameters and grids](/chapter/upper-bound-objects/)). This chapter needs the grid $z = \text{false}$ for the chain determinant. The source proves the results of this section and of Section 5 for both values of $z$, since a later chapter uses the grid $z = \text{true}$. We write the case $z = \text{false}$ and remark on the other case where it differs.

The triangle has the positions $(i, n)$ with $i, n \in \mathbb{N}$. Write $V_{i,n}$ for the hermitian space `gridSpace i z 0 n`, the node $(0, n)$ of the grid with offset $i$. Its index set is that of $Y_n$: the $r$ basis vectors of $Y_0$ and $n$ blocks of $t$ vectors. The offset $i$ changes the signs and the parameter at infinity. For $i = 0$ the space $V_{0,n}$ is $Y_n$. The space $V_{i+1,0}$ is the opposite space $-V_{i,0}$, the same lattice with the negated hermitian form.

**Definition (Forms of the triangle).** $F_{i,n}$ is the space of forms on $V_{i,n}$ whose type at infinity is the discrete series kernel of the parameter of the node. The finite adelic group of $V_{i,n}$ acts on $F_{i,n}$ by right translation.

Lean: `New.Data.TriangleForm` (New/Determinant/Chain/TriangleLifts.lean).

The modulus of the triangle is $\mathfrak{m} = \varpi Q$ for $z = \text{false}$, and $\varpi^b$ with $b$ = `natB` for $z = \text{true}$.

**Definition (Lifts of the triangle).** The lift $a_{i,n} : F_{i,n} \to F_{i,n+1}$ is the theta lift for the twist $\vartheta$ that adds the block $n + i + 1$. Its character is the character of the lift of index $n + i + 1$, twisted by $\vartheta^{n+i+1}$ for $z = \text{false}$, times a power of $\upsilon$. Its polynomial at infinity is the joint harmonic of the two parameters. Its finite datum is the indicator function of the inclusion matrix $x_0 = \binom{1}{0}$ modulo $\mathfrak{m}$, and the vacuum at the other places.

Lean: `New.Data.triangleLift` (New/Determinant/Chain/TriangleLifts.lean).

**Lemma (The lifts are edges).** For $i + n < m$ the lift $a_{i,n}$ is an edge in the sense of [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/).

Lean: `New.Data.isEdgeFamily_triangleKernel` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* The parameters of $(i, n)$ and $(i, n+1)$ correspond, by the theorem that each step inserts a block ([parameters and grids](/chapter/upper-bound-objects/)). The characters have the weights of the two ends. So the theorem that corresponding parameters give an edge applies. $\square$

This lemma is the source of every analytic property of $a_{i,n}$ below.

### The opposite space

Row $i$ starts at $V_{i,0}$, which is $Y_0$ with the sign $(-1)^i$. A form $y$ on $V$ gives the form $y \circ \nu$ on $-V$, where $\nu$ identifies the two unitary groups.

**Lemma (Forms on the opposite space).** For a parameter $l$, the map $y \mapsto y \circ \nu^{-1}$ is a linear isometry from the forms of type $l$ on $V$ to the forms of type $l$ on $-V$. It commutes with right translation by the finite adelic group.

Lean: `New.formNegEquiv`, `New.formNegEquiv_formRep` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* The identification $\nu$ maps the automorphic quotient of $V$ onto that of $-V$, and it carries the quotient measure to the quotient measure (`New.integral_neg_quotMeasure`). So the Petersson products agree. The map $\nu$ is the identity on the finite adelic points, so it commutes with right translation. $\square$

**Definition (Copies in each row).** $\epsilon_i : F_{0,0} \to F_{i,0}$ is the composite of $i$ of these isometries. So $\epsilon_0 = 1$ and $\epsilon_{i+1} = \nu_* \circ \epsilon_i$.

Lean: `New.Data.triangleNegEquiv` (New/Determinant/Chain/TriangleLifts.lean).

**Definition (The base).** The base level is the level $J_M$ of $Y_0$ for $z = \text{false}$, and the principal level of $\varpi^b$ for $z = \text{true}$. The base $B \subseteq F_{0,0}$ is the space of forms that the base level fixes.

Lean: `New.Data.triangleBaseLevel`, `New.Data.triangleBase` (New/Determinant/Chain/TriangleLifts.lean).

**Lemma (The copies keep the level).** Each $\epsilon_i$ commutes with right translation. For $y \in B$, the copy $\epsilon_i y$ is fixed by the base level and by the principal level of $\mathfrak{m}$.

Lean: `New.Data.triangleNegEquiv_triangleRep`, `New.Data.hasLevel_triangleNegEquiv` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* Induction on $i$ with the last lemma. The principal level of $\mathfrak{m}$ is in the base level, since the chosen places divide $\mathfrak{m}$. $\square$

The source also has the adjoint of a lift. It is a transposed lift from the opposite space.

**Theorem (Adjoint of a lift).** Let $\Phi$ make an edge from $V$ to $W$ with the characters $a$ and the flag false, and let $\Phi'$ make an edge from $-V$ to $W$ with the characters $(a_M)^{-1}\upsilon^{\#M}$ and the flag true. For every finite datum $\Psi$ there is a finite datum $\Psi'$ with
$$\langle x, L_{\Phi,\Psi}\,y\rangle = \langle L^{\top}_{\Phi',\Psi'}\,x, \nu_* y\rangle$$
for all forms $y$ on $V$ and $x$ on $W$. Here $L^\top$ is the transposed lift from $W$ to $-V$.

Lean: `New.Exchange.IsEdgeFamily.exists_inner_modLift_eq_inner_modTransposedLift` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* The complex conjugate of the theta kernel of $(V, W)$ with $\Psi$ and $\Phi$ is $c$ times the theta kernel of $(-V, W)$ with the datum $\Psi_0(x) = \overline{\Psi(\epsilon^{-1}x)}$, the conjugate polynomial $\bar\Phi$ and the opposite characters (`New.exists_conj_modKernel_eq_mul_modKernel_neg`, [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/)). Here $\epsilon$ is a fixed scalar of norm $-1$. So $\overline{L_{\Phi,\Psi}\,y} = c\,L'$, where $L'$ is the lift of $\overline{\nu_* y}$ from $-V$ with $\Psi_0$ and $\bar\Phi$. The edge $\Phi'$ gives one $\kappa$ with $\langle x, \overline{L'}\rangle_{\mathrm{Pet}} = \kappa\,\langle L^\top_{\Phi',\Psi_0}x, \nu_* y\rangle$ ([seesaw for periods](/chapter/theta-lifts-seesaw/)). So $\langle x, L_{\Phi,\Psi}\,y\rangle = \bar c\,\kappa\,\langle L^\top_{\Phi',\Psi_0}x, \nu_* y\rangle$. The transposed lift is linear in the datum, so $\Psi' = c\,\bar\kappa\,\Psi_0$ works. $\square$

### Left pairs and descents

**Definition (Left and reversed pairs).** The left pair of row $i$ at column $n$ joins $(i+1, n)$ and $(i, n+1)$. Its character on a space of rank $M$ is $\lambda_i(M) = \alpha_i(M)^{-1}\upsilon^{M}$, where $\alpha_i$ is the character of the first lift $a_{i,0}$. A polynomial $\Phi$ is a left pair if it makes an edge from $(i+1, n)$ to $(i, n+1)$ with these characters and the flag true. It is a reversed pair if it makes the edge from $(i, n+1)$ to $(i+1, n)$.

Lean: `New.Data.leftPairChar`, `New.Data.IsLeftPair`, `New.Data.IsReversedPair` (New/Determinant/Chain/TriangleLifts.lean).

**Lemma (Left pairs exist).** For $i + n < m$ there are a left pair and a reversed pair.

Lean: `New.Data.exists_isLeftPair`, `New.Data.exists_isReversedPair` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* The negated parameters of $(i+1, n)$ and $(i, n+1)$ correspond in both directions, since the second adds the first block $i + 1$ to an interval of blocks (`New.Data.paramsCorrespond_leftPair`, [parameters and grids](/chapter/upper-bound-objects/)). So the theorem that corresponding parameters give an edge applies ([seesaw for periods](/chapter/theta-lifts-seesaw/)). $\square$

**Definition (Descents and ascents).** For a left pair $\Phi$ and a finite datum $\Psi$ modulo $\mathfrak{m}$, the descent $d_{i,n} : F_{i,n+1} \to F_{i+1,n}$ is the transposed lift along the left pair. For a reversed pair, the ascent $F_{i+1,n} \to F_{i,n+1}$ is the transposed lift along the reversed pair.

Lean: `New.Data.triangleTransposedLift`, `New.Data.triangleReversedLift` (New/Determinant/Chain/TriangleLifts.lean).

Both are linear in the datum: they are the sums $\sum_\eta \Psi(\eta)$ times the map for the indicator function of $\eta$ (`New.Data.triangleTransposedLift_eq_sum`, `New.Data.triangleReversedLift_eq_sum`). Section 5 chooses the data.

### The first lift of each row

**Definition (First lift of a row).** For $i < m$, the first lift of row $i$ is $a_i = a_{i,0} \circ \epsilon_i : F_{0,0} \to F_{i,1}$.

Lean: `New.Data.triangleFirstLift` (New/Determinant/Chain/TriangleLifts.lean).

The first lift goes from a space of rank $r$ to a space of rank $r + t = 6r$. For $z = \text{true}$ the ranks are $r + 1$ and $r + t$.

**Lemma (Range of Rallis' formula).** For both grids, $2\,\#\text{index}(0,0) < \#\text{index}(0,1)$.

Lean: `New.Data.two_mul_card_gridIndex_zero_lt` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* For $z = \text{false}$, $2r < 6r$. For $z = \text{true}$, $2(r + 1) < r + 5r$, since $r \geq 3$. $\square$

**Lemma (Intertwining).** Let $i < m$ and let $u$ be an integral point of the finite adelic group of $V_{i,0}$. There are a point $g$ of the group of $V_{i,1}$ and $c \in \mathbb{C}$ with $|c| = 1$ such that $g \cdot a_{i,0}(f) = c\,a_{i,0}(u \cdot f)$ for every $f \in F_{i,0}$.

Lean: `New.Data.exists_triangleRep_triangleLift_eq_smul` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* Reduction modulo $\mathfrak{m}$ is onto the general linear group of the residue ring. So there is an integral $g$ whose reduction is the block matrix $\mathrm{diag}(\bar u, 1)$. Then $\bar g^{-1}x_0\bar u = x_0$ for the inclusion matrix $x_0$. The pair $(u, g)$ fixes the indicator function of $x_0$, so in the Weil representation it acts on the finite datum by the value $c$ of the character of the pair, which has $|c| = 1$. The lift is an edge, so the law for translates of lifts ([theta lifts and the seesaw](/chapter/theta-lifts-seesaw/)) gives the claim. $\square$

**Lemma (Sharpness of the point datum).** The finite datum of $a_{i,0}$ is sharp for the principal level $J$ of $\mathfrak{m}$, with the mass
$$\frac{1}{\#\mathrm{Mat}_{(r+t) \times r}(O/\mathfrak{m})\cdot\#\mathrm{GL}_r(O/\mathfrak{m})}.$$

Lean: `New.Data.isSharp_pointDatum` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* The datum is $F = 1_{x_0}$, with $\langle F, F\rangle = 1$. On its support $x_0^\top x = 1$. The criterion for sharp vacuum data of [the inner product formula](/chapter/rallis-inner-product/) applies, since the character of the lift has trivial tame part outside the places of $\mathfrak{m}$. It gives the mass $\langle F, F \rangle/[K_0 : J]$, which is the displayed number. $\square$

**Lemma (Fixed vectors).** Let $i < m$ and $y \in B$. If $v \in F_{0,0}$ has $\langle v, x\rangle = \langle a_i y, a_i x\rangle$ for every $x$, then $v \in B$.

Lean: `New.Data.mem_triangleBase_of_inner_eq_inner_triangleFirstLift` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* Let $u$ be in the base level, and write $\pi$ for right translation on $F_{0,0}$. The intertwining lemma gives $g$ and $|c| = 1$ with $g\,a_i(x) = c\,a_i(\pi(u)x)$ for every $x$, because $\epsilon_i$ commutes with translation. Also $\pi(u)y = y$. Right translation is unitary and bijective, so it suffices to test $\pi(u)v$ against the vectors $\pi(u)x$:
$$\langle \pi(u)v, \pi(u)x\rangle = \langle a_i y, a_i x\rangle = \langle c\,a_i(\pi(u) y), c\,a_i(\pi(u)x)\rangle = \langle a_i y, a_i(\pi(u) x)\rangle = \langle v, \pi(u) x\rangle.$$
So $\pi(u)v = v$. $\square$

**Lemma (Injectivity of the first lift).** For $i < m$ and $y \in B$, $a_i y = 0$ implies $y = 0$.

Lean: `New.Data.eq_zero_of_triangleFirstLift_eq_zero` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* Rallis' formula with injectivity ([the unramified series and injectivity](/chapter/rallis-inner-product/)) applies to the edge $(V_{i,0}, V_{i,1})$, by the lemma on the range. The point datum is sharp for $J$, and $\epsilon_i y$ has level $J$. So the lift is injective on $\epsilon_i y$, and $\epsilon_i y = 0$. Since $\epsilon_i$ is an isometry, $y = 0$. $\square$

**Theorem (Norm of the first lift).** For $i < m$ there is $C \in \mathbb{C}$ such that for every $m$-fold twist $\vartheta$ and every $y \in B$:

1. if $v$ has $\langle v, x\rangle = \langle a_i y, a_i x\rangle$ for every $x \in F_{0,0}$, then $v \in B$, and $v = 0$ implies $y = 0$;
2. for every $x \in F_{0,0}$, the series over the cosets $\gamma$ of the points that are integral outside $\mathfrak{m}$ and its conjugate
$$\sum_\gamma C\,T_\gamma(x, y)$$
converges to $\#\mathrm{GL}_r(O/\mathfrak{m})\,\langle a_i x, a_i y\rangle$. Here $T_\gamma(x, y)$ is the coset term $\mathrm{mc}(g_\gamma)\langle x, g_\gamma y\rangle$ of [the inner product formula](/chapter/rallis-inner-product/), divided by $\#\mathrm{Mat}_{(r+t)\times r}(O/\mathfrak{m})$.

Lean: `New.Data.exists_hasSum_inner_triangleFirstLift` (New/Determinant/Chain/TriangleLifts.lean).

*Proof.* Part 1 is the lemma on fixed vectors. If $v = 0$, then $\langle a_i y, a_i y \rangle = \langle v, y\rangle = 0$, so $a_i y = 0$ and $y = 0$ by injectivity. For part 2, Rallis' formula with the sharp point datum gives a constant $C$, independent of $\vartheta$, such that the series of $C$ times the mass times the coset terms of $\epsilon_i x$ and $\epsilon_i y$ converges to $\langle a_i x, a_i y\rangle$. The coset terms of $\epsilon_i x, \epsilon_i y$ are those of $x, y$, since $\epsilon_i$ is a unitary map that commutes with translation. Multiply by $\#\mathrm{GL}_r(O/\mathfrak{m})$. It cancels the factor in the mass. $\square$

**Remark (Formalization).** The constant $C$ comes from an existence statement and is never computed. The first lift is the composite with $\epsilon_i$, so all first lifts start from the same space $F_{0,0}$. The theorem of Section 2 needs this, because there the first lift of each row starts at the common corner. The file declares `attribute [local implicit_reducible]` for `GridIndex`, `BlockIndex` and `kernelPair` (TriangleLifts.lean, line 516), so that rewriting sees through these definitions. The simp call at the end of the proof of part 2 removes the lemma `Bool.cond_eq_ite` from the simp set.

### Example: the first row

For $i = 0$ the first lift is $a_{0,0} : F_{0,0} \to F_{0,1}$, the first lift of the chain from $Y_0$ to $Y_1$, for $z = \text{false}$. The theorem on the norm of the first lift is then the formula of [injectivity and the norm of one lift](/chapter/single-theta-lifts/) for $j = 1$ at a point datum. For $i = 1$ the space $V_{1,0}$ is $-Y_0$, and $a_1$ lifts to $V_{1,1}$, which has the block $2$ of $Y_2$ in place of the block $1$. The descent $d_{0,1} : F_{0,2} \to F_{1,1}$ removes the block $1$.
