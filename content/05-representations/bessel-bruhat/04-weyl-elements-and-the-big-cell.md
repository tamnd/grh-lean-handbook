---
title: Weyl elements and the big cell
lean:
  - Lib/DiscreteSeries/Bruhat/FloorGroups.lean
  - Lib/DiscreteSeries/Bruhat/BigCell.lean
decls:
  - New.Floors.FloorGroups.weylElem
  - New.Floors.FloorGroups.floorWeyl
  - New.Floors.FloorGroups.leadingMinor_frameGram_partialUnitriangularGroup_mul
  - New.Filling.leadingMinor_frameGram_besselU_mul
  - New.Filling.frameGram_weylElem_mul
  - New.Filling.leadingMinor_weylElem_mul
  - New.Filling.exists_pivot_mul_eq_one
  - New.Filling.exists_eq_mul_floorWeyl_mul_of_mem_intGL
  - New.Filling.exists_integral_big_cell_decomp
  - New.Filling.exists_big_cell_decomp
  - New.Filling.big_cell_factors_unique
  - New.Filling.big_cell_factors_mem_intGL
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Weyl elements and the big cell

The unfolding of Poincaré series gives a sum over double cosets $\mathsf U \gamma \mathsf U$. This section proves that an element whose frame matrix has nonzero leading minors is $u^{-1} w_p \sigma u'$, where $w_p$ is a Weyl element on all hyperbolic pairs and $\sigma$ fixes these pairs, and that the factors are unique. Over a subring $R$ the factors are integral when the minors are units of $R$.

For a connected reductive group over a field the Bruhat decomposition is $G = \bigsqcup_w B w B$, and the big cell is the open cell of the longest Weyl element (Borel, *Linear Algebraic Groups*, 2nd ed., Theorem 14.12). Here the unipotent group $\mathsf U$ is the unipotent radical of a parabolic subgroup, not of a Borel subgroup, and the Levi part on the middle block is the factor $\sigma$. The source proves this case directly, over a commutative ring with involution, by a descent through the floors.

### Leading minors and the frame matrix

Recall the frame $f = (e_0, \dots, e_{\varrho - 1}, z)$ and the frame matrix $Z(\gamma)_{jl} = h(f_j, \gamma f_l)$, of size $n = \varrho + 1$. For $0 \le l \le n$ let $\delta_l(\gamma)$ be the leading minor of order $l$ of $Z(\gamma)$, so $\delta_0 = 1$ (Lean: `New.leadingMinor`).

**Proposition.** Let $s, s' \in Q_l$ and $j \le l$. Then $\delta_j(s^{-1} \gamma s') = \delta_j(\gamma)$ for every $\gamma \in G_T$.

Lean: `New.Floors.FloorGroups.leadingMinor_frameGram_partialUnitriangularGroup_mul` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

*Proof.* First consider a right factor. An element $s' \in Q_l$ sends each frame vector $f_b$ with $b < j$ to $f_b$ plus a combination of basis vectors of level below $b$. The basis vectors of level below $b$ are $e_0, \dots, e_{b-1}$, which are earlier frame vectors. So on the first $j$ frame vectors $s'$ acts by a unitriangular matrix, and the upper left $j \times j$ block of $Z(\gamma s')$ is the block of $Z(\gamma)$ times a matrix of determinant $1$. Now consider a left factor. With $J = J_T$ we have $J s^{-1} = s^* J$, so $J s^{-1} \gamma s' = ((J\gamma)^* s)^* s'$. Two applications of the case of a right factor, with a conjugate transpose between them, give the claim, since $\det(M^*) = \overline{\det M}$. $\square$

**Corollary.** For $u, u' \in \mathsf U$ and all $j \le n$, $\delta_j(u^{-1} \gamma u') = \delta_j(\gamma)$.

Lean: `New.Filling.leadingMinor_frameGram_besselU_mul` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

*Proof.* $\mathsf U \subset Q_{\varrho + 1}$ and $n = \varrho + 1$. $\square$

### Weyl elements

**Definition.** Let $l \in \mathbb N$ and let $p : \mathbb N \to A^\times$. The *Weyl element* $w_p = w_{l, p}$ is the isometry with $e_a \mapsto p_a e^*_a$ and $e^*_a \mapsto \bar p_a^{-1} e_a$ for $a < \min(l, \varrho)$, which fixes all other basis vectors. For $c \in A$ the *floor Weyl element* $w_l(c)$ sends $e_l \mapsto c e^*_l$ and $e^*_l \mapsto \bar c^{-1} e_l$ and fixes the other basis vectors.

Lean: `New.Floors.FloorGroups.weylElem` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

Lean: `New.Floors.FloorGroups.floorWeyl` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

The map is an isometry since $h(p_a e^*_a, \bar p_a^{-1} e_a) = \bar p_a \bar p_a^{-1} = 1$. We have $w_{l+1, p} = w_l(p_l) w_{l, p}$ (Lean: `New.Floors.FloorGroups.weylElem_succ`), and $w_{l, p}$ commutes with every element of $H_l$ (Lean: `New.Floors.FloorGroups.commute_weylElem`).

**Remark (Formalization).** Two conventions of the source have junk cases. First, $w_l(c)$ is the identity when $l \ge \varrho$ or when $c$ is not a unit. Second, $w_{l, p}$ is defined for a whole sequence $p : \mathbb N \to A^\times$, and only the values $p_a$ with $a < \min(l, \varrho)$ matter (Lean: `New.Filling.weylElem_congr`). So the theorems below determine $p_a$ only for $a < \varrho$, and the values $p_a$ for $a \ge \varrho$ are arbitrary. No statement of the argument reads these values.

**Proposition.** Let $\sigma \in H_\varrho$ and $p : \mathbb N \to A^\times$. Then $Z(w_{\varrho, p}\sigma)$ is the diagonal matrix with entries $p_0, \dots, p_{\varrho - 1}, h(z, \sigma z)$. For $l < \varrho$ the leading minor is $\delta_{l+1}(w_{\varrho, p}\sigma) = p_0 p_1 \cdots p_l$.

Lean: `New.Filling.frameGram_weylElem_mul` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

Lean: `New.Filling.leadingMinor_weylElem_mul` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* The element $\sigma$ fixes all $e_a$ and $e^*_a$, so it preserves the middle block. So $w_p \sigma e_a = p_a e^*_a$, and $w_p \sigma z = \sigma z$ lies in the middle block. Then $h(e_b, p_a e^*_a) = p_a \delta_{ab}$, $h(z, p_a e^*_a) = 0$ and $h(e_b, \sigma z) = 0$. $\square$

For $\varrho = 1$ this is the computation of the model case in Section 1: the big cell is the set where $h(e_0, \gamma e_0) \ne 0$, and for $\gamma$ acting on the hyperbolic plane by $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ the condition is $c \ne 0$, as for $SL_2$.

### The pivot and one step of the descent

The descent works on one floor at a time. After $j$ steps the element is $u^{-1} w_{j, p} \sigma u'$ with $\sigma \in H_j$. The next pivot is $h(e_j, \sigma e_j)$, the coefficient of $e^*_j$ in $\sigma e_j$.

**Lemma.** Let $R \subset A$ be a subring and let $J_T$ have entries in $R$. Let $j < \varrho$, $\sigma \in H_j$ and $p : \mathbb N \to A^\times$, and let $w_{j, p}\sigma$ have entries in $R$. Let $d \in R$ with $\delta_{j+1}(w_{j, p}\sigma)\, d = 1$. Then there is $y \in R$ with $h(e_j, \sigma e_j)\, y = 1$.

Lean: `New.Filling.exists_pivot_mul_eq_one` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* Let $M$ be the upper left block of order $j + 1$ of $Z(w_{j,p}\sigma)$, and let $x = h(e_j, \sigma e_j)$. Since $w_{j,p}$ commutes with $\sigma$ and fixes $e_j$, the last column of $M$ has the entries $h(e_c, \sigma e_j)$ for $c \le j$. For $c < j$ the element $\sigma$ fixes $e_c$, so $h(e_c, \sigma e_j) = h(\sigma^{-1} e_c, e_j) = h(e_c, e_j) = 0$. So the last column of $M$ is $(0, \dots, 0, x)$. Expansion along it gives $\det M = x D$, where $D$ is the minor of order $j$. All entries are in $R$, so $D \in R$, and $x (D d) = 1$. $\square$

**Lemma.** Let $J_T$ be hermitian and invertible, let $A$ have an element $\tau$ with $\tau + \bar\tau = 1$, and let $R \subset A$ be a subring with $\bar R = R$ such that $J_T$ is unimodular over $R$, that is $J_T^* = J_T$ and $J_T \in GL(R)$. Let $j < \varrho$ and $\sigma \in H_j \cap GL(R)$. Let $x \in A^\times$ with $h(e_j, \sigma e_j) = x$ and $x, x^{-1} \in R$. Then there are $a \in \mathsf U \cap H_j$, $b \in \mathsf U$ and $\sigma' \in H_{j+1}$ with
$$\sigma = a\, w_j(x)\, \sigma'\, b^{-1},$$
and $a$, $b$ and $\sigma'$ lie in $GL(R)$.

Lean: `New.Filling.exists_eq_mul_floorWeyl_mul_of_mem_intGL` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* The vector $w = x^{-1} \sigma e_j$ is isotropic, it vanishes on the floors below $j$ since $\sigma \in H_j$, and its $e^*_j$ coefficient is $1$. By the computation in Section 3 it equals $\nu_j(v, \beta) e^*_j$ for a Heisenberg element $a = \nu_j(v, \beta)$ (Lean: `New.Floors.FloorGroups.exists_col_eq_heisenbergElem`). So $\sigma e_j = a\, w_j(x) e_j$. The vector $w$ has entries in $R$, and a Heisenberg element whose column at $e^*_j$ is integral lies in $GL(R)$ when $J_T$ is unimodular (Lean: `New.Filling.heisenbergElem_mem_intGL`). Put $g = \sigma^{-1} a\, w_j(x)$. It lies in $H_j$, it fixes $e_j$, and so it lies in $Q_{j+1} \cap H_j$. By Section 3 there is a Heisenberg element $b$ of floor $j$ with $\sigma' = g^{-1} b \in H_{j+1}$. Then $\sigma = a\, w_j(x)\, \sigma'\, b^{-1}$. The vector $b e^*_j = g e^*_j$ is integral since $g \in GL(R)$, so $b \in GL(R)$, and then $\sigma' \in GL(R)$. $\square$

### Existence on the big cell

**Theorem (Integral big cell).** Let $J_T$ be hermitian and invertible, let $A$ have an element $\tau$ with $\tau + \bar\tau = 1$, and let $R \subset A$ be a subring with $\bar R = R$ such that $J_T$ is unimodular over $R$. Let $\gamma \in G_T \cap GL(R)$, and assume that for every $l < \varrho$ there is $d \in R$ with $\delta_{l+1}(\gamma) d = 1$. Then for every $j \le \varrho$ there are $u, u' \in \mathsf U$, $p : \mathbb N \to A^\times$ and $\sigma \in H_j$ with
$$\gamma = u^{-1} (w_{j, p} \sigma) u',$$
such that $u$, $u'$ and $\sigma$ lie in $GL(R)$, and $p_a, p_a^{-1} \in R$ for all $a < j$.

Lean: `New.Filling.exists_integral_big_cell_decomp` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* Induction on $j$. For $j = 0$ take $u = u' = 1$ and $\sigma = \gamma$. Let the statement hold for $j < \varrho$, with $\gamma = u^{-1} w_{j,p} \sigma u'$. By the corollary on leading minors, $\delta_{j+1}(w_{j,p}\sigma) = \delta_{j+1}(\gamma)$, which has an inverse $d \in R$. The element $w_{j,p}\sigma$ is integral, since $w_{j,p}$ is integral when $p_a, p_a^{-1} \in R$ for $a < j$. The pivot lemma gives $x = h(e_j, \sigma e_j)$ with $x, x^{-1} \in R$. The step lemma gives $\sigma = a\, w_j(x)\, \sigma' b^{-1}$. Since $a \in H_j$ commutes with $w_{j,p}$, and $w_j(x) w_{j,p} = w_{j+1, p'}$ for the sequence $p'$ equal to $p$ except $p'_j = x$,
$$\gamma = (a^{-1} u)^{-1}\, w_{j+1, p'}\, \sigma'\, (b^{-1} u').$$
All new factors are integral, and $p'_a, (p'_a)^{-1} \in R$ for $a \le j$. $\square$

**Corollary (Big cell over a field).** Let $A$ be a field with an involution and an element $\tau$ with $\tau + \bar\tau = 1$, and let $J_T$ be hermitian and invertible. Let $\gamma \in G_T$ with $\delta_l(\gamma) \ne 0$ for $0 \le l \le \varrho$. Then there are $u, u' \in \mathsf U$, $p : \mathbb N \to A^\times$ and $\sigma \in H_\varrho$ with $\gamma = u^{-1}(w_{\varrho, p}\sigma) u'$.

Lean: `New.Filling.exists_big_cell_decomp` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* Apply the theorem with $R = A$ and $j = \varrho$. Every element of $G_T$ lies in $GL(A)$, and a nonzero minor has an inverse in $A$. $\square$

**Remark (Formalization).** The hypothesis of the corollary is indexed by $l = 0, \dots, \varrho$, so it includes $\delta_0 = 1 \ne 0$, which is free. The real conditions are $\delta_1, \dots, \delta_\varrho \ne 0$. The last minor $\delta_n = \det Z(\gamma)$ is not assumed. By the proposition on $Z(w_p\sigma)$ it equals $p_0 \cdots p_{\varrho - 1} h(z, \sigma z)$, and $h(z, \sigma z)$ may be $0$. So the big cell of the source is the set where the first $\varrho$ minors are nonzero, and $\sigma$ is any element of $H_\varrho$, not only an element that fixes $z$.

### Uniqueness and integrality

**Theorem (Uniqueness).** Let $\sigma, \tau \in H_\varrho$, $u, u', v, v' \in \mathsf U$ and $p, q : \mathbb N \to A^\times$, with
$$u^{-1}(w_{\varrho, p}\sigma)u' = v^{-1}(w_{\varrho, q}\tau)v'.$$
Then $p_a = q_a$ for all $a < \varrho$, $\sigma = \tau$, $u = v$ and $u' = v'$.

Lean: `New.Filling.big_cell_factors_unique` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* Put $y = u v^{-1}$ and $y' = u' v'^{-1}$, both in $\mathsf U$. The equation becomes $w_p \sigma y' = y\, w_q \tau$. Apply both sides to $e_b$ for $b < \varrho$. On the left, $y' e_b$ is $e_b$ plus a combination of the $e_a$ with $a < b$, and $w_p \sigma$ sends it to $p_b e^*_b$ plus a combination of the $p_a e^*_a$ with $a < b$. On the right we get $q_b\, y e^*_b$. Since $y \in \mathsf U$, the coefficient of $e^*_b$ in $y e^*_b$ is $1$ and the coefficients of the $e^*_a$ with $a < b$ are $0$. A comparison gives $p_b = q_b$ and $y e^*_b = e^*_b$ (Lean: `New.Filling.big_cell_column_eq`). An element of $\mathsf U$ that fixes all $e^*_b$ is $1$: its rows at the middle block and at the $e^*_a$ agree with $1$, and the isometry equation then gives the rows at the $e_a$ (Lean: `New.eq_one_of_mem_besselU_of_fix`). So $y = 1$ and $w_p = w_q$. Then $y' = \sigma^{-1} \tau$ lies in $H_\varrho \cap \mathsf U$, which is trivial by Section 3. $\square$

**Corollary.** Let $J_T$ be hermitian, invertible and unimodular over a subring $R$ with $\bar R = R$, and let $A$ have an element $\tau$ with $\tau + \bar\tau = 1$. Let $u, u' \in \mathsf U$, $\sigma \in H_\varrho$, and $p : \mathbb N \to A^\times$ with $p_a^{-1} \in R$ for all $a < \varrho$. If $u^{-1}(w_{\varrho, p}\sigma)u' \in GL(R)$, then $u$, $\sigma$ and $u'$ lie in $GL(R)$.

Lean: `New.Filling.big_cell_factors_mem_intGL` (Lib/DiscreteSeries/Bruhat/BigCell.lean).

*Proof.* The minors $\delta_{l+1} = p_0 \cdots p_l$ have the inverses $p_0^{-1} \cdots p_l^{-1} \in R$. The integral theorem with $j = \varrho$ gives an integral decomposition, and by uniqueness it is the given one. $\square$

**Remark (Formalization).** The corollary assumes $p_a^{-1} \in R$ but not $p_a \in R$. The proof does not need $p_a \in R$: the integral theorem asks only that the minors have inverses in $R$, and it returns $p_a \in R$ as part of its conclusion. Unimodularity of $J_T$ over $R$ is used in one place, to show that an isometry with entries in $R$ has an inverse with entries in $R$, since $\gamma^{-1} = J_T^{-1} \gamma^* J_T$ (Lean: `New.Filling.mem_intGL_of_isIntMatrix`).
