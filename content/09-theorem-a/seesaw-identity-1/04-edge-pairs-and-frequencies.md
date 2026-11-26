---
title: Edge pairs and frequencies
lean:
  - New/UpperBound/Seesaw/EdgePairEvaluation.lean
  - New/UpperBound/Seesaw/Frequency.lean
decls:
  - New.Seesaw.zeroTermFin
  - New.Seesaw.zeroTermFin_omega
  - New.Seesaw.zeroTermFin_mem_finitePart
  - New.Seesaw.zeroTermFin_vacElem_ne_zero
  - New.Seesaw.zeroTermLattice
  - New.Seesaw.mem_zeroTermLattice_iff_selfDualAddChar
  - New.Seesaw.exists_zeroTermFin_vacElem_eq_sum
  - New.Seesaw.exists_eq_add_of_zeroTermFin_ne_zero
  - New.Grading.IsGraded.mulVec_mem_of_homogeneous
  - New.Grading.exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap
  - New.Grading.smul_map_stringMapFin_latticePlus_le
  - New.Seesaw.GradeZeroPart
  - New.Seesaw.GradeZeroPart.card_pos_eq_card_neg
  - New.Seesaw.GradeZeroPart.splitting
  - New.Seesaw.HasConsecutiveStrings
  - New.Seesaw.DoubleLiftData
  - New.Seesaw.DoubleLiftData.finEval
  - New.Seesaw.DoubleLiftData.zeroTerm_splitting_tripleWeil
  - New.Seesaw.DoubleLiftData.finEval_arrowProduct_equivariant
  - New.Seesaw.middleDoubleLift
  - New.Seesaw.lastDoubleLift
  - New.Data.doubleLiftEvalY
  - New.Data.evaluatedDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Edge pairs and frequencies

The step of the unfolding replaces the theta kernel of $\mathrm{Hom}(Y_k, Y_{k+1})$ by its constant term at the shift $T = \mathrm{sh}$, as in [one step of unfolding](/chapter/bessel-periods/). This section proves two facts. The first is a frequency condition: if the constant term at $\mathrm{sh}$ does not vanish at two points, then a multiple of $\mathrm{sh}$ maps the lattice of the first into that of the second. Section 6 uses it. The second is an equivariant evaluation of two lifts at once on the doubled space $\mathrm{Hom}(V', V^- \oplus V'')$.

Background: splittings and zero terms are in [the Weil representation](/chapter/weil-representation/), the joined datum of two edges in [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), and gradings and the shift in [Bessel periods](/chapter/bessel-periods/).

### The finite part of the zero term

Let $D$ be a splitting of $V$ over $V_0$: dual isotropic frames $k$, $l$ with columns indexed by $p$, and an isometry $i$ of $V_0$ onto their orthogonal complement. The zero term $D.\mathrm{zeroTerm} : \mathcal{S}(V) \to \mathcal{S}(V_0)$ sends $f$ to the function whose value at $y$ is the mean of $f(iy + kb)$ over $b \in \mathbb{A}^p / E^p$.

**Definition (The finite zero term).** Choose an adelic point $g$ of $U(V)$ that is adapted to $D$: the frame of $D$ moved by $g^{-1}$ is orthonormal at the infinite places and integral at the finite places. The finite zero term is

$$\mathrm{ZT}^{\mathrm{f}}_D(f) = D.\mathrm{zeroTerm}(v_g \otimes f),$$

where $v_g$ is the Fock vacuum moved by the real part of $g$, and $\otimes$ joins a real Fock vector and a finite datum into a datum of $\mathcal{S}(V)$.

Lean: `New.Seesaw.zeroTermFin` (New/UpperBound/Seesaw/EdgePairEvaluation.lean).

**Remark (Formalization).** The adapted point is `Classical.choose` of an existence statement. The map depends on the choice through $v_g$, and every statement below holds for each choice.

**Proposition (Properties of the finite zero term).** Let $D$ be a splitting of $V$ over $V_0$.

1. (Law of the parabolic subgroup.) Let $g$ be a finite point of $U(V)$ with $gk = ka$, $\det a = d$, acting on $V_0$ as $g_0$. Then $\mathrm{ZT}^{\mathrm{f}}_D(\omega(1, g) f) = \chi(d)^{-1}\, \omega(g_0)\, \mathrm{ZT}^{\mathrm{f}}_D(f)$, where $\chi(d) = \upsilon(d)|d|^{-1/2}$ and $\upsilon$ is the splitting character of the Weil data.
2. $\mathrm{ZT}^{\mathrm{f}}_D$ sends the finite part of $\mathcal{S}(V)$, the span of the finite Heisenberg translates of the vacuum, into the finite part of $\mathcal{S}(V_0)$.
3. $\mathrm{ZT}^{\mathrm{f}}_D(\mathrm{vac}_V) \neq 0$.

Lean: `New.Seesaw.zeroTermFin_omega`, `New.Seesaw.zeroTermFin_mem_finitePart`, `New.Seesaw.zeroTermFin_vacElem_ne_zero`.

*Proof.* (1) This is the law of the zero term for the parabolic subgroup, `New.Space.Splitting.zeroTerm_omega`, applied to $(1, g)$; the real vector $v_g$ is not moved because the real part of $(1, g)$ is $1$. (2) For the adapted point $g$, the mixed model of $\omega(g)\mathrm{vac}$ is a multiple of the vacuum of $V_0$ in each slice. So the zero term of $\omega(g)$ of a finite translate of the vacuum is a multiple of a translate of the vacuum of $V_0$, and these span the finite part. (3) By the next theorem, the value at a translate of the vacuum is $0$ or a root of unity times a translate of the value at the vacuum. So it suffices that the value at $\omega(1, g_{\mathrm f})\mathrm{vac}$ is $c\,\mathrm{vac}_{V_0}$ with $c \neq 0$, which holds (Lean: `New.Seesaw.exists_zeroTermFin_ne_zero`). $\square$

The support of the finite zero term on translates of the vacuum is described by a lattice of $V_0$.

**Definition (The zero term lattice).** $L'_D$ is the set of $w \in \mathbb{A}_{\mathrm f}^{n_0}$ such that $iw + kb \in \hat{\mathcal{O}}^n$ for some $b$. It is the image in $V_0 = I^\perp / I$ of $\hat{\mathcal{O}}^n \cap I^\perp$, where $I$ is spanned by the columns of $k$.

Lean: `New.Seesaw.zeroTermLattice`.

**Theorem (Translates of the vacuum).** Let $D$ be a splitting of $V$ over $V_0$.

1. If $\mathrm{ZT}^{\mathrm{f}}_D(\varrho_{\mathrm f}(y)\mathrm{vac}_V) \neq 0$, then $y = iw + kb + l$ with $l \in \hat{\mathcal{O}}^n$.
2. $L'_D$ is unimodular: $w \in L'_D$ if and only if $\psi_{\mathrm f}(x^* w) = 1$ for all $x \in L'_D$, where $\psi_{\mathrm f}$ is the character of $\mathbb{A}_{\mathrm f}$ for which $\hat{\mathcal{O}}$ is self-dual.
3. Let $r_1, \ldots, r_m$ represent $L'_D$ modulo $L'_D \cap \hat{\mathcal{O}}^{n_0}$, a finite set. Then $\mathrm{ZT}^{\mathrm{f}}_D(\mathrm{vac}_V)$ is a nonzero multiple of $\sum_j \varrho_{\mathrm f}(r_j)\mathrm{vac}_{V_0}$.

Lean: `New.Seesaw.exists_eq_add_of_zeroTermFin_ne_zero`, `New.Seesaw.mem_zeroTermLattice_iff_selfDualAddChar`, `New.Seesaw.exists_zeroTermFin_vacElem_eq_sum`.

*Proof.* (1) The vacuum is fixed by the translations of $\hat{\mathcal{O}}^n$ up to a root of unity. The zero term is a mean over $b \in \mathbb{A}^p/E^p$, and it kills the translate unless the component of $y$ along the dual frame is integral. So $y$ lies in $I^\perp + \hat{\mathcal{O}}^n$, and a vector of $I^\perp$ is $iw + kb$. (2) There are a finite unitary point $g$ of $V_0$ and a matrix $c$ such that $ig + kc$ is integral. Then $L'_D = g\hat{\mathcal{O}}^{n_0}$, and the image of the self-dual lattice $\hat{\mathcal{O}}^{n_0}$ under a unitary point is self-dual. (3) The quotient is finite because $g\hat{\mathcal{O}}^{n_0} \cap \hat{\mathcal{O}}^{n_0}$ has finite index in $g\hat{\mathcal{O}}^{n_0}$. The value at the vacuum is fixed by the translations of $L'_D$ and, by (1), is a combination of translates of $\mathrm{vac}_{V_0}$ by vectors of $L'_D$, so it is a multiple of the sum over representatives. $\square$

### Graded lattices and homogeneous parts

Let $\mathsf{Y}$ and $\mathsf{Y}'$ grade $V$ and $V'$ by integers. A matrix $W : V \to V'$ has *degree at least* $d$ if its entry $(p, q)$ is $0$ whenever $\mathrm{grade}'(p) < \mathrm{grade}(q) + d$ (Lean: `New.HasDegreeGe`). A lattice is *graded* if it contains each graded part of each of its vectors.

**Lemma (Homogeneous parts).** Let $L$, $L'$ be graded lattices of $V$, $V'$, and let $W$ map $L$ into $L'$. For an integer $e$, let $T$ be the part of $W$ of degree $e$: its entry $(p, q)$ is that of $W$ if $\mathrm{grade}'(p) = \mathrm{grade}(q) + e$, and $0$ otherwise. Then $T$ maps $L$ into $L'$.

Lean: `New.Grading.IsGraded.mulVec_mem_of_homogeneous` (New/UpperBound/Seesaw/Frequency.lean).

*Proof.* Let $y \in L$ and write $y = \sum_d y_d$ by grades. Then $T y = \sum_d (W y_d)_{d + e}$, the grade $d + e$ part of $W y_d$, because only the summand of the grade of $q$ contributes to the entry $(p, q)$. Each $y_d$ lies in $L$, so $W y_d \in L'$, and each graded part of it lies in $L'$. $\square$

The shift $\mathrm{sh} : V \to V'$ kills $X$ and sends each string vector of $V$ to a multiple of the string vector of $V'$ with the same number. It is homogeneous of degree $-1$ (Lean: `New.Grading.stringMap_eq_zero_of_gradeOf_ne`). A finite point of the Bessel group of $\mathsf{Y}$ does not lower grades (Lean: `New.Grading.hasDegreeGe_zero_ratCoordMatrixFin`).

### The frequency condition

Let $t$ be a real Fock vector and $f$ a finite datum of $\mathrm{Hom}(V, V')$, let $x$, $x'$ be adelic points, and let $\mathrm{CT}_{\mathrm{sh}}(t \otimes f)(x, x')$ be the constant term at $\mathrm{sh}$ of the translate of $t \otimes f$ by $(x, x')$, twisted by characters $\mu$ (Lean: `New.Grading.constTermAtStringMap`). Let $\alpha$ be the finite idele of the Weil data, and $V.\mathrm{lattice}(g)$ the lattice $g\hat{\mathcal{O}}^n$ in rational coordinates.

**Theorem (Frequency).** Suppose that $\mathrm{CT}_{\mathrm{sh}}(t \otimes f)(x, x') \neq 0$ and that $f$ is fixed by the finite Heisenberg operators of $b\,\hat{\mathcal{O}}^{\iota' \times \iota}$, for a finite idele $b$.

1. There is a matrix $W$ that maps $V.\mathrm{lattice}(x_{\mathrm f})$ into $V'.\mathrm{lattice}(x'_{\mathrm f})$ and such that $W - (\bar b/\alpha)\,\mathrm{sh}$ has degree at least $0$.
2. Let $r$, $r'$ be finite points of the Bessel groups of $\mathsf{Y}$, $\mathsf{Y}'$ such that the lattices $\Lambda$ of $r x_{\mathrm f}$ and $\Lambda'$ of $r' x'_{\mathrm f}$ are graded. Then

$$\frac{\bar b}{\alpha}\, \mathrm{sh}(\Lambda^+) \subseteq \Lambda'^-.$$

Lean: `New.Grading.exists_mapsTo_lattice_hasDegreeGe_sub_smul_stringMap`, `New.Grading.smul_map_stringMapFin_latticePlus_le`.

*Proof.* (1) Take a splitting $D$ of $\mathrm{Hom}(V, V')$ whose isotropic frame consists of the maps of positive degree (Lean: `New.Grading.exists_splitting_constTerm`). So the finite zero term does not vanish at the translate of $\omega(1, g)f$ by the finite coordinates $z$ of $\mathrm{sh}$, with $g$ the finite part of $(x, x')$. The datum $\omega(1, g) f$ is fixed by the translations of $bg\,\hat{\mathcal{O}}$, and $(bg)(\bar b^{-1} g)^* = 1$ because $g$ is unitary. By the support lemma (Lean: `New.Seesaw.exists_sub_orthogonal_of_zeroTermFin_ne_zero`) with $M = bg$ and $M' = \bar b^{-1}g$, $z$ lies in $\bar b^{-1} g\,\hat{\mathcal{O}} + k^\perp$, where $k^\perp$ is the kernel of $k^*$. Write $z = \bar b^{-1} g\, l + (\text{a vector of } k^\perp)$ with $l$ integral, and let $W$ be the matrix of $l$ in rational coordinates, moved by the frames of $x'$ and $x$. Since $l$ is integral, $W$ maps the lattice of $x_{\mathrm f}$ into that of $x'_{\mathrm f}$. The vectors of $k^\perp$ have zero entries of negative degree, so $W$ and $\alpha^{-1}\bar b\,\mathrm{sh}$ agree in negative degree.

(2) Put $W_0 = r' W r^{-1}$, which maps $\Lambda$ into $\Lambda'$. Since $r$ and $r'$ do not lower grades and $\mathrm{sh}$ is fixed by the Bessel groups modulo degree at least $0$, $W_0 - c\,\mathrm{sh}$ has degree at least $0$, where $c = \bar b/\alpha$ (Lean: `New.Grading.hasDegreeGe_zero_mul_mul_sub`). As $\mathrm{sh}$ has degree $-1$, the part of $W_0$ of degree $-1$ is $c\,\mathrm{sh}$. By the lemma on homogeneous parts, $c\,\mathrm{sh}$ maps $\Lambda$ into $\Lambda'$. As $\mathrm{sh}$ kills $X$, $c\,\mathrm{sh}(\mathrm{pr}\,y) = c\,\mathrm{sh}(y) \in \Lambda'$ for $y \in \Lambda$, and it lies in the span of the string of $V'$, so in $\Lambda'^-$. $\square$

At the standard lattices of Section 3 the shift satisfies $\mathrm{sh}(\Lambda^+_k) = a\,\Lambda^-_{k+1}$, by the [theorem on the shift of the standard lattices](/decl/New.Grading.SpansLattice.map_stringMapFin_latticePlus/). Section 6 compares the two statements to bound the points that contribute.

### The part of grade zero

To evaluate two lifts at once the source works on the doubled space. Let $V$, $V'$, $V''$ be graded with strings of lengths $s$, $s - 1$, $s - 2$. The sum $V^- \oplus V''$, with the negated form on $V$, is graded by the grades of $V$ and of $V''$.

**Definition (Grade zero part).** Let $w$ be integer weights on the basis of $V$ such that the Gram matrix pairs two basis vectors only if their weights add to $0$. A grade zero part of $V$ is a space $V_0$ with an injection of its basis onto the indices of weight $0$ and a rational isometry $V_0 \to V$ with no component along the vectors of nonzero weight.

Lean: `New.Seesaw.GradeZeroPart`.

**Lemma.** A space with a grade zero part has as many basis vectors of positive weight as of negative weight. The vectors of positive weight form an isotropic frame, the columns of $J^{-1}$ at those indices form a dual frame, and together with $V_0$ they give a splitting of $V$ over $V_0$.

Lean: `New.Seesaw.GradeZeroPart.card_pos_eq_card_neg`, `New.Seesaw.GradeZeroPart.splitting`.

*Proof.* Let $P$ and $Q$ be the diagonal projections onto the indices of positive and of negative weight. Since $J$ pairs weight $d$ only with weight $-d$, $PJ = JQ$, so $P = JQJ^{-1}$ and $\mathrm{tr}\, P = \mathrm{tr}\, Q$. Two vectors of positive weight have weights with positive sum, so they are orthogonal, and the frame is isotropic. $J^{-1}$ also pairs only opposite weights (Lean: `New.Seesaw.GradeZeroPart.inv_J_apply_eq_zero_of_pos`), which gives the dual frame. $\square$

**Definition (Consecutive strings, double lift data).** The gradings $\mathsf{Y}$, $\mathsf{Y}'$, $\mathsf{Y}''$ have *consecutive strings* if $s$ is odd, $s' = s - 1$, $s'' = s' - 1$ (truncated subtraction, so $s'' = 0$ if $s = 1$), and $\mathsf{Y}$, $\mathsf{Y}'$ have the same constant $c$. *Double lift data* add: $\dim V + \dim V''$ even; a grade zero part of $V^- \oplus V''$ equal to $q$ hyperbolic planes plus $X^- \oplus X''$; a determinant preserving map $\epsilon : U(X_0) \to U(X'')$ compatible with the inclusion; and an injection of $q$ into the grade $1$ indices of $V'$ such that the stacked map $(\mathrm{sh}^*, \mathrm{sh}')$, in the rows of grade $0$, is $c$ times the second vector of the $j$-th plane in column $j$ and $0$ in the other columns.

Lean: `New.Seesaw.HasConsecutiveStrings`, `New.Seesaw.DoubleLiftData`.

All grades on $V^- \oplus V''$ are even, since $s$ is odd and $s''$ is odd or $0$. The string of $V'$ has even length, so its grades are odd (Lean: `New.Seesaw.DoubleLiftData.even_gradeOf`, `New.Seesaw.DoubleLiftData.even_length_middle`). Give the entry $(a, b)$ of a map $V' \to V^- \oplus V''$ the weight $\mathrm{grade}(a) - \mathrm{grade}'(b)$. It is even only if $b \in X'$, and then it is $0$ only if $a$ has grade $0$. So the grade zero part of $\mathrm{Hom}(V', V^- \oplus V'')$ is $\mathrm{Hom}(X', Z)$, with $Z$ the grade zero part of $V^- \oplus V''$ (Lean: `New.Seesaw.DoubleLiftData.homZeroPart`).

**Example (The two kinds of pairs).** Let $s = 3$. The string of $V$ has grades $2, 0, -2$ and middle vector $z$ of norm $-N$; the string of $V''$ is one vector $z'$ of grade $0$ and norm $-N$. In $V^- \oplus V''$ the vector $z$ has norm $N$ and $z'$ has norm $-N$, so $z + z'$ and $z - z'$ are isotropic with $\langle z + z', z - z'\rangle = 2N$: they span a hyperbolic plane. The grade zero part is $X^- \oplus X''$ plus this plane, with $q$ of one element. This is the construction of `New.Seesaw.middleDoubleLift`, for every odd $s \neq 1$: the plane spanned by the middle vectors of $\mathsf{Y}$ and $\mathsf{Y}''$ is removed. Let $s = 1$. Then $V'$ and $V''$ have no string, and the string of $V$ is $z$ of norm $-N$, so of norm $N$ in $V^-$. If $N = p\bar p$, then $z/p$ has norm $1$ in $V^-$, and it is adjoined to $X_0$ as the last basis vector of $X''$; there is no plane. This is `New.Seesaw.lastDoubleLift`.

Lean: `New.Seesaw.middleDoubleLift`, `New.Seesaw.lastDoubleLift`.

### The finite evaluation of a pair

Let $D$ be double lift data. Its splitting removes from $\mathrm{Hom}(V', V^- \oplus V'')$ first the maps of nonzero degree, then the maps into the $q$ hyperbolic planes, and leaves $\mathrm{Hom}(X', X^- \oplus X'')$ (Lean: `New.Seesaw.DoubleLiftData.splitting`). The joined datum $\Phi \boxtimes \Phi'$ of data on $\mathrm{Hom}(V, V')$ and $\mathrm{Hom}(V', V'')$ is a datum on $\mathrm{Hom}(V', V^- \oplus V'')$ (Lean: `New.Seesaw.arrowProduct`), and on the definite spaces the map $\Phi_1 \otimes \Phi_2 \mapsto \Phi_1 \boxtimes \Phi_2$ is injective on finite parts with a left inverse (Lean: `New.Seesaw.arrowTensor`).

**Definition (The finite evaluation).** $\mathrm{ev}_D$ translates a datum on $\mathrm{Hom}(V', V^- \oplus V'')$ by the finite coordinates of the stacked map $(\mathrm{sh}^*, \mathrm{sh}')$, takes the finite zero term along the splitting of $D$, and applies the left inverse of $\Phi_1 \otimes \Phi_2 \mapsto \Phi_1 \boxtimes \Phi_2$. Its values are tensors of finite data on $\mathrm{Hom}(X, X')$ and $\mathrm{Hom}(X', X'')$.

Lean: `New.Seesaw.DoubleLiftData.finEval`.

**Remark (Formalization).** The left inverse is a choice off the range. On joined finite data the value is determined, because the translation and the zero term preserve finite parts (Lean: `New.Seesaw.DoubleLiftData.arrowTensor_finEval`).

Let $\mathrm{tw}_{a,b}(g, g', k)$ be the Weil operator of $(g', g \oplus k)$ on $\mathrm{Hom}(V', V^- \oplus V'')$ times the scalar characters of the two edges and of $\upsilon$ (Lean: `New.Seesaw.tripleWeil`).

**Theorem (Equivariance of the evaluation).** Let $D$ be double lift data and $a$, $b$ characters of $[U(1)]$.

1. The zero term along the splitting of $D$ carries $\mathrm{tw}_{a,b}(\iota g, \iota' g', \iota'' k)$ to the same operator of the definite spaces at $(g, g', \epsilon(k))$, with no further scalar.
2. Let $g$, $g'$, $k$ be finite points of $U(X)$, $U(X')$, $U(X_0)$, embedded by $\iota$, and let $\epsilon(1, k) = (1, k')$. If $\Phi$ and $\Phi'$ are finite data moved by $(\iota g, \iota' g')$ and $(\iota' g', \iota'' k)$, then $\mathrm{ev}_D(\Phi \boxtimes \Phi')$ is $\mathrm{ev}_D$ of the unmoved data, moved by $(g, g')$ in the first factor and by $(g', k')$ in the second.

Lean: `New.Seesaw.DoubleLiftData.zeroTerm_splitting_tripleWeil`, `New.Seesaw.DoubleLiftData.finEval_arrowProduct_equivariant`.

*Proof.* (1) The zero term is taken in two stages, to the part of weight zero (Lean: `New.Seesaw.GradeZeroPart.zeroTerm_hom_omega`) and then off the hyperbolic planes. Each stage multiplies by a power of $\upsilon$ at a determinant. For the first stage the exponents are $s'/2$ at $\det g$ and the number of indices of positive weight at $\det h$. The rank formulas, with $s'$ and $\dim V + \dim V''$ even, make the exponents on the two sides agree. The group element is the identity away from weight zero, and on the planes it is $1$ by the intertwining condition of $D$.

(2) The embedded elements fix $\mathrm{sh}$ and $\mathrm{sh}'$, since $\mathrm{sh}$ kills $X$ and has image in the string (Lean: `New.Seesaw.inclX_mul_stringMap_mul_inclX_inv`). So they commute with the translation, and, having trivial real part, they fix the real Fock vector. By (1) the finite zero term carries the operator to the operator of the definite spaces, and the joined datum splits over the two factors. $\square$

### The pairs of the tower

On the tower, the grading $\mathsf{Y}_k$ of $Y_k$ has the string of length $s_k = 2\varrho + 1 - k$ and the constant $c = -(jM\delta_E)^{-1}$, which does not depend on $k$ (Lean: `New.Data.gradingY`). The pairs are $Y_{2i} \to Y_{2i+1} \to Y_{2i+2}$.

**Definition (Evaluation of the pairs of the tower).** For $i < \varrho$ the pair $i$ is evaluated by the middle double lift, for $i = \varrho$ by the last double lift, and for $i > \varrho$ the evaluation is $0$. The evaluated datum of pair $i$ is this evaluation applied to the joined data of lifts $2i + 1$ and $2i + 2$, each moved by the finite points $(y_{2i}, y_{2i+1})$ and $(y_{2i+1}, y_{2i+2})$.

Lean: `New.Data.doubleLiftEvalY`, `New.Data.evaluatedDatum`.

**Remark (Formalization).** The value $0$ for $i > \varrho$ is a junk value: no pair exists there, and no statement uses it.
