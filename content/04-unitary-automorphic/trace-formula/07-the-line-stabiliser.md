---
title: The line stabiliser and the proof
lean:
  - Lib/Adelic/TraceFormula/LineStabiliser.lean
  - Lib/Adelic/TraceFormula/LineDeterminant.lean
  - Lib/Adelic/TraceFormula/LevelCut.lean
  - Lib/Adelic/TraceFormula/OffPlace.lean
  - Lib/Adelic/TraceFormula/CuspidalComparison.lean
decls:
  - New.lineStabilizer
  - New.lineHecke
  - New.lineRaise_lineLower
  - New.inner_lineRaise
  - New.lineHecke_pow_mem_spanOn
  - New.LineRelation
  - New.LineRelation.trace_mul_mean_eq
  - New.cutLevel
  - New.trace_eq_of_trace_cutLevel_eq
  - New.offPlace
  - New.IsCuspidalAt.convIndicator_offPlace
  - New.exists_atPlace_eq_of_convIndicator_ne_zero
  - New.exists_auxiliary_place
  - New.trace_eq_of_isCuspidalAt
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The line stabiliser and the proof

[The comparison of traces](/decl/New.trace_comparison/) has a hypothesis at a second place $w'$: on the support of the test function, the component at $w'$ has a simple zero. This section removes it. The idea is to pass to a smaller level at an auxiliary split place $v$, the stabiliser $J$ of a line modulo $v$. There the Hecke operator $T^+$ of $\operatorname{diag}(\varpi, 1, \dots, 1)$ has positive powers supported on elements with a simple zero. A relation $T^+ T^- = q^{N-2}(1 + (q^N - 1) e)$ in the Hecke algebra of $J$ then lets the traces of the products $A^l (T^+)^m$, $l, m \geq 1$, determine the trace of $A$ on the vectors fixed by $\mathrm{GL}_N(\mathcal{O}_v)$. The argument is linear algebra on a finite-dimensional space.

### The stabiliser of a line

Let $v$ be a finite place of $E$, with local field $E_v$, ring of integers $\mathcal{O}$, uniformiser $\varpi$, and residue field $k$ of $q$ elements. Fix an index $i$. Write $e_i$ for the $i$-th basis vector and $t = \operatorname{diag}(\varpi, 1, \dots, 1)$ for the diagonal matrix with $\varpi$ at the index $i$ and $1$ elsewhere.

**Definition (Line stabiliser).** The group $J \subset \mathrm{GL}_N(\mathcal{O})$ is the set of $k \in \mathrm{GL}_N(\mathcal{O})$ whose reduction modulo $\varpi$ keeps the line $k e_i$. In other words, the reduction lies in the parabolic subgroup whose $i$-th column vanishes outside the row $i$.
Lean: `New.lineStabilizer` (Lib/Adelic/TraceFormula/LineStabiliser.lean).

For $N = 2$ and $i$ the first index, $J$ is the Iwahori subgroup of matrices that are upper triangular modulo $\varpi$. In general $J$ is a parahoric subgroup, of index $(q^N - 1)/(q - 1)$ in $\mathrm{GL}_N(\mathcal{O})$, the number of lines in $k^N$.

**Definition (The operators).** Let $T^+$ be the sum in the group algebra $\mathbb{C}[\mathrm{GL}_N(E_v)]$ of chosen representatives of the cosets in $J t J / J$. Let $T^-$ be the same sum for $J t^{-1} J / J$, and let $e_{\mathrm{sph}}$ be the mean of chosen lifts to $\mathrm{GL}_N(\mathcal{O})$ of the elements of $\mathrm{GL}_N(k)$.
Lean: `New.lineHecke` (Lib/Adelic/TraceFormula/LineStabiliser.lean).

In a representation $\rho$ these give operators on the vectors fixed by $J$ (`New.lineRaise`, `New.lineLower`, `New.sphericalMean`). On vectors fixed by the kernel of the reduction, $e_{\mathrm{sph}}$ is the mean over $\mathrm{GL}_N(\mathcal{O})$, so it projects onto the spherical vectors.

The cosets in $J t J / J$ have the representatives $r_\xi$ indexed by $\xi \in k^N$ with $\xi_i = 1$. So there are $q^{N-1}$ of them. The same holds for $J t^{-1} J / J$, with representatives indexed by $z \in k^N$ with $z_i = 1$.

**Theorem.** Let $\rho$ be a complex representation of $\mathrm{GL}_N(E_v)$, and let $y$ be fixed by $J$. Then
$$ T^+ T^- y = q^{N-2} \big( y + (q^N - 1)\, e_{\mathrm{sph}}\, y \big). $$
Here $N - 2$ is an integer exponent.
Lean: `New.lineRaise_lineLower` (Lib/Adelic/TraceFormula/LineStabiliser.lean).

*Proof.* For $z \in k^N$, $z \neq 0$, let $y[z] = \rho(k_z) y$, where $k_z \in \mathrm{GL}_N(\mathcal{O})$ takes $e_i$ to $z$ modulo $\varpi$. Since $y$ is fixed by $J$, $y[z]$ depends only on the line of $z$, and $y[e_i] = y$. A count of cosets gives
$$ T^+ T^- y = \sum_{\xi : \xi_i = 1} \; \sum_{z : \xi \cdot z = 1} y[z]. $$
Fix $z \neq 0$ and count the $\xi$ with $\xi_i = 1$ and $\xi \cdot z = 1$. If $z = e_i$, all $q^{N-1}$ values of $\xi$ count. If $z = c e_i$ with $c \neq 1$, none count. If $z$ is not on the line of $e_i$, the condition is one affine equation in the $N - 1$ free coordinates of $\xi$, with $q^{N-2}$ solutions. So
$$ T^+ T^- y = q^{N-1} y + q^{N-2} \sum_{z \notin k e_i} y[z] = q^{N-2} \Big( y + \sum_{z \neq 0} y[z] \Big), $$
since the $q - 1$ nonzero $z$ on the line of $e_i$ give $(q - 1) y$. Since $\mathrm{GL}_N(k)$ acts transitively on $k^N \setminus \{0\}$, $\sum_{z \neq 0} y[z] = (q^N - 1)\, e_{\mathrm{sph}}\, y$. $\square$

**Theorem.** Let $\rho$ be a unitary representation of $\mathrm{GL}_N(E_v)$ on an inner product space. For $x$ and $y$ fixed by $J$, $\langle T^+ x, y \rangle = \langle x, T^- y \rangle$.
Lean: `New.inner_lineRaise` (Lib/Adelic/TraceFormula/LineStabiliser.lean).

*Proof.* Each of $T^+ x$ and $T^- y$ is a sum over $q^{N-1}$ cosets. Since $x$ and $y$ are fixed by $J$, every term of $\langle T^+ x, y\rangle$ equals $\langle \rho(t) x, y \rangle$, and every term of $\langle x, T^- y \rangle$ equals $\langle x, \rho(t^{-1}) y \rangle$. These agree, since $\rho$ is unitary. $\square$

**Theorem (Support of the powers).** For $m \geq 1$, the element $(T^+)^m$ of $\mathbb{C}[\mathrm{GL}_N(E_v)]$ is a combination of elements $g$ such that $g k$ has a simple zero for every $k \in J$.
Lean: `New.lineHecke_pow_mem_spanOn` (Lib/Adelic/TraceFormula/LineStabiliser.lean).

*Proof.* Let $D$ be the set of integral $g$ whose reduction $\bar g$ keeps the line of $e_i$, acts invertibly on $k^N / k e_i$, and has $\bar g_{ii} = 0$. Every element of $J t J$ lies in $D$. If $g \in D$ and $h$ is integral and keeps the line with an invertible action on the quotient, then $g h \in D$, since $\overline{(gh)}_{ii} = \bar g_{ii} \bar h_{ii} = 0$. So by induction $(T^+)^m$ is a combination of elements of $D$, and $D J = D$. An element of $D$ has, in a basis that starts with $e_i$, the reduction $\begin{pmatrix} 0 & * \\ 0 & g' \end{pmatrix}$ with $g'$ invertible. Its characteristic polynomial is $X \det(X - g')$ with $\det g' \neq 0$, so $0$ is a simple root, as in [the definition](/decl/New.HasSimpleZero/). $\square$

**Remark (Formalization).** The element $T^+$ is a sum over chosen representatives (`Quotient.out`), and $e_{\mathrm{sph}}$ uses chosen lifts. On vectors fixed by $J$, or by the kernel of the reduction, the action does not depend on the choices. The sum over cosets is defined by a `finsum`, so it would be $0$ if there were infinitely many cosets. Here there are $q^{N-1}$.

### Traces from the line relations

**Definition (Line relations).** Let $B$ be an inner product space over $\mathbb{C}$, and let $d, c$ be real numbers. Operators $A, T^+, T^-, e$ on $B$ satisfy the *line relations* if $d > 0$ and $c > 0$, $e$ is idempotent, $\langle T^+ x, y\rangle = \langle x, T^- y \rangle$ for all $x, y$, $T^+ T^- = d(1 + c\, e)$, and $A$ commutes with $T^+$ and with $T^-$.
Lean: `New.LineRelation` (Lib/Adelic/TraceFormula/LineDeterminant.lean).

Since $e = c^{-1}(d^{-1} T^+ T^- - 1)$, $A$ also commutes with $e$.

**Theorem.** Let $B$ and $B'$ be finite-dimensional, and let $A, T^+, T^-, e$ on $B$ and $A', T'^+, T'^-, e'$ on $B'$ satisfy the line relations for the same $d$ and $c$. Suppose
$$ \operatorname{tr}\big(A^{l+1} (T^+)^{j+1}\big) = \operatorname{tr}\big(A'^{\,l+1} (T'^+)^{j+1}\big) \quad \text{for all } l, j \geq 0. $$
Then $\operatorname{tr}(A e) = \operatorname{tr}(A' e')$.
Lean: `New.LineRelation.trace_mul_mean_eq` (Lib/Adelic/TraceFormula/LineDeterminant.lean).

*Proof.* Decompose $B$ into the generalised eigenspaces $B_\alpha$ of $A$. They are stable under $T^\pm$ and $e$, and the line relations hold on each $B_\alpha$ (`New.LineRelation.restrict_maxGenEigenspace`). On $B_\alpha$, $A - \alpha$ is nilpotent and commutes with $e$, so $\operatorname{tr}(A e) = \sum_\alpha \alpha \operatorname{rank}(e|_{B_\alpha})$. The term of $\alpha = 0$ vanishes. Fix $\alpha \neq 0$. In the same way $\operatorname{tr}(A^{l+1} (T^+)^{j+1}) = \sum_\alpha \alpha^{l+1} \operatorname{tr}((T^+)^{j+1}|_{B_\alpha})$. Since these agree with the primed sums for all $l$, a Vandermonde argument gives $\operatorname{tr}((T^+)^{j+1}|_{B_\alpha}) = \operatorname{tr}((T'^+)^{j+1}|_{B'_\alpha})$ for every $j$. On $B_\alpha$,
$$ |\det T^+|^2 = \det(T^+ T^-) = d^{\dim B_\alpha} (1 + c)^{\operatorname{rank} e|_{B_\alpha}} \neq 0 $$
(`New.LineRelation.norm_det_sq`). So $T^+$ is invertible on $B_\alpha$. For invertible operators the traces of the positive powers determine the characteristic polynomial. So $T^+|_{B_\alpha}$ and $T'^+|_{B'_\alpha}$ have the same characteristic polynomial. This gives the same dimension and the same determinant. By the formula for $|\det T^+|^2$ and $d > 0$, $(1 + c)^{\operatorname{rank}}$ agrees, and since $1 + c > 1$, the ranks agree. $\square$

The positivity of $c$ is used only in the last step, to recover the rank from $(1 + c)^{\operatorname{rank}}$.

### Cutting the level

**Definition (Cut level).** For a subgroup $K$ of $G_f$, a finite place $v$ and a subgroup $J$ of $\mathrm{GL}_N(E_v)$, the cut level $K_J$ is the set of $g \in K$ whose component at $v$ lies in $J$.
Lean: `New.cutLevel` (Lib/Adelic/TraceFormula/LevelCut.lean).

If $K$ is a level and $J$ is the line stabiliser, $K_J$ is again a level (`New.isLevel_cutLevel_lineStabilizer`). For a split place $v$, write $\iota_v(x)$ for the element of $G_f$ with component $x$ at $v$, the matching component at $\bar v$, and $1$ elsewhere (`New.ofSplitPlace`). Let $K_v^{\max} = \iota_v(\mathrm{GL}_N(\mathcal{O}_v))$ (`New.maxCompactAt`).

**Definition (Part off a place).** For a split place $v$, the homomorphism $g \mapsto g\, \iota_v(g_v)^{-1}$ of $G_f$ removes the components of $g$ at $v$ and $\bar v$.
Lean: `New.offPlace` (Lib/Adelic/TraceFormula/OffPlace.lean).

**Theorem (Passage to the cut level).** Let $v$ be a split place, $K$ a subgroup of $G_f$ with $K_v^{\max} \subset K$, and $i$ an index. Let $\rho$ and $\rho'$ be unitary representations of $G_f$ such that the vectors fixed by $K' = K_J$ form finite-dimensional spaces. Let $a \in \mathbb{C}[G_f]$ keep the $K$-fixed vectors in every representation, and let $a$ be a combination of elements that are integral at $v$. Suppose that for all $l, m \geq 0$ the element
$$ b = \iota_v\big((T^+)^{m+1}\big) \cdot \operatorname{off}_v(a^{l+1}) $$
has the same trace on the $K'$-fixed vectors of $\rho$ and of $\rho'$. Then operators $T$, $T'$ that act as $a$ on the $K$-fixed vectors of $\rho$ and $\rho'$ have the same trace.
Lean: `New.trace_eq_of_trace_cutLevel_eq` (Lib/Adelic/TraceFormula/LevelCut.lean).

*Proof.* On a $K$-fixed vector, $a$ acts through $\operatorname{off}_v(a)$, since $a$ is integral at $v$ and the vector is spherical at $v$. Let $A$ be the action of $\operatorname{off}_v(a)$ on the $K'$-fixed vectors. It commutes with the action of $\mathrm{GL}_N(E_v)$ through $\iota_v$, since the two act at disjoint sets of places (`New.commute_offPlace_ofSplitPlace`). With $T^\pm$ and $e = e_{\mathrm{sph}}$ at $v$, the four operators satisfy the line relations with $d = q^{N-2}$ and $c = q^N - 1$, by the two theorems of the first part. The range of $e$ is the space of $K$-fixed vectors, so $\operatorname{tr}(A e) = \operatorname{tr} T$ (`New.trace_offAction_mul_mean`). The operator $A^{l+1} (T^+)^{m+1}$ is the action of $b$. Apply [the trace theorem](/decl/New.LineRelation.trace_mul_mean_eq/). $\square$

Here $c = q^N - 1 > 0$ because $q \geq 2$ and $N \geq 1$.

### Cuspidality and the support after the cut

**Lemma.** Let $v$ be a split place and $w$ a split place with $v \neq w$ and $\bar v \neq w$. Let $K$ be compact and open with $K_v^{\max} \subset K$, and let $J$ be a subgroup of $\mathrm{GL}_N(E_v)$ with $K_J$ compact and open. Let $a$ be a combination of elements integral at $v$. If $a \star 1_K$ is cuspidal at $w$, then $\operatorname{off}_v(a) \star 1_{K_J}$ is cuspidal at $w$.
Lean: `New.IsCuspidalAt.convIndicator_offPlace` (Lib/Adelic/TraceFormula/OffPlace.lean).

*Proof.* The function $\operatorname{off}_v(a) \star 1_{K_J}$ is $a \star 1_K$ times the indicator of the set of $g$ with $g_v \in J$ (`New.convIndicator_mapDomain_offPlace`). A translation at $w$ does not change the component at $v$. So each sum of translates in [the definition of cuspidality](/decl/New.IsCuspidalAt/) is either the sum for $a \star 1_K$, which is $0$, or a sum of zeros. $\square$

**Lemma.** Let $v$ be split, $S \subset \mathrm{GL}_N(E_v)$, and $J$ a subgroup. Let $u \in \mathbb{C}[\mathrm{GL}_N(E_v)]$ be a combination of elements of $S$, and let $b \in \mathbb{C}[G_f]$. If the function $(\iota_v(u) \cdot \operatorname{off}_v(b)) \star 1_{K_J}$ does not vanish at $g$, then $g_v = x k$ for some $x \in S$ and $k \in J$.
Lean: `New.exists_atPlace_eq_of_convIndicator_ne_zero` (Lib/Adelic/TraceFormula/OffPlace.lean).

*Proof.* By linearity it suffices to take $u = x \in S$ and $b$ a group element $h$. The function is the indicator of $\iota_v(x) \operatorname{off}_v(h) K_J$. Its points have component $x k$ at $v$ with $k \in J$. $\square$

**Lemma (Auxiliary place).** Let $E$ contain a primitive $5040$-th root of unity. Let $K$ be an open subgroup of $G_f$, $a \in \mathbb{C}[G_f]$, and $w$ a finite place. Then there is a split place $v$ with $v \neq w$ and $\bar v \neq w$, $K_v^{\max} \subset K$, and $a$ a combination of elements that are integral at $v$.
Lean: `New.exists_auxiliary_place` (Lib/Adelic/TraceFormula/CuspidalComparison.lean).

*Proof.* There are infinitely many places $v$ with $q_v$ prime (`New.frequently_prime_q`). Under the hypothesis on roots of unity, a place fixed by the conjugation has $q_v = r^2$, so a place with $q_v$ prime is split (`New.isSplit_of_q_prime`). The other three conditions hold at all but finitely many places. $\square$

### The proof of the main theorem

**Theorem (Comparison for cuspidal test functions).** Let $E$ contain a primitive $5040$-th root of unity and have an even number of infinite places. Let $N \geq 2$, and let $V$ and $V'$ be spaces of signs $s$ and $s'$. Let $l$ be a family of doubled parameters with the gap condition with constant $10 N^5$ for $s$ and for $s'$. Let $K$ be a level, and let $a \in \mathbb{C}[G_f]$ keep the $K$-fixed vectors in every representation. Let $w$ be a split place with $a \star 1_K$ cuspidal at $w$. Let $T$ and $T'$ be operators that act as $a$ on the forms of type $e_\lambda$ and level $K$ for $V$ and for $V'$. Then $\operatorname{tr} T = \operatorname{tr} T'$.
Lean: `New.trace_eq_of_isCuspidalAt` (Lib/Adelic/TraceFormula/CuspidalComparison.lean).

*Proof.* Take $v$ by [the auxiliary place lemma](/decl/New.exists_auxiliary_place/), and fix an index $i$. Let $K' = K_J$ with $J$ the line stabiliser at $v$. By [finiteness](/decl/New.Space.finite_levelSpace/), the forms of level $K'$ form a finite-dimensional space for $V$ and for $V'$. The representations on forms are unitary (`New.Space.inner_formRep`). By [the passage to the cut level](/decl/New.trace_eq_of_trace_cutLevel_eq/) it suffices to show, for all $l, m \geq 0$, that $b = \iota_v((T^+)^{m+1}) \operatorname{off}_v(a^{l+1})$ has the same trace at level $K'$ for $V$ and for $V'$. Apply [the comparison of traces](/decl/New.trace_comparison/) to $b$, at level $K'$, with $w' = v$. Two hypotheses remain.

1. Cuspidality at $w$. Write $a^{l+1} = a^l \cdot a$. Since $a$ is integral at $v$, $\operatorname{off}_v(a) \star 1_{K'}$ is cuspidal at $w$ by [the first lemma](/decl/New.IsCuspidalAt.convIndicator_offPlace/). A product on the left keeps cuspidality ([Section 2](/decl/New.IsCuspidalAt.convIndicator_mul/)). So $b \star 1_{K'}$ is cuspidal at $w$.
2. The simple zero at $v$. Let $(b \star 1_{K'})(g) \neq 0$. By [the support theorem](/decl/New.lineHecke_pow_mem_spanOn/), $(T^+)^{m+1}$ is a combination of elements $x$ with $x k$ of simple zero for all $k \in J$. By [the second lemma](/decl/New.exists_atPlace_eq_of_convIndicator_ne_zero/), $g_v = x k$ for such $x$ and some $k \in J$. So $g_v$ has a simple zero.

This gives the equality of the traces of $b$, and the theorem follows. $\square$

**Remark (Formalization).** The hypothesis that $a$ keeps the $K$-fixed vectors in every representation (`New.universalLevelAlgebra`) appears here, not in [the comparison of traces](/decl/New.trace_comparison/). It is used to restrict $a$ to the $K$-fixed vectors in the passage to the cut level. The roots of unity are used twice in this section: for the comparison itself, and to make the places of prime norm split. As in Section 6, the hypothesis that the number of infinite places is even follows from the roots of unity (finding F-140).
