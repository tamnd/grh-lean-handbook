---
title: The root lemma and the Pieri volume
lean:
  - New/UpperBound/ElementaryDivisors/RootLemma.lean
  - New/UpperBound/ElementaryDivisors/Edges.lean
  - New/UpperBound/ElementaryDivisors/PieriCone.lean
  - New/UpperBound/ElementaryDivisors/DefectCount.lean
decls:
  - New.stepanov_count
  - New.adicFiltration
  - New.gaussFiltration
  - New.rootSL
  - New.FrobeniusCycle.RootAt.HasBoundedIncrements.weight_zeroOrder_mul_card_le
  - New.FrobeniusCycle.defect_nonpos_of_extreme_term
  - New.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three
  - New.FrobeniusCycle.weight_defectWeight_nonpos_of_least
  - New.FrobeniusCycle.pow_add_dvd_of_le_defect
  - New.FrobeniusCycle.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms
  - New.FrobeniusCycle.allEdgesForms_le_defectConditions
  - New.FrobeniusCycle.IsEdgePairing.pow_dvd_pairing_letterRep
  - New.FrobeniusCycle.defectCone
  - New.pieriCone
  - New.prod_mul_volume_real_inter_degreeSlab
  - New.FrobeniusCycle.exists_finrank_defectConditions_le_volume
  - New.FrobeniusCycle.index_mul_relIndex_le
  - New.FrobeniusCycle.index_mul_finrank_defectConditions_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The root lemma and the Pieri volume

This section treats the defect. The first half shows that a large defect forces divisibility: if all translates of a form are divisible by $w^m$ after the depth scaling, then at a monomial of defect at least $3j$ they are divisible by $w^{m+j}$. The tool is a polynomial in one variable with many zeros and small degree, as in Stepanov's method. The second half counts, over the residue field, the forms whose block diagonal translates have no term of large defect. Their number is about $1/[\mathrm{GL}_k(W) : P_r]$ times the number of all forms. The tool is a cone cut out by Pieri's inequalities and its volume.

Throughout, $T$ is a Frobenius cycle with $N$ letters, $w = \sqrt p$, $P = p^f$ and $q = P^N$. For indices $a \ne a'$ and a letter $s$, let $Y_s$ be the variable $u_s$ of Section 2, that is $(a', s)$ for even $s$ and $(a, s)$ for odd $s$, and let $X_s$ be the other of the two. Write $P_s = P^{\langle s - i\rangle}$, so $P_i = 1$.

### Stepanov's count

**Lemma (Stepanov's count).** Let $W$ be a local ring, $R$ a commutative ring, $\iota : W \to R$ a ring map, $E \in \mathbb N$ and $\Phi \ne 0$ in $R[X]$. If $X^E$ divides $\Phi(X + \iota(x))$ for every $x \in W$, then $E\cdot \mathrm{Nat.card}(k_W) \le \deg \Phi$.

Lean: `New.stepanov_count` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

*Proof.* If $k_W$ is infinite, its Nat.card is $0$ and there is nothing to prove. Otherwise choose a lift $\tilde x \in W$ of each $x \in k_W$ and put $a_x = \iota(\tilde x)$. For $x \ne y$ the difference $\tilde x - \tilde y$ is not in the maximal ideal, so it is a unit of $W$, and $a_x - a_y$ is a unit of $R$. Hence the polynomials $(X - a_x)^E$ are pairwise coprime. Each divides $\Phi$ by hypothesis, so their product divides $\Phi$. The product is monic of degree $E|k_W|$. A monic polynomial of larger degree than a nonzero $\Phi$ cannot divide it. $\square$

**Remark (Formalization).** Nat.card of an infinite type is $0$ in Lean, so for an infinite residue field the lemma says nothing. Here it is applied with $k_W$ of $q$ elements, by the definition of a Frobenius cycle. $R$ need not be a domain, which allows $R/(w^{l+1})$.

### Filtrations

**Definition (Filtrations).** For $w \in R$ and real $t$, $\mathrm{adicFiltration}(w, t)$ is the additive group of $x \in R$ with $w^{\lceil t\rceil_+} \mid x$, where $\lceil t\rceil_+ = \max(\lceil t\rceil, 0)$. For a family $F_t$ of subgroups and weights $c$ of the variables, $\mathrm{gaussFiltration}(F, c, t)$ is the group of polynomials whose coefficient at $x^\alpha$ lies in $F_{t - c\cdot\alpha}$, where $c \cdot \alpha = \sum_x c(x)\alpha(x)$ is the weight of $\alpha$.

Lean: `New.adicFiltration` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

Lean: `New.gaussFiltration` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

So $f$ lies in level $t$ when every term $\lambda x^\alpha$ has $w$-order plus weight at least $t$.

**Definition (Root subgroup).** $\mathrm{rootSL}(W, a, a')$ is the subgroup of $g \in \mathrm{GL}_k(W)$ with $\det g = 1$ that agree with the identity at $(b, c)$ unless both $b$ and $c$ lie in $\{a, a'\}$. It is a copy of $\mathrm{SL}_2(W)$ in the rows and columns $a$, $a'$.

Lean: `New.rootSL` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

### Zeros against degree

**Lemma (Zeros against degree).** Let $a \ne a'$ and a letter $i$. Let the weights $c$ satisfy $c(Y_s) - c(X_s) \in [\frac12, 1]$ for all $s$. Suppose that for all $g \in \mathrm{rootSL}(W, a, a')$ each term of $g\cdot f$ has order plus $c$-weight at least $l + c\cdot\alpha$, and that $w^{l+1}$ does not divide the coefficient of $x^\alpha$ in $f$. Put

$$\nu = q\,\alpha(Y_i) + \sum_{s \ne i} P_s\,\alpha(Y_s), \qquad \pi = q\sum_s P_s\,\alpha(X_s).$$

Then $\nu q \le \pi$.

Lean: `New.FrobeniusCycle.RootAt.HasBoundedIncrements.weight_zeroOrder_mul_card_le` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

*Proof (main steps).* The source substitutes, for the variables of the root, polynomials in one new variable $t$: $X_s \mapsto t^{qP_s}X_s$ and the variable $Y_i$ is merged with $X_i$; for $s \ne i$ cross terms $\pm X_s$, $\pm t^{P_s}Y_s$ are subtracted (`New.FrobeniusCycle.RootAt.mainSubst`, `New.FrobeniusCycle.RootAt.crossSubst`). Let $\Phi(t)$ be the coefficient of the merged monomial of $\alpha$, read modulo $w^{l+1}$. Three facts hold. First, the coefficient of $t^\pi$ is the coefficient of $x^\alpha$ in $f$ modulo $w^{l+1}$, so $\Phi \ne 0$. Second, all coefficients of $t^j$ with $j > \pi$ vanish modulo $w^{l+1}$, so $\deg\Phi \le \pi$: this is the expansion at infinity, where $t$ has weight $-\rho$ with $\rho = (c(Y_i) - c(X_i))/q > 0$. Third, for each $r \in W$ the shift $\Phi(t + \iota_i(r))$ is divisible by $t^\nu$: the shift is the translate of $f$ by a product of the swap of $a$, $a'$ and a transvection with entry $r$, which lies in $\mathrm{rootSL}$, and in that expansion $t$ has weight $+\rho$. The congruence $\iota_{s+1} \equiv \iota_s^P$ controls the other letters; the increments in $[\frac12, 1]$ give a margin of $1/20$ that absorbs the error. Stepanov's count with $E = \nu$ over $R/(w^{l+1})$ gives $\nu q \le \deg \Phi \le \pi$. $\square$

### The root lemma

**Theorem (Root lemma).** Let $a \ne a'$, a letter $i$, and weights $c$ with $c(Y_s) - c(X_s) \in [\frac12, 1]$ for all $s$. If every translate of $f$ by $\mathrm{rootSL}(W, a, a')$ lies in level $l + c\cdot\alpha$ of the Gauss filtration for $w$, and $w^{l+1}$ does not divide the coefficient of $x^\alpha$ in $f$, then the defect of $\alpha$ at $i$ along $(a, a')$ is at most $0$.

Lean: `New.FrobeniusCycle.defect_nonpos_of_extreme_term` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

*Proof.* By Section 2 the defect weights are $q/(q-1)$ at $Y_i$, $P_s/(q-1)$ at $Y_s$ for $s \ne i$, $-P_s/(q-1)$ at $X_s$, and $0$ elsewhere. So the defect of $\alpha$ is $(\nu - \pi/q)/(q-1)$. By the last lemma $\nu \le \pi/q$, and $q > 1$. $\square$

In words: a term that is least among the terms of all $\mathrm{SL}_2$ translates satisfies Pieri's inequality along the root.

**Corollary (Least terms).** Let $K$ be a field of characteristic $p$, $a \ne a'$, and weights $h$ with $h(Y_s) - h(X_s) = 1$ for all $s$. If every translate of $f$ by $\mathrm{rootSL}(W, a, a')$ has only terms of $h$-weight at least $h \cdot \alpha$, and the coefficient of $x^\alpha$ in $f$ is nonzero, then the defect of $\alpha$ at every letter is at most $0$.

Lean: `New.FrobeniusCycle.weight_defectWeight_nonpos_of_least` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

*Proof.* In $K$ one has $w^2 = p = 0$, so $w = 0$. Then order plus weight at least $h\cdot\alpha$ means that terms of smaller weight vanish, and $w^1 \nmid \lambda$ means $\lambda \ne 0$. Apply the root lemma with $c = h$ and $l = 0$. $\square$

### A third of the defect

**Theorem (Gain from the defect).** Let $a \ne a'$, a letter $i$, and weights $d$ with $d(Y_s) - d(X_s) = 1$ for all $s$. If every translate of $f$ by $\mathrm{rootSL}(W, a, a')$ lies in level $v_0$ of the Gauss filtration for $w$ and $d$, then $f$ lies in level $v_0$ for the weights $\omega = d - \delta_i/3$, where $\delta_i$ is the defect weight along $(a, a')$.

Lean: `New.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three` (New/UpperBound/ElementaryDivisors/RootLemma.lean).

*Proof.* By Section 2, $\delta_i(Y_s) - \delta_i(X_s) \in [0, \frac32]$. So $\omega(Y_s) - \omega(X_s) = 1 - (\delta_i(Y_s) - \delta_i(X_s))/3 \in [\frac12, 1]$. Let "low" be the set of pairs $(\beta, l)$ with $l + \omega\cdot\beta < v_0$ such that, for some $g \in \mathrm{rootSL}$, $w^{l+1}$ does not divide the coefficient of $x^\beta$ in $g\cdot f$. If low is empty, $f$ lies in level $v_0$ for $\omega$. Suppose low is not empty. It is finite: translates do not raise the total degree (`New.FrobeniusCycle.totalDegree_polyAction_le`), so $\beta$ ranges over a finite set, and $l < v_0 - \omega\cdot\beta$. Take $(\alpha, l)$ in low with $l + \omega\cdot\alpha$ least, witnessed by $g_0$. Every pair in low has value at least $l + \omega\cdot\alpha$, which is below $v_0$. Hence every translate of $g_0 \cdot f$ lies in level $l + \omega\cdot\alpha$ for $\omega$. The root lemma for $g_0 \cdot f$, with $c = \omega$, gives $\delta_i\cdot\alpha \le 0$. Then $d\cdot\alpha = \omega\cdot\alpha + \delta_i\cdot\alpha/3 \le \omega\cdot\alpha$, so $l < v_0 - d\cdot\alpha$. The hypothesis for $g_0$ says $w^{\lceil v_0 - d\cdot\alpha\rceil}$ divides the coefficient, and this exponent is at least $l + 1$. This is a contradiction. $\square$

### Large defect on the edges

Now return to coefficient vectors $F : \mathrm{Exp} \to O$, with $O$ a domain of characteristic $0$, and to the block $r$ of Section 3. The depth of Section 2 is the weight with $1$ at the deep variables, and it rises by $1$ from $X_s$ to $Y_s$ along a root $(a, r)$ with $a < r$.

**Lemma (Large defect).** Let $a < r$ and a letter $i$. Suppose $w^m$ divides $w^{\mathrm{depth}\,\beta}(\rho(g)F)_\beta$ for all $g \in \mathrm{GL}_k(W)$ and $\beta \in \mathrm{Exp}$. If $\beta$ has defect at least $3j$ at $i$ along $(a, r)$, then $w^{m+j}$ divides $w^{\mathrm{depth}\,\beta}(\rho(g)F)_\beta$ for every $g$.

Lean: `New.FrobeniusCycle.pow_add_dvd_of_le_defect` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* Let $f$ be the polynomial with coefficients $\rho(g)F$. For $\gamma \in \mathrm{rootSL}$ the polynomial $\gamma \cdot f$ has coefficients $\rho(\gamma g)F$, so by hypothesis its terms have order at least $m - \mathrm{depth}$; it lies in level $m$ for the depth. By the gain from the defect, $w$ to the power $\lceil m - \mathrm{depth}\,\beta + \mathrm{defect}/3\rceil_+$ divides $(\rho(g)F)_\beta$. With defect at least $3j$ this exponent plus $\mathrm{depth}\,\beta$ is at least $m + j$. $\square$

**Corollary (Edges).** Let $a < r$ and $v \in \mathrm{allEdgesForms}(k, n, r)$, and let $g$ be block diagonal for the blocks $r$, $k - r$. If $\beta$ has defect at least $3j$ at some letter along $(a, r)$, then $w^j \mid (\rho(g)v)_\beta$. Hence, for every $c$,

$$\mathrm{allEdgesForms}(k, n, r) \subseteq \mathrm{defectConditions}(n, a, r, (w^c), 3c^*), \qquad c^* = 3kc.$$

Lean: `New.FrobeniusCycle.pow_dvd_letterRep_mulVec_of_mem_allEdgesForms` (New/UpperBound/ElementaryDivisors/Edges.lean).

Lean: `New.FrobeniusCycle.allEdgesForms_le_defectConditions` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* By Section 3, $w^m v = \Delta h$ for some $m$ and $h$, where $\Delta$ multiplies the coefficient at $\beta$ by $w^{\mathrm{depth}\,\beta}$, and $w^m$ divides all coefficients of $\Delta\rho(\gamma)h$ for all $\gamma$. A block diagonal $g$ commutes with $\Delta$, since it does not mix deep and shallow variables. So $w^m(\rho(g)v)_\beta = w^{\mathrm{depth}\,\beta}(\rho(g)h)_\beta$. The large defect lemma for $h$ makes this divisible by $w^{m+j}$. Cancel $w^m$, which is not a zero divisor in the domain $O$. For the inclusion, take $j = c$: a defect above $3c^*$ is above $3c$, because $3c \le c^*$. $\square$

**Corollary (Edge pairing).** Let $(b, b')$ be an edge pairing (Section 3), $a < r$, $v \in \mathrm{allEdgesForms}(k, n, r)$ and $g$ block diagonal. If $\beta$ has defect above $c^*$ at some letter along $(a, r)$, then $w^c$ divides $v \cdot (b \ast \rho(g)e_\beta)$, where $b\ast$ is multiplication by $b$ entrywise and $e_\beta$ is the unit vector.

Lean: `New.FrobeniusCycle.IsEdgePairing.pow_dvd_pairing_letterRep` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* The adjointness of the pairing gives $v\cdot(b \ast\rho(g)e_\beta) = (\rho(g^{\mathsf T})v)_\beta\,b_\beta$. The transpose $g^{\mathsf T}$ is block diagonal. Apply the last corollary with $j = c$, as $3c \le c^*$ is below the defect. $\square$

### The cone of Pieri's inequalities

Now work over a field $K$ of characteristic $p$, which in the application is the residue field of $O$.

**Definition (Defect cone).** For $a$ and real $h$, $\mathrm{defectCone}(a, h)$ is the set of real vectors $\beta$ on $\{0, \dots, k-1\} \times \mathbb Z/N$ whose defect along $(b, b+1)$ at every letter is at most $h$ if $b = a$ and at most $0$ otherwise. The slab $\mathrm{degreeSlab}(k, D)$ is the set of $\beta \ge 0$ with $\sum_b\beta(b, s) \in [D_s - 1, D_s]$ for every $s$.

Lean: `New.FrobeniusCycle.defectCone` (New/UpperBound/ElementaryDivisors/DefectCount.lean).

For $h = 0$ these are Pieri's inequalities. In the coordinates $\nu$ given by the step map $\beta(b, s) = \pm(P\nu(b, s+1) - \nu(b, s))$, with $+$ at even $s$, the cone becomes $\mathrm{pieriCone}$: $P\nu(b+1, s+1) \le \nu(b, s)$ at even $s$ and $\nu(b+1, s) \le P\nu(b, s+1)$ at odd $s$ (`New.FrobeniusCycle.permStep_mem_defectCone_iff`). For one letter, with $P$ replaced by $q$, these are interlacing conditions of the shape that appears in Pieri's rule.

Lean: `New.pieriCone` (New/UpperBound/ElementaryDivisors/PieriCone.lean).

**Theorem (Volume of the cone).** Let $P > 1$, $q = P^N$, $D : \mathbb Z/N \to \mathbb R$, and let $\Omega$ be a set with $\mathrm{permStep}(\nu) \in \Omega \iff \nu \in \mathrm{pieriCone}$. Then

$$\prod_{l < k}\frac{q^{l+1} - 1}{q - 1}\cdot \mathrm{vol}(\Omega \cap \mathrm{degreeSlab}(k, D)) = \mathrm{vol}(\mathrm{degreeSlab}(k, D)).$$

Lean: `New.prod_mul_volume_real_inter_degreeSlab` (New/UpperBound/ElementaryDivisors/PieriCone.lean).

*Proof (main steps).* Expand the indicator of the cone, in each letter, as a signed sum over permutations of indicators of sets where all steps are positive; this is a determinant of interlacing indicators (`New.det_interlacing_indicator`). The change of variables by the step map has a determinant $\det(1 - \cdot)$ that is computed in closed form (`New.exists_det_permStep_eq`). The result (`New.volume_real_inter_degreeSlab_eq_signed_sum`) is that the share of $\Omega$ in the slab is a number $c$ that depends only on $k$ and $q$. So it can be computed for one letter with $q$ in place of $P$, where the step map is a homothety. The share is $\prod_{l<k}(q-1)/(q^{l+1}-1)$, by the direct computation `New.volume_real_pieriCone_inter_degreeSlab_one`. $\square$

The number $\prod_{l<k}(q^{l+1}-1)/(q-1)$ is the number of full flags in $k_W^k$. So the theorem says: the cone of Pieri's inequalities fills one part in "number of flags" of each slab (`New.FrobeniusCycle.prod_mul_volume_defectCone_inter_degreeSlab`).

### Few forms have bounded defect

**Theorem (Flags and volume).** Let $K$ have characteristic $p$, $a + 1 = a'$, $n \in \mathbb N$ and $t \ge 2(k + 1)$. Let $L$ be the block diagonal group for the blocks $a'$, $k - a'$, and $S = \mathrm{defectConditions}(n, a, a', 0, 3t)$. There are $D_s \in [1, n + 4tP^{2a'}]$ such that

$$\dim_K S \le [L : L \cap B^-]\cdot\mathrm{vol}(\mathrm{defectCone}(a, 0) \cap \mathrm{degreeSlab}(k, D)),$$

where $B^- = \mathrm{parahoric}(W, \mathrm{Fin.val})$ is the lower Iwahori subgroup: the matrices whose $(b, c)$ entry is in the maximal ideal for $b < c$.

Lean: `New.FrobeniusCycle.exists_finrank_defectConditions_le_volume` (New/UpperBound/ElementaryDivisors/DefectCount.lean).

*Proof (main steps).* Choose an integral $\sigma \ge 0$ in $\mathrm{defectCone}(a, -1)$ of degree at most $P^{2a'} - 1$ in each letter (`New.FrobeniusCycle.exists_mem_defectCone_sum_le`), and put $D_s = n + k + 1 + 4t\sum_b\sigma(b, s)$. For $m = q^j$, pack $m^{kN}$ forms of $S$ into one polynomial: substitute $x^m$ for $x$ in each and multiply by one monomial for each class of exponents modulo $m$ (`New.powerPacking`). In characteristic $p$ this substitution commutes with the action. Take representatives of $L/(L \cap B^-)$. Order the terms by the height $\pm b$ of the variables. By the corollary on least terms, applied along each simple root inside the blocks, a translate by a representative has a nonzero term $\alpha$ of defect at most $0$ along those roots (`New.FrobeniusCycle.exists_coeff_ne_zero_weight_defectWeight_nonpos`). Since the forms lie in $S$, $\alpha/m$ has defect at most $4t$ along $(a, a')$ (`New.FrobeniusCycle.div_mem_defectCone_inter_degreeSlab`), and $\alpha/m + 4t\sigma$ lies in the cone of Pieri's inequalities cut by the slab of degrees $D$. The map from the packed forms to their coefficients at these points is injective. So $m^{kN}\dim S$ is at most the index times the number of points of $m^{-1}\mathbb Z^{kN}$ in this bounded convex set (`New.FrobeniusCycle.finrank_defectConditions_mul_pow_le`). Divide by $m^{kN}$ and let $j \to \infty$: the count tends to the volume. $\square$

**Lemma (Indices).** For every $r$, $[\mathrm{GL}_k(W) : P_r]\cdot[L : L\cap B^-] \le \prod_{l<k}(q^{l+1}-1)/(q-1)$, where $P_r = \mathrm{parahoric}(W, \mathrm{twoBlock}(k, r))$ and $L$ is its Levi group.

Lean: `New.FrobeniusCycle.index_mul_relIndex_le` (New/UpperBound/ElementaryDivisors/DefectCount.lean).

*Proof.* $L \subseteq P_r$, so $[L : L \cap B^-] \le [P_r : B^-]$. Also $B^- \subseteq P_r$, so the product is at most $[\mathrm{GL}_k(W) : B^-]$. This index equals the index of the lower triangular group in $\mathrm{GL}_k(k_W)$, which is at most the number of flags (`New.index_borel_le`). $\square$

**Theorem (Few forms of bounded defect).** Let $K$ have characteristic $p$, $a + 1 = a'$, $n > 0$, $t \ge 2(k+1)$, $\theta \le 1$ and $8Nkt\,P^{2a'} \le \theta n$. Then

$$[\mathrm{GL}_k(W) : P_{a'}]\cdot\dim_K\mathrm{defectConditions}(n, a, a', 0, 3t) \le (1 + \theta)\,|\mathrm{Mon}_k(n)|^N,$$

where $\mathrm{Mon}_k(n)$ is the set of monomials of degree $n$ in $k$ variables.

Lean: `New.FrobeniusCycle.index_mul_finrank_defectConditions_le` (New/UpperBound/ElementaryDivisors/DefectCount.lean).

*Proof.* Put $E = 4tP^{2a'}$, so $2NkE \le \theta n$. By flags and volume, the indices lemma and the volume of the cone, the left side is at most $\mathrm{vol}(\mathrm{degreeSlab}(k, D))$ with $D_s \le n + E \le e^{E/n}n$. Write $k = k' + 1$. The slab is contained in a product over the letters of the simplex shells $\{y \ge 0 : \sum y \in [D_s - 1, D_s]\}$ in $\mathbb R^k$, each of volume at most $B^{k'}/k'!$ for $B = e^{E/n}n$ (`New.volume_degreeSlab_le`). So the volume is at most $e^x(n^{k'}/k'!)^N$ with $x = Nk'E/n \le \theta/2 \le \frac12$. Then $e^x \le 1 + 2x \le 1 + \theta$. Finally $n^{k'}/k'! \le \binom{n+k'}{k'} = |\mathrm{Mon}_k(n)|$ (`New.pow_div_factorial_le_card_monomials`). $\square$

**Remark (Formalization).** The space is $\mathrm{defectConditions}$ with the ideal $\bot = 0$: over the field $K$ the source asks that the coefficients vanish. In Section 6 this theorem is applied with $t = c^*$ to the Frobenius cycle reduced to the residue field of $O$, which has characteristic $p$ when $p$ is not a unit of $O$. Part 5 of the sizes lemma of Section 2 gives $8Nkc^*P^{2r} \le \theta n$.
