---
title: Denominators, sizes and spanning forms
lean:
  - New/Determinant/AuxiliaryForms/SpanningForms.lean
decls:
  - New.Data.lastPathBound
  - New.Data.liftDenominator
  - New.Data.liftDenominator_smul_lastPathEdgeDatum_mem_raises
  - New.Data.generator_inv_mul_normQ_mul_star_mem
  - New.Data.norm_mul_det_flipScalar_zpow_le_one
  - New.Data.exists_norm_mul_lastPathPairing_le_one
  - New.Data.exists_mul_lastPathPeriod_mem_embValRing
  - New.Data.card_stdClasses_lastPathLevel_le
  - New.Data.sqrt_weylNormSq_lastPathKernel_le
  - New.Data.norm_lastPathPeriod_le
  - New.Data.exists_integral_lowerChainUpTo_eq_lastPathPeriod
  - New.Data.DualVector
  - New.Data.dualPairing
  - New.Data.isDualPairing_dualPairing
  - New.Data.dualHook
  - New.Data.dualHook_mul_exp_le
  - New.Data.mem_embValRing_of_dualPairing_eq_dualHook_mul
  - New.Data.weylNormSq_le_of_dualPairing
  - New.Data.lastPathDelta
  - New.Data.lastPathConjDelta
  - New.Data.lastPathToAlgForm_lastPathConjDelta
  - New.Data.fixedByOuterLevels_lastPathConjDelta
  - New.Data.integral_lastPathConjDelta_mul
  - New.Data.weylGauge_lastPathConjDelta_le_one
  - New.Data.weylNormSq_lastPathConjDelta_le
  - New.Data.exists_dualPairing_eq_mul_lastPathPeriod
  - New.Data.exists_lowerChain_integral_and_weylNormSq_le
  - New.Data.span_isShort_eq_top_gridLevelForms
  - New.Data.exists_span_short_lifts_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Denominators, sizes and spanning forms

Let $\Xi = \mathrm{lastPathPeriod}(\Psi, y)$ be the sum attached to the last path: the sum over tuples $S$ of matrices on its edges of $\Psi(S)$ times the integrated pairing of the lifts of the two forms $y_{\text{false}}$, $y_{\text{true}}$ along the two halves. This section bounds the denominators and the conjugates of $\Xi$, moves back to the first path, and reads the values of the chain of lifts with delta forms. Write $G_k = \exp(x^k b^2)$.

### Background in one line each

- From [grids, columns and turns](/chapter/grids-paths-turns/), linked by chapter only: the last path, its kernels, edge data, levels and branching matrix; $\Xi$ is a sum of $L$ copies of branching pairings of vectors got by $m$ lifts from each end (`exists_lastPathPeriod_mem_smul_norm_le`); the branching pairing is equivariant with a character $\prod_\tau\det^{L_\tau}$, $|L_\tau| \le b r^4 + \lceil 20b\rceil$; the turns carry the first path to the last path at the cost of constants $c(\vartheta)$ with $|c(\vartheta)|$ = turn ratios up to $C\,\mathrm{Nm}\,Q^k$ (`exists_transfersPeriods_first_last`).
- Gauges, integral forms, delta forms $\delta_x(v)$ and their gauge and size bounds, and the isomorphism of algebraic forms with forms of a level ([automorphic forms](/chapter/automorphic-forms/), [deltaForm](/decl/New.deltaForm/), [algFormEquiv](/decl/New.Space.algFormEquiv/)).
- Dual pairings and hook numbers: an integer matrix $C$ with $C\cdot P = h\cdot 1$, and a vector $w$ with $u\cdot P\zeta = \langle w, u\rangle$ and $\|w\|^2 = \|\zeta\|^2$ ([IsDualPairing](/decl/New.IsDualPairing/), [hookNumber](/decl/New.hookNumber/)).
- Short bases: for a level small enough that no class has an extra automorphism, the algebraic forms with integral values and conjugates of squared norm at most a constant span (`New.span_isShort_eq_top`, [automorphic forms](/chapter/automorphic-forms/)).
- Class counts are at most $\exp(\dots)$ in the data sizes ([card_stdClasses_le_exp_mul_log](/decl/New.Data.card_stdClasses_le_exp_mul_log/)).
- $|c(\vartheta)| \sim$ turn ratios is [HasAbsUpToNormPower](/decl/New.Data.HasAbsUpToNormPower/).

### Denominators

**Definition.** $\mathrm{lastPathBound}(\vartheta) = \mathrm{vectorCountBound}(\vartheta)^{m^2}\,\mathrm{edgeMatrixCountBound}(\vartheta)^{2m}$, one factor per turn times the bound of the first path. The lift denominator is

$$d = (M^b)^{2f(2n_m)^2}\,(M^bp_d)^{b r^4},$$

with $n_m$ = `D.n D.m`, $p_d$ = `P.d`.

Lean: `New.Data.lastPathBound`, `New.Data.liftDenominator` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

**Lemma.** Let $p \nmid \mathrm{Nm}\,Q$. Each edge datum of the last path, times $d$, lies in the raises $(1,1,1)$ of its kernel: its lifts do not increase $p$-adic gauges.

Lean: `New.Data.liftDenominator_smul_lastPathEdgeDatum_mem_raises` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* The datum is standard after a factor $(M^b)^{2f\cdot\#}$, and the boxes of the diagram cost $(M^bp_d)^{\text{boxes}}$. The ranks are at most $2n_m$ and the boxes at most $br^4$, so this factor divides $d$. $\square$

**Lemma.** With $t$ the generator of $\mathfrak m = \varpi^bQ$ and $\alpha$ the fixed idele ($q_1\alpha$, $\alpha^{-1}$ integral), $t^{-1}\,\mathrm{Nm}Q\,M^b\,\overline{t q_1\alpha}\,\alpha^{-1}$ is integral. For $p\nmid\mathrm{Nm}Q$, every $\tau$ and every $l \in\mathbb Z$, $|(M^bq_1)^{m|l|}\,\delta^{-l}|_p \le 1$, with $\delta$ the image at $\tau$ of $\det(u^m)^{-1}$, $u = \overline{t\alpha}/(t\alpha)$.

Lean: `New.Data.generator_inv_mul_normQ_mul_star_mem`, `New.Data.norm_mul_det_flipScalar_zpow_le_one` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* $t$ divides $\mathrm{Nm}Q\cdot M^b$, and the other factors are integral. So the first adele $a$ is integral. For $l \ge 0$ the number is a power of the image of $a$ divided by the unit $\mathrm{Nm}Q^{ml}$; for $l < 0$ the same holds for $\bar a$. $\square$

**Lemma.** There is $N \ne 0$ with $\log N \le x^{98}b^2$ such that for all $\vartheta$, $p\nmid\mathrm{Nm}Q$, and vectors $v'$, $v$ of gauge $\le 1$ at $g$ and at $\mathrm{diag}(g, u^m)$, $|N\cdot\langle v', v\rangle|_p \le 1$.

Lean: `New.Data.exists_norm_mul_lastPathPairing_le_one` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Take $N = \prod_\tau (M^bq_1)^{m|L_\tau|}$. By equivariance, the pairing is $\prod_\tau\chi_\tau^{-1}$ times the pairing of the translated vectors, whose entries are integral, and the branching matrix is integral. The previous lemma bounds $|N_\tau\chi_\tau^{-1}|_p \le 1$. The bound on $\log N$ is a size inequality. $\square$

**Proposition (Denominators of $\Xi$).** There is $0 < N \le G_{99}$ such that for every $\vartheta$, path datum $\Psi$ on the last path, pair $y$ fixed by the outer levels, and $p\nmid\mathrm{Nm}Q$: if both algebraic forms of $y$ have gauge $\le 1$ everywhere, then $N\,\Xi$ is $p$-integral.

Lean: `New.Data.exists_mul_lastPathPeriod_mem_embValRing` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Put $N = N_0 d^{2m}$ with $N_0$ from the previous lemma. By induction, $d^j$ times a vector after $j$ lifts has gauge $\le 1$. At the middle, $N_0d^{2m}$ times the pairing is integral. $\Xi$ is a sum of $L$ such terms, and integral numbers form a group. $\log N \le x^{99}b^2$ is a size inequality. $\square$

### Sizes

**Lemma.** For the trivial twist, the class numbers along the last path are at most $G_{99}$. Each lift of the last path multiplies $\sqrt{\|\sigma v\|^2}$ by at most $G_{99}$, for every $\sigma \in \mathrm{Aut}\,\mathbb C$.

Lean: `New.Data.card_stdClasses_lastPathLevel_le`, `New.Data.sqrt_weylNormSq_lastPathKernel_le` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* The levels contain the principal level of $M^b$, so the class count applies. The edge datum is the indicator of one matrix, so the operator bound for Schur jets applies with size $1$, and every row of the diagram is at most $br^4$ long. $\square$

**Proposition (Conjugates of $\Xi$).** For the trivial twist, a path datum $\Psi$ with bound lastPathBound, $y$ fixed by the outer levels and $\|\sigma(y_z)(g)\|^2 \le B_z$ for all $g$:

$$|\sigma\Xi| \le G_{200}\sqrt{B_{\text{false}}}\sqrt{B_{\text{true}}}.$$

Lean: `New.Data.norm_lastPathPeriod_le` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* After $j$ lifts a vector is at most $G_{99}^j\sqrt{B_z}$. The branching pairing has norm at most $C = ((br^4)^{br^4})^3$ times the norms. The number of terms is $L$ times $2m + 1$ class numbers, at most $L\,G_{99}^{2m+1}$. The product $L\,G_{99}^{2m+1}\,C\,G_{99}^{2m}$ is at most $G_{200}$ by a size inequality. $\square$

### Back to the first path

**Proposition.** There are $c(\vartheta)$ with $|c(\vartheta)| \sim \prod_{i,j<m}\mathrm{turnRatio}(i,j)$, path data $\Psi_\vartheta$ on the last path, a number $\beta$ and a map $r$ onto the principal forms with

$$n(\vartheta)\int y'\cdot\Theta_\vartheta(r\varphi) = \beta\,\Xi(\Psi_\vartheta; y', \varphi)/c(\vartheta),$$

where $n(\vartheta)$ is the index of the level $J(\mathfrak m_0)$ on $Y_m$.

Lean: `New.Data.exists_integral_lowerChainUpTo_eq_lastPathPeriod` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Take $\Psi_0, g, \alpha, r$ from the theorem on the first path (Section 7). The turns of [grids, columns and turns](/chapter/grids-paths-turns/) give $c$ and $\Psi$, and a $\beta'$ with $\mathrm{gridPeriod}(\Psi_0, g) = \beta'\,\Xi/n(\vartheta)/c(\vartheta)$. Put $\beta = \alpha\beta'$ and use $n(\vartheta) \ne 0$. $\square$

### Values from pairings

**Definition.** $\mathrm{DualVector}$ is the space of values of the dual weight on $Y_m$. $P$ = `dualPairing` is an integer matrix of the invariant pairing of the dual weight with the weight on $Y_m$, chosen with `choose`; it is a dual pairing normalised at the highest vector. $h$ = `dualHook` is the hook number of the dual weight, a positive integer.

Lean: `New.Data.DualVector`, `New.Data.dualPairing`, `New.Data.isDualPairing_dualPairing`, `New.Data.dualHook` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

**Lemma.** (i) $h\,G_{99}G_{200} \le G_{201}$. (ii) If $w\cdot P\zeta \in h\cdot\mathcal O_p$ for every integer vector $w$, then $\zeta$ is $p$-integral. (iii) If $|\sigma(v\cdot P\zeta)| \le K\sqrt{\|\sigma v\|^2}$ for all $v$, with $K \ge 0$, then $\|\sigma\zeta\|^2 \le K^2$.

Lean: `New.Data.dualHook_mul_exp_le`, `New.Data.mem_embValRing_of_dualPairing_eq_dualHook_mul`, `New.Data.weylNormSq_le_of_dualPairing` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* (i) $h \le ((br^4)^{br^4})^3$ and a size inequality. (ii) Take $C$ with $CP = h$. Then $h\zeta_i = (C_i)\cdot P\zeta = h a$ with $a$ integral, and $h \ne 0$. (iii) Take $w$ with $\|w\|^2 = \|\sigma\zeta\|^2$ and $u\cdot P\sigma\zeta = \langle w, u\rangle$. Then $\|w\|^2 = \sigma((\sigma^{-1}w)\cdot P\zeta) \le K\|w\|$, so $\|w\| \le K$. $\square$

**Definition (Delta forms).** $\delta_x(v)$ = `lastPathDelta` is the algebraic form of the dual weight and level $J(\mathfrak m_0)$ on $Y_m$ with value $v$ on the class of $x$. `lastPathConjDelta` is the same as a conjugate form on $Y_m$.

Lean: `New.Data.lastPathDelta`, `New.Data.lastPathConjDelta`, `New.Data.lastPathToAlgForm_lastPathConjDelta` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

**Lemma.** (i) For $\varphi \in \mathcal F_{\mathfrak b}^m$, the pair $(\delta_x(v), \varphi)$ is fixed by the outer levels. (ii) For a principal form $y$,

$$n(\vartheta)\int\delta_x(v)\cdot\Theta_\vartheta y = \frac{v\cdot P\,(\Theta_\vartheta y)^{\mathrm{alg}}(x)}{\dim}.$$

(iii) If $x$ is integral above $p$ and $w$ is an integer vector, $\delta_x(w)$ has gauge $\le 1$. (iv) $\|\sigma\delta_x(v)(g)\|^2 \le \|\sigma v\|^2$.

Lean: `New.Data.fixedByOuterLevels_lastPathConjDelta`, `New.Data.integral_lastPathConjDelta_mul`, `New.Data.weylGauge_lastPathConjDelta_le_one`, `New.Data.weylNormSq_lastPathConjDelta_le` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* (i) $\delta$ has level $J(\mathfrak m_0)$, and $\varphi$ has level $J(\mathfrak b)$, which lies in the outer level of $\tilde Y^m_0$. (ii) The integrand $v\cdot P(\cdot)$ is invariant under the level, so the integral is a class sum. It is supported on the class of $x$. The factor $1/\dim$ is Schur's orthogonality for the weight and its dual. (iii) and (iv) are the gauge and size bounds of delta forms; for (iv) the level is small enough that no class has extra automorphisms. $\square$

**Proposition.** There are $c$, $\Psi$, $\beta$ and $r$ as above with

$$v\cdot P\big((c(\vartheta)/c(1))\,\Theta_\vartheta(r\varphi)\big)(x) = \beta\,\Xi(\Psi_\vartheta; \delta_x(v), \varphi).$$

Lean: `New.Data.exists_dualPairing_eq_mul_lastPathPeriod` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Combine (ii) with the proposition on the first path at $y' = \delta_x(v)$, and replace $\beta$ by $\dim\cdot\beta/c(1)$. $\square$

### Integrality and size

**Theorem.** There are $c$ as above, a map $r$ onto the principal forms, and $s \ne 0$ such that for $\varphi \in\mathcal F^m_{\mathfrak b}$:

1. if the algebraic form of $\varphi$ is $p$-integral and $p\nmid\mathrm{Nm}Q(\vartheta)$, then $(c(\vartheta)/c(1))\,\Theta_\vartheta(s\,r\varphi)$ is $p$-integral;
2. if $\|\sigma\varphi^{\mathrm{alg}}(g)\|^2 \le B$ for all $g$, then $\|\sigma\Theta_1(s\,r\varphi)(g)\|^2 \le G_{201}^2 B$.

Lean: `New.Data.exists_lowerChain_integral_and_weylNormSq_le` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Take $N$ from the proposition on denominators. If $\beta = 0$, put $s = 1$, $\varepsilon = 0$. Otherwise put $s = hN/\beta$, $\varepsilon = 1$. In both cases $s\beta = h\varepsilon N$, and

$$v\cdot P\big((c(\vartheta)/c(1))\Theta_\vartheta(s\,r\varphi)\big)(x) = h\,\varepsilon\,N\,\Xi(\delta_x(v), \varphi).$$

For 1, take $x$ integral above $p$ and $w$ integral. By (i), (iii) and the proposition on denominators, $N\Xi$ is integral. Lemma (ii) of the dual pairing gives integrality at $x$. Integral points above $p$ suffice for the gauge. For 2, $c(1)/c(1) = 1$. By (iv) and the proposition on conjugates, $|\sigma\Xi| \le G_{200}\sqrt{\|\sigma v\|^2}\sqrt B$. So $|\sigma(v\cdot P\cdots)| \le h\,G_{99}G_{200}\sqrt B\sqrt{\|\sigma v\|^2} \le G_{201}\sqrt B\sqrt{\|\sigma v\|^2}$. Lemma (iii) finishes. $\square$

**Remark (Formalization).** If $\beta = 0$, the proof takes $s = 1$, and then every value $v\cdot P\,\Theta_\vartheta(r\varphi)(x)$ is $0$. So both properties hold for the trivial reason that the lifts vanish. The source does not show $\beta \ne 0$ in this file. The constants $\alpha$ of Section 7 and $\beta$ may be $0$ as far as these statements go. The theorem is still true as stated. The choices $P$, $c$, $r$ and $s$ are made with `choose` or existentials.

### Spanning

**Lemma.** $\mathcal F_{\mathfrak b}^m$ is spanned by the forms whose algebraic forms are short: integral at every prime, with conjugates of squared norm at most $G_{99}$.

Lean: `New.Data.span_isShort_eq_top_gridLevelForms` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* As $\varpi \mid \mathfrak b$, the level lies in $J_M$, and no class has extra automorphisms. The short basis theorem gives the statement for algebraic forms, with the short basis constant at most $G_{99}$. The isomorphism with $\mathcal F^m_{\mathfrak b}$ carries it over. $\square$

**Theorem (Spanning forms).** There are constants $c(\vartheta) \ne 0$ with $|c(\vartheta)| \sim \prod_{i,j<m}\mathrm{turnRatio}(i,j)$ such that the principal forms on $Y_0$ are spanned by the forms $y$ with:

1. for all $\vartheta$ and primes $l\nmid\mathrm{Nm}Q(\vartheta)$, $(c(\vartheta)/c(1))\,\Theta_\vartheta y$ (at level) is $l$-integral;
2. for all $\sigma$ and $g$, $\|\sigma\,\Theta_1 y(g)\|^2 \le G_{202}$.

Lean: `New.Data.exists_span_short_lifts_eq_top` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

*Proof.* Take $c$, $r$, $s$ from the theorem above. As $r$ is onto and the short $\varphi$ span $\mathcal F^m_{\mathfrak b}$, the forms $r\varphi$ span. For short $\varphi$, the form $s\,r\varphi$ has both properties: 1 by part 1, and 2 by part 2 with $B = G_{99}$, as $G_{201}^2G_{99} \le G_{202}$. As $s \ne 0$, the span of the $s\,r\varphi$ is that of the $r\varphi$. $\square$
