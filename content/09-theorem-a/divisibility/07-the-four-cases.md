---
title: The four cases
lean:
  - New/UpperBound/Divisibility/LocalDivisibility.lean
decls:
  - New.GaugeLe.rpow_mono
  - New.GaugeLe.add
  - New.GaugeLe.smul
  - New.GaugeLe.zpow_neg_smul
  - New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_of_mem_raises
  - New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_one
  - New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_collisionSum
  - New.Data.IsWeakChainDatum.gaugeLe_pow_collisionExponent_smul
  - New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_of_isFullMark
  - New.Data.IsMarked.mul_sum_heckeScalingExponent_le_loss
  - New.Data.IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow
  - New.Data.mem_smallNonsplitPrimes_iff_isSmallNonsplit
  - New.Data.chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes
  - New.Data.IsChainDatum.gaugeLe_compositeLift_of_isFullMark
  - New.Data.exists_colengthDvd_gaugeLe_compositeLift
  - New.Data.exists_err_gaugeLe_compositeLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The four cases

This section proves the theorem of the chapter. At each prime $p$ it gives a module $S$ of source forms of small colength on which the composite lift $B_{\vartheta,\Psi}$ has valuation at least $\mathrm{gain}(p) - \mathrm{allowed}(p)$. There are four cases: $p \ne N$ with no gain; $p < x_1$ nonsplit and not exceptional; $p < x_1$ exceptional; and $p = N$.

A form $\varphi$ *has valuation at least $v$* if $\mathrm{GaugeLe}(1, p^{-v}, \varphi)$. For a weak chain datum $\Psi$, write $R_\Psi\varphi = \mathrm{res}\,\mathrm{CC}(\vartheta, \Psi, \cdot, m)\,\varphi$ for the restricted chain of [the objects of the upper bound](/chapter/upper-bound-objects/). The gain $\mathrm{gain}(p)$, the loss $\mathrm{loss}(p)$, the collision sum $\mathrm{coll}_p(S)$ (the sum of $a/p^e$ over the collisions $(\tau, e)$ outside $S$) and $j_p = \lceil 2mfa/p\rceil$ are from [short columns and the gain](/chapter/short-columns-gain/). The allowed loss $\mathrm{allowed}(p)$ is from [the archimedean size](/decl/New.Data.allowedLoss/): $2\,\mathrm{loss}(p)$ on the small nonsplit primes, $2mfb$ at $p = N$ outside them, and $0$ otherwise.

### Gauges under sums and scalars

**Lemma.** Let $\mathrm{GaugeLe}(d, c, \varphi)$ and $\mathrm{GaugeLe}(d, c, \psi)$. Then:

1. $\mathrm{GaugeLe}(d, c, \varphi + \psi)$;
2. $\mathrm{GaugeLe}(d, |\iota_p z|_p\,c, z\varphi)$ for $z \in \mathbb C$;
3. if $c = p^r$ and $r \le r'$, then $\mathrm{GaugeLe}(d, p^{r'}, \varphi)$;
4. if $c = p^r$ and $\beta \in \mathbb Z$ with $\beta \le -r$, then $\mathrm{GaugeLe}(d, 1, p^{-\beta}\varphi)$.

Lean: `New.GaugeLe.add`, `New.GaugeLe.smul`, `New.GaugeLe.rpow_mono`, `New.GaugeLe.zpow_neg_smul` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* The gauge is ultrametric and scales with $|\iota_p z|_p$. Since $p > 1$, $p^r \le p^{r'}$. For item 4, $|\iota_p p^{-\beta}|_p = p^\beta$, so item 2 gives the bound $p^{\beta + r} \le 1$. $\square$

### Chains away from $N$

**Lemma.** Let $\Psi$ be a weak chain datum, $p$ prime to $\mathrm NQ$, $p \ne N$, and let $v_{x,j} \in \mathrm{raises}(1, 1, p^{r_j})$ for $x \in \mathrm{supp}\,\Psi$ and all $j$. Then $\mathrm{GaugeLe}(1, p^{\sum_{j<m}r_j}, R_\Psi v)$ for every $v \in \mathcal A_\iota$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_of_mem_raises` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* Apply [the gauge of a weak chain](/decl/New.Data.IsWeakChainDatum.gaugeLe_chain/) with base points $1$, then [restriction to $Y$](/decl/New.Data.GaugeLe.restrictToY/), which keeps gauges for $p \ne N$. $\square$

**Lemma (Case 1).** Let $\Psi$ be a weak chain datum, $p$ prime to $\mathrm NQ$, $p \ne N$ and $p \ne d$. Then $\mathrm{GaugeLe}(1, 1, R_\Psi v)$ for every $v \in \mathcal A_\iota$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_one` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* The translated data are standard for $\delta = \bar\pi_m$ ([standard data](/decl/New.Data.IsWeakChainDatum.translateDatum_mem_standardData/)). By [the bound for standard data](/chapter/theta-kernels-gauges/), a lift with standard data multiplies gauges by at most $(|\iota_p c|_p/|\iota_p cd|_p)^{\mathrm{boxes}}$ with $c = \bar\pi_m$. Since $p \ne d$, $|\iota_p d|_p = 1$, so the factor is $1$. Apply the last lemma with $r_j = 0$. $\square$

**Lemma (Case 2).** Let $p < x_1$ be nonsplit and prime to $\mathrm NQ$. Then for every $v \in \mathcal A_\iota$, $R_\Psi v$ has valuation at least $\mathrm{gain}(p) - \mathrm{loss}(p) - m\,\mathrm{coll}_p(\emptyset)$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_collisionSum` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* By [the not-dividing lemma](/decl/New.Data.IsSmallNonsplit.not_dvd_M_mul_N/), $p \nmid MN$. So the data are standard for every $\delta$, and lift $j$ lies in $\mathrm{raises}(p^{-D_{p,j}(\emptyset)})$ by `New.Data.mem_raises_neg_divisibilityBound` of Section 5. By [short columns and the gain](/chapter/short-columns-gain/) (`New.Data.le_divisibilityBound`, `New.Data.le_loss`),

$$D_{p,j}(\emptyset) \ge \frac{\mathrm{gain}(p)}{m} - \mathrm{coll}_p(\emptyset) - \frac{f(\log b)^2a}{pm} \ge \frac{\mathrm{gain}(p) - \mathrm{loss}(p)}{m} - \mathrm{coll}_p(\emptyset).$$

Sum over $j < m$ and apply the lemma above. $\square$

**Lemma (The crude bound).** Under the same hypotheses, $R_\Psi(p^{j_p}v)$ has valuation at least $\mathrm{gain}(p) - \mathrm{loss}(p)$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_pow_collisionExponent_smul` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* Every collision has $e \ge 1$, so `New.Data.collisionSum_le` gives $\mathrm{coll}_p(\emptyset) \le 2fa/p$ and $m\,\mathrm{coll}_p(\emptyset) \le j_p$. The factor $p^{j_p}$ adds $j_p$ to the valuation of Case 2. $\square$

### The exceptional primes

**Theorem (Valuation on the image).** Let $\Lambda$ be a full mark, $p$ prime to $\mathrm NQ$, $Y = \prod_{\mathfrak l\in\Lambda}Y_{\mathfrak l}$ and $v \in \mathcal A_\iota$. Then $R_\Psi(Y^mv)$ has valuation at least $\mathrm{gain}(p) - 2\,\mathrm{loss}(p)$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_of_isFullMark` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* By the last theorem of Section 5 it is enough to show, for each $j < m$,

$$\#\Lambda\,\nu_p + \mathrm{liftLoss}(\Lambda, j) \le \frac{2\,\mathrm{loss}(p) - \mathrm{gain}(p)}{m}.$$

Since $p$ is exceptional, $p \ne d$, so $v(\pi_p) = 1$. A full mark leaves no collision outside $\Phi_\Lambda$ ([full marks](/decl/New.Data.IsFullMark.collisionSum_placesInducing_eq_zero/)). So the lower bound of `New.Data.le_divisibilityBound` reads

$$D_{p,j}(\Phi_\Lambda) \ge \frac{\mathrm{gain}(p)}{m} + \#(\Phi_a\cap\Phi_\Lambda)\frac{a}{x_1} - \frac{\mathrm{loss}(p)}{m}.$$

[The cost of the low columns](/decl/New.Data.IsMarked.card_mul_transferExponent_add_sum_lowColumns_le/) gives $\#\Lambda\,\nu_p + r\sum_{\Phi_\Lambda}L_j \le \mathrm{loss}(p)/m + \#(\Phi_a\cap\Phi_\Lambda)\,a/x_1$. Since $\mathrm{liftLoss}(\Lambda, j) = r\sum_{\Phi_\Lambda}L_j - D_{p,j}(\Phi_\Lambda)$, the sum of the two inequalities is the claim. $\square$

The surplus $a/x_1$ at each a-place of $\Phi_\Lambda$ in the divisibility bound pays for its low columns. This is why the full mark is used: it removes all collisions and puts the surplus where the cost is.

**Lemma (Colength budget).** For a marked set $\Lambda$,

$$m\sum_{\mathfrak l\in\Lambda}\Big(\frac{12A_{\mathfrak l}}{mp} + \frac{j_p}{m^2f}\Big) \le \mathrm{loss}(p).$$

Lean: `New.Data.IsMarked.mul_sum_heckeScalingExponent_le_loss` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* By [the sum of the scaling exponents](/decl/New.Data.sum_heckeScalingExponent/), $\sum A_{\mathfrak l} \le af$, and $\#\Lambda \le f$ ([the size of a marked set](/decl/New.Data.IsMarked.card_le/)). With $j_p \le 2mfa/p + 1$ the left side is at most $(14fa + p/m)/p$. The bounds on the parameters, with $p < x_1$, give $14fa + p/m \le f(\log b)^2a$, and $f(\log b)^2a/p \le \mathrm{loss}(p)$. $\square$

**Theorem (Colength of the image).** For a marked set $\Lambda$, $\mathrm{IsOntoUpToColength}(p, \mathcal A_\iota, j_p, Y^m, \mathrm{loss}(p)\,D_X)$.

Lean: `New.Data.IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* $Y^m$ is the product over the list of $m$ copies of $\Lambda$. The exponents of [products of operators](/chapter/twisted-lattices/) (`New.IsOntoUpToColength.prod`) add. The theorem of Section 6 with $j_0 = j_p$ bounds each factor, and the budget bounds the sum. $\square$

**Lemma (Case 3).** Let $\Psi$ be a chain datum, $p$ prime to $\mathrm NQ$, $\Lambda$ a full mark, and $\varphi \in Y^m\mathcal A_\iota + p^{j_p}\mathcal A_\iota$. Then $B_{\vartheta,\Psi}\varphi$ has valuation at least $\mathrm{gain}(p) - 2\,\mathrm{loss}(p)$.

Lean: `New.Data.IsChainDatum.gaugeLe_compositeLift_of_isFullMark` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* By [the expansion of the gluing](/decl/New.Data.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq/), $B_{\vartheta,\Psi} = R_{\Psi'}$ for a weak chain datum $\Psi'$. Write $\varphi = Y^mu + p^{j_p}v$. The first term has the bound of the theorem on the image. The second has the crude bound, which is better since $\mathrm{loss}(p) \ge 0$. Add. $\square$

### The theorem at one prime

A prime lies in the set $\mathcal S$ of small nonsplit primes if and only if $p < x_1$ and $\chi_K(p) \ne 1$. Outside $\mathcal S$, $\chi_K(p) = 1$ or $p \ge x_1$.

Lean: `New.Data.mem_smallNonsplitPrimes_iff_isSmallNonsplit`, `New.Data.chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes` (New/UpperBound/Divisibility/LocalDivisibility.lean).

**Theorem (Divisibility at one prime).** Let $p$ be prime. There are $l \in \mathbb N$ with $l \le \mathrm{allowed}(p)\,D_X$ and an $\mathcal O_\iota$-module $S$ of source forms with $\mathrm{ColengthDvd}(\mathcal A_\iota, S, p^l)$, such that for every twist $\vartheta$, every chain datum $\Psi$ with $p$ prime to $\mathrm NQ$, and every ramified $\varphi \in S$, $B_{\vartheta,\Psi}\varphi$ has valuation at least $\mathrm{gain}(p) - \mathrm{allowed}(p)$.

Lean: `New.Data.exists_colengthDvd_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* Case 1: $p \notin \mathcal S$ and $p \ne N$. Then $\mathrm{allowed}(p) = 0$ and $\mathrm{gain}(p) = 0$ ([no gain](/decl/New.Data.gain_eq_zero/)). Also $p \ne d$, since $d < x_1$ and $\chi_K(d) = 0$. Take $l = 0$ and $S = \mathcal A_\iota$. Expand $\Psi$ to $\Psi'$ and apply Case 1 above.

Case 2: $p \in \mathcal S$ is not exceptional. Then $m\,\mathrm{coll}_p(\emptyset) \le \mathrm{loss}(p)$ (`New.Data.mul_collisionSum_le_loss`). Take $l = 0$ and $S = \mathcal A_\iota$. Case 2 above gives valuation at least $\mathrm{gain}(p) - 2\,\mathrm{loss}(p)$.

Case 3: $p \in \mathcal S$ is exceptional. Take a [full mark](/decl/New.Data.exists_isFullMark/) $\Lambda$ and $S = Y^m\mathcal A_\iota + p^{j_p}\mathcal A_\iota$. The colength theorem gives $l \le \mathrm{loss}(p)D_X \le 2\,\mathrm{loss}(p)D_X$, and Case 3 above gives the valuation.

Case 4: $p \notin \mathcal S$ and $p = N$. Then $\mathrm{gain}(N) = 0$, since $x_1 \le N$. Take $S = \mathcal A'$, read as an $\mathcal O_\iota$-module. Section 3 gives $l \le mfbD_X \le 2mfbD_X$, and Section 4 gives the gauge bound $N^{2mfb}$ for ramified forms of $\mathcal A'$. $\square$

**Remark (Formalization).** In Cases 3 and 4 the source proves a colength exponent of $\mathrm{loss}(p)D_X$ and $mfbD_X$. The statement uses the weaker $\mathrm{allowed}(p)D_X$, the same number as in the valuation, so that one function $\mathrm{err}$ serves both. The full mark and the module $S$ come from existence statements, and $S$ depends on $p$ and $\iota_p$, not on $\vartheta$ or $\Psi$.

**Theorem (Divisibility of the composite lift).** There is $\mathrm{err} : \mathbb N \to \mathbb R$ with:

1. $\mathrm{err}(p) \ge 0$ for every $p$;
2. if $p \ne N$, and $\chi_K(p) = 1$ or $x_1 \le p$, then $\mathrm{err}(p) = 0$;
3. $\sum_{p\in U}\mathrm{err}(p)\log p \le fa\log^3b$ for every finite set $U$;
4. for every prime $p$ and every $\iota_p$, there are $l \le \mathrm{err}(p)D_X$ and an $\mathcal O_\iota$-submodule $S$ of $L = \mathcal A_\iota \cap \{\text{ramified}\}$ with $\mathrm{ColengthDvd}(L, S, p^l)$, such that for every twist $\vartheta$ and chain datum $\Psi$ with $p$ prime to $\mathrm NQ$ and every $\varphi \in S$, $B_{\vartheta,\Psi}\varphi$ has valuation at least $\mathrm{gain}(p) - \mathrm{err}(p)$.

Lean: `New.Data.exists_err_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* Take $\mathrm{err} = \mathrm{allowed}$. Item 1 is [nonnegativity](/decl/New.Data.allowedLoss_nonneg/). For item 2, such a $p$ is not in $\mathcal S$ and is not $N$, so $\mathrm{allowed}(p) = 0$. Item 3 is [the sum of the allowed losses](/decl/New.Data.sum_allowedLoss_mul_log_le/). For item 4, take $l$ and $S$ of the last theorem and put $S' = L \cap S$. A colength bound passes to intersections with $L$, so $\mathrm{ColengthDvd}(L, S', p^l)$. Every element of $S'$ is ramified and lies in $S$, so the last theorem gives the valuation. $\square$

**Remark (Formalization).** The hypothesis that $p$ is prime to $\mathrm NQ$ stays in item 4: the theorem says nothing at $p$ for a twist with $p \mid \mathrm NQ$. The error function does not depend on $\iota_p$, but $S$ does.
