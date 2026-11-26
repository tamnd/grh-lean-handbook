---
title: The frame and the losses
lean:
  - New/Derivatives/Sharpness/Cases.lean
decls:
  - New.isIntegralAbove_of_isIntegral_mul
  - New.CMLattice.thetaProd_smul
  - New.Parameters.resolutionForms
  - New.Data.resolutionVectors
  - New.Data.taylorScale
  - New.Data.isResolution_resolutionVectors
  - New.Data.resolutionForms_eq_smul
  - New.Data.not_dvd_q₁_mul_M
  - New.Data.isIntegralAbove_resolutionVectors
  - New.Data.norm_taylorScale
  - New.Data.norm_resolutionForms_le_one
  - New.Data.leastValLE_six_zero_of_inert
  - New.Data.exists_hasNormalForm_resolutionForms
  - New.Data.IsNearWeights
  - New.Data.le_two_mul_b
  - New.Data.div_le_lossFactorCount
  - New.Data.posPart_le_localPrimeSum
  - New.Data.padicValNat_factorial_sub_min_le
  - New.Data.sum_padicValNat_factorial_le_add
  - New.Data.gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The frame and the losses

Sections 3 and 4 work with any integral linear forms. This section fixes the forms of a tight frame. It proves that at a non-split prime these forms satisfy the hypotheses of Sections 3 and 4. It then proves the inequalities between factorials and the forced divisibility that the three cases of Section 6 need.

### The forms of a frame

Let $D$ be admissible data. A *tight frame* of length $M$ with multiplicities $c$ is a family $w_i \in E$ in the lattice $\mathfrak{a}_0$ with $\sum_ic_i\,\sigma(w_i)\overline{\tau(w_i)} = M\delta_{\sigma\tau}$ for all places $\sigma$, $\tau$ (`New.IsTightFrame`, in [tight frames](/chapter/integral-vacuum/#tight-frames)). The curve is `P.cmCurve`, with the theta series $\theta$. The complex number `P.periodFactor` normalizes the Taylor series of theta functions.

**Definition (Forms, vectors and scale).** For a family $w$ in $E$:

1. the forms are $\mu_i(\tau) = \iota_p(\mathrm{periodFactor}\cdot\overline{\tau(w_i)})$, for $\tau \in \Phi$;
2. the vectors are $u_i = w_i/\bar\pi_M$, where $\bar\pi_M = $ `D.piMBar` is an integer of $K$ of norm $M$;
3. the scale is $\mathfrak{s} = \iota_p(\mathrm{periodFactor}\cdot\pi_M)$, with $\pi_M = \overline{\bar\pi_M}$.

Lean: `New.Parameters.resolutionForms`, `New.Data.resolutionVectors`, `New.Data.taylorScale` (New/Derivatives/Sharpness/Cases.lean).

All theta products of this chapter from now on are $\Theta = \prod_i\theta(\mu_iz)^{c_i}$ along these forms.

**Lemma (A resolution).** If $w$ is a tight frame of length $M$ with multiplicities $c$, then $u$ is a resolution of the identity: $\sum_ic_i\,\sigma(u_i)\overline{\tau(u_i)} = \delta_{\sigma\tau}$. The forms are $\mu = \mathfrak{s}\,u^\dagger$, that is, $\mu_i(\tau) = \mathfrak{s}\,\iota_p(\overline{\tau(u_i)})$.

Lean: `New.Data.isResolution_resolutionVectors`, `New.Data.resolutionForms_eq_smul` (New/Derivatives/Sharpness/Cases.lean), with `New.Data.piMBar_mul_conj`.

*Proof.* As $\bar\pi_M\pi_M = M$, $\sigma(u_i)\overline{\tau(u_i)} = \sigma(w_i)\overline{\tau(w_i)}/M$. Sum with the weights $c_i$. For the forms, $\overline{\tau(w_i)} = \overline{\tau(u_i)}\cdot\pi_M$, since $\bar\pi_M \in K$ and $\tau$ is the identity on $K$. $\square$

**Lemma (Integrality at a non-split prime).** Let $p$ not split in $K$.

1. $p$ does not divide $q_1M$.
2. If $y \in E$ and $Ny$ is an algebraic integer for a natural number $N$ prime to $p$, then $y$ is integral at every place above $p$.
3. The vectors $u_i$ are integral at every place above $p$.
4. $|\mathfrak{s}| = 1$.

Lean: `New.Data.not_dvd_q₁_mul_M`, `New.isIntegralAbove_of_isIntegral_mul`, `New.Data.isIntegralAbove_resolutionVectors`, `New.Data.norm_taylorScale` (New/Derivatives/Sharpness/Cases.lean), with `New.Data.norm_taylorScale_eq_one_of_not_dvd`.

*Proof.* (1) A prime dividing $q_1$ splits in $K$ (`New.Parameters.chiK_eq_one_of_dvd`). The two primes of $M$ are $\equiv 1$ modulo $q_1d$ (`New.Data.levelPrime_modEq_one`), so they split too (`New.Parameters.chiK_eq_one_of_modEq_one`). (2) At a place $v$ above $p$, $|N|_v = 1$ and $|Ny|_v \leq 1$. (3) We have $q_1Mu_i = (q_1w_i)\pi_M$. Here $q_1w_i$ is an algebraic integer because $q_1\mathfrak{a}_0 \subseteq \mathcal{O}_E$, and $\pi_M$ is an integer. Apply (2) with $N = q_1M$. (4) The two integers $\pi_M$, $\bar\pi_M$ have the product $M$, a $p$-adic unit, so both are units. The factor $\iota_p(\mathrm{periodFactor})$ is a unit when $p \nmid q_1$ (`New.Parameters.norm_iota_periodFactor_eq_one`). $\square$

**Lemma (Integral forms).** For a tight frame and every prime $p$, $|\mu_i(\tau)| \leq 1$.

Lean: `New.Data.norm_resolutionForms_le_one` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* This is [the integrality of the period factor](/decl/New.Parameters.norm_periodFactor_mul_conj_le_one/) for $w_i \in \mathfrak{a}_0$. $\square$

**Theorem (Valuation zero at an inert prime).** Let $p$ be inert and $w$ a tight frame of length $M$. Then $\mathrm{val}_6(\nu) \leq 0$ for every $\nu$.

Lean: `New.Data.leastValLE_six_zero_of_inert` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* Put $a_{\tau,i} = c_i\,\iota_p(\tau(u_i))$. It is integral by the last lemma but one. By the resolution,
$$\sum_ia_{\tau,i}\,\mu_i(\tau') = \mathfrak{s}\,\iota_p\Bigl(\sum_ic_i\,\tau(u_i)\overline{\tau'(u_i)}\Bigr) = \mathfrak{s}\,\delta_{\tau\tau'}.$$
As $|\mathfrak{s}| = 1$, [valuation zero on six copies](/decl/New.CMLattice.leastValLE_zero_of_span/) applies. $\square$

**Theorem (Normal form along the frame).** Let $p$ be inert and $w$ a tight frame of length $M$. There are $\varpi$ and integral $\lambda_{e,j}$ with $|\varpi| = p^{-\rho_p}$, $\lambda_{e,0}$ a unit for odd $e$, such that $\Theta$ has the normal form with $\varpi$, $\lambda$ and the partner rule $\tau \mapsto -p^e\tau$.

Lean: `New.Data.exists_hasNormalForm_resolutionForms` (New/Derivatives/Sharpness/Cases.lean), with `New.CMLattice.thetaProd_smul`.

*Proof.* [The normal form of theta products](/chapter/cm-formal-group/#resolutions-partners-and-theta-products) (`New.Parameters.exists_hasNormalForm`) applies to the resolution $u$, which is integral above $p$. It gives $\varpi$, $\lambda$ for the forms $u^\dagger$, with $\lambda_{e,0}$ a unit. Now $\mu = \mathfrak{s}u^\dagger$, so $\Theta$ along $\mu$ is $\Theta_u(\mathfrak{s}z)$. A coupling $z_\tau^{p^e}z_{\tau^+}$ has degree $p^e + 1$, so the scaling multiplies $\Gamma_e^{p^j}$ by $\mathfrak{s}^{(p^e+1)p^j}$ (`New.HasNormalForm.rescale`). Take $\lambda'_{e,j} = \mathfrak{s}^{(p^e+1)p^j}\lambda_{e,j}$. As $\mathfrak{s}$ is a unit, $\lambda'_{e,0}$ is a unit. $\square$

### Degrees near the weights

**Definition (Near the weights).** A degree $l$ on $\Phi$ is *near the weights* if $\kappa(\tau) \leq l_\tau \leq \kappa(\tau) + x^{42}$ for every $\tau$.

Lean: `New.Data.IsNearWeights` (New/Derivatives/Sharpness/Cases.lean).

The following facts are proved in [short columns gain](/chapter/short-columns-gain/), where Theorem A uses them as well. We state them here:

- $\kappa(\tau) + x^{42} \leq 2b$ (`New.Data.weight_add_x_pow_le_two_mul_b`), and $x^{42} \leq n^\sharp = \lceil 6b/k\rceil$ (`New.Data.lossFactorCount`, `New.Data.x_pow_le_lossFactorCount`);
- the *loss product* is $B(l) = (l^- + 1)(l^- + 2)\cdots(l^- + n^\sharp)$ with $l^- = (l - n^\sharp)_+$ (`New.Data.lossProduct`); then $v(n^\sharp!) \leq v(B(l))$ and $v(l!) \leq v(l^-!) + v(B(l))$;
- for $p \geq 3$ and $n_1 + n_2 + n_3 \leq 2b$, $v((n_1 + n_2 + n_3)!) \leq v(n_1!) + v(n_2!) + v(n_3!) + 3(\log b + 2)$ (`New.Data.padicValNat_factorial_add_add_le`);
- with $R_\tau = \sum_{e \in I_p}\min(\kappa(\tau)/p^e, \kappa(-p^e\tau))$ (`New.Data.partnerMinSum`), $\gamma_p\sum_\tau\kappa(\tau) - S_p = v(\pi_p)\sum_\tau R_\tau$ (`New.Data.mul_sum_weight_sub_localPrimeSumTotal`);
- if a near pair at $\tau$ can only have the exponent $e_0$, and then $\kappa(\tau)/p^{e_0} \leq c + 1$ with $c \geq 0$, then $R_\tau \leq c + 1 + l_0a/x_1 + 2b/(kp)$ (`New.Data.partnerMinSum_le`);
- for $p \leq k$, $3(\log b + 2) + x^{42} + 1 + l_0a/x_1 + 2b/(kp) \leq v(B(l))$ (`New.Data.error_le_padicValNat_lossProduct`).

Near pairs are defined in Section 6. Legendre's formula in one step, $v(n!) = \lfloor n/p\rfloor + v(\lfloor n/p\rfloor!)$, is `New.padicValNat_factorial_eq_div_add`.

**Remark (Formalization).** The sum $R_\tau$ is a `tsum` over all $e \in \mathbb{N}$, with the term $0$ for $e \notin I_p$. A `tsum` of a series that is not summable is $0$ by convention. Here the terms are at most $\kappa(\tau)/p^e$, so the series is summable and the junk value does not occur.

**Lemma (Degrees are at most $2b$).** If $l$ is near the weights, then $l_\tau \leq 2b$ for every $\tau$.

Lean: `New.Data.le_two_mul_b` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* $l_\tau \leq \kappa(\tau) + x^{42} \leq 2b$. $\square$

### The inert primes above $k$

**Lemma (A quotient below $n^\sharp$).** Let $p > k$ and $l$ near the weights. Then $\lfloor(l_\tau - n^\sharp)_+/p\rfloor \leq n^\sharp$.

Lean: `New.Data.div_le_lossFactorCount` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* $\lfloor(l_\tau - n^\sharp)_+/p\rfloor \leq l_\tau/p \leq 2b/k \leq 6b/k \leq n^\sharp$. $\square$

**Lemma (The first term).** At an inert prime, $(\kappa(\tau)/p - \kappa(-p\tau))_+ \leq s_p(\kappa(\tau), \tau)$.

Lean: `New.Data.posPart_le_localPrimeSum` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* At an inert prime $v(\pi_p) = 1$, $1 \in I_p$ and all terms of $s_p$ are nonnegative. The term for $e = 1$ is the left side. $\square$

**Lemma (The loss at one place).** Let $p > k$ be inert and $l$ near the weights. Put $i_\tau = \lfloor(l_\tau - n^\sharp)_+/p\rfloor$ and $j_\tau = \min(i_\tau, l_{-p\tau})$. Then
$$v(l_\tau!) - j_\tau \leq s_p(\kappa(\tau), \tau) + 2v(B(l_\tau)).$$

Lean: `New.Data.padicValNat_factorial_sub_min_le` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* Write $B = B(l_\tau)$ and $i = i_\tau$. By the last lemma but one, $i \leq n^\sharp$, so $v(i!) \leq v(n^\sharp!) \leq v(B)$. With Legendre's formula in one step,
$$v(l_\tau!) \leq v(l_\tau^-!) + v(B) = i + v(i!) + v(B) \leq i + 2v(B).$$
Next, $l_\tau^- \leq \kappa(\tau)$, because $l_\tau \leq \kappa(\tau) + x^{42} \leq \kappa(\tau) + n^\sharp$. So $i \leq \kappa(\tau)/p$. Also $l_{-p\tau} \geq \kappa(-p\tau)$. Hence
$$i - j_\tau = (i - l_{-p\tau})_+ \leq \Bigl(\frac{\kappa(\tau)}{p} - \kappa(-p\tau)\Bigr)_+ \leq s_p(\kappa(\tau), \tau).$$
Add the two inequalities. $\square$

### The primes up to $k$

**Lemma (Legendre with three parts).** Let $p \geq 3$, $l$ near the weights and $l = \nu' + \nu'' + \eta$. Then
$$v(l!) \leq v(\nu'!) + v(\nu''!) + v(\eta!) + 3f(\log b + 2).$$

Lean: `New.Data.sum_padicValNat_factorial_le_add` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* At each place $l_\tau \leq 2b$. Apply the three-part bound above at each of the $f$ places and add. $\square$

**Lemma (The comparison).** Let $p \leq k$ be prime and $l$ near the weights. Let $e, j : \Phi \to \mathbb{N}$ be such that every near pair $(\tau, e')$ has $e' = e(\tau)$ and $j(\tau) = \lfloor l_\tau/p^{e'}\rfloor$. Then
$$\gamma_p|l| - \sum_\tau j(\tau) + 3f(\log b + 2) \leq S_p + \sum_\tau v(B(l_\tau)).$$

Lean: `New.Data.gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add` (New/Derivatives/Sharpness/Cases.lean), with `New.gammaPrime_le_one`.

*Proof.* As $\gamma_p \leq 1$ and $\kappa(\tau) \leq l_\tau \leq \kappa(\tau) + x^{42}$,
$$\gamma_p|l| \leq \gamma_p\sum_\tau\kappa(\tau) + fx^{42}.$$
As $v(\pi_p) \leq 1$ and $R_\tau \geq 0$, the identity for $R_\tau$ gives $\gamma_p\sum_\tau\kappa(\tau) - S_p \leq \sum_\tau R_\tau$. Fix $\tau$ and apply the bound for $R_\tau$ with $c = j(\tau)$ and $e_0 = e(\tau)$. For a near pair $(\tau, e')$, $e' = e(\tau)$ and
$$\frac{\kappa(\tau)}{p^{e'}} \leq \frac{l_\tau}{p^{e'}} < \Bigl\lfloor\frac{l_\tau}{p^{e'}}\Bigr\rfloor + 1 = j(\tau) + 1.$$
So $R_\tau \leq j(\tau) + 1 + l_0a/x_1 + 2b/(kp)$. With the error bound for $p \leq k$,
$$3(\log b + 2) + x^{42} + R_\tau - j(\tau) \leq v(B(l_\tau)).$$
Sum over $\tau$ and combine the three inequalities. $\square$

The loss products $B(l_\tau)$ enter only through $v(B(l_\tau))$. The number $t$ of the main theorem contains $\prod_\tau B(l_\tau)^2$, so these valuations are absorbed into $v(t)$ in Section 7.
