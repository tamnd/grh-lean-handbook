---
title: The count
lean:
  - New/Derivatives/Divisibility/Count.lean
decls:
  - New.dvd_subst_coupling
  - New.dvd_subst_coupling_directionSubst
  - New.IsChargeExponent
  - New.dvd_subst_coupling_directionSubst_of_charges
  - New.predictedDivisibility
  - New.eraseHeightOne
  - New.deductionAt
  - New.deductionTerm_empty
  - New.deductionTerm_eraseHeightOne
  - New.summable_deductionAt
  - New.mul_tsum_deductionAt
  - New.mul_sum_deductionTerm_le
  - New.Parameters.norm_jet_minorProd_le_of_isChargeExponent
  - New.Parameters.norm_jet_minorProd_le_of_charges
  - New.Parameters.norm_jet_minorProd_le_of_hasNormalForm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The count

This section proves the count for a series with the normal form. It joins the three parts of the argument: the new directions of Section 3 make the couplings divisible by $\pi_p$, the normal form then makes the series integral in degree $B$, and Legendre's bound of Section 2 gives the divisibility. The chain rule pays for the change of variables, and the price is the deduction.

### Couplings after the substitution

The coupling of the exponent $e$ is the series $\Gamma_e = \sum_{x} X_x^{p^e} X_{(\mathrm{pr}_e x_1, x_2)}$, where $x = (\tau, c)$ runs over the variables and $\mathrm{pr}_e\tau$ is the partner of $\tau$ ([the CM curve, its formal group and the normal form](/chapter/cm-formal-group/)).

**Lemma (Couplings of linear forms).** Let $\pi \mid p$ and substitute integral linear forms $X_x = \sum_o z_{x,o}\, s_o$ into $\Gamma_e$. If $\pi$ divides $\sum_x z_{x,o}^{p^e} z_{(\mathrm{pr}_e x_1, x_2), q}$ for all $o$ and $q$, then $\pi$ divides $\Gamma_e(z(s))$.

Lean: `New.dvd_subst_coupling` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Modulo $p$, and so modulo $\pi$, the power $(\sum_o z_{x,o} s_o)^{p^e}$ is $\sum_o z_{x,o}^{p^e} s_o^{p^e}$ (`New.dvd_sum_pow_sub_sum`). So $\Gamma_e(z(s))$ is congruent to $\sum_{o,q} \big(\sum_x z_{x,o}^{p^e} z_{(\mathrm{pr}_e x_1,x_2),q}\big)\, s_o^{p^e} s_q$, and each coefficient is divisible by $\pi$. $\square$

For the substitution $z_{\tau,b,a} = \sum_{h,k} c_{\tau,h,b}\, \beta_{\tau,h,k,a}\, s_{\tau,h,k,b}$ of Section 2, with row factors $c$ and directions $\beta$, the coefficient of $s_o^{p^e}s_q$ is zero unless $q$ sits at the partner of the place of $o$ and in the same row $b$. Otherwise it is $c_{\tau,h,b}^{p^e}\, c_{\tau',h',b}\, \langle \beta_{\tau,h,k}, \beta_{\tau',h',k'} \rangle_e$.

Lean: `New.dvd_subst_coupling_directionSubst` (New/Derivatives/Divisibility/Count.lean).

### Charges

The row factors are powers of $p$, the *charges*. In the plain count they are all $1$. The charges pay for the exempt pairs of Section 3, which the new directions do not cover.

**Definition (Charge exponents).** Exponents $w_{\tau,h,b} \ge 0$ (place, height, row) are *charge exponents* for a set of marked places and a map $\tau \mapsto \tau'$ if, for every place $\tau$, height $h$ and row $b$ such that $\tau$ is marked, or $h = 1$ and $\tau'$ is marked, one of $w_{\tau,1,b}$ and $w_{\tau',h,b}$ is not zero.

Lean: `New.IsChargeExponent` (New/Derivatives/Divisibility/Count.lean).

**Lemma (Couplings with charges).** Let $\pi \mid p$, let $w$ be charge exponents for the partners $\mathrm{pr}_e$, and suppose that $\pi$ divides $\langle \beta_{\tau,h,k}, \beta_{\mathrm{pr}_e\tau,h',k'} \rangle_e$ for every pair $(h,h')$ that is not exempt. Then $\pi$ divides $\Gamma_e(z(s))$ for the substitution with the row factors $p^{w}$.

Lean: `New.dvd_subst_coupling_directionSubst_of_charges` (New/Derivatives/Divisibility/Count.lean).

*Proof.* By the previous lemma it suffices that $\pi$ divides each coefficient. If the pair is not exempt, the pairing is divisible. If it is exempt, then $h = 1$ and the condition on $w$ applies to the row $b$ and the height $h'$; so $p$ divides $(p^{w_{\tau,1,b}})^{p^e} p^{w_{\tau',h',b}}$, and $\pi \mid p$. $\square$

The *filling charge* $m = \sum w_{\tau,h,i'(\text{box})}$ is the sum of the exponents over the boxes of the diagrams (Section 2). It is added to the valuation of the jet in the bounds below, since the substitution multiplies a row by $p^{w}$.

### The predicted divisibility

Fix $d$, $p$, the partners $\tau' = \mathrm{pr}_e\tau$ and $N$. Among the heights below $N$, let $a_\tau$ be the number of columns of height one at $\tau$, $a'_\tau$ the number of the other columns and $l_\tau$ the number of boxes in these. Write $x^+ = \max(x, 0)$.

**Definition (Predicted divisibility).** The predicted divisibility of $\kappa$ at $p$ is

$$D_p(\kappa) = v(\pi_p) \sum_{e \in I_p} \sum_\tau \Big( \Big(\frac{a_\tau}{p^e} - a_{\tau'} - a'_{\tau'}\Big)^+ + \Big(\frac{l_\tau}{p^e} - l_{\tau'}\Big)^+ - \frac{a'_\tau}{p^e} \Big) - [p = d]\, \frac12 \sum_\tau \big(\min(a_\tau, a_{\tau'} + a'_{\tau'}) + a'_\tau + \min(l_\tau, l_{\tau'})\big),$$

with $\tau' = \mathrm{pr}_e\tau$ in the first sum and $\tau' = \mathrm{pr}_0\tau$ in the second.

Lean: `New.predictedDivisibility` (New/Derivatives/Divisibility/Count.lean).

The first sum is over $I_p$, the *positive* exponents of $I_p^\circ$. If $p = d$, the exponent $e = 0$ lies in $I_p^\circ$ and its contribution is the second term. If $p$ is inert, $0 \notin I_p^\circ$ and the second term is absent.

The sum over $e$ is an infinite sum. The deduction terms of Section 3 for the empty set of marked places are the sums

$$\mathrm{ded}(e) = \begin{cases} \sum_\tau \mathrm{ded}_e(\tau, \mathrm{pr}_e\tau) & e \in I_p^\circ, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.deductionAt` (New/Derivatives/Divisibility/Count.lean).

Without marked places, $\mathrm{ded}_e(\tau,\tau') = \min(a_\tau/p^e, a_{\tau'} + a'_{\tau'}) + a'_\tau/p^e + \min(l_\tau/p^e, l_{\tau'})$ (`New.deductionTerm_empty`). Each term is at most $(a_\tau + a'_\tau + l_\tau)/p^e$, so the sum over $e$ converges (`New.summable_deductionAt`).

Lean: `New.deductionTerm_empty`, `New.summable_deductionAt` (New/Derivatives/Divisibility/Count.lean).

**Lemma (The deduction).** Let $B$ be the number of boxes of $\kappa$ in the columns of height below $N$. Then

$$v(\pi_p) \sum_{e \ge 0} \mathrm{ded}(e) = \gamma_p B - D_p(\kappa).$$

Lean: `New.mul_tsum_deductionAt` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The number of boxes is $B = \sum_\tau (a_\tau + l_\tau)$ (`New.boxes_eq_sum`). For real $u$ and $u'$, $(u - u')^+ = u - \min(u, u')$. So, for $e \in I_p$, the summand of $D_p$ at $e$ is $\sum_\tau (a_\tau + l_\tau)/p^e - \mathrm{ded}(e) = B/p^e - \mathrm{ded}(e)$. The sum of $B/p^e$ over $e \in I_p$ is $B\gamma_p/v(\pi_p)$ (`New.hasSum_div_pow_positivePartnerExponents`, in [CM elliptic curves](/chapter/cm-elliptic-curves/)). For instance, if $p$ is inert this is $B\sum_{e\text{ odd}} p^{-e} = Bp/(p^2-1) = B\gamma_p$. If $p = d$, the term $e = 0$ of $\mathrm{ded}$ is the sum in the second line of $D_p$, and $v(\pi_d) = 1/2$. Sum these identities as convergent series and multiply by $v(\pi_p)$. $\square$

**Remark (Formalization).** The predicted divisibility is defined with the Lean sum `tsum`, which takes the value $0$ for a family that is not summable. The family here is summable, and the proof of the lemma uses the statement `HasSum`, so the value $0$ never enters.

**Lemma (Marked places and a cut).** Let $\kappa^\circ$ be $\kappa$ without its columns of height one at the marked places, and $e_0 \ge 0$. Then

$$v(\pi_p) \sum_{\substack{e \le e_0 \\ e \in I_p^\circ}} \sum_\tau \mathrm{ded}_e^{\mathrm{marked}}(\tau, \mathrm{pr}_e\tau) \le \gamma_p B(\kappa^\circ) - D_p(\kappa^\circ).$$

Lean: `New.mul_sum_deductionTerm_le` (New/Derivatives/Divisibility/Count.lean); also `New.eraseHeightOne`, `New.deductionTerm_eraseHeightOne`.

*Proof.* A marked place gives $t_\sigma = 0$ in the deduction term, so marking the places has the same effect as removing their columns of height one (`New.deductionTerm_eraseHeightOne`). The finite sum of the nonnegative terms $\mathrm{ded}(e)$ for $\kappa^\circ$ is at most the full sum, which the previous lemma computes. $\square$

### The count with charges

**Theorem (Count with charge exponents).** Let $p$ be non-split, let $v(\varpi) = \rho_p$, and let $F$ have the normal form for the exponents of $I_p^\circ$, with the partners $-p^e\tau$ and the coefficients $l$. Fix marked places and charge exponents $w$ for every $e \in I_p^\circ$. Let $i'$ be a filling of $\kappa$, $y$ integral directions, $N = |n'|$ and $B$ the number of boxes in columns of height below $N$. Then

$$v\big(\mathrm{jet}(P_y)(F)\big) + m \ge \gamma_p B - v(\pi_p) \sum_{\substack{e \le \lfloor \log_p B \rfloor \\ e \in I_p^\circ}} \sum_\tau \mathrm{ded}^{\mathrm{marked}}_e(\tau, \tau') - fN^3\big(\lfloor\log_p B\rfloor + 1\big),$$

where $m$ is the filling charge.

Lean: `New.Parameters.norm_jet_minorProd_le_of_isChargeExponent` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Let $\pi = \pi_p$ and $S = \{e \in I_p^\circ : e \le \lfloor\log_p B\rfloor\}$, and let $D$ be the double sum of deduction terms.

*Step 1.* Section 3 gives integral matrices $g_{\tau,h}$ with $\pi \mid \langle\beta,\beta'\rangle_e$ for all pairs that are not exempt, for every $e \in S$, and with $\sum \kappa_\tau(h)\, v(\det g_{\tau,h}) \le v(\pi) D$. Let $z$ be the substitution with the new directions $\beta = \beta_{\tau,h,k}$ and the row factors $p^{w}$, and let $G(s) = F(\varpi z(s))$. The chain rule in norms of Section 2 gives

$$\|\mathrm{jet}(Q)(G)\| = c\, \|\mathrm{jet}(P_y)(F)\|, \qquad c = \|\varpi\|^B\, p^{-m} \prod_{\tau, h<N} \|\det g_{\tau,h}\|^{\kappa_\tau(h)},$$

with $Q$ the product of the column determinants.

*Step 2.* The series $G$ is integral in degree $B$. The normal form gives $F(\varpi z) = W \exp(c_\varpi\, \Xi(z))$ with $W$ integral, $c_\varpi = \varpi^{p+1}/p$, and $\Xi$ an integral combination of the powers $\Gamma_e^{p^j}$, $e \in I_p^\circ$. Here $v(c_\varpi \pi_p) = 1/(p-1)$ (`New.Parameters.norm_pow_succ_div_mul_piPrimeInt`). By the lemma with charges, $\pi_p$ divides $\Gamma_e(z)$ for $e \in S$. For $e \in I_p^\circ$ with $e > \lfloor \log_p B\rfloor$ the degree $p^e + 1$ of $\Gamma_e$ is greater than $B$, so this coupling does not contribute in degree at most $B$. So $\pi_p$ divides $\Xi(z)$ in degrees at most $B$, and the exponential is integral in these degrees, since $v(x^k/k!) \ge k/(p-1) - (k-1)/(p-1) > 0$ for $v(x) \ge 1/(p-1)$ and $k \ge 1$. The lemma `New.HasNormalForm.norm_coeff_subst_le_one` of [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/) states this.

*Step 3.* The polynomial $Q$ is homogeneous of degree $B$ with integral coefficients, in at most $fN^3$ variables (Section 2). Legendre's bound gives $v(\mathrm{jet}(Q)(G)) \ge B/(p-1) - fN^3(\lfloor \log_p B\rfloor + 1)$. Also $v(c) \le \rho_p B - m + v(\pi_p) D$. Divide: $v(\mathrm{jet}(P_y)(F)) = v(\mathrm{jet}(Q)(G)) - v(c)$, and $1/(p-1) - \rho_p = \gamma_p$. $\square$

**Theorem (Count with charges).** In the setting of the previous theorem, suppose the condition on $w$ only where it matters: for $e \in I_p^\circ$, places $\tau$ with $\kappa_\tau(1) \ne 0$, heights $h$ with $\kappa_{\tau'}(h) \ne 0$ and rows $b$, such that $\tau$ is marked or $h = 1$ and $\tau'$ is marked, one of $w_{\tau,1,b}$ and $w_{\tau',h,b}$ is not zero. Then

$$v\big(\mathrm{jet}(P_y)(F)\big) + m \ge D_p(\kappa^\circ) + \gamma_p\big(B - B(\kappa^\circ)\big) - fN^3\big(1 + \log_p \max(B, 1)\big).$$

Lean: `New.Parameters.norm_jet_minorProd_le_of_charges` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Put $w'_{\tau,h,b} = 1$ if $\kappa_\tau(h) = 0$ and $w'_{\tau,h,b} = w_{\tau,h,b}$ otherwise. Then $w'$ is a family of charge exponents, and its filling charge is that of $w$, since only heights that occur carry boxes (`New.fillingCharge_congr`). Apply the previous theorem to $w'$, and the lemma on marked places with $e_0 = \lfloor\log_p B\rfloor$. Finally $\lfloor \log_p B \rfloor \le \lfloor \log_p \max(B,1)\rfloor \le \log_p \max(B,1)$. $\square$

**Theorem (The count).** Let $p$ be non-split, $v(\varpi) = \rho_p$, and let $F$ have the normal form for $I_p^\circ$. For every filling $i'$ and integral directions $y$,

$$v\big(\mathrm{jet}(P_y)(F)\big) \ge D_p(\kappa) - fN^3\big(1 + \log_p \max(B,1)\big).$$

Lean: `New.Parameters.norm_jet_minorProd_le_of_hasNormalForm` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Take no marked places and $w = 0$. Then $\kappa^\circ = \kappa$, the condition on $w$ is empty and the filling charge is $0$. $\square$

**Remark (Formalization).** The theorem with charge exponents cuts the deduction at $\lfloor\log_p B\rfloor$ with the natural logarithm `Nat.log`, which is $0$ for $B = 0$. The two later theorems use the real logarithm $\log_p \max(B, 1)$ and the full deduction, which is larger. Both changes weaken the bound. The norm $\varpi$ and the coefficients $l$ of the normal form are hypotheses here; Section 8 obtains them from an existence statement.

**Remark (Formalization).** The factor $fN^3$ comes from `New.card_directionVar_le`. The exact number of new variables is $f N \sum_{h<N} h = fN^2(N-1)/2$, so the bound is loose by a factor of about $2$. The source records the size of this factor as an open question (F-096 in its findings): it must stay small against the main terms of the later chapters.

### Examples

**One column.** Let $p$ be inert, $N \ge 2$, and let $\kappa$ have one column of height one at $\tau$ and nothing else. Suppose that no partner $-p^e\tau$ with $e$ odd is equal to $\tau$. At $e$ odd, the summand at $\tau$ is $(1/p^e - 0 - 0)^+ = 1/p^e$. At the other places $\sigma$, $a_\sigma = l_\sigma = a'_\sigma = 0$, so the summand is $(0 - a_{\sigma'} - a'_{\sigma'})^+ + 0 - 0 = 0$. So $D_p = \sum_{e\text{ odd}} p^{-e} = \gamma_p$. If instead $-p^e\tau = \tau$ for every odd $e$, the summand at $\tau$ is $(1/p^e - 1)^+ = 0$, and $D_p = 0$: the single box gains nothing.

**A ramified case.** Let $p = d$ and take the same diagram, with no partner $-d^e\tau$, $e \ge 1$, equal to $\tau$. Then $v(\pi_d) = 1/2$, $I_d$ consists of all $e \ge 1$, and the first sum gives $\tfrac12 \sum_{e\ge1} d^{-e} = 1/(2d-2) = \gamma_d$. If the partner $-\tau$ at $e = 0$ carries no column, the second term is $\tfrac12 \min(1, 0) = 0$, so again $D_d = \gamma_d$.

**Remark.** The source states that divisibility results in one and two variables at an inert prime over an imaginary quadratic field are known, and names as related work: N. Katz, *Divisibilities, congruences, and Cartier duality* (1981); Chellali (1990), on congruences between Bernoulli Hurwitz numbers in the supersingular case; Fujiwara (1988), on divisibilities of special values of real analytic Eisenstein series; and Bannai, Kobayashi and Yasuda, *Radius of convergence of the p-adic sigma function* (2017). The count for products of minors in many variables is the form that the source proves; we do not know a textbook statement of it.
