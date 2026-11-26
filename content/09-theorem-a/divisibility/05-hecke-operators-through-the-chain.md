---
title: Hecke operators through the chain
lean:
  - New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean
decls:
  - New.Data.liftLoss
  - New.Data.mem_raises_neg_divisibilityBound
  - New.Data.markedIndices
  - New.Data.neighborExponent
  - New.Data.neighborCharge
  - New.Data.neighborDiagonal
  - New.Data.sum_card_boxes_le
  - New.Data.IsMarked.neighborCharge_ne_zero_or_partner
  - New.Data.IsMarked.exists_eq_mul_neighborDiagonal_mul
  - New.Data.IsMarked.map_ofSplitPlaces_neighborDiagonal
  - New.Data.IsMarked.sum_neighborExponent_mul_lastEntry_eq_zero
  - New.Data.IsMarked.sum_neighborExponent_add_neighborCharge_le
  - New.Data.IsMarked.ω_ofSplitPlaces_mem_raises
  - New.Data.IsMarked.notMem_asIdeal
  - New.Data.IsMarked.charUnramifiedAt_rankTwist
  - New.Data.IsWeakChainDatum.projOn_translateDatum_eq_self
  - New.Data.IsMarked.norm_baseChange_atUniformizer
  - New.Data.IsMarked.exists_q_eq_sq
  - New.Data.IsWeakChainDatum.exists_heckePolyOp_lift
  - New.Data.heckePolyOp_mul_apply
  - New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_smul
  - New.Data.pow_mul_pow_choose_two_dvd
  - New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_pow_smul
  - New.Data.IsWeakChainDatum.exists_sum_heckeSplit_chain_eq_pow_smul
  - New.Data.mul_le_transferExponent
  - New.Data.IsWeakChainDatum.liftKernel_omega_translateDatum_of_mem_maxCompactAt
  - New.Data.IsWeakChainDatum.exists_hecke_transfer
  - New.Data.liftTargetRep
  - New.Data.liftKernel_omega_heckeSplit
  - New.Data.liftKernel_lift_heckeSplit
  - New.Data.IsMarked.ω_heckeSplit_mem_raises
  - New.Data.IsWeakChainDatum.exists_lift_eq_chain_scaledHeckeOperator
  - New.Data.IsWeakChainDatum.gaugeLe_scaledHeckeOperator_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke operators through the chain

This section treats an exceptional prime $p$. It proves that on the image of $Y^m$, where $Y = \prod_{\mathfrak l\in\Lambda} p^{A_{\mathfrak l}}T_{\mathfrak l, r_p}$ for a marked set $\Lambda$, the restricted chain of a weak chain datum loses at most $\#\Lambda\,\nu_p + \mathrm{liftLoss}(\Lambda, j)$ at lift $j$. The Hecke operators pass through the lifts onto their data, and the moved data are bounded by the divisibility with charges.

Throughout, $\Lambda$ is a marked set of primes above $p$ ([marked sets](/chapter/chain-valuation/)), $r = r_p$ and $\nu_p = r f(n_m + r)$. So $p < x_1$ is exceptional, $\chi_K(p) = -1$, and each $\mathfrak l \in \Lambda$ is split with uniformiser $p$. The sets $\Phi_\Lambda$, $\bar\Phi_\Lambda$ and the low column counts $L_j(\tau)$ are those of [the scaled Hecke operator](/chapter/chain-valuation/). The divisibility bound $D_{p,j}(S)$ of [short columns and the gain](/chapter/short-columns-gain/) (`New.Data.divisibilityBound`) is the predicted divisibility of the diagrams without the columns of height one at $S$, plus $\gamma_p$ per removed box, less $f n_{j+1}^3(1 + \log_p\max(B,1))$, with $B$ the number of boxes. The datum $v_{x,j}$ is the vacuum translated by $x_j$, and $k_j$ is the lift kernel. We write $\phi \in \mathrm{raises}(c)$ if the kernel of $\phi$ multiplies gauges from the point $1$ to the point $1$ by at most $c$ ([Definition](/decl/New.Kernel.raises/)).

### One lift at a non-split prime

**Definition.** $\mathrm{liftLoss}(\Lambda, j) = r\sum_{\sigma\in\Phi_\Lambda} L_j(\sigma) - D_{p,j}(\Phi_\Lambda)$.

Lean: `New.Data.liftLoss` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

**Lemma.** Let $\chi_K(p) \ne 1$ and let $\phi$ be a standard datum of level one for $k_j$. Then $\phi \in \mathrm{raises}(p^{-D_{p,j}(\emptyset)})$.

Lean: `New.Data.mem_raises_neg_divisibilityBound` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* With $S = \emptyset$ nothing is removed. The kernel $k_j$ has scale $\overline{\bar\pi_M}$ times the jet scale, and $|\iota_p\overline{\bar\pi_M}| \le 1$ ([Lemma](/decl/New.Data.norm_star_piMBar_le_one/)). Apply [the bound for one lift at a non-split prime](/decl/New.Parameters.mem_raises_predictedDivisibility/). $\square$

### The neighbour and its count

Fix sets $J(\mathfrak l)$ of row indices of $X_{j+1}$, $\mathfrak l \in \Lambda$.

**Definition.** The *marked indices* at $\tau$ are $M_\tau = J(w_\tau)$ if $w_\tau \in \Lambda$, and $M_\tau = J(\bar w_\tau)$ if not. The *exponent* of an index $b$ at $\tau$ is $\varepsilon_\tau(b) = 1$ if $\tau \in \Phi_\Lambda$ and $b \in M_\tau$, $\varepsilon_\tau(b) = -1$ if $\tau \in \bar\Phi_\Lambda$ and $b \in M_\tau$, and $0$ otherwise. The *charge* $c_\tau(h, b)$ of $b$ in a column of height $h$ is $1$ if $\tau\in\Phi_\Lambda$, $h = 1$ and $b \notin M_\tau$, or if $\tau \in \bar\Phi_\Lambda$ and $b \in M_\tau$; otherwise it is $0$. The *neighbour diagonal* is $\Delta_J(\mathfrak l) = \mathrm{diag}(p \text{ on } J(\mathfrak l), 1 \text{ elsewhere})$.

Lean: `New.Data.markedIndices`, `New.Data.neighborExponent`, `New.Data.neighborCharge`, `New.Data.neighborDiagonal` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

**Lemma (Boxes in a set).** Let $T$ be a filling of the diagrams of $X_{j+1}$ and $I$ a set of at most $r$ indices. At a place $\tau$, the number of boxes with index in $I$, plus the number of boxes in columns of height one with index not in $I$, is at most $[\tau\in\Phi_a]\,a + r L_j(\tau)$.

Lean: `New.Data.sum_card_boxes_le` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* A column of height one has one box, counted exactly once. A column of height $h \ne 1$ has distinct indices, as a filling is injective on columns, so at most $r$ of its boxes have index in $I$. At $\tau$ there are $a$ columns of height one at an a-place and none elsewhere, and $L_j(\tau)$ other columns. $\square$

**Lemma (The charges are a charge system).** Let $e$ be a partner exponent of $p$ and $\tau' = [-p^e]\tau$. If $\tau \in \Phi_\Lambda$, or $h = 1$ and $\tau' \in \Phi_\Lambda$, then $c_\tau(1, b) \ne 0$ or $c_{\tau'}(h, b) \ne 0$.

Lean: `New.Data.IsMarked.neighborCharge_ne_zero_or_partner` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* As $p$ is inert in $K$, the partner exponents are odd, so $w_{\tau'} = \bar w_\tau$ ([induced primes](/chapter/chain-valuation/)). As $\Lambda \cap \bar\Lambda = \emptyset$, $M_{\tau'} = M_\tau$ when $\tau \in \Phi_\Lambda \cup \bar\Phi_\Lambda$. If $\tau \in \Phi_\Lambda$, then $\tau' \in \bar\Phi_\Lambda$, and $c_\tau(1,b) = 1$ for unmarked $b$, $c_{\tau'}(h, b) = 1$ for marked $b$. If $h = 1$ and $\tau' \in \Phi_\Lambda$, exchange the roles of $\tau$ and $\tau'$. $\square$

So $c$ is a charge system for [the divisibility with charges](/decl/New.Parameters.norm_schurJet_jetSeries_le_of_charges/), with erased places $\Phi_\Lambda$.

**Lemma (Cartan form).** Let $g_{\mathfrak l} \in \mathrm{GL}_n(\mathcal O_{\mathfrak l})\,\mathrm{diag}(\varpi 1_i, 1)\,\mathrm{GL}_n(\mathcal O_{\mathfrak l})$ with some $i \le r$, for each $\mathfrak l \in \Lambda$. Then there are sets $J(\mathfrak l)$ with $\#J(\mathfrak l) \le r$ and integral invertible $a_{\mathfrak l}$, $b_{\mathfrak l}$ with $g = a\,\Delta_J\,b$.

Lean: `New.Data.IsMarked.exists_eq_mul_neighborDiagonal_mul` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* The double coset is not empty, so $i \le n$; take any $J(\mathfrak l)$ with $i$ elements. As $p$ is a uniformiser at $\mathfrak l$, $\Delta_J(\mathfrak l)$ lies in the double coset ([the basic double cosets](/chapter/iwahori-satake/)). $\square$

**Lemma.** Let $\epsilon(\Delta_J)$ be the unitary point with component $\Delta_J(\mathfrak l)$ at $\mathfrak l \in \Lambda$, its conjugate inverse at $\bar{\mathfrak l}$, and $1$ elsewhere. Read at $\tau$ through $z \mapsto \iota_p(\tau\bar z)$, it is the diagonal matrix with entries $p^{-\varepsilon_\tau(b)}$.

Lean: `New.Data.IsMarked.map_ofSplitPlaces_neighborDiagonal` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* The embedding $z \mapsto \iota_p(\tau\bar z)$ factors through the completion at $\bar w_\tau$. If $\bar w_\tau = \mathfrak l' \in \Lambda$ the component there is $\Delta_J(\mathfrak l')$, with $p = p^{-(-1)}$ on $M_\tau$. If $w_\tau \in \Lambda$ the component at $\bar w_\tau$ is the inverse, with $p^{-1}$ on $M_\tau$. Otherwise it is $1$. $\square$

**Lemma (Balance).** $\sum_{\tau}\big(\sum_b \varepsilon_\tau(b)\big)\,e_{j+1}(\tau) = 0$, where $e_{j+1}(\tau)$ is the exponent of the determinant in the weight on $X_{j+1}$.

Lean: `New.Data.IsMarked.sum_neighborExponent_mul_lastEntry_eq_zero` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* $\sum_b\varepsilon_\tau(b)$ is $\#J(w_\tau)$ on $\Phi_\Lambda$, $-\#J(\bar w_\tau)$ on $\bar\Phi_\Lambda$ and $0$ elsewhere, and $e_{j+1}(\tau) = n_j/2 - \kappa_{j+1}(\tau)$. Apply the [balance corollary](/decl/New.Data.IsMarked.sum_inducedPlace_sub_star_eq_zero/) with $G(c, \mathfrak l) = \#J(\mathfrak l)(n_j/2 - c)$. $\square$

**Lemma (Cost).** Let $\#J(\mathfrak l) \le r$ for $\mathfrak l \in \Lambda$, and let $T$ be a filling. Then the sum of $\varepsilon_\tau(b) + c_\tau(h, b)$ over all boxes of $T$ is at most $\sum_{\mathfrak l\in\Lambda} A_{\mathfrak l} + r\sum_{\tau\in\Phi_\Lambda}L_j(\tau)$.

Lean: `New.Data.IsMarked.sum_neighborExponent_add_neighborCharge_le` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* At $\tau \in \Phi_\Lambda$ the cost of a box is $[b \in J(w_\tau)] + [h = 1,\ b \notin J(w_\tau)]$, and the lemma on boxes gives at most $[\tau\in\Phi_a]a + rL_j(\tau)$. At $\tau \in \bar\Phi_\Lambda$ a marked box costs $-1 + 1 = 0$ and an unmarked box $0$. At other places every cost is $0$. Finally $\sum_{\tau\in\Phi_\Lambda}[\tau\in\Phi_a]a = a\,\#(\Phi_a\cap\Phi_\Lambda) = \sum_{\mathfrak l\in\Lambda}A_{\mathfrak l}$ ([Lemma](/decl/New.Data.sum_heckeScalingExponent/)). $\square$

**Theorem (One lift at a neighbour).** Let $\phi$ be a standard datum of level one for $k_j$. Let $g = (g_{\mathfrak l})_{\mathfrak l\in\Lambda}$ with each $g_{\mathfrak l}$ in the double coset of $\mathrm{diag}(\varpi 1_i, 1)$ for some $i \le r$, and let $\epsilon(g)$ be the unitary point it defines. Then
$$\omega(1, \epsilon(g))\,\phi \in \mathrm{raises}\Big(p^{\sum_{\mathfrak l\in\Lambda}A_{\mathfrak l} + \mathrm{liftLoss}(\Lambda, j)}\Big).$$

Lean: `New.Data.IsMarked.ω_ofSplitPlaces_mem_raises` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* Write $g = a\Delta_J b$ by the Cartan form. The points $\epsilon(a)$, $\epsilon(b)$ are integral above $p$. By [gauges from an entrywise bound](/decl/New.Parameters.omega_mem_raises_of_schurJet_le/) and the lemma on $\epsilon(\Delta_J)$, it suffices to prove, for each standard $f$ and fillings $i'$, $i$,
$$\mathrm{dw}(p^{-\varepsilon}, i')\,\big|\iota_p\,\mathrm{schurJet}(f)_{i', i}\big| \le p^{\sum A_{\mathfrak l} + \mathrm{liftLoss}(\Lambda, j)}.$$
By the divisibility with charges, with erased places $\Phi_\Lambda$ and the charges $c$, the jet factor is at most $p^{\sum_{\text{boxes}} c - D_{p,j}(\Phi_\Lambda)}$. Since $|p^{-\varepsilon}|_p = p^{\varepsilon}$, the diagonal weight is $p^{\sum_\tau e_{j+1}(\tau)\sum_b\varepsilon_\tau(b)}\cdot p^{\sum_{\text{boxes}}\varepsilon}$, and the first factor is $1$ by the balance. So the product is at most $p^{\sum_{\text{boxes}}(\varepsilon + c) - D_{p,j}(\Phi_\Lambda)}$. Apply the cost lemma. $\square$

### The vacuum at a marked prime

From now on $\Psi$ is a weak chain datum for the twist $\vartheta$, and $p$ is prime to the norm $\mathrm NQ$ of the places of $\vartheta$.

**Lemma.** For $\mathfrak l \in \Lambda$, none of $\mathrm NQ$, $\pi_M$, $\bar\pi_M$ and $N$ lies in $\mathfrak l$.

Lean: `New.Data.IsMarked.notMem_asIdeal` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* $\mathfrak l \cap \mathbb Z = p\mathbb Z$. So $\mathrm NQ \in \mathfrak l$ gives $p \mid \mathrm NQ$. If $\pi_M$ or $\bar\pi_M$ lies in $\mathfrak l$, so does $M = \pi_M\bar\pi_M$, and $p \mid M$. If $N \in \mathfrak l$, then $p = N$. A small non-split prime divides neither $M$ nor $N$ ([Lemma](/decl/New.Data.IsSmallNonsplit.not_dvd_M_mul_N/)). $\square$

**Lemma.** For $\mathfrak l \in \Lambda$ and all $j$, $k$: the base change of the character of lift $j$, twisted for the rank of $X_k$, is unramified at $\mathfrak l$. The data $v_{x,j}$, $x \in \mathrm{supp}\,\Psi$, are fixed by the projection to the vacuum at $\mathfrak l$.

Lean: `New.Data.IsMarked.charUnramifiedAt_rankTwist`, `New.Data.IsWeakChainDatum.projOn_translateDatum_eq_self` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* The tame part of the character is trivial at a place that is not in $Q$ and is not chosen. A translation of a weak chain datum is admissible, so the datum $v_{x,j}$ is the vacuum at such a place if the place also avoids the level ([Lemma](/decl/New.Data.projOn_translateDatum/)). By the last lemma, $\mathfrak l$ and $\bar{\mathfrak l}$ satisfy these conditions. $\square$

**Lemma.** For $\mathfrak l \in \Lambda$, the value of the base change of the character $\chi^{(e)}$ of lift $e$ at a uniformiser of $\mathfrak l$ has $|\iota_p\,\cdot\,| = 1$. The norm of $\mathfrak l$ is $(p^h)^2$ with $2h \le f$.

Lean: `New.Data.IsMarked.norm_baseChange_atUniformizer`, `New.Data.IsMarked.exists_q_eq_sq` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* The value is $\chi^{(e)}(\varpi/\bar\varpi)$. Since $p$ is a uniformiser at $\mathfrak l$, $|\iota_p\sigma(\varpi)|$ is $1/p$ if $\sigma$ induces $\mathfrak l$ and $1$ otherwise. As the character has a weight, the norm is $p$ to the power $\sum_{w_\tau = \mathfrak l}(-\kappa_e(\tau)) + \sum_{w_\tau = \bar{\mathfrak l}}\kappa_e(\tau)$, which is $0$ by the balance corollary. The norm is $p^o$ with $o$ the order of $[-p]$ ([Lemma](/decl/New.Data.IsExceptional.q_eq_pow_orderOf/)); $m \mid o$ and $m$ is even, so $o = 2h$, and $o \le f$ as $[-p]$ lies in a group of order $f$. $\square$

### The transfer through one lift

Let $\mathfrak l \in \Lambda$ with norm $q_{\mathfrak l} = z^2$, and let $t = n_{e+1} - n_e - 1$. For forms on $X_e$ the Hecke polynomial operator is $H_e(U) = \sum_i (-U)^i q_{\mathfrak l}^{\binom i2} T_{\mathfrak l,i}$ ([Iwahori and Satake](/chapter/iwahori-satake/)). Let $\Theta = \Theta_{x,e}$ be the lift by $v_{x,e}$.

**Lemma.** There is $R \in \mathcal O_\iota[X]$ with $R(0) = 1$, the same for all $x \in \mathrm{supp}\,\Psi$, such that for $\varphi$ spherical at $\mathfrak l$ the form $\Theta\varphi$ is spherical at $\mathfrak l$ and $H_{e+1}(U)\,\Theta\varphi = R(U)\,\Theta\big(H_e(z^{t+1}U)\varphi\big)$ for all $U \in \mathbb C$.

Lean: `New.Data.IsWeakChainDatum.exists_heckePolyOp_lift` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* Let $\chi$ be the value of the last lemma for lift $e + 1$; it lies in $\mathcal O_\iota$. Put $R = \prod_{k\le t}(1 - q_{\mathfrak l}^k z^{n_e}\chi X)$. The datum is the vacuum at $\mathfrak l$, both characters are unramified there, and the lift is equivariant. So the transfer through a pairing ([Iwahori and Satake](/chapter/iwahori-satake/), `New.SiegelWeil.hecke_transfer_of_pairing`) gives the identity with $\prod_{k\le t}(1 - q_{\mathfrak l}^k\alpha U)$ and the argument $q_{\mathfrak l}^{t+1}\alpha\beta^{-1}U$. The ranks are even, so $\alpha = z^{n_e}\chi$ and $\beta = z^{n_{e+1}}\chi$, and $q_{\mathfrak l}^{t+1}\alpha/\beta = z^{t+1}$. $\square$

**Proposition (One lift).** There are $c_{i i'} \in \mathcal O_\iota$, the same for all $x$, such that for $\varphi$ spherical at $\mathfrak l$ and $i \le n_e$
$$\sum_{i'\le i} c_{ii'}\,T_{\mathfrak l,i'}\,\Theta\varphi = z^{(t+1)i}q_{\mathfrak l}^{\binom i2}\,\Theta\,T_{\mathfrak l,i}\varphi.$$

Lean: `New.Data.heckePolyOp_mul_apply`, `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_smul` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* By definition $H_e(sU)\varphi = \sum_{i\le n_e} U^i(-s)^i q_{\mathfrak l}^{\binom i2}T_{\mathfrak l,i}\varphi$. Expand both sides of the lemma in this way. Both are polynomials in $U$, equal for all $U$. Since $R(0) = 1$, $R$ is invertible in $\mathcal O_\iota[[X]]$; let $R^{-1} = \sum_k b_k X^k$. Multiply by $R^{-1}$ and compare the coefficients of $U^i$:
$$\sum_{i'\le i} b_{i-i'}(-1)^{i'}q_{\mathfrak l}^{\binom{i'}2}T_{\mathfrak l,i'}\Theta\varphi = (-z^{t+1})^i q_{\mathfrak l}^{\binom i2}\,\Theta T_{\mathfrak l,i}\varphi.$$
Multiply by $(-1)^i$, and put $c_{ii'} = (-1)^{i+i'}b_{i-i'}q_{\mathfrak l}^{\binom{i'}2}$. $\square$

**Corollary.** There are $c_{ii'} \in \mathcal O_\iota$ with $\sum_{i'\le i}c_{ii'}T_{\mathfrak l,i'}\Theta\varphi = p^{frt}\,\Theta T_{\mathfrak l,i}\varphi$ for $i \le r$.

Lean: `New.Data.pow_mul_pow_choose_two_dvd`, `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_pow_smul` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* Write $\mathrm N\mathfrak l = (p^h)^2$ with $2h \le f$. Since $r \le t$ ([sizes](/chapter/data-and-sizes/)), $i \le r \le t \le n_e$. The factor of the proposition is $p^{hi(t+i)}$, and $hi(t+i) \le hr\cdot 2t \le frt$. Multiply its coefficients by $p^{frt - hi(t+i)}$. $\square$

### The transfer through the chain

Let $C_e = C_{x,e}$ be the chain of the first $e$ lifts with the data $v_{x,j}$.

**Proposition (Iteration).** There are $c_i \in \mathcal O_\iota$, the same for all $x$, such that for $\varphi$ spherical at $\mathfrak l$, $C_e\varphi$ is spherical at $\mathfrak l$ and $\sum_{i\le r}c_iT_{\mathfrak l,i}C_e\varphi = p^{efrt}\,C_eT_{\mathfrak l,r}\varphi$.

Lean: `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_chain_eq_pow_smul` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* Induction on $e$. For $e = 0$ take $c_i = [i = r]$. For the step apply $\Theta_{x,e}$ to the identity for $e$, multiply by $p^{frt}$, and use the corollary. $\square$

**Theorem (Hecke transfer).** Let $\mathfrak l \in \Lambda$ and $j \in \mathbb N$. Then $\omega(1, b)v_{x,j} = v_{x,j}$ for $x \in \mathrm{supp}\,\Psi$ and $b \in K_{\mathfrak l}$, the maximal compact group at $\mathfrak l$ of $X_{j+1}$. There are $c_i \in \mathbb C$, in $\mathcal O_\iota$ if $j < m$, such that for $\varphi$ spherical at $\mathfrak l$
$$\sum_{i\le r}c_i\,T_{\mathfrak l,i}\,C_{j+1}\varphi = p^{\nu_p}\,C_{j+1}T_{\mathfrak l,r}\varphi.$$

Lean: `New.Data.mul_le_transferExponent`, `New.Data.IsWeakChainDatum.liftKernel_omega_translateDatum_of_mem_maxCompactAt`, `New.Data.IsWeakChainDatum.exists_hecke_transfer` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* On the vacuum at $\mathfrak l$, $b$ acts by a character of $\det b$ that is unramified at $\mathfrak l$, so by $1$. For the identity, multiply the coefficients of the iteration with $e = j + 1$ by $p^{\nu_p - (j+1)frt}$. If $j < m$, then $(j+1)t \le mt \le n_m$, so $(j+1)frt \le \nu_p$ and the coefficients stay in $\mathcal O_\iota$. $\square$

### Moving the operators onto the data

Let $\rho_j(b) = \omega(1, b)$ on the data of $k_j$, with Hecke operators $T^{\mathrm{dat}}_{\mathfrak l,i}$.

**Lemma.** Let $\psi$ be a datum fixed by $\rho_j(K_{\mathfrak l})$. For $a$ in the group of $X_j$ and $b$ in the standard maximal compact group of $X_{j+1}$, $\omega(a,b)T^{\mathrm{dat}}_{\mathfrak l,i}\psi = T^{\mathrm{dat}}_{\mathfrak l,i}\omega(a,b)\psi$. For every datum $\psi$ and form $\varphi$, $k_j.\mathrm{lift}(T^{\mathrm{dat}}_{\mathfrak l,i}\psi)\varphi = T_{\mathfrak l,i}\,k_j.\mathrm{lift}(\psi)\varphi$.

Lean: `New.Data.liftTargetRep`, `New.Data.liftKernel_omega_heckeSplit`, `New.Data.liftKernel_lift_heckeSplit` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* The action of $a$ commutes with that of the second group. Write $b = b_{\mathfrak l}b'$ with $b_{\mathfrak l} \in K_{\mathfrak l}$ and $b'$ trivial at $\mathfrak l$, $\bar{\mathfrak l}$. Then $b'$ commutes with the coset points $\epsilon(u)$ at $\mathfrak l$, and $b_{\mathfrak l}$ fixes $\psi$ and $T^{\mathrm{dat}}_{\mathfrak l,i}\psi$. The second claim is the equivariance of the lift. $\square$

**Lemma.** Let $\mathfrak l \in \Lambda$ and $i \in \mathbb N$. If $\omega(1, \epsilon(g\cdot u_{\mathfrak l}))\psi \in \mathrm{raises}(c)$ for every $u$ in the double coset of $\mathrm{diag}(\varpi 1_i, 1)$ at $\mathfrak l$, then $\omega(1, \epsilon(g))\,T^{\mathrm{dat}}_{\mathfrak l, i}\psi \in \mathrm{raises}(c)$.

Lean: `New.Data.IsMarked.ω_heckeSplit_mem_raises` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* $T^{\mathrm{dat}}_{\mathfrak l,i}\psi = \sum_u\rho_j(\epsilon(u))\psi$ over coset representatives, and $\omega(1,\epsilon(g))\rho_j(\epsilon(u)) = \omega(1, \epsilon(g\cdot u_{\mathfrak l}))$. The set $\mathrm{raises}(c)$ is closed under sums. $\square$

**Theorem (Operators on the data).** Let $L$ be a list of distinct elements of $\Lambda$, $Y_{\mathfrak l} = p^{A_{\mathfrak l}}T_{\mathfrak l,r}$, and $j \in \mathbb N$. There is a complex linear operator $t$ on the data of $k_j$ such that for every $x \in \mathrm{supp}\,\Psi$:

1. $\omega(a, b)\,t(v_{x,j}) = t(\omega(a,b)v_{x,j})$ for all $a$ and all $b$ in the standard maximal compact group of $X_{j+1}$;
2. $k_j.\mathrm{lift}(t\,v_{x,j})(C_jy) = C_{j+1}\big(\prod_{\mathfrak l\in L}Y_{\mathfrak l}\,y\big)$ for every source form $y$;
3. if $j < m$, and $g$ has $g_{\mathfrak l} = 1$ for $\mathfrak l \in L$ and $g_{\mathfrak l}$ in a double coset of index $i \le r$ for $\mathfrak l \notin L$, then $\omega(1,\epsilon(g))\,t(v_{x,j}) \in \mathrm{raises}(p^{\beta_L})$ with $\beta_L = \sum_{\mathfrak l\in L}(\nu_p - A_{\mathfrak l}) + \sum_{\mathfrak l\in\Lambda}A_{\mathfrak l} + \mathrm{liftLoss}(\Lambda, j)$.

Lean: `New.Data.IsWeakChainDatum.exists_lift_eq_chain_scaledHeckeOperator` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* Induction on $L$. For $L$ empty take $t = 1$. Claims 1 and 2 are clear. For claim 3, $v_{x,j}$ is standard of level one ([Lemma](/decl/New.Data.IsWeakChainDatum.translateDatum_mem_standardData/), as $p \nmid MN$), and the theorem on one lift at a neighbour applies.

For $\mathfrak l :: L$ let $t$ be the operator for $L$, let $c_i$ be the coefficients of the Hecke transfer at $\mathfrak l$, and put $s = p^{A_{\mathfrak l}}/p^{\nu_p}$ and $t' = \big(\sum_{i\le r}c_is\,T^{\mathrm{dat}}_{\mathfrak l,i}\big)\circ t$. The datum $\psi = t(v_{x,j})$ is fixed by $\rho_j(K_{\mathfrak l})$, by claim 1 for $t$ and the Hecke transfer. Claim 1 for $t'$ follows from the commutation lemma. For claim 2, the lemma on lifts gives
$$k_j.\mathrm{lift}(t'v_{x,j})(C_jy) = \sum_{i\le r}c_i\,T_{\mathfrak l,i}\,C_{j+1}(z),\qquad z = s\prod_{\mathfrak l'\in L}Y_{\mathfrak l'}y.$$
The form $z$ is fixed by $K_0 \ge K_{\mathfrak l}$. The Hecke transfer turns the sum into $p^{\nu_p}C_{j+1}T_{\mathfrak l,r}z = C_{j+1}(Y_{\mathfrak l}\prod_{L}Y_{\mathfrak l'}y)$. For claim 3, let $g$ be as stated for $\mathfrak l :: L$. For $u$ in a double coset of index $i \le r$ at $\mathfrak l$, the tuple $g\cdot u_{\mathfrak l}$ is as in claim 3 for $L$, since $g_{\mathfrak l} = 1$. So the last lemma gives $\omega(1,\epsilon(g))T^{\mathrm{dat}}_{\mathfrak l,i}\psi \in \mathrm{raises}(p^{\beta_L})$. The scalar has $|\iota_p(c_is)| \le p^{\nu_p - A_{\mathfrak l}}$, as $c_i \in \mathcal O_\iota$ for $j < m$. A sum of such terms lies in $\mathrm{raises}(p^{\nu_p - A_{\mathfrak l} + \beta_L}) = \mathrm{raises}(p^{\beta_{\mathfrak l::L}})$. $\square$

**Theorem (The chain on the image of the scaled Hecke operators).** Let $Y = \prod_{\mathfrak l\in\Lambda}Y_{\mathfrak l}$. For every integral source form $v \in \mathcal A_\iota$,
$$\mathrm{GaugeLe}\Big(1,\ p^{\sum_{j<m}(\#\Lambda\,\nu_p + \mathrm{liftLoss}(\Lambda, j))},\ \mathrm{res}\,\mathrm{CC}(\vartheta, \Psi, v, m)(Y^m v)\Big).$$

Lean: `New.Data.IsWeakChainDatum.gaugeLe_scaledHeckeOperator_pow` (New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean).

*Proof.* For each $j$ take the operator $t_j$ of the last theorem with $L$ the list of all of $\Lambda$, and $g = 1$. Then $\beta_L = \#\Lambda\,\nu_p + \mathrm{liftLoss}(\Lambda, j)$. By claim 2 and induction on $j$, the chain with data $t_jv_{x,j}$ sends $v$ to $C_j(Y^jv)$. So the restricted chain of $Y^mv$ is $\mathrm{res}$ of the chain combination with these data. Claim 1 gives condition 1 of [the gauge of a weak chain](/decl/New.Data.IsWeakChainDatum.gaugeLe_chain/), since $K_j$ lies in the standard maximal compact group; claim 3 gives condition 2; and $\mathrm{GaugeLe}(1,1,v)$ is condition 3. The restriction to $Y_m$ keeps the bound, as $p \ne N$ ([Lemma](/decl/New.Data.GaugeLe.restrictToY/)). $\square$

**Remark (Formalization).** The operators $t_j$ are chosen by `choose`; they depend on the order of the list $\Lambda$, and the statement does not. The hypothesis that $p$ is prime to $\mathrm NQ$ stays a hypothesis of the main theorem of Section 7.
