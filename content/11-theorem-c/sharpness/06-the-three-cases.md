---
title: The three cases
lean:
  - New/Derivatives/Sharpness/Cases.lean
decls:
  - New.Data.isCouplingFamily_of_isNearPair
  - New.Data.powerDegree_add_partnerDegree_le_of_isNearPair
  - New.Data.partner_bijective
  - New.Data.powerDegree_add_partnerDegree_le_of_k_lt
  - New.Data.leastValLE_twelve_of_split
  - New.Data.leastValLE_twelve_of_lt
  - New.chiK_eq_neg_one_of_ne
  - New.Data.leastValLE_six_of_isNearPair
  - New.Data.leastValLE_twelve_localPrimeSumTotal_of_le
  - New.Data.leastValLE_twelve
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three cases

This section proves the bound on twelve copies at every prime. Let $D$ be admissible data, $w$ a tight frame of length $M$ with multiplicities $c$, and $\Theta$ the theta product along the forms $\mu_i$ of Section 5. Let $l$ be near the weights. We write $v(l!) = \sum_\tau v(l_\tau!)$ and $B_\tau = B(l_\tau)$. The goal is
$$\mathrm{val}_{12}(l) \leq S_p + 2\sum_\tau v(B_\tau) - v(l!).$$
There are three cases: $p$ splits in $K$; $p$ is inert and $p > k$; $p$ does not split and $p \leq k$.

### Near pairs

Let $\Phi_b \subseteq \Phi$ be the set of $b$-places, a field of the data, and these places have weight $b$ (`New.Data.bPlaces`, in [the places and the weights](/chapter/data-and-sizes/#the-places-and-the-weights)). Let $l_0$ be the least power of $3$ above $27$ times the tower exponent.

**Definition (Near pair, from Volume 9).** The pair $(\tau, e)$ is a *near pair* at $p$ if $e \in I_p$, $2e < l_0$, $\tau \in \Phi_b$ and the partner $-p^e\tau \in \Phi_b$. The place $\tau$ is the *start* and $-p^e\tau$ is the *end*.

Lean: `New.Data.IsNearPair` (New/Derivatives/Sharpness/NearPairs.lean).

This definition and the following facts are proved in [short columns gain](/chapter/short-columns-gain/). Let $(\tau, e)$ be a near pair. Then $p \neq d$, $p$ is inert and $e$ is odd (`New.Data.IsNearPair.inert`, `New.Data.IsNearPair.odd`). Let also $p \leq k$ be a prime that does not split. Then:

- two near pairs with the same start have the same exponent (`New.Data.IsNearPair.exponent_unique`);
- two near pairs with the same end are equal (`New.Data.IsNearPair.eq_and_eq_of_partner_eq`);
- the end of a near pair is not the start of a near pair (`New.Data.IsNearPair.end_ne_start`).

All three follow from one fact: for $0 < i < j < l_0$, the places $\sigma$, $(-p)^i\sigma$, $(-p)^j\sigma$ are not all $b$-places (`New.Data.notMem_bPlaces_of_two_partners`). That fact is the sparseness of [progression-free sets](/chapter/progression-free-sets/#from-progressions-to-places). The weight of a $b$-place is $b$, a natural number (`New.Data.weight_of_mem`, `New.Data.b_le_weight`).

### Couplings along near pairs

**Lemma (Near pairs are a coupling family).** Let $p \leq k$ be a prime that does not split. Let $\Phi_0 \subseteq \Phi$ and $e : \Phi \to \mathbb{N}$ be such that $(\tau, e(\tau))$ is a near pair for every $\tau \in \Phi_0$. Then $(\Phi_0, e)$ is a coupling family for the partner rule $\mathrm{pr}(e, \tau) = -p^e\tau$.

Lean: `New.Data.isCouplingFamily_of_isNearPair` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* The exponents $e(\tau)$ are odd. Let $\tau, \tau_1 \in \Phi_0$ and $e' \leq e(\tau)$ odd with $-p^{e'}\tau_1 = -p^{e(\tau)}\tau$. Then $(\tau_1, e')$ is a near pair: $e'$ is odd and $p$ is inert, so $e' \in I_p$; $2e' \leq 2e(\tau) < l_0$; $\tau_1 \in \Phi_b$ as the start of a near pair; and its end is the end of $(\tau, e(\tau))$, which is in $\Phi_b$. The two near pairs have the same end, so they are equal: $\tau_1 = \tau$ and $e' = e(\tau)$. $\square$

**Lemma (The couplings fit in $l$, for $p \leq k$).** Let $p \leq k$ be a prime that does not split and $l$ near the weights. Let $(\tau, e(\tau))$ be a near pair for $\tau \in \Phi_0$, and $j(\tau) = \lfloor l_\tau/p^{e(\tau)}\rfloor$ for $\tau \in \Phi_0$. Then $\nu' + \nu'' \leq l$.

Lean: `New.Data.powerDegree_add_partnerDegree_le_of_isNearPair` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* Fix a place $t$. The value of $\nu''$ at $t$ is $\sum j(\tau)$ over the $\tau \in \Phi_0$ with end $t$.

Let $t \in \Phi_0$. Then $t$ is a start, so no end equals $t$, and $\nu''_t = 0$. Also $\nu'_t = p^{e(t)}\lfloor l_t/p^{e(t)}\rfloor \leq l_t$.

Let $t \notin \Phi_0$. Then $\nu'_t = 0$. If no end equals $t$, then $\nu''_t = 0$. Otherwise let $t$ be the end of $(\tau, e(\tau))$. Two near pairs with the same end are equal, so $\nu''_t = j(\tau)$. As $p^{e(\tau)} \geq p \geq 2$ and $l_\tau \leq 2b$,
$$j(\tau) \leq \frac{2b}{2} = b \leq \kappa(t) \leq l_t,$$
because the end $t$ is a $b$-place. $\square$

**Lemma (Partners are a bijection).** For every $p$ and $e$, the map $\tau \mapsto -p^e\tau$ is a bijection of $\Phi$.

Lean: `New.Data.partner_bijective` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* It is the left multiplication by one element of the group of places. $\square$

**Lemma (The couplings fit in $l$, for $p > k$).** Let $p > k$ and $l$ near the weights. Take $\Phi_0 = \Phi$, $e = 1$ and
$$j(\tau) = \min\Bigl(\Bigl\lfloor\frac{(l_\tau - n^\sharp)_+}{p}\Bigr\rfloor,\; l_{-p\tau}\Bigr).$$
Then $\nu' + \nu'' \leq l$.

Lean: `New.Data.powerDegree_add_partnerDegree_le_of_k_lt` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* Every place is $t = -p\tau$ for one $\tau$, by the bijection. So $\nu''_t = j(\tau)$ and $\nu'_t = p\,j(t)$. Now $p\,j(t) \leq (l_t - n^\sharp)_+$. By [the quotient lemma](/decl/New.Data.div_le_lossFactorCount/), $j(\tau) \leq \min(n^\sharp, l_t)$. The sum $(l_t - n^\sharp)_+ + \min(n^\sharp, l_t)$ is $l_t$. $\square$

### The split case

**Theorem (Twelve copies at a split prime).** Let $p$ split in $K$. Let $w$ be any family and suppose that the form $\mu_{i_0}$ has $|\mu_{i_0}(\tau)| = 1$ for every $\tau$. Then $S_p = 0$ and $\mathrm{val}_{12}(l) \leq S_p - v(l!)$ for every $l$.

Lean: `New.Data.leastValLE_twelve_of_split` (New/Derivatives/Sharpness/Cases.lean), with `New.positivePartnerExponents_of_split` and `New.gammaPrime_of_split`.

*Proof.* For a split prime $I_p$ is empty, so every $s_p$ is $0$ and $S_p = 0$. Also $\gamma_p = 0$. [The rate on six copies](/decl/New.CMLattice.leastValLE_of_unit_coefficients/) gives $\mathrm{val}_6(l) \leq 0\cdot|l| - v(l!)$. The other six copies are taken in degree $0$, with $\mathrm{val}_6(0) \leq 0$. Add the two bounds. $\square$

### The inert primes above $k$

**Theorem (Twelve copies at an inert prime above $k$).** Let $p > k$ be inert, $w$ a tight frame of length $M$ and $l$ near the weights. Then
$$\mathrm{val}_{12}(l) \leq S_p + 2\sum_\tau v(B_\tau) - v(l!).$$

Lean: `New.Data.leastValLE_twelve_of_lt` (New/Derivatives/Sharpness/Cases.lean), with `New.Parameters.thirteen_le_of_chiK_ne_one`.

*Proof.* A prime that does not split is at least $13$, so $p > 2$. Take $\Phi_0 = \Phi$, $e = 1$ and $j$ as in the last lemma but one. This is a coupling family: $1$ is odd, and if $-p^{e'}\tau_1 = -p\tau$ with $e'$ odd and $e' \leq 1$, then $e' = 1$ and $\tau_1 = \tau$ by the bijection. By that lemma, $l = \nu' + \nu'' + \eta$ for an exponent $\eta$.

[The normal form along the frame](/decl/New.Data.exists_hasNormalForm_resolutionForms/) gives $\varpi$ and $\lambda$. The forms are integral. So [couplings on six copies](/decl/New.CMLattice.leastValLE_six_of_isCouplingFamily/) gives $\mathrm{val}_6(\nu' + \nu'') \leq -\sum_\tau j(\tau)$. [Valuation zero at an inert prime](/decl/New.Data.leastValLE_six_zero_of_inert/) gives $\mathrm{val}_6(\eta) \leq 0$. Add the two bounds:
$$\mathrm{val}_{12}(l) \leq -\sum_\tau j(\tau).$$
Sum [the loss at one place](/decl/New.Data.padicValNat_factorial_sub_min_le/) over $\tau$:
$$v(l!) - \sum_\tau j(\tau) \leq S_p + 2\sum_\tau v(B_\tau).$$
Combine the two inequalities. $\square$

The tight frame enters this case twice: in the normal form and in valuation zero. The hypothesis on $\mu_{i_0}$ is not used.

### The primes up to $k$

**Lemma (Inert or ramified).** Let $d$ and $p$ be primes with $p \neq d$. If $p$ does not split in $K$, then $p$ is inert, that is, $\chi_K(p) = -1$.

Lean: `New.chiK_eq_neg_one_of_ne` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* The value $\chi_K(p)$ is $0$, $1$ or $-1$, and it is $0$ only for $p = d$ (`New.chiK_cases`). $\square$

**Theorem (Six copies along near pairs).** Let $2 < p \leq k$ be a prime that does not split, and $w$ a tight frame of length $M$. Let $(\tau, e(\tau))$ be a near pair for $\tau \in \Phi_0$, and let $j : \Phi \to \mathbb{N}$ be arbitrary. Then
$$\mathrm{val}_6(\nu' + \nu'') \leq \gamma_p|\nu' + \nu''| - \sum_{\tau \in \Phi_0}j(\tau) - v(\nu'!) - v(\nu''!).$$

Lean: `New.Data.leastValLE_six_of_isNearPair` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* If $\Phi_0$ is empty, then $\nu' = \nu'' = 0$, and the bound is $\mathrm{val}_6(0) \leq 0$. Otherwise take $\tau \in \Phi_0$. As $(\tau, e(\tau))$ is a near pair, $p$ is inert. The normal form along the frame applies, the forms are integral, and $(\Phi_0, e)$ is a coupling family by the first lemma of this section. The second bound of [couplings on six copies](/decl/New.CMLattice.leastValLE_six_of_isCouplingFamily/) is the claim. $\square$

**Remark (Formalization).** For $p = d$ there are no near pairs, because $I_d$ is not empty but every near pair has $p \neq d$. So at $p = d$ the set $\Phi_0$ is empty and the couplings give nothing. The bound at $p = d$ then comes from the rate $\gamma_d = 1/(2d - 2)$ alone, together with the comparison of Section 5.

**Theorem (Twelve copies at a prime up to $k$).** Let $p \leq k$ be a prime that does not split. Let $w$ be a tight frame of length $M$ such that $|\mu_{i_0}(\tau)| = 1$ for every $\tau$, and let $l$ be near the weights. Then
$$\mathrm{val}_{12}(l) \leq S_p + \sum_\tau v(B_\tau) - v(l!).$$

Lean: `New.Data.leastValLE_twelve_localPrimeSumTotal_of_le` (New/Derivatives/Sharpness/Cases.lean).

*Proof.* A prime that does not split is at least $13$. Let $\Phi_0$ be the set of places $\tau$ that are the start of some near pair. For $\tau \in \Phi_0$ choose one such pair $(\tau, e(\tau))$. Put $j(\tau) = \lfloor l_\tau/p^{e(\tau)}\rfloor$ for $\tau \in \Phi_0$ and $j(\tau) = 0$ otherwise.

Every near pair $(\tau, e')$ has $\tau \in \Phi_0$. Two near pairs with the same start have the same exponent, so $e' = e(\tau)$ and $j(\tau) = \lfloor l_\tau/p^{e'}\rfloor$. These are the hypotheses of [the comparison](/decl/New.Data.gammaPrime_mul_degree_sub_le_localPrimeSumTotal_add/).

By the lemma on near pairs above, $l = \nu' + \nu'' + \eta$ for an exponent $\eta$. Six copies along near pairs give the bound for $\nu' + \nu''$. [The rate on six copies](/decl/New.CMLattice.leastValLE_of_unit_coefficients/) gives $\mathrm{val}_6(\eta) \leq \gamma_p|\eta| - v(\eta!)$. As $j = 0$ off $\Phi_0$, $\sum_{\tau \in \Phi_0}j(\tau) = \sum_\tau j(\tau)$. Add the two bounds, with $|l| = |\nu' + \nu''| + |\eta|$:
$$\mathrm{val}_{12}(l) \leq \gamma_p|l| - \sum_\tau j(\tau) - v(\nu'!) - v(\nu''!) - v(\eta!).$$
By [Legendre with three parts](/decl/New.Data.sum_padicValNat_factorial_le_add/),
$$-v(\nu'!) - v(\nu''!) - v(\eta!) \leq -v(l!) + 3f(\log b + 2).$$
By the comparison,
$$\gamma_p|l| - \sum_\tau j(\tau) + 3f(\log b + 2) \leq S_p + \sum_\tau v(B_\tau).$$
Combine the three inequalities. $\square$

**Remark (Formalization).** The exponent $e(\tau)$ comes from `choose!` applied to the existence of a near pair at $\tau$. Off $\Phi_0$ its value is a junk value, but only $e$ on $\Phi_0$ is used. On $\Phi_0$ the choice does not matter, since the exponent of a near pair is unique.

### All primes

**Theorem (Twelve copies).** Let $D$ be admissible data, $p$ a prime with an embedding $\iota_p$, and $w$ a tight frame of length $M$ such that the form $\mu_{i_0}$ has $|\mu_{i_0}(\tau)| = 1$ for every $\tau$. Let $l$ be near the weights. Then
$$\mathrm{val}_{12}(l) \leq S_p + 2\sum_\tau v(B_\tau) - v(l!).$$

Lean: `New.Data.leastValLE_twelve` (New/Derivatives/Sharpness/Cases.lean), with `New.Data.nat_le_of_hasLogBound`.

*Proof.* The valuations $v(B_\tau)$ are nonnegative.

1. If $p$ splits, the split case gives the bound without the term $2\sum v(B_\tau)$.
2. If $p$ does not split and $p > k$, then $p > k \geq d$ (`New.Data.nat_le_of_hasLogBound`). So $p \neq d$ and $p$ is inert by the lemma above. The case above $k$ gives the bound.
3. If $p$ does not split and $p \leq k$, the last theorem gives the bound with $\sum v(B_\tau) \leq 2\sum v(B_\tau)$. $\square$

In the first case $w$ need not be a tight frame. In the second case the unit form is not needed. Only the statement of the theorem asks for both. Section 7 supplies a frame with both properties.
