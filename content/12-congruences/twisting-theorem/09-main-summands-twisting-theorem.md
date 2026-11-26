---
title: Main summands and the twisting theorem
lean:
  - New/Congruences/Selmer/MainSummands.lean
  - New/Congruences/Selmer/TwistingTheorem.lean
decls:
  - New.Selmer.IsMainSummandLike.conjGal_inv_eq_smul_one
  - New.Selmer.IsMainSummandLike.normLength_congruenceTerm_le
  - New.Selmer.IsMainSummandLike.normLength_localTerm_le
  - New.Selmer.IsMainSummandLike.normLength_firstPrimeTerms_le
  - New.Selmer.IsMainSummandLike.normLength_placeTerms_add_firstPrimeTerms_le
  - New.Selmer.IsMainSummandLike.eventually_exists_selmerDatum
  - New.Selmer.exists_selmerData_isTorsionLevel
  - New.Selmer.divisibleSelmerLength_le_divisibleLength
  - New.Selmer.SelmerDatum.TwistedLengthLe.hasDivisibleSelmerLengthLe
  - New.Selmer.IsSmallTwist.isAuxTwist
  - New.Selmer.four_mul_ellVal_levelPrime_sub_one_add_le_twistError
  - New.Selmer.invAvatar_pow
  - New.Selmer.tamePart_ne_one_of_invAvatar_ne_one
  - New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Main summands and the twisting theorem

This section applies the general theorem of [the general twisting theorem](/chapter/twisting-theorem/#the-general-twisting-theorem) to the main summands and to the Stickelberger systems of the ramified pairs. The results are in [MainSummands.lean](lean:New/Congruences/Selmer/MainSummands.lean#L1) and [TwistingTheorem.lean](lean:New/Congruences/Selmer/TwistingTheorem.lean#L1).

Background. A row $R$ is a representation that satisfies `IsMainSummandLike` ([inertia above the level](/chapter/main-summands/#inertia-above-the-level-and-main-summand-like)). A lattice $u$ in $R$ over $O$ (`IsLatticeIn`) is a conjugate of $R$ with entries in $O$ ([avatars](/chapter/main-summands/#avatars-and-conjugate-self-duality)). The terms of $\beta_T$ are defined in [Selmer data](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma). Let $v$ be the $\ell$-adic valuation, $V = v(\mathrm{chosenGroupOrder})$, $f$ the number of infinite places and $d = \mathrm{card}\, n$.

### Main summands are Selmer data

**Lemma.** Let the values of $u$ span $M_n(O)$ and let $u(g) = y \cdot 1$. Then $u((g^c)^{-1}) = \mathrm{cyc}(g)^{t-1} y \cdot 1$.

Lean: `New.Selmer.IsMainSummandLike.conjGal_inv_eq_smul_one` (New/Congruences/Selmer/MainSummands.lean).

*Proof.* Conjugate self-duality gives $\mathrm{tr}\, u(x^c) = \mathrm{cyc}(x)^{1-t}\, \mathrm{tr}\, u(x^{-1})$ (`New.Selmer.IsMainSummandLike.trace_lattice_conjGal`). Apply it at $x^c g^{-1}$ and at $x^c$. Then $\mathrm{tr}(u(x) u((g^c)^{-1}))$ and $\mathrm{tr}(u(x) \cdot y')$ agree for all $x$, with $y'$ the claimed scalar. The $u(x)$ span $M_n(O)$ and the trace form is nondegenerate, so the two matrices are equal. $\square$

**Lemma (Global term).** Let the values of $u$ span $M_n(O)$, and let $u(g) = \alpha \cdot 1$ with $\mathrm{cyc}(g) = p_l^{d}$ for a prime $p_l$ of the data. Then $\mathrm{normLength}(\mathrm{congruenceTerm}\, u) \leq d V$.

Lean: `New.Selmer.IsMainSummandLike.normLength_congruenceTerm_le` (New/Congruences/Selmer/MainSummands.lean).

*Proof.* By the lemma above, $(g^c)^{-1}$ acts by $\alpha'$. Put $\delta = \alpha - \mathrm{cyc}(g^c)\alpha'$. A computation gives $\delta = (1 - p_l^{e})\alpha$ with $e = d \cdot t$ (and $e = d$ if $t = 0$), so $1 \leq e \leq D.r \cdot D.t$. A scalar of $u$ is a unit, since its $d$-th power is a determinant (`New.Selmer.IsMainSummandLike.isUnit_of_eq_smul_one`). So $v(\delta) = v(p_l^e - 1) \leq V$ (`New.Selmer.ellVal_levelPrime_pow_sub_one_le`). The bound for the global term ([the global term](/chapter/tied-selmer-groups/#the-global-term)) gives $\mathrm{congruenceTerm} \leq d \cdot v(\delta)$. $\square$

**Lemma (Local terms).** Let $w$ be a chosen place above $p_0 p_1$, prime to $\ell$, with tame generator $\gamma$. Let $S$ be the places above $\ell p_0 p_1$.

1. For $v$ above $p_0 p_1$ and prime to $\ell$, $\mathrm{normLength}(\mathrm{localTerm}\, u\, v) \leq dV$.
2. $\mathrm{normLength}(\mathrm{firstPrimeTerms}\, u\, \gamma) \leq 2dV$.
3. $\mathrm{normLength}(\mathrm{placeTerms}\, u\, S + \mathrm{firstPrimeTerms}\, u\, \gamma) \leq (4f + 2) dV$.

Lean: `New.Selmer.IsMainSummandLike.normLength_localTerm_le`, `New.Selmer.IsMainSummandLike.normLength_firstPrimeTerms_le`, `New.Selmer.IsMainSummandLike.normLength_placeTerms_add_firstPrimeTerms_le` (New/Congruences/Selmer/MainSummands.lean).

*Proof.* The row gives at $v$ an inertial $\gamma_v$ with $v(\det(R(\gamma_v) - 1)) \leq dV$, and an $m$ prime to $v$ with $R(s^m) = 1$ on inertia. At the chosen place $\gamma_v = \gamma$, and the bound holds for $\gamma$ and $(\gamma^c)^{-1}$. For (1), take $a \neq 0$ and $M$ with $a \mid \ell^M$ (`New.Selmer.exists_dvd_ell_pow`). The local cocycles with values in $(O/a)^n$ exceed $\mathrm{len}\,(O/a)^n$ by at most the length of the kernel of $u(\gamma_v) - 1$. That length is at most $\mathrm{addVal}\, \det(u(\gamma_v) - 1)$. Its normalized value is $v(\det(R(\gamma_v) - 1))$ (`New.Selmer.IsLatticeIn.normLength_addVal_det_sub_one`). (2) is the same identity for the two terms. For (3), at most $4f$ places of $S$ are prime to $\ell$ (`New.Selmer.card_le_of_subset_placesAboveM`). Add (1) over them and (2). $\square$

**Theorem (Main summands are Selmer data).** Let $R$ be a row, and let $w$ be a chosen place above $p_0 p_1$ and prime to $\ell$. For all large coefficient rings $O$ there is a Selmer datum $T$ for $\mathrm{badPlaces}\, D\, \ell$ and the tame generator at $w$ such that $T.\rho$ is a lattice in $R$, $T.\mathrm{places}$ is the set of places above $\ell p_0 p_1$, $T.\mathrm{localRelations} = \mathrm{crysRelations}\, T.\rho$, and $\mathrm{normLength}\, \beta_T \leq (4f + 3) dV$.

Lean: `New.Selmer.IsMainSummandLike.eventually_exists_selmerDatum` (New/Congruences/Selmer/MainSummands.lean).

*Proof.* For large $O$ there is a lattice $u$ in $R$, its values span $M_n(O)$, and some $g$ acts by $\alpha$ with $\mathrm{cyc}(g) = p_l^d$. Some inertial $\gamma$ above $p_0 p_1$, prime to $\ell$, acts by $\zeta$ with $\zeta^2 - 1$ a unit (`New.Selmer.IsMainSummandLike.exists_mem_inertiaAbove_eq_smul_one_isUnit`). The cyclotomic character is trivial at $\gamma$, so $(\gamma^c)^{-1}$ also acts by $\zeta$. The local modules are the crystalline cocycles. Their ranks satisfy the rank bound (`New.Selmer.IsMainSummandLike.sum_finrank_crysCocyclesAt_le`). The two lemmas above make the terms finite and give $\mathrm{normLength}\, \beta_T \leq dV + (4f + 2)dV$. $\square$

**Lemma.** Let $R_i$ be finitely many rows, $w$ as above and $c = (4f + 3) \cdot r \cdot V$. Some $O$ carries Selmer data $T_i$ as in the theorem with $\mathrm{normLength}\, \beta_{T_i} \leq c$, and $c + 2$ is a torsion level for the $T_i$.

Lean: `New.Selmer.exists_selmerData_isTorsionLevel` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* The theorem holds for all $i$ on a common tail of rings. On that tail some $O$ has residue field with more than $2r(c + 2)\, \mathrm{addVal}(\ell) + 1$ elements. Since $d_i \leq r$, $\beta_{T_i} \leq c$, so $\beta_{T_i} + 1 < c + 2$, and $2 d_i\, \mathrm{addVal}(\ell^{c+2}) + 1$ is below the size of the residue field. $\square$

### From twisted lengths to Selmer lengths

**Lemma.** Let $\rho$ be the twist of $T.\rho$ by $\psi$ along $e : O_0 \to O$, and $S = T.\mathrm{places} \cup Q \cup \bar{Q}$. If a set $L$ of relations contains the images of $T.\mathrm{classRelations}$, then the cocycles unramified outside $S$ that obey $L$ have length at most $T.\mathrm{divisibleLength}\, Q\, e\, \psi$.

Lean: `New.Selmer.divisibleSelmerLength_le_divisibleLength` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Both modules have the same places, and a cocycle that obeys $L$ obeys the smaller set. So the first module lies in the second. $\square$

**Lemma.** Let $T$ be a datum from the theorem for a row $R$, let $Q$ be auxiliary, and let $\psi$ be from $U(1)$ with level $Q$. If $T$ satisfies `TwistedLengthLe Q ψ b`, then `HasDivisibleSelmerLengthLe ψ R Q T.γ ζ b` holds, with $\zeta$ the image of $T.\zeta$ ([Selmer lengths](/chapter/main-summands/#cocycles-relations-and-selmer-lengths)).

Lean: `New.Selmer.SelmerDatum.TwistedLengthLe.hasDivisibleSelmerLengthLe` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Take $O' \supseteq O$ and $\psi'$ from the hypothesis. Then $\psi'(T.\gamma) = 1$ (`New.Selmer.SelmerDatum.apply_γ_eq_one`), so the twisted lattice has $T.\gamma$ acting by $\zeta$ and is a twisted lattice for $R$. $\psi'$ is trivial on the decomposition groups above $\ell$, so the crystalline relations of $T.\rho$ map into those of the twist (`New.Selmer.mapRel_crysRelations_subset`). The relation $g \mapsto \delta_{T.\gamma}$ is in the class relations. The lemma above bounds the crystalline Selmer length by $T.\mathrm{divisibleLength}$, which has normalized length at most $b$. $\square$

### Four small facts

**Lemma.** Let $\psi$ be a small twist for $\varepsilon$, $Q$ auxiliary and $S_0$ contain the places above $\ell$. Then `IsAuxTwist S₀ Q ψ ε` holds ([even classes](/chapter/tied-traces/#even-classes-and-cocycles-of-tate-twists)).

Lean: `New.Selmer.IsSmallTwist.isAuxTwist` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Items 1 and 6 of the definition give the form of $\psi$ and the sum over $Q \cup \bar{Q}$, which bounds the sum over $Q$. The places of $Q$ are prime to $\ell$ because $Q$ misses $S_0$. $\square$

**Lemma.** For $i = 0, 1$, $4v(p_i - 1) + 2^{-\ell} \leq e'_\ell$.

Lean: `New.Selmer.four_mul_ellVal_levelPrime_sub_one_add_le_twistError` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* $v(p_i - 1) \leq V$ (`New.Selmer.ellVal_levelPrime_pow_sub_one_le` with exponent $1$), and $4 \leq (4f + 3) r$ for the data. $\square$

**Lemma.** $(\tau^j)^{\mathrm{inv}} = (\tau^{\mathrm{inv}})^j$ for a tame character $\tau$. If $\tau^{\mathrm{inv}}(g) \neq 1$ for $g$ in inertia at $w \in Q$, then the tame part of $\tau$ at $w$ is not trivial.

Lean: `New.Selmer.invAvatar_pow`, `New.Selmer.tamePart_ne_one_of_invAvatar_ne_one` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Both sides of the first claim agree on Artin symbols, which exhaust the group. For the second, $g$ is the local Artin symbol of a unit $x$ at $w$. If the tame part at $w$ were trivial, $\tau$ would be unramified at $w$, as it is at $\bar{w}$. Then $\tau^{\mathrm{inv}}(g) = 1$. $\square$

### The twisting theorem

**Theorem (Twisting theorem).** Let $R_i$ be finitely many rows and fix $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. There is an $m$-fold twist $\tau$ ([twists](/chapter/regular-families-plan/#heights-twists-and-ratios)) such that for every $1 \leq j \leq m$, with $\xi = \tau^j$:

1. `IsAuxTwist (badPlaces D ℓ) ξ.Q ξ.invAvatar e'_ℓ`;
2. for each $i$ there are $\gamma$ and $\zeta$ with `HasDivisibleSelmerLengthLe ξ.invAvatar (R i) ξ.Q γ ζ e'_ℓ`;
3. for every ramified critical pair $p$ and sign $s$, $v(\iota(p.\mathrm{ratio}\, \xi\, s)) \leq e'_\ell$.

Lean: `New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe` (New/Congruences/Selmer/TwistingTheorem.lean).

*Proof.* Take a chosen place $w_0$ above $p_{i_0}$, prime to $\ell$, with $q_{w_0} = p_{i_0}$ (`New.Selmer.exists_chosen_notMem_placesDividing`). Let $g_0$ be its tame generator, $\varepsilon = 2^{-\ell}$ and $c$ as above, so $e'_\ell = c + \varepsilon$. The lemma above gives $O$ and data $T_i$ with torsion level $c + 2$. For each ramified pair and sign, [L-value systems](/chapter/twisting-theorem/#the-stickelberger-systems-of-the-l-values) gives $Y_k$ with this property: if $v(\psi(\Theta_{Y_k, Q})) \leq \beta_{Y_k} + b$, then the ratio has valuation at most $4v(q_{w_0} - 1) + b$. The general theorem with $m = D.m$ gives $Q$ and $\psi$ with $\psi^j$ a small twist for $\varepsilon$. Item 1 of the definition and [twist measures](/chapter/twisting-theorem/#twist-measures-of-critical-pairs) give $\tau$ with $\tau.Q = Q$ and $\tau^{\mathrm{inv}} = \psi$. By the power lemma, $(\tau^j)^{\mathrm{inv}} = \psi^j$ is a small twist. Item 3 and the tame part lemma show that each $\tau^j$ ramifies at every $w \in Q$. So $\tau$ is an $m$-fold twist.

Fix $j$. Conclusion 1 follows from the monotonicity lemma for $\varepsilon \leq e'_\ell$ and the lemma on auxiliary twists. For 2, item 4 and $\beta_{T_i} \leq c$ give `TwistedLengthLe` for $c + \varepsilon$. The lemma above then gives the Selmer bound with $\gamma = T_i.\gamma$. For 3, item 5 gives the hypothesis of $Y_k$ with $b = \varepsilon$, and the bound $4v(p_{i_0} - 1) + \varepsilon \leq e'_\ell$ ends the proof. $\square$

**Remark (Formalization).** The data $T_i$, the systems $Y_k$ and the twist $\tau$ are obtained by `choose`, so they are not canonical. The scalar $\zeta$ of conclusion 2 is $T_i.\zeta$ mapped into $\bar{\mathbb{Z}}_\ell$.
