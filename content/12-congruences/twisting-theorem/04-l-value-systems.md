---
title: The Stickelberger systems of the L-values
lean:
  - New/Congruences/Selmer/LValueSystems.lean
decls:
  - New.Selmer.not_isChosen_of_notMem_badPlaces
  - New.Data.CriticalPair.stickelbergerChar
  - New.Selmer.charUnramifiedAt_zpow_neg_of_notMem_badPlaces
  - New.Selmer.stickelbergerChar_eq_one_of_mem_inertiaAbove
  - New.Selmer.stickelbergerChar_tameGenerator_ne_one_and_pow_eq_one
  - New.Selmer.stickelbergerChar_mul_invAvatar_frob
  - New.Selmer.exists_finPart_baseChange_eq
  - New.Data.TameChar.zpowOfAuxiliary
  - New.Selmer.exists_groupRingEval_eq_of_isIntegralMeasure
  - New.Selmer.ellVal_stickelbergerChar_tameGenerator_sub_one_le
  - New.Selmer.apply_insert_eq_mul_eulerFactor
  - New.Selmer.norm_apply_twist
  - New.Selmer.exists_stickelbergerSystem_β_le_and_norm_eq
  - New.Selmer.ellVal_le_of_norm_eq_mul_pow
  - New.Selmer.exists_stickelbergerSystem_ellVal_ratio_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Stickelberger systems of the L-values

This section maps the twist measure of a ramified pair to the group rings of the class groups $\mathrm{Cl}_Q$. The result is a Stickelberger system whose values at twists give the ratios of $L$-values. All results are in [LValueSystems.lean](lean:New/Congruences/Selmer/LValueSystems.lean#L1).

Background used: the avatar of an algebraic Hecke character, its values at local Artin symbols and at Frobenius elements, and its continuity (`New.AlgHeckeChar.avatar`, [rank one](/chapter/attached-representations/#rank-one)); the tame generator of a place and its tame unit (`New.IsPlaceOver.tameGenerator`, Lib/ClassField/Local/ArtinMap.lean); the bad places $\mathrm{badPlaces}(D, \ell)$, the places dividing $\ell p_0 p_1 N$ ([auxiliary primes](/chapter/tied-traces/#auxiliary-primes)).

Fix a ramified pair $p = (\nu, z)$, a sign $\delta = \pm 1$, a chosen place $w$ not above $\ell$, and its tame generator $g_0$. For a tame character $\tau$ write $\tau^{\mathrm{inv}}$ for the avatar of $\tau^{-1}$.

### The character of the system

**Lemma.** Let $v \notin \mathrm{badPlaces}(D, \ell)$. Then $\ell \notin v$, and neither $v$ nor $\bar v$ is chosen. The algebraic Hecke character of the base change of $\nu^{-\delta}$ is unramified at $v$.

Lean: `New.Selmer.not_isChosen_of_notMem_badPlaces`, `New.Selmer.charUnramifiedAt_zpow_neg_of_notMem_badPlaces` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* The places above $\ell$ and the places above $M$, which contain the chosen places and their conjugates, are bad. The tame part of $\nu$ is trivial off the chosen places, so it is trivial at $v$ and at $\bar v$, and the base change is unramified at $v$. $\square$

**Definition.** The *Stickelberger character* $\vartheta_\delta$ of $p$ is the avatar of the algebraic Hecke character given by the base change of $\nu^{-\delta}$ to $E$.

Lean: `New.Data.CriticalPair.stickelbergerChar` (New/Congruences/Selmer/LValueSystems.lean).

**Lemma.** (1) $\vartheta_\delta$ is trivial on the inertia groups at all places outside the bad places. (2) If $p$ is ramified, then $\vartheta_\delta(g_0) \neq 1$ and $\vartheta_\delta(g_0)^{\mathrm{N}w - 1} = 1$. (3) Let $v$ be good, with $v, \bar v \notin Q_\tau$, and $\varphi$ an arithmetic Frobenius element at a place above $v$. Then $\vartheta_\delta(\varphi)\tau^{\mathrm{inv}}(\varphi) = \iota_\ell(y)^\delta$, with $y$ the value of the base change of $\nu\tau^\delta$ at the uniformizer at $v$.

Lean: `New.Selmer.stickelbergerChar_eq_one_of_mem_inertiaAbove`, `New.Selmer.stickelbergerChar_tameGenerator_ne_one_and_pow_eq_one`, `New.Selmer.stickelbergerChar_mul_invAvatar_frob` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* (1) Let $g$ be in the inertia group at a place above a good $v$. Then $g$ is the local Artin symbol of a local unit $x$ at $v$. The avatar at a local Artin symbol at a place not above $\ell$ is the value of the character at $x$, and this is $1$ since the character is unramified at $v$.

(2) Let $x$ be the tame unit at $w$, whose Artin symbol is $g_0$ and whose residue $\gamma$ generates the units of the residue field. Then $\vartheta_\delta(g_0) = \iota_\ell(\chi_w(\gamma))^{-\delta}$, with $\chi_w$ the tame part of $\nu$ at $w$. Since $p$ is ramified, $\chi_w \neq 1$, so $\chi_w(\gamma) \neq 1$. The residue field has $\mathrm{N}w$ elements, so $\chi_w(\gamma)^{\mathrm{N}w - 1} = 1$. Both claims pass to the power $-\delta$, since $\delta = \pm 1$.

(3) Write $\varphi = \phi^{-1}$ with $\phi$ a geometric Frobenius element. At a geometric Frobenius element the avatar of an unramified character is the inverse of $\iota_\ell$ of its Hecke coefficient. Both characters are unramified at $v$, by the lemma and since the tame part of $\tau$ is trivial at $v$ and $\bar v$. The product of the two Hecke coefficients is the value at the uniformizer of the base change of $\nu^{-\delta}\tau^{-1}$, which is $y^{-\delta}$. $\square$

**Lemma.** $v(\vartheta_\delta(g_0) - 1) \leq v(\mathrm{N}w - 1)$.

Lean: `New.Selmer.ellVal_stickelbergerChar_tameGenerator_sub_one_le` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* By (2), $\vartheta_\delta(g_0)$ and $1$ are distinct roots of $X^n - 1$ with $n = \mathrm{N}w - 1$. Two distinct $n$-th roots of unity are at distance at least $\|n\|$. So $\|\vartheta_\delta(g_0) - 1\| \geq \|n\|$, which is the claim. $\square$

### The elements $\Theta_I$

**Lemma.** For every $x \in U(1)(\mathbb{A})$ there is a finite idele $y$ such that $\tau(x)$ is the value at $y$ of the base change of $\tau$, for every tame character $\tau$.

Lean: `New.Selmer.exists_finPart_baseChange_eq` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* There is $y$ such that $x/(y/\bar y)$ has finite part $1$. A tame character has weight $0$, so it is trivial on this quotient. $\square$

**Definition.** For an auxiliary $I$ and a tame character $\tau$ whose tame part is trivial off $I$, $\tau^\delta$ with modulus $I$ is the tame character of $\tau^\delta$ in $\mathrm{tameChars}(I)$.

Lean: `New.Data.TameChar.zpowOfAuxiliary` (New/Congruences/Selmer/LValueSystems.lean).

**Lemma.** Let $F$ be an integral measure at every modulus. There are elements $\Theta_I$ of the group rings of $\mathrm{Cl}_I$ over $\bar{\mathbb{Z}}_\ell$ such that $1(\Theta_\emptyset) = \iota_\ell F(1)$ and: for $I$ auxiliary, $\tau$ with tame part trivial off $I$, and $\tau^{\mathrm{inv}}$ a character for $I$, $\tau^{\mathrm{inv}}(\Theta_I) = \iota_\ell F(\tau^\delta)$, with $\tau^\delta$ of modulus $I$.

Lean: `New.Selmer.exists_groupRingEval_eq_of_isIntegralMeasure` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* For $I$ auxiliary, apply the measure property at the trivial tame character of modulus $I$. It gives points $u_j$ and coefficients $\alpha_j$ with $F(\tau) = \sum_j \alpha_j \tau(u_j)$ for all $\tau$ of modulus $I$, and $\alpha_j$ integral at every prime prime to $\prod_{v \in I}\mathrm{N}v$. This product is prime to $\ell$, so $\|\iota_\ell(\alpha_j)\| \leq 1$. Let $y_j$ be the idele of the last lemma for $u_j$, and put
$$\Theta_I = \sum_j \iota_\ell(\alpha_j)\, [\mathrm{cl}_I(y_j^{-\delta})].$$
For $I$ not auxiliary, put $\Theta_I = 0$. The empty set is auxiliary, and its value at $1$ is $\iota_\ell \sum_j \alpha_j = \iota_\ell F(1)$. For $I$ and $\tau$ as stated, the lemma on the lift gives $\tau^{\mathrm{inv}}(\mathrm{lift}(\mathrm{cl}_I(z))) = \iota_\ell(b(z))^{-1}$, with $b$ the base change of $\tau$. For $z = y_j^{-\delta}$ this is $\iota_\ell \tau^\delta(u_j)$. Sum over $j$. $\square$

**Remark (Formalization).** The value $\Theta_I = 0$ for $I$ not auxiliary is a junk value. The norm relation only concerns auxiliary sets, so the system does not see it. The points $u_j$, the coefficients and the ideles $y_j$ are chosen with `choose`. The lemma states only the values at characters for $I$, and these do not depend on the choices.

### Euler factors and values at twists

**Lemma.** Let $F$ be a twist measure for $p$, $K$ and $m$. Let $\tau$ have modulus $Q$, with $Q$ and $Q \cup \{v\}$ auxiliary and $v \notin Q$, and let $\varphi$ be an arithmetic Frobenius element at a place above $v$. Then
$$\iota_\ell F(\tau^\delta \text{ of modulus } Q \cup \{v\}) = \iota_\ell F(\tau^\delta \text{ of modulus } Q) \cdot \mathrm{Eul}_K(\vartheta_\delta(\varphi)\tau^{\mathrm{inv}}(\varphi), \mathrm{N}v),$$
with the list of $K$ as exponents. If $\xi$ is a twist with $Q_\xi$ auxiliary, then $\|\iota_\ell F(\xi^\delta)\| = \|\iota_\ell F(1)\| \cdot \|\iota_\ell\, \mathrm{ratio}(\xi, \delta)\|^{m+1}$.

Lean: `New.Selmer.apply_insert_eq_mul_eulerFactor`, `New.Selmer.norm_apply_twist` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* The axiom of insertion gives the factor $\prod_{l \in K}\prod_\epsilon (1 - y^\epsilon/q_v^l)$, with $y$ the value of $\nu\tau^\delta$ at $v$. By (3), $\iota_\ell(y) = (\vartheta_\delta(\varphi)\tau^{\mathrm{inv}}(\varphi))^\delta$, and $\mathrm{Eul}$ does not change under $a \mapsto a^\delta$. For the second claim, $\xi^\delta$ is again a twist, since its tame part is not trivial at the places of $Q_\xi$. The axiom at twists gives $F(1)\mathrm{normQ}^m \mathrm{ratio}^{m+1}$. Since $Q_\xi$ is auxiliary, $\mathrm{normQ}$ is prime to $\ell$, so its image has norm $1$. $\square$

### The system of a ramified pair

**Theorem.** There is a Stickelberger system $Y$ for the bad places and $g_0$ with
$$\beta_Y \leq v(1(\Theta_\emptyset)) + 4v(\mathrm{N}w - 1),$$
and with the following property. Let $\xi$ be a twist with $Q_\xi$ auxiliary and $\xi^{\mathrm{inv}}$ a character for $Q_\xi$. Then
$$\|\xi^{\mathrm{inv}}(\Theta_{Q_\xi})\| = \|1(\Theta_\emptyset)\| \cdot \|\iota_\ell\, \mathrm{ratio}(\xi, \delta)\|^{i},$$
with $i = 2$ if $z = 1$ and $i = 1$ otherwise.

Lean: `New.Selmer.exists_stickelbergerSystem_β_le_and_norm_eq` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* Let $K = \{0, 1\}$ if $z = 1$ and $K = \{z\}$ otherwise, and let $F$ be the twist measure of the last section, with $m = 1$ or $m = 0$. Take $\Theta$ from the lemma on the elements, and $\vartheta = \vartheta_\delta$, which is continuous as an avatar. The axioms on $\vartheta$ are (1) and (2). The exponents are the list of $K$. $1(\Theta_\emptyset) = \iota_\ell F(1) \neq 0$.

Norm relation: let $Q \cup \{v\}$ be auxiliary, $v \notin Q$, and $\psi$ a character for $Q$. Then $Q$ is auxiliary, and the last lemma of the previous section gives $\tau$ with modulus $Q$ and $\psi = \tau^{\mathrm{inv}}$. The character $\psi$ is also a character for $Q \cup \{v\}$. The lemma on the elements gives the values at $Q$ and $Q \cup \{v\}$, and the Euler factor lemma relates them.

Bound for $\beta$: $\#K \leq 2$, and each term $2v(\vartheta(g_0) - 1)$ is at most $2v(\mathrm{N}w - 1)$. So the sum is at most $4v(\mathrm{N}w - 1)$.

Values at twists: the lemma on the elements gives $\xi^{\mathrm{inv}}(\Theta_{Q_\xi}) = \iota_\ell F(\xi^\delta)$, and the norm lemma gives the claim with $m + 1 = i$. $\square$

**Lemma.** Let $x_0 \neq 0$ be integral, $i \geq 1$ and $\|x\| = \|x_0\|\|r\|^i$. If $v(x) \leq v(x_0) + c$, then $v(r) \leq c$.

Lean: `New.Selmer.ellVal_le_of_norm_eq_mul_pow` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* If $\|r\| \leq 1$, then $v(x) = v(x_0) + i v(r)$. Since $v(x_0) < \infty$, $i v(r) \leq c$, and $v(r) \leq i v(r)$. If $\|r\| > 1$, then $v(r) = 0$ since $v$ is truncated at $0$. $\square$

**Corollary.** There is a Stickelberger system $Y$ for the bad places and $g_0$ such that, for each twist $\xi$ as in the theorem and each $c \geq 0$: if $v(\xi^{\mathrm{inv}}(\Theta_{Q_\xi})) \leq \beta_Y + c$, then
$$v(\iota_\ell\, \mathrm{ratio}(\xi, \delta)) \leq 4v(\mathrm{N}w - 1) + c.$$

Lean: `New.Selmer.exists_stickelbergerSystem_ellVal_ratio_le` (New/Congruences/Selmer/LValueSystems.lean).

*Proof.* Take $Y$ from the theorem. Then $v(\xi^{\mathrm{inv}}(\Theta_{Q_\xi})) \leq v(1(\Theta_\emptyset)) + 4v(\mathrm{N}w - 1) + c$. Apply the lemma with $x_0 = 1(\Theta_\emptyset)$, which is not zero and is integral. $\square$

The general theorem of section 8 makes $v(\psi(\Theta_Q)) \leq \beta + \varepsilon$. The corollary then bounds the ratio. Section 9 bounds $4v(\mathrm{N}w - 1)$ by the twist error.
