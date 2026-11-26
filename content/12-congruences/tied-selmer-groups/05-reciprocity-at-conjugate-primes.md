---
title: Reciprocity at conjugate primes
lean:
  - New/Congruences/Selmer/Mirror.lean
decls:
  - New.Selmer.isTameGeneratorFor_conjGal_inv
  - New.Selmer.characterModule_eq_zero_of_span
  - New.Selmer.SelmerDatum.reductionKerInfConj
  - New.Selmer.SelmerDatum.mem_reductionKerInfConj
  - New.Selmer.SelmerDatum.isOpen_reductionKerInfConj
  - New.Selmer.SelmerDatum.sahGroup_le_reductionKerInfConj
  - New.Selmer.SelmerDatum.mem_reductionKerInfConj_of_mem_inertiaGroup
  - New.Selmer.SelmerDatum.γ₀_mem_reductionKerInfConj
  - New.Selmer.SelmerDatum.γ₀_mul_mem_normalClosure_inertiaAbove
  - New.Selmer.SelmerDatum.exists_isNewAuxiliaryPrime
  - New.Selmer.SelmerDatum.exists_apply_pair_eq_nsmul
  - New.Selmer.SelmerDatum.mirrorForm
  - New.Selmer.SelmerDatum.frobInTameImage
  - New.Selmer.SelmerDatum.apply_conj_of_mem_dualSelmer
  - New.Selmer.SelmerDatum.apply_first_tameGenerator_eq_zero_of_mem_dualSelmer
  - New.Selmer.SelmerDatum.eq_zero_of_mem_dualSelmer_of_forall_sahGroup
  - New.Selmer.SelmerDatum.dualSelmer_frob_add_conj_frob_eq_zero
  - New.Selmer.SelmerDatum.mirrorForm_self_eq_zero
  - New.Selmer.SelmerDatum.mirrorForm_add_swap_eq_zero
  - New.Selmer.SelmerDatum.mirrorForm_conj_γ_left
  - New.Selmer.SelmerDatum.mirrorForm_conj_γ_right
  - New.Selmer.SelmerDatum.mirrorForm_eq_zero
  - New.Selmer.SelmerDatum.exists_linearMap_apply_eq_dualSelmer_conj
  - New.Selmer.SelmerDatum.mem_conjDualHom_of_apply_eq
  - New.Selmer.SelmerDatum.length_dualSelmer_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Reciprocity at conjugate primes

The count of the previous section bounds the tied Selmer group by its dual. This section bounds the dual by the global term $\mathrm{glob}(T) = \sup_{b \neq 0} \mathrm{len}\, \mathrm{Hom}_G(W_b, W_b^{*c})$. The tool is a class $z$ in the tied Selmer group of full order. To each $y$ in the dual group the proof attaches a $G$-map $\eta : W_a \to W_a^{*c}$ with $\eta(z(h)) = y(h^c)$ on $H$. This map determines $y$, so the dual group embeds in $\mathrm{Hom}_G(W_a, W_a^{*c})$. All results are in [Mirror.lean](lean:New/Congruences/Selmer/Mirror.lean#L1).

Background used:

- Auxiliary primes with a Frobenius element near a given element of the normal closure of inertia exist by Chebotarev (`New.Selmer.exists_isAuxPrimeDataAt`, [auxiliary primes](/chapter/tied-traces/#auxiliary-primes)).
- At a split prime $P$ prime to $m$, a locally constant function on inertia that is additive there is determined by its value at a normalised tame generator: $f(\tau) = k\, f(\delta)$ for some $k \in \mathbb{N}$ (`New.IsTameGeneratorFor.exists_apply_eq_nsmul`, from the file SplitPrimeReciprocity of [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula)).
- Normalised tame generators exist at every place (`New.exists_isTameGeneratorFor`, from the file SelmerLevels of the same section).

### Textbook form and source form

There is no single textbook theorem here. The idea is Sah's: an element $\gamma_*$ that acts by a scalar $\zeta \neq 1$ makes $H^1(G, W)$ small, and the classes are controlled by their values on the commutator group $H$. The source applies this to the dual group and adds a step that uses the conjugate primes $P$ and $\bar P$ of the CM field $E$. The pairing of a class with a member of the dual group at $P$ and at $\bar P$ gives a form on $H \times H$ that the reciprocity law forces to be zero.

For $u \in W_a$ and $f \in W_a^* = \mathrm{Hom}(W_a, \mathbb{Q}/\mathbb{Z})$ the source pairs $u$ and $f$ by the character $t \mapsto f(t u)$ of $O$. So all identities below hold for every $t \in O$.

### The group $U \cap U^c$

**Definition.** $U \cap U^c = \{g : g \in U \text{ and } g^c \in U\}$, with $U = U_{M, N}$ of the previous section.

Lean: `New.Selmer.SelmerDatum.reductionKerInfConj`, `New.Selmer.SelmerDatum.mem_reductionKerInfConj` (New/Congruences/Selmer/Mirror.lean).

**Lemma.** The group $U \cap U^c$ is open and contains $H$. If $P, \bar P \notin S_0$ and $B$ is a place over $P$, it contains the inertia group of $B$. It contains the tame generator $\gamma_0$ of the first prime $P_0$.

Lean: `New.Selmer.SelmerDatum.isOpen_reductionKerInfConj`, `New.Selmer.SelmerDatum.sahGroup_le_reductionKerInfConj`, `New.Selmer.SelmerDatum.mem_reductionKerInfConj_of_mem_inertiaGroup`, `New.Selmer.SelmerDatum.γ₀_mem_reductionKerInfConj` (New/Congruences/Selmer/Mirror.lean).

*Proof.* $U$ is open and $g \mapsto g^c$ is continuous. $H$ lies in $U$ and is stable under $h \mapsto h^c$. For $\tau$ in the inertia group of $B$, $\tau$ is inertial above $P$ and $\tau^c$ is inertial above $\bar P$. Both places are outside $S$, so both elements lie in $U$ by the inertia lemma of the previous section. The element $\gamma_0$ is inertial at a place over $P_0$, and $P_0, \bar P_0 \notin S_0$ because $J$ is auxiliary. $\square$

### New auxiliary primes near $\gamma_0 H$

**Lemma.** Let $h \in H$, and let $R$ contain $P_0$ and each $v \in S_0$ with its conjugate. Then $\gamma_0 h$ lies in the normal closure of the inertia groups above the places of $R$ that are not above $\ell$ and are not in $(J \setminus \{P_0\}) \cup \overline{(J \setminus \{P_0\})}$.

Lean: `New.Selmer.SelmerDatum.γ₀_mul_mem_normalClosure_inertiaAbove` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Call this set of places $Z$. The place $P_0$ is in $Z$, since $P_0 \in R$, $P_0$ is not in $J \setminus \{P_0\}$, $\bar P_0 \notin J$, and $P_0$ is prime to $\ell$. So $\gamma_0$ is in the normal closure. Each $v \in S$ prime to $\ell$ and its conjugate lie in $R$ and not in $J \cup \bar J$, since $J$ avoids $S_0$. So $H$ lies in the normal closure by the lemma on $H$ and inertia of [Selmer data, tied Selmer groups and Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma). $\square$

**Lemma (New primes near $\gamma_0 h$).** Let $U_i(g)$ hold exactly when $g$ acts trivially on $T/\ell^M$. Let $h \in H$, $R$ a finite set of places and $X$ a neighbourhood of $\gamma_0 h$. Then there are a place $P$ and data $l$ such that $P$ with $l$ is a new auxiliary prime for the datum $i$, $P \notin R$, $\bar P \notin R$ and $\varphi_l \in X$.

Lean: `New.Selmer.SelmerDatum.exists_isNewAuxiliaryPrime` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Let $R_0$ be the places that divide the norm $q_0$ of $P_0$, and let $R' = J \cup S_0 \cup R \cup \bar S_0 \cup R_0$. By the last lemma $\gamma_0 h$ lies in the normal closure of the inertia groups above the places of $R'$ that are prime to $\ell$ and outside $(J \setminus \{P_0\})$ and its conjugate. The characters $\chi_v$, $v \in J$, are locally constant, so they are constant near $\gamma_0 h$. The set $U \cap U^c$ is an open neighbourhood of $\gamma_0 h$. Apply the theorem that auxiliary primes exist with the set $J \setminus \{P_0\}$, the set $R'$ and the neighbourhood $X \cap (U \cap U^c) \cap \{\chi_v \text{ constant}\}$. It gives $P \notin R' \cup \bar R'$ of prime norm and data $l$ with $\chi_l(\varphi) = 1$ that are auxiliary for every set inside $(J \setminus \{P_0\}) \cup \{w \mid \ell\}$. These give conditions 1, 2, 4 and 5 of a new auxiliary prime, and $P \notin R_0$ gives condition 3. For condition 6, $\chi_v(\varphi) = \chi_v(\gamma_0 h) = \chi_v(\gamma_0)$, since $\chi_v$ is trivial on $H$, and $\chi_v(\gamma_0)$ is $1$ for $v = P_0$ and $0$ otherwise. For condition 7, $\varphi$ and $\varphi^c$ lie in $U$, so $\varphi$ and $(\varphi^c)^{-1}$ act trivially on $T/\ell^M$. $\square$

### Tame generators at conjugate places

**Lemma.** If $\delta$ is a normalised tame generator at $B$ over $P$, then $(\delta^c)^{-1}$ is a normalised tame generator at the conjugate place $\bar B$.

Lean: `New.Selmer.isTameGeneratorFor_conjGal_inv` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Let $\varpi$ be a uniformiser at $B$ and $r$ an $m$-th root of $\varpi$ with $\delta(r)/r = \zeta_m$. Then $\bar\varpi$ is a uniformiser at $\bar B$ and $c(\delta(r))$ is an $m$-th root of it. The element $(\delta^c)^{-1} = c\,\delta^{-1} c$ sends $c(\delta(r))$ to $c(r)$. So it divides that root by $c(\zeta_m) = \zeta_m^{-1}$, that is, it multiplies by $\zeta_m$. $\square$

**Lemma.** Let $a \mid \ell^M$, $M < N$, $P, \bar P \notin S_0$, $B$ over $P$, $\tau$ in the inertia group of $B$, and $\delta$ a normalised tame generator at $B$ for $\ell^N$. For a locally constant cocycle $z$ with values in $W_a$ there is $k \in \mathbb{N}$ with $z(\tau) = k\, z(\delta)$ and $z((\tau^c)^{-1}) = k\, z((\delta^c)^{-1})$.

Lean: `New.Selmer.SelmerDatum.exists_apply_pair_eq_nsmul` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Put $f(g) = (z(g), z((g^c)^{-1}))$. On the inertia group of $B$ the elements $g$ and $(g^c)^{-1}$ lie in $U$, so they act trivially on $W_a$ and $f$ is additive there. The prime $P$ is prime to $\ell$, since the places above $\ell$ lie in $S \subseteq S_0$. Apply the background lemma on tame generators to $f$, with $W_a$ a module over $\mathbb{Z}/\ell^N$. $\square$

### The dual group

Fix tied primes $(J, x)$, $a \mid \ell^M$, $M < N$, places $A$ and a finite set $R$, and let $y$ lie in $\mathrm{Sel}^*(J)$.

**Lemma.** For $u \in U$ and $g \in G$, $y(g u g^{-1})(m) = y(u)(\mathrm{cyc}(g)\, \rho(g^{-1}) m)$.

Lean: `New.Selmer.SelmerDatum.apply_conj_of_mem_dualSelmer` (New/Congruences/Selmer/Mirror.lean).

*Proof.* This is the equivariance condition of a relation. It is stated with the cyclotomic character modulo $\ell^N$. On $W_a$, killed by $\ell^N$, the $\ell$-adic character acts through that reduction. $\square$

**Lemma.** $y(\gamma_0) = 0$ and $y(\gamma_0^c) = 0$.

Lean: `New.Selmer.SelmerDatum.apply_first_tameGenerator_eq_zero_of_mem_dualSelmer` (New/Congruences/Selmer/Mirror.lean).

*Proof.* $y$ is zero on inertia above primes outside $R \setminus \{P_0, \bar P_0\}$, and $\gamma_0$, $\gamma_0^c$ are inertial above $P_0$ and $\bar P_0$. $\square$

**Lemma (Sah for the dual group).** If $y$ vanishes on $H$, then $y = 0$.

Lean: `New.Selmer.SelmerDatum.eq_zero_of_mem_dualSelmer_of_forall_sahGroup` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Outside $U$, $y = 0$ by definition. Let $g \in U$. Then $g = [g, \gamma_*] \cdot \gamma_* g \gamma_*^{-1}$, both factors lie in $U$, and $y$ is additive on $U$, so $y(g) = y(\gamma_* g \gamma_*^{-1})$. By the last lemma with $\mathrm{cyc}(\gamma_*) = 1$, $y(g)(\rho(\gamma_*) m) = y(g)(m)$. So $y(g)$ kills the image of $\rho(\gamma_*) - 1$, which is all of $W_a$. $\square$

**Lemma (Reciprocity at $P$ and $\bar P$).** Let $P$ with data $l$ be a new auxiliary prime for $i$ with $P, \bar P \notin R$, and let $\varphi, \varphi^c \in U$, where $\varphi$ and $\gamma$ are the Frobenius element and tame generator of $l$. Let $z \in \mathrm{Sel}^{J \cup \{P\}}_J(x, i, a)$, the tied group in which ramification is also allowed at $P$ and $\bar P$, with no tie there. Then for all $t \in O$
$$y(\varphi)(t\, z(\gamma)) + y(\varphi^c)(t\, z((\gamma^c)^{-1})) = 0.$$

Lean: `New.Selmer.SelmerDatum.dualSelmer_frob_add_conj_frob_eq_zero` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Choose a normalised tame generator $\delta$ at the place of $l$. The last lemma of the previous part gives $k$ with $z(\gamma) = k z(\delta)$ and $z((\gamma^c)^{-1}) = k z((\delta^c)^{-1})$. Form two split primes for the setting: $p = (P, \varphi, \delta)$ and $p' = (\bar P, \varphi^c, (\delta^c)^{-1})$. The second is valid by the lemma on conjugate tame generators, and $p \neq p'$ because $\bar P \neq P$. The cocycle $t k z$ is unramified at $P_0, \bar P_0$ by the lemma of the previous section, and it is ramified only at $S'$, $P$ and $\bar P$. So it lies in $Z(\{P, \bar P\})$ of the tied setting. The primes $P, \bar P$ are outside $R$. The reciprocity condition of a relation gives $y(\varphi)(t k z(\delta)) + y(\varphi^c)(t k z((\delta^c)^{-1})) = 0$, which is the claim. $\square$

### The mirror form

**Definition (Mirror form).** For functions $z : G \to W_a$ and $y : G \to W_a^*$, and $t \in O$,
$$\Psi_t(h, h') = y(h')(t\, z(h)) - y(h^c)(t\, z(h'^c)).$$

Lean: `New.Selmer.SelmerDatum.mirrorForm` (New/Congruences/Selmer/Mirror.lean).

**Definition.** For a new prime $P$ with data $l$, $\mathrm{frobInTameImage}(P, l)$ is the set of functions $z$ such that the pair $(z(\varphi), z((\varphi^c)^{-1}))$ equals $(z'(\gamma), z'((\gamma^c)^{-1}))$ for some $z' \in \mathrm{Sel}^{J \cup \{P\}}_J(x, i, a)$.

Lean: `New.Selmer.SelmerDatum.frobInTameImage` (New/Congruences/Selmer/Mirror.lean).

In words: the Frobenius values of $z$ at $P$ and $\bar P$ are the tame values of a class that may ramify at $P$ and $\bar P$. The hypothesis of the three steps below is that $z \in \mathrm{Sel}(J)$ lies in $\mathrm{frobInTameImage}(P, l)$ for every new auxiliary prime $P$ with data $l$ for $i$. Call this hypothesis (F).

**Lemma (First step).** Under (F), $\Psi_t(h, h) = 0$ for all $h \in H$ and $t \in O$.

Lean: `New.Selmer.SelmerDatum.mirrorForm_self_eq_zero` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Let $g = \gamma_0 h$. The values $z(\gamma_0)$, $z(\gamma_0^c)$, $y(\gamma_0)$ and $y(\gamma_0^c)$ are $0$, and $\gamma_0, \gamma_0^c$ act trivially on $W_a$. The cocycle rule for $z$ and additivity of $y$ on $U$ give $\Psi_t(g, g) = \Psi_t(h, h)$. The function $u \mapsto \Psi_t(u, u)$ is locally constant. So there is a neighbourhood of $g$ on which it is constant and which lies in $U \cap U^c$. Take a new prime $P$ with data $l$, $P, \bar P \notin R$, and $\varphi$ in that neighbourhood. By (F) there is $z'$ with $z'(\gamma) = z(\varphi)$ and $z'((\gamma^c)^{-1}) = z((\varphi^c)^{-1}) = -z(\varphi^c)$, since $\varphi^c$ acts trivially. So
$$\Psi_t(h, h) = \Psi_t(\varphi, \varphi) = y(\varphi)(t\, z'(\gamma)) + y(\varphi^c)(t\, z'((\gamma^c)^{-1})),$$
which is $0$ by reciprocity at $P$ and $\bar P$. $\square$

**Lemma.** Under (F), $\Psi_t(h, h') + \Psi_t(h', h) = 0$ for $h, h' \in H$.

Lean: `New.Selmer.SelmerDatum.mirrorForm_add_swap_eq_zero` (New/Congruences/Selmer/Mirror.lean).

*Proof.* On $H$, $z$ and $y$ are additive, so $\Psi_t$ is biadditive on $H \times H$. Expand $\Psi_t(h h', h h') = 0$ and use $\Psi_t(h, h) = \Psi_t(h', h') = 0$. $\square$

**Lemma.** Let $z$ be a cocycle with values in $W_a$, and $h, h^c \in U$. Then
$$\Psi_t(\gamma_* h \gamma_*^{-1}, h') = \Psi_{\zeta t}(h, h'), \qquad \Psi_{\zeta t}(h', \gamma_* h \gamma_*^{-1}) = \Psi_t(h', h).$$

Lean: `New.Selmer.SelmerDatum.mirrorForm_conj_γ_left`, `New.Selmer.SelmerDatum.mirrorForm_conj_γ_right` (New/Congruences/Selmer/Mirror.lean).

*Proof.* As $h$ acts trivially, $z(\gamma_* h \gamma_*^{-1}) = \rho(\gamma_*) z(h) = \zeta z(h)$. The conjugate of $\gamma_* h \gamma_*^{-1}$ is $\gamma_*^c h^c (\gamma_*^c)^{-1}$, and $\gamma_*^c$ acts by $\zeta^{-1}$ with $\mathrm{cyc}(\gamma_*^c) = 1$. The equivariance of $y$ then gives $y((\gamma_* h \gamma_*^{-1})^c)(b) = y(h^c)(\zeta b)$ and $y(\gamma_* h \gamma_*^{-1})(\zeta b) = y(h)(b)$. In the same way $\zeta\, z((\gamma_* h \gamma_*^{-1})^c) = z(h^c)$. Put these into the definition of $\Psi$. $\square$

**Lemma (Second step).** Under (F), $\Psi_t(h, h') = 0$ for all $h, h' \in H$ and $t \in O$.

Lean: `New.Selmer.SelmerDatum.mirrorForm_eq_zero` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Since $\zeta^2 - 1$ is a unit, write $t = (\zeta^2 - 1) s$. Antisymmetry at $(h, h')$ gives $\Psi_s(h, h') + \Psi_s(h', h) = 0$. Antisymmetry at $(\gamma_* h \gamma_*^{-1}, h')$ with parameter $\zeta s$, together with the last lemma, gives $\Psi_{\zeta^2 s}(h, h') + \Psi_s(h', h) = 0$. Subtract: $\Psi_{\zeta^2 s}(h, h') - \Psi_s(h, h') = 0$. The left side is $\Psi_t(h, h')$, since $\Psi$ is additive in $t$. $\square$

### The map $\eta$

**Lemma.** A character $f$ of an $O$-module $X$ that kills all multiples $t u$ of the members $u$ of a spanning set is $0$.

Lean: `New.Selmer.characterModule_eq_zero_of_span` (New/Congruences/Selmer/Mirror.lean).

*Proof.* The set of $u$ with $f(t u) = 0$ for all $t$ is a submodule. It contains the spanning set, so it is everything. $\square$

**Lemma (Third step).** Under (F), if $z(H)$ spans $W_a$, there is an $O$-linear $\eta : W_a \to W_a^*$ with $\eta(z(h)) = y(h^c)$ for all $h \in H$.

Lean: `New.Selmer.SelmerDatum.exists_linearMap_apply_eq_dualSelmer_conj` (New/Congruences/Selmer/Mirror.lean).

*Proof.* Let $\pi$ and $\theta$ be the maps from the free module $O^{(H)}$ that send the basis vector $e_h$ to $z(h)$ and to $y(h^c)$. The map $\pi$ is onto. By the second step and linearity, $\theta(\alpha)(t\, z(h'^c)) = y(h')(t\, \pi(\alpha))$ for $h' \in H$. If $\pi(\alpha) = 0$, then $\theta(\alpha)$ kills all $t\, z(h'^c)$ with $h' \in H$. Since $H$ is stable under $c$, these elements are the multiples of $z(H)$, which spans. So $\theta(\alpha) = 0$ by the last lemma. Hence $\theta$ factors through $\pi$, and the factor is $\eta$. $\square$

**Lemma.** Let $z$ be a cocycle with $z(H)$ spanning $W_a$, and $\eta$ linear with $\eta(z(h)) = y(h^c)$ on $H$. Then $\eta \in \mathrm{Hom}_G(W_a, W_a^{*c})$: $\eta(\rho(g) u)(m) = \eta(u)(\mathrm{cyc}(g^c)\, \rho((g^c)^{-1}) m)$.

Lean: `New.Selmer.SelmerDatum.mem_conjDualHom_of_apply_eq` (New/Congruences/Selmer/Mirror.lean).

*Proof.* It suffices to take $u = z(h)$ with $h \in H$. As $h$ acts trivially, $\rho(g) z(h) = z(g h g^{-1})$, and $g h g^{-1} \in H$. So $\eta(\rho(g) z(h)) = y(g^c h^c (g^c)^{-1})$. Since $h^c \in U$, the equivariance of $y$ turns this into $y(h^c)(\mathrm{cyc}(g^c)\, \rho((g^c)^{-1}) m) = \eta(z(h))(\ldots)$. $\square$

**Theorem (The mirror bound).** Let $z \in \mathrm{Sel}(J)$ have a value with a unit coordinate, and let (F) hold. Then for all $A$ and $R$,
$$\mathrm{len}\, \mathrm{Sel}^*(J) \leq \mathrm{glob}(T).$$

Lean: `New.Selmer.SelmerDatum.length_dualSelmer_le` (New/Congruences/Selmer/Mirror.lean).

*Proof.* The class $z$ vanishes at $\gamma_*$, so by the spanning lemma of [Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma) $z(H)$ spans $W_a$. For each $y$, the third step gives $\eta_y$, and the last lemma puts it in $\mathrm{Hom}_G(W_a, W_a^{*c})$. Since $z(H)$ spans, $\eta_y$ is unique, so $y \mapsto \eta_y$ is $O$-linear. It is injective: if $\eta_y = 0$, then $y(h) = \eta_y(z(h^c)) = 0$ for $h \in H$, so $y = 0$ by Sah for the dual group. Hence $\mathrm{len}\, \mathrm{Sel}^*(J) \leq \mathrm{len}\, \mathrm{Hom}_G(W_a, W_a^{*c}) \leq \mathrm{glob}(T)$, as $a \neq 0$. $\square$

**Remark (Formalization).** The map $y \mapsto \eta_y$ is built with `choose`. Linearity holds because two linear maps that agree on the spanning set $z(H)$ are equal, so the choice does not matter. Hypothesis (F) quantifies over all new auxiliary primes, with no bound on $R$. The proof uses it only at one prime, chosen near $\gamma_0 h$ and outside $R$. The next sections show how the descent makes (F) true: when (F) fails at some $P$, adding $P$ to $J$ makes the tied Selmer groups shorter.
