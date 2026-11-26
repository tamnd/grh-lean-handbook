---
title: The Greenberg-Wiles count
lean:
  - New/Congruences/Selmer/Count.lean
decls:
  - New.Selmer.SelmerDatum.smul_eq_self_of_reduceModPow_eq_one
  - New.Selmer.SelmerDatum.reductionModule
  - New.Selmer.SelmerDatum.reductionKer
  - New.Selmer.SelmerDatum.mem_reductionKer_of_mem_sahGroup
  - New.Selmer.SelmerDatum.mem_reductionKer_of_mem_inertiaAbove
  - New.Selmer.SelmerDatum.mem_obeying_tieRelations_iff
  - New.Selmer.SelmerDatum.coboundary_mem_obeying_tieRelations
  - New.Selmer.SelmerDatum.coboundary_mem_selmerModule
  - New.Selmer.SelmerDatum.apply_first_tameGenerator_eq_zero_of_mem_tiedSelmer
  - New.Selmer.SelmerDatum.mem_selmerModule_erase
  - New.Selmer.SelmerDatum.tiedSetting
  - New.Selmer.SelmerDatum.mem_cocycles_tiedSetting
  - New.Selmer.SelmerDatum.tiedSetting_avoids
  - New.Selmer.SelmerDatum.dualSelmer
  - New.Selmer.SelmerDatum.exists_length_localCocycles_tied_le
  - New.Selmer.SelmerDatum.length_add_length_tiedSelmer_le
  - New.Selmer.SelmerDatum.exists_length_cocycles_le
  - New.Selmer.SelmerDatum.sum_length_localCocycles_placesDividing_le
  - New.Selmer.SelmerDatum.sum_length_localCocycles_placeOver_le
  - New.Selmer.SelmerDatum.exists_sum_length_localCocycles_tied_le
  - New.Selmer.SelmerDatum.exists_length_tiedSelmer_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Greenberg-Wiles count

This section proves that the tied Selmer group is no longer than its dual plus the local terms at the places of $S$ prime to $\ell$, by the Greenberg-Wiles count of Volume 3. All results are in [Count.lean](lean:New/Congruences/Selmer/Count.lean#L1).

Background used: relation settings, the module of relations off a set $T'$ of primes, avoidable numbers, and the count `New.RelationSetting.exists_card_cocycles_le`, from [relations in place of the dual Selmer group](/chapter/local-duality/#relations-in-place-of-the-dual-selmer-group). A cocycle with values in a module killed by $\ell^M$ that vanishes at the tame generator of a prime $v$ (or of $\bar v$) is unramified at $v$, and if it also vanishes at the Frobenius element it vanishes on the decomposition group (`New.Selmer.exists_conj_side_detects`, in the file TameSelmerCocycles of [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula)).

### The textbook form

Let $K$ be a number field, $W$ a finite Galois module, $\mathcal{L} = (L_v)$ local conditions at a finite set $S$ of places that contains the places above $\#W$ and the infinite places, and $\mathcal{L}^*$ the dual conditions on $W^*$. The Greenberg-Wiles formula (Darmon, Diamond and Taylor, *Fermat's Last Theorem*, Theorem 2.19) says
$$\frac{\#H^1_{\mathcal{L}}(K, W)}{\#H^1_{\mathcal{L}^*}(K, W^*)} = \frac{\#H^0(K, W)}{\#H^0(K, W^*)} \prod_{v \in S} \frac{\#L_v}{\#H^0(K_v, W)}.$$
The source uses a cocycle form as an inequality, with the dual Selmer group replaced by a module of relations at split primes. For a totally complex field with $r_2$ complex places, a relation setting $D$ with primes $S'$, local cocycle modules $A_v$ and an element $\sigma$ that is central modulo the subgroup $U$ of $D$, has cyclotomic character $1$ and fixes no nonzero vector, the count gives a finite set $R$ of primes, avoiding a given number, with
$$\#Z(\emptyset) \cdot \#W^{\#S' + r_2} \leq \#\mathrm{relations}(R) \cdot \#W \cdot \prod_{v \in S'} \#A_v.$$

### The setting

Fix tied primes $(J, x)$ with first prime $P_0$, levels $M < N$, and $a \mid \ell^M$. Let $U_i(g)$ mean that $g$ acts trivially on $T/\ell^M$; this is the hypothesis `hV` of all results below.

**Lemma.** If $g$ acts trivially on $T/\ell^M$, it acts trivially on $W_a$ for $a \mid \ell^M$.

Lean: `New.Selmer.SelmerDatum.smul_eq_self_of_reduceModPow_eq_one` (New/Congruences/Selmer/Count.lean).

*Proof.* The action on $W_a$ factors through the action on $T/\ell^M$, since $\ell^M$ kills $O/a$. $\square$

**Definition.** $W_a$ with the discrete topology is a discrete Galois module (`reductionModule`). The subgroup $U = U_{M, N}$ is the kernel of the action on $T/\ell^M$ and of the cyclotomic character modulo $\ell^N$. It is open and normal.

Lean: `New.Selmer.SelmerDatum.reductionModule`, `New.Selmer.SelmerDatum.reductionKer` (New/Congruences/Selmer/Count.lean).

**Lemma.** The Sah group $H$ lies in $U$. The inertia groups above places outside $S$ lie in $U$.

Lean: `New.Selmer.SelmerDatum.mem_reductionKer_of_mem_sahGroup`, `New.Selmer.SelmerDatum.mem_reductionKer_of_mem_inertiaAbove` (New/Congruences/Selmer/Count.lean).

*Proof.* On $H$ the action is trivial and every character is trivial, by the lemmas on $H$ of [Selmer data, tied Selmer groups and Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma). Inertia outside $S$ acts trivially on $T$, and since $S$ contains the places above $\ell$, the cyclotomic character is $1$ on it. $\square$

**Lemma.** A function $c$ obeys the ties of index $i$ on $J$ if and only if $c(\iota_b(\gamma_v)) = s_v(i)\, c(\iota_b(\varphi_v))$ for all $v \in J$ and both $b$.

Lean: `New.Selmer.SelmerDatum.mem_obeying_tieRelations_iff` (New/Congruences/Selmer/Count.lean).

*Proof.* This is the definition of the tie relations, with $f(g) = 1$ at $\iota_b(\gamma_v)$ and $-s_v(i)$ at $\iota_b(\varphi_v)$. $\square$

**Lemma.** For $b \in W_a$ the coboundary $g \mapsto \rho(g) b - b$ obeys the ties on $J$. It lies in $\mathrm{Sel}(\rho, S, T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i), O/a)$.

Lean: `New.Selmer.SelmerDatum.coboundary_mem_obeying_tieRelations`, `New.Selmer.SelmerDatum.coboundary_mem_selmerModule` (New/Congruences/Selmer/Count.lean).

*Proof.* The elements $\iota_b(\gamma_v)$ lie in inertia groups above $v$ or $\bar v$, which are outside $S_0 \supseteq S$, so $\rho(\iota_b(\gamma_v)) = 1$ and the coboundary is $0$ there. If $s_v(i) = 0$ the tie says that this value is $0$. If $s_v(i) \neq 0$, condition 6 of tied primes gives $U_i$ at $\iota_b(\varphi_v)$, so $\iota_b(\varphi_v)$ fixes $W_a$ and the coboundary is $0$ there too. The coboundary is a locally constant cocycle, is unramified outside $S$, and obeys the local relations by the lemma of the previous section. $\square$

**Lemma.** Every $z \in \mathrm{Sel}^R_J(x, i, a)$ vanishes at $\iota_b(\gamma_{P_0})$ for both $b$. If $a \mid \ell^M$, then $z$ is unramified at $P_0$ and $\bar P_0$: it lies in the Selmer module for the places $S \cup R' \cup \bar R'$ with $R' = R \setminus \{P_0\}$.

Lean: `New.Selmer.SelmerDatum.apply_first_tameGenerator_eq_zero_of_mem_tiedSelmer`, `New.Selmer.SelmerDatum.mem_selmerModule_erase` (New/Congruences/Selmer/Count.lean).

*Proof.* The slope at $P_0$ is $0$, so the tie reads $z(\iota_b(\gamma_{P_0})) = 0$. The place $P_0$ is outside $S$, so $\rho$ is unramified at $P_0$ and $\bar P_0$. The detection lemma `exists_conj_side_detects` gives a side $b$ such that vanishing at $\iota_b(\gamma_{P_0})$ makes $z$ zero on the inertia groups above $P_0$, or above $\bar P_0$, as needed. $\square$

**Definition (Tied setting).** The relation setting $D = \mathrm{tiedSetting}$ for the module $W_a$ and $m = \ell^N$ has the subgroup $U_{M, N}$, the local primes $S' = S \cup I \cup \bar I$ with $I = J \setminus \{P_0\}$, chosen places $A_v$ above each $v$, and as allowed local cocycles at $v$ the module $\mathrm{Loc}(\rho, T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i), A_v, O/a)$. The two conditions on complex conjugations hold because $E$ is totally complex.

Lean: `New.Selmer.SelmerDatum.tiedSetting` (New/Congruences/Selmer/Count.lean).

The setting needs $\ell^N$ to kill $W_a$, which holds since $a \mid \ell^M$ and $M < N$. Its allowed local cocycles contain the coboundaries by the coboundary lemma.

**Lemma.** Let $c$ be in a Selmer module $\mathrm{Sel}(\rho, S'', K, O/a)$ with $T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i) \subseteq K$ and $S'' \subseteq S' \cup P$. Then $c$ lies in the group $Z(P)$ of the tied setting.

Lean: `New.Selmer.SelmerDatum.mem_cocycles_tiedSetting` (New/Congruences/Selmer/Count.lean).

*Proof.* This is `mem_selmerZ1_of_mem_selmerModule` of the previous section. $\square$

**Lemma.** The norm $q_0$ of $P_0$ can be avoided in the tied setting.

Lean: `New.Selmer.SelmerDatum.tiedSetting_avoids` (New/Congruences/Selmer/Count.lean).

*Proof.* Since $q_0 \equiv 1 \bmod \ell^N$, it is prime to $\ell^N$. By condition 5 of tied primes no place of $S_0 \supseteq S$ and no $v \in I$ divides $q_0$. The conjugate of a place that divides $q_0$ divides $q_0$, so no place of $\bar I$ divides it either. The primes above $q_0$ are outside $S$, so their inertia groups lie in $U$ by the lemma above. $\square$

**Definition (Dual Selmer group).** For a finite set $R$ of primes, $\mathrm{Sel}^*(J) = D.\mathrm{relations}(R \setminus \{P_0, \bar P_0\})$.

Lean: `New.Selmer.SelmerDatum.dualSelmer` (New/Congruences/Selmer/Count.lean).

A member $y$ is a locally constant function $G \to W_a^*$ that is $0$ outside $U$, a homomorphism on $U$, equivariant up to the cyclotomic character, zero on inertia above primes outside $R \setminus \{P_0, \bar P_0\}$, and satisfies $\sum_j y(\varphi_j)(z(\gamma_j)) = 0$ for split primes $p_j$ outside that set and $z \in Z(\{p_j\})$. Removing $P_0$ and $\bar P_0$ from $R$ is what lets [reciprocity at conjugate primes](/chapter/tied-selmer-groups/#reciprocity-at-conjugate-primes) use the Frobenius elements near $\gamma_0$.

**Remark (Formalization).** The dual Selmer group is not a group of dual cocycles. It is the module of relations of Volume 3, with the reciprocity law as part of the definition. The places $A_v$ and the set $R$ are chosen by an existence statement, so the bound below holds for some $A$ and $R$. The bound of the next section holds for all $A$ and $R$, so the choice does no harm.

### The local terms

**Lemma (Ties cut the auxiliary terms).** Let $v \in S \cup J \cup \bar J$ with $v \notin S$. For a suitable place $B$ above $v$,
$$\mathrm{len}\, \mathrm{Loc}(\rho, T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i), B, O/a) \leq \mathrm{len}\, W_a.$$

Lean: `New.Selmer.SelmerDatum.exists_length_localCocycles_tied_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Write $v = w$ or $v = \bar w$ with $w \in J$. The detection lemma gives a side $b$ and a place $B$ above $v$ such that a cocycle that vanishes at $\iota_b(\gamma_w)$ is unramified at $v$, and one that also vanishes at $\iota_b(\varphi_w)$ is zero on $D_B$. Let $c$ be a global cocycle that obeys the ties, with $c(\iota_b(\varphi_w)) = 0$. The tie gives $c(\iota_b(\gamma_w)) = s_w(i) \cdot 0 = 0$. So $c$ vanishes on $D_B$. Hence the restriction to $D_B$ is determined by the value at $\iota_b(\varphi_w)$, which is a vector of $W_a$. $\square$

The textbook local term at an auxiliary prime with trivial action is $\#Z^1(D_v, W) = \#W^2$. The tie halves it, which cancels the factor $\#W$ that each new prime of $S'$ brings to the left side of the count.

**Lemma.** $\sum_{w \mid \ell} \mathrm{len}\, \mathrm{Loc}(\rho, T.\mathrm{localRelations}, A_w, O/a) \leq (\#\{w \mid \ell\} + r_\infty)\, \mathrm{len}\, W_a$.

Lean: `New.Selmer.SelmerDatum.sum_length_localCocycles_placesDividing_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Each term is at most $\mathrm{rk}(Z_w)\, \mathrm{len}(O/a)$, by the rank bound of the previous section. Sum, use condition 3 of a Selmer datum, and use $\mathrm{len}\, W_a = n\, \mathrm{len}(O/a)$. $\square$

**Lemma.** For $a \neq 0$, $\sum_{v \in S} \mathrm{len}\, \mathrm{Loc}(\rho, T.\mathrm{localRelations}, A_v, O/a) \leq (\#S + r_\infty)\, \mathrm{len}\, W_a + \mathrm{places}(T)$.

Lean: `New.Selmer.SelmerDatum.sum_length_localCocycles_placeOver_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Split $S$ into the places above $\ell$ and the others. The first part is the previous lemma. At $v \nmid \ell$, dropping the relations gives a larger module, whose length is at most $\mathrm{len}\, W_a + \mathrm{loc}_v(\rho)$ by the definition of $\mathrm{loc}_v$ as a supremum over $a \neq 0$. $\square$

**Lemma.** For suitable places $A_v$,
$$\sum_{v \in S'} \mathrm{len}\, \mathrm{Loc}(\rho, T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i), A_v, O/a) \leq (\#S' + r_\infty)\, \mathrm{len}\, W_a + \mathrm{places}(T).$$

Lean: `New.Selmer.SelmerDatum.exists_sum_length_localCocycles_tied_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Choose $A_v = $ `placeOver v` for $v \in S$, and the place $B$ of the tie lemma for $v \in S' \setminus S$. On $S$ the ties only shrink the modules, so the previous lemma applies. Each place of $S' \setminus S$ adds at most $\mathrm{len}\, W_a$. $\square$

### The count

**Lemma.** $\mathrm{len}\, W_a + \mathrm{len}\, \mathrm{Sel}(J) \leq \mathrm{len}\, Z(\emptyset)$, where $Z(\emptyset)$ is the group of the tied setting.

Lean: `New.Selmer.SelmerDatum.length_add_length_tiedSelmer_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Let $\mathrm{ev}(c) = c(\gamma_*)$ on $Z(\emptyset)$. It is onto $W_a$: every $y = (\zeta - 1) b$ is the value at $\gamma_*$ of the coboundary of $b$, which lies in $Z(\emptyset)$. Each $z \in \mathrm{Sel}(J)$ lies in $Z(\emptyset)$, since it is unramified at $P_0$ and $\bar P_0$, and it lies in the kernel of $\mathrm{ev}$. So $\mathrm{len}\, Z(\emptyset) = \mathrm{len}\, W_a + \mathrm{len}\, \ker \mathrm{ev} \geq \mathrm{len}\, W_a + \mathrm{len}\, \mathrm{Sel}(J)$. $\square$

**Lemma (A case of the Greenberg-Wiles inequality).** For some finite set $R$,
$$\mathrm{len}\, Z(\emptyset) + (\#S' + r_\infty)\, \mathrm{len}\, W_a \leq \mathrm{len}\, \mathrm{Sel}^*(J) + \mathrm{len}\, W_a + \sum_{v \in S'} \mathrm{len}\, \mathrm{Loc}(\rho, T.\mathrm{localRelations} \cup \mathrm{tie}(J, x, i), A_v, O/a).$$

Lean: `New.Selmer.SelmerDatum.exists_length_cocycles_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Apply the count of Volume 3 with $\sigma = \gamma_*$ and the avoidable number $q_0$. The hypotheses hold: $\mathrm{cyc}(\gamma_*) = 1$, since $\gamma_*$ is inertial at a place prime to $\ell$; $[\gamma_*, g] \in H \subseteq U$; and $\gamma_*$ fixes no nonzero vector, since $\rho(\gamma_*) - 1 = \zeta - 1$ is a unit. The set $R$ avoids $q_0$, so $P_0, \bar P_0 \notin R$ and $R \setminus \{P_0, \bar P_0\} = R$. The count is an inequality of orders of finite modules. The length of a finite $O$-module is the exponent of $\#k$ in its order, so the inequality of orders is an inequality of lengths. Finally $A_v$ in the count is the intersection of the allowed module with all local cocycles, which is no longer than the allowed module. $\square$

**Theorem (The count).** For suitable places $A$ and a finite set $R$ of primes,
$$\mathrm{len}\, \mathrm{Sel}(J) \leq \mathrm{len}\, \mathrm{Sel}^*(J) + \mathrm{places}(T).$$

Lean: `New.Selmer.SelmerDatum.exists_length_tiedSelmer_le` (New/Congruences/Selmer/Count.lean).

*Proof.* Put $d = \#S' + r_\infty$ and $L = \mathrm{len}\, W_a$, which is finite. By the last three lemmas,
$$L + dL + \mathrm{len}\, \mathrm{Sel}(J) \leq \mathrm{len}\, Z(\emptyset) + dL \leq \mathrm{len}\, \mathrm{Sel}^*(J) + L + dL + \mathrm{places}(T).$$
Cancel the finite number $L + dL$. $\square$
