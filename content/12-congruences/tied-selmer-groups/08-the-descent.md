---
title: The descent
lean:
  - New/Congruences/Selmer/Descent.lean
decls:
  - New.Selmer.tilting
  - New.Selmer.exists_injective_quotSpan_onto_torsion
  - New.Selmer.isUnit_of_pow_smul_ne_zero
  - New.Selmer.exists_length_selmerModule_pow_le
  - New.Selmer.exists_unit_residue_notMem
  - New.Selmer.sum_lt_sum_of_ne_top
  - New.Selmer.exists_isTiedPrimes_singleton
  - New.Selmer.SelmerDatum.finite_tiedSelmer
  - New.Selmer.SelmerDatum.selmerModule_inf_ker_le
  - New.Selmer.SelmerDatum.tiedSelmer_le_of_slope_eq_zero
  - New.Selmer.SelmerDatum.tiedSelmer_insert_inf_ker_le
  - New.Selmer.SelmerDatum.tiedSelmer_update_le
  - New.Selmer.SelmerDatum.exists_length_tiedSelmer_insert_le
  - New.Selmer.SelmerDatum.length_tiedSelmer_le_of_isUnit
  - New.Selmer.SelmerDatum.length_tiedSelmer_pow_le
  - New.Selmer.totalTiedLength
  - New.Selmer.exists_slope_totalTiedLength_lt
  - New.Selmer.exists_isTiedPrimes_length_tiedSelmer_le
  - New.Selmer.exists_totalTiedLength_le
  - New.Selmer.exists_isTiedPrimes_card_le_and_length_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The descent

Start from the first prime alone. While some new auxiliary prime $P$ has a class outside the image (F) of the [mirror](/chapter/tied-selmer-groups/#reciprocity-at-conjugate-primes), add $P$ with a unit slope; the total length drops. When no prime can be added, the count and the mirror bound every tied group by $\mathrm{glob} + \mathrm{places}$. All results are in [Descent.lean](lean:New/Congruences/Selmer/Descent.lean#L1).

Background used: if $f$ identifies $O/a$ with the $a$-torsion of $B$, the Selmer module with values in $O/a$ has the length of the $a$-torsion of the one with values in $B$ (`New.Selmer.length_torsionBy_selmerModule`, file DivisibleSelmerModules); a cocycle in $\mathrm{Sel}(\rho, S, L)$ that vanishes on inertia above $S \setminus S'$ lies in $\mathrm{Sel}(\rho, S', K)$ for $K \subseteq L$ (`New.Selmer.mem_selmerModule_of_eq_zero_on_inertiaAbove`, file TameSelmerCocycles). Both files belong to [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula).

### The textbook form

Lowering Selmer groups modulo $\ell^n$ by local conditions at Chebotarev primes is known; the source cites Mazur and Rubin, Diophantine stability (2018), and Fakhruddin, Khare and Patrikis, Relative deformation theory, relative Selmer groups, and lifting irreducible Galois representations (2021). The source's form is below.

### Tilting

**Lemma (Tilting).** Let $O$ be a discrete valuation ring, $\mathrm{ev}_\gamma, \mathrm{ev}_\varphi : B \to (O/I)^m$ linear, and $C \subseteq B$. Off at most $m$ residues of $a$,
$$\mathrm{len}\big(C \cap \ker(a\, \mathrm{ev}_\gamma - \mathrm{ev}_\varphi)\big) \leq \mathrm{len}\big(C \cap \ker \mathrm{ev}_\gamma \cap \mathrm{ev}_\varphi^{-1}(\mathrm{ev}_\gamma C)\big).$$

Lean: `New.Selmer.tilting` (New/Congruences/Selmer/Descent.lean).

*Proof.* Let $C' = \sum_a C \cap \ker(a\,\mathrm{ev}_\gamma - \mathrm{ev}_\varphi)$. If $a\,\mathrm{ev}_\gamma(z) = \mathrm{ev}_\varphi(z)$ then $\mathrm{ev}_\varphi(z) = \mathrm{ev}_\gamma(az)$, so $\mathrm{ev}_\varphi C' \subseteq \mathrm{ev}_\gamma C'$. Let $\Lambda \subseteq O^m$ be the preimage of $\mathrm{ev}_\gamma C'$, free of rank at most $m$, with $\pi : \Lambda \to \mathrm{ev}_\gamma C'$ onto. By projectivity choose $\sigma : \Lambda \to C'$ with $\mathrm{ev}_\gamma \sigma = \pi$, and $U : \Lambda \to \Lambda$ with $\pi U = \mathrm{ev}_\varphi \sigma$. Let the bad residues be the residual roots of the characteristic polynomial of $U$; there are at most $m$. Off them $a - U$ is bijective, so $(a\,\mathrm{ev}_\gamma - \mathrm{ev}_\varphi)\sigma = \pi(a - U)$ maps onto $\mathrm{ev}_\gamma C'$. Every map splits $\mathrm{len}\, C'$ into image plus kernel. The image of $a\,\mathrm{ev}_\gamma - \mathrm{ev}_\varphi$ on $C'$ is no shorter than that of $\mathrm{ev}_\gamma$, so its kernel is no longer than $C' \cap \ker \mathrm{ev}_\gamma$, which lies in the right side. Cancel the finite image length. $\square$

### Levels

**Lemma.** For $a, c \neq 0$, multiplication by $c$ identifies $O/a$ with the $a$-torsion of $O/ac$. An element of $O/\varpi^{i+1}$ not killed by $\varpi^i$ is a unit.

Lean: `New.Selmer.exists_injective_quotSpan_onto_torsion`, `New.Selmer.isUnit_of_pow_smul_ne_zero` (New/Congruences/Selmer/Descent.lean).

*Proof.* If $ac \mid as$ then $c \mid s$. If $s$ is in the maximal ideal $(\varpi)$, then $\varpi^{i+1} \mid \varpi^i s$. $\square$

**Lemma (Passage to the exponent).** For some $i \leq k$, $\mathrm{len}\,\mathrm{Sel}(O/\varpi^k) \leq \mathrm{len}\,\mathrm{Sel}(O/\varpi^i)$, and if $i \neq 0$ some member of $\mathrm{Sel}(O/\varpi^i)$ has a value with a unit coordinate.

Lean: `New.Selmer.exists_length_selmerModule_pow_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* Let $\varpi^i$ be the exponent of $\mathrm{Sel}(O/\varpi^k)$, the least $i$ with $\varpi^i \mathrm{Sel} = 0$. The whole module is its $\varpi^i$-torsion, which has the length of $\mathrm{Sel}(O/\varpi^i)$ by the first part of the last lemma and the background. If $i = m + 1$, some $z$ has $\varpi^m z \neq 0$; it comes from $\mathrm{Sel}(O/\varpi^i)$, and a value with $\varpi^m z(g)_j \neq 0$ is a unit. $\square$

### Adding a prime

**Lemma.** Tied Selmer groups modulo $a \mid \ell^M$ are finite. A cocycle of $\mathrm{Sel}(\rho, T.\mathrm{places} \cup J \cup \bar J, L)$ that vanishes at $\gamma_v$ and $\iota_{\mathrm{false}}(\gamma_v)$ for $v \in J \setminus R$ is unramified outside $T.\mathrm{places} \cup R \cup \bar R$. So if all slopes of datum $i$ are $0$, then $\mathrm{Sel}(J) \subseteq \mathrm{Sel}(\emptyset)$. If $P$ is new auxiliary and a member of $\mathrm{Sel}^P(J)$ vanishes at $\gamma$ and $\iota_{\mathrm{false}}(\gamma)$ for $\gamma = \gamma_P$, it lies in $\mathrm{Sel}(J)$.

Lean: `New.Selmer.SelmerDatum.finite_tiedSelmer`, `New.Selmer.SelmerDatum.selmerModule_inf_ker_le`, `New.Selmer.SelmerDatum.tiedSelmer_le_of_slope_eq_zero`, `New.Selmer.SelmerDatum.tiedSelmer_insert_inf_ker_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* Finiteness is `New.Selmer.finite_selmerModule` of [one system](/chapter/tied-selmer-groups/#one-system-for-all-twists). For the second claim, let $v \notin T.\mathrm{places}$ be $w$ or $\bar w$ with $w \in J \setminus R$. $\rho$ is trivial on inertia at $v$, and by `New.Selmer.exists_conj_side_detects` a cocycle that vanishes at the tame generator on the side of $v$ vanishes on inertia at $v$. The background lemma finishes. Slope $0$ makes the ties read $z(\gamma_v) = 0$; take $R = \emptyset$. For the last claim, $J \cup \{P\}$ with slope $0$ at $P$ is tied by `New.Selmer.IsTiedPrimes.insert_of_isNewAuxiliaryPrime`; take $R = J$. $\square$

**Lemma.** If $P \notin J$, a member $z$ of $\mathrm{Sel}(J \cup \{P\})$ with slopes $s$ at $P$ lies in $\mathrm{Sel}^P(J)$ and $\mathrm{ev}_\gamma z = s_j\, \mathrm{ev}_\varphi z$, where $\mathrm{ev}_g z = (z(g), z(\iota_{\mathrm{false}}(g)))$.

Lean: `New.Selmer.SelmerDatum.tiedSelmer_update_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* The ties at $J$ are unchanged by the update at $P \notin J$. The tie at $P$ is the second claim. $\square$

**Lemma.** Let $P$ with data $l$ be new auxiliary for datum $i$ and $a \mid \ell^M$. For units $u$ off at most $2 \cdot \mathrm{rank}\, T$ residues, adding $P$ with slope $u^{-1}$ gives
$$\mathrm{len}\, \mathrm{Sel}(J \cup \{P\}) \leq \mathrm{len}\big(\mathrm{Sel}(J) \cap \mathrm{F}(J, P)\big).$$

Lean: `New.Selmer.SelmerDatum.exists_length_tiedSelmer_insert_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* Apply tilting to $C = \mathrm{Sel}^P(J)$, $\mathrm{ev}_\gamma$, $\mathrm{ev}_\varphi$ with $m = 2n$. The tie with slope $u^{-1}$ says $u\,\mathrm{ev}_\gamma = \mathrm{ev}_\varphi$. By the last two lemmas, the new group is $C \cap \ker(u\,\mathrm{ev}_\gamma - \mathrm{ev}_\varphi)$, and $C \cap \ker \mathrm{ev}_\gamma \cap \mathrm{ev}_\varphi^{-1}(\mathrm{ev}_\gamma C)$ is $\mathrm{Sel}(J) \cap \mathrm{F}(J, P)$. $\square$

### The end of the descent

**Lemma.** Let $V_i(g)$ mean $\rho(g) \equiv 1 \bmod \ell^M$, $M < N$, $a \mid \ell^M$. If some $z \in \mathrm{Sel}(J)$ has a unit coordinate and $\mathrm{Sel}(J) \subseteq \mathrm{F}(J, P)$ for every new auxiliary $P$, then $\mathrm{len}\,\mathrm{Sel}(J) \leq \mathrm{glob}(T) + \mathrm{places}(T)$. The same bound holds modulo $\varpi^e \mid \ell^M$ if the inclusions hold modulo $\varpi^k$ for $1 \leq k \leq e$.

Lean: `New.Selmer.SelmerDatum.length_tiedSelmer_le_of_isUnit`, `New.Selmer.SelmerDatum.length_tiedSelmer_pow_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* The [count](/chapter/tied-selmer-groups/#the-greenberg-wiles-count) gives $\mathrm{len}\,\mathrm{Sel}(J) \leq \mathrm{len}\,\mathrm{Sel}^*(J) + \mathrm{places}(T)$, and the mirror bound gives $\mathrm{len}\,\mathrm{Sel}^*(J) \leq \mathrm{glob}(T)$. For the second claim pass to the exponent $\varpi^k$, $k \leq e$. If $k = 0$ the group is $0$. Otherwise it has a unit value, and the first claim applies at $a = \varpi^k$. $\square$

### The loop

**Definition.** $\mathrm{tot}(J, x) = \sum_i \sum_{k=1}^{e} \mathrm{len}\, \mathrm{Sel}_i(J) \bmod \varpi^k$.

Lean: `New.Selmer.totalTiedLength` (New/Congruences/Selmer/Descent.lean).

**Lemma.** A set of fewer than $q - 1$ residues, $q = \#k$, misses the residue of a unit. In $\mathbb{N} \cup \{\infty\}$, if $f \leq g$ on $s$, $g$ is finite and $f(b) < g(b)$ for one $b \in s$, then $\sum_s f < \sum_s g$.

Lean: `New.Selmer.exists_unit_residue_notMem`, `New.Selmer.sum_lt_sum_of_ne_top` (New/Congruences/Selmer/Descent.lean).

*Proof.* There are $q - 1$ nonzero residues. Split off $b$. $\square$

**Lemma (One step).** Let $\#k > 2 \cdot \mathrm{rank}(T_i) \cdot e + 1$, and let $P$ be new auxiliary for $i$ with $\mathrm{Sel}_i(J) \not\subseteq \mathrm{F}(J, P)$ modulo some $\varpi^k$, $1 \leq k \leq e$. Then for some unit $s$, adding $P$ with slope $s$ for $i$ and $0$ for the other data lowers $\mathrm{tot}$.

Lean: `New.Selmer.exists_slope_totalTiedLength_lt` (New/Congruences/Selmer/Descent.lean).

*Proof.* The bad residues of all levels number at most $2\,\mathrm{rank}(T_i)\, e$, so a unit $u$ avoids them. Take $s = u^{-1}$. For datum $i$ the new groups are no longer than $\mathrm{Sel}_i(J) \cap \mathrm{F}$, and at level $k$ strictly shorter, since $\mathrm{relLength}(\mathrm{Sel}_i(J), \mathrm{F}) > 0$. For $j \neq i$ the slope at $P$ is $0$, so the new group lies in $\mathrm{Sel}_j(J)$. All terms are finite. $\square$

**Lemma (The loop).** Under $\#k > 2\,\mathrm{rank}(T_i)\, e + 1$ for all $i$, $M < N$ and $\varpi^e \mid \ell^M$, from tied primes $(J, x)$ there are tied primes $(J', x')$ with the same $P_0$, $\#J' \leq \#J + \mathrm{tot}(J, x)$ and $\mathrm{len}\, \mathrm{Sel}_i(J') \bmod \varpi^e \leq \mathrm{glob}(T_i) + \mathrm{places}(T_i)$ for all $i$.

Lean: `New.Selmer.exists_isTiedPrimes_length_tiedSelmer_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* Among tied primes with $\#J' + \mathrm{tot}(J') \leq \#J + \mathrm{tot}(J)$, take one with least $\mathrm{tot}$. If some inclusion failed, one step would add one prime and lower $\mathrm{tot}$ by at least $1$, giving a member of the set with smaller $\mathrm{tot}$. So all inclusions hold, and the last lemma of the previous subsection applies. $\square$

**Lemma.** There is $b$, independent of $N$, $P_0$, $J$ and $x$, with $\mathrm{tot}(J, x) \leq b$ whenever all slopes are $0$.

Lean: `New.Selmer.exists_totalTiedLength_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* With slopes $0$, $\mathrm{Sel}_i(J) \subseteq \mathrm{Sel}_i(\emptyset)$. Take for $b$ the finite sum of the lengths of the $\mathrm{Sel}_i(\emptyset) \bmod \varpi^k$. $\square$

**Lemma (The first prime).** For $g_0$ inertial at a place of $S_0$ prime to $\ell$ and $W$ a neighbourhood of $g_0$, some $P_0$ with data, of prime norm divisible by no prime of $S_0$, makes $\{P_0\}$ with slopes $0$ tied.

Lean: `New.Selmer.exists_isTiedPrimes_singleton` (New/Congruences/Selmer/Descent.lean).

*Proof.* Let $R$ be the finite set of primes that divide the norm of a prime of $S_0$. Apply `New.Selmer.exists_isAuxPrimeDataAt` with $R$ avoided and $\varphi_{P_0} \in W$. If $v \in S_0$ divided the prime $\mathrm{N}P_0$, then $P_0$ would divide $\mathrm{N}v$ and lie in $R$. $\square$

**Theorem (Descent).** Let $T_i$ be finitely many Selmer data, $g_0$ inertial at a place of $S_0$ prime to $\ell$, $W$ a neighbourhood of $g_0$, and $\#k > 2\,\mathrm{rank}(T_i)\, v(\ell^M) + 1$. There is $s$ such that for every $N > M$ there are tied primes $(P_0, J, x)$ with $\#J \leq s$ and $\mathrm{len}\, \mathrm{Sel}_i(J) \bmod \ell^M \leq \mathrm{glob}(T_i) + \mathrm{places}(T_i)$ for all $i$.

Lean: `New.Selmer.exists_isTiedPrimes_card_le_and_length_le` (New/Congruences/Selmer/Descent.lean).

*Proof.* Write $(\ell^M) = (\varpi^e)$. Take $b$ from the last lemma but one and $s = 1 + b$. Given $N$, start from $\{P_0\}$ and run the loop: $\#J \leq 1 + \mathrm{tot}(\{P_0\}) \leq 1 + b$. The ideals $(\ell^M)$ and $(\varpi^e)$ are equal, so the groups agree. $\square$

**Remark (Formalization).** The bound $s$ does not depend on $N$. Lengths count composition factors, so a strict drop of $\mathrm{tot}$ is a drop by at least $1$; this pays for the new prime.
