---
title: Tame places and the cyclotomic generator
lean:
  - New/Congruences/FirstOrder/TraceRelations.lean
  - New/Congruences/FirstOrder/DenominatorBound.lean
decls:
  - New.Selmer.pow_chosenGroupOrder_eq_one_of_mem_inertiaAbove
  - New.Selmer.exists_tame_relations
  - New.Selmer.exists_isUnit_cyclotomicChar_pow_sub_one
  - New.Selmer.exists_cyclotomicChar_pow_sub_one_dvd_pow_padicValNat
  - New.Selmer.exists_cyclotomicChar_pow_sub_one_dvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tame places and the cyclotomic generator

Two more inputs complete the Galois side. The first is a set of tame relations: at the places above $p_0 p_1$ prime to $\ell$ and at the places of the twist, inertia acts through a finite group, and a polynomial kills it. Ribet's element must pay for these relations, and the payment is the term $8ft\,v$ of $e_\ell$ and the term $2t'\,\mathrm{ram}$. The second is an element $\gamma$ of $G$ whose cyclotomic character separates the characters $\chi^a$, $0 < a < t$. The separation costs $\ell^h$ with $h \leq v$, and $h = 0$ for every large $\ell$.

### Inertia above $p_0 p_1$

**Lemma (Inertia above $p_0 p_1$ has order dividing $N$).** Let $V$ with type polynomials $c_i$ be a lift setting for $\vartheta$. Let $R$ be a representation of the type $\mathrm{scaledTypePoly}(V, c, i)\,(X - 1)^t$ with jumps $J$ and level $S$. Let $g$ lie in an inertia group above a place of $S_M \setminus S_\ell$. Then $R(g)^N = 1$.

Lean: `New.Selmer.pow_chosenGroupOrder_eq_one_of_mem_inertiaAbove` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Let $v$ be the place, above $p_i$ and not above $\ell$. By [the inertia spectrum](/chapter/main-summands/) (`New.Selmer.exists_inertiaGroup_isInertiaSpectrum`) there is a multiset $\mu$ such that $\prod_{y \in \mu}(X - y)$ kills $R(g)$, and each $y \in \mu$ satisfies $y^{p_i^d - 1} = 1$ for some $1 \leq d \leq r$. The number $p_i^d - 1$ divides $N$: the order of $\mathrm{GL}_{rt}(\mathbb{F}_{q})$ is $q^{\binom{rt}{2}} \prod_{j=1}^{rt}(q^j - 1)$, and the residue fields of the chosen places have $q = p_i$ (`New.Selmer.levelPrime_pow_sub_one_dvd_chosenGroupOrder`). So $y^N = 1$ for every $y \in \mu$.

The representation is of finite type at $v$: inertia at $v$ acts through a finite quotient (`IsFiniteTypeAt`, part of the local conditions of a representation of a type). Since $v$ is prime to $\ell$, a polynomial that vanishes on $\mu$ then kills $R(g)$. So $X^N - 1$ kills $R(g)$. $\square$

**Remark.** The roots in $\mu$ may repeat, so $\prod (X - y)$ alone does not give $R(g)^N = 1$: a unipotent part would survive. The finite type condition excludes it, and this is why the lemma uses it.

### The tame relations

[An auxiliary twist](/chapter/tied-traces/) (`New.Selmer.IsAuxTwist`) for the bad places and a set $Q$ with cost $\mathrm{ram}$ is a character $\psi$ that comes from $U(1)$ with modulus $Q$, with $Q$ disjoint from the places above $\ell p_0 p_1 N_D$, and with tame generators $\sigma_k$ at the places $k \in Q$ such that $\sum_{k \in Q} \mathrm{ellVal}(\psi(\sigma_k) - 1) \leq \mathrm{ram}$.

**Theorem (Tame relations).** Let $V$ with type polynomials $c_i$ be a lift setting for $\vartheta$, and let $\psi$ be an auxiliary twist with set $Q$ and cost $\mathrm{ram}$. Let the $u_x$, $x \in Y$, be representations of the type, with
$$(u_x(g) - \psi(g))(u_x(g) - 1) = 0 \quad \text{for all } g \text{ in inertia above } Q \cup \bar Q.$$
Let $u'_x$ be lattices in the $u_x$ over $O$, and let $\psi' : G \to O$ agree with $\psi$. Then there are a finite type $W$, places $q : W \to $ places of $E$, elements $\delta : W \to G$ and polynomials $o_k \in O[X]$ for $k \in W \times \{\mathrm{true}, \mathrm{false}\}$ such that:

1. $(q, \delta, 1)$ is a tame generator family of level $0$;
2. $S_M \cup Q \cup \bar Q \subseteq S_\ell \cup q(W) \cup \overline{q(W)}$;
3. $o_k(u'_x(g_k))\,(u'_x(g_k) - 1) = 0$ for every $k$ and $x$, where $g_k = \mathrm{withConjInv}\,\delta\,(k)$;
4. $\mathrm{normLength}_O\big(\sum_k \mathrm{addVal}_O\, o_k(1)\big) \leq 2\,\mathrm{ram} + 8 f v$.

Lean: `New.Selmer.exists_tame_relations` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Let $M_\ell$ be the finite set of places in $S_M \setminus S_\ell$. It is finite because these places are bad. Index the new places by $W = Q \sqcup M_\ell$. At $k \in Q$ take $\delta_k = \sigma_k$, the tame generator of the twist. At $v \in M_\ell$ take $\delta_v$ the chosen tame generator at $v$. Part 1 holds by construction, and part 2 holds since every place of $S_M$ off $\ell$ is in $M_\ell$.

Define $o$. At a copy of $k \in Q$, $o = \psi'(g_k) - X$. At a copy of $v \in M_\ell$, $o = \sum_{i < N} X^i$.

*Part 3 at $Q$.* The element $g_k$ lies in inertia above $Q \cup \bar Q$. The hypothesis gives $(\psi(g_k) - u_x(g_k))(u_x(g_k) - 1) = 0$. The lattice $u'_x$ maps to $u_x$ under an injective algebra map that sends the scalar $\psi'(g_k)$ to $\psi(g_k)$. So the same identity holds for $u'_x$.

*Part 3 at $M_\ell$.* The element $g_k$ lies in inertia above $v$ or $\bar v$, both in $S_M \setminus S_\ell$. By the lemma above, $u_x(g_k)^N = 1$. Since $(\sum_{i<N} X^i)(X - 1) = X^N - 1$, the relation holds for $u_x$, and so for $u'_x$.

*Part 4.* At a copy of $k \in Q$, $o(1) = \psi(g_k) - 1$. For $(j, \mathrm{false})$ the element is $(\sigma_j^c)^{-1}$, and a character from $U(1)$ satisfies $\psi(g^c) = \psi(g)^{-1}$, so the value is $\psi(\sigma_j) - 1$ again. At a copy of $v \in M_\ell$, $o(1) = N$. So
$$\sum_k \mathrm{ellVal}\, o_k(1) = 2 \sum_{k \in Q} \mathrm{ellVal}(\psi(\sigma_k) - 1) + 2\,\#M_\ell\, v.$$
A subset of $S_M$ has at most $4f$ places (`New.Selmer.card_le_of_subset_placesAboveM`): a place above $p_i$ is a chosen place or the conjugate of one, and $f$ places above each $p_i$ are chosen. So the sum is at most $2\,\mathrm{ram} + 8 f v$. $\square$

**Remark (Formalization).** Part 4 is stated with $\mathrm{normLength}_O$ of a sum of normalized valuations of $O$. This is the valuation $\mathrm{ellVal}$ with $\mathrm{ellVal}(\ell) = 1$, independent of $O$. The hypothesis $\mathrm{tame} \leq 2\,\mathrm{ram} + 8fv$ of [the cost of the characters](/chapter/denominator-bound/#the-constants) is exactly part 4. Each of the $t'$ characters pays it once, which gives the term $8ft\,v$ of $e_\ell$ and the term $2t'\,\mathrm{ram}$ of the lift bound.

### The cyclotomic generator

The characters $\chi^a$, $0 \leq a < t$, must be told apart. One element $\gamma$ with $u = \chi_{\mathrm{cyc}}(\gamma) \in \mathbb{Z}_\ell^\times$ does this if $u^a - 1$ has small valuation for $0 < a < t$. Write $\mathrm{cyc}$ for the $\ell$-adic cyclotomic character of $G$.

**Lemma (Large primes).** Let $h_{\mathrm{gap}}^2 < \ell$. Then there is $\gamma \in G$ such that $\mathrm{cyc}(\gamma)^a - 1$ is a unit of $\mathbb{Z}_\ell$ for every $0 < a < t$.

Lean: `New.Selmer.exists_isUnit_cyclotomicChar_pow_sub_one` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $b$ generate the cyclic group $(\mathbb{Z}/\ell)^\times$, of order $\ell - 1$. Fix a place of $\overline{\mathbb{Q}}$ above $\ell$. Some $\gamma$ in its inertia group in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ has $\mathrm{cyc}(\gamma) \equiv b \pmod{\ell}$, since inertia at $\ell$ maps onto $\mathrm{Gal}(\mathbb{Q}(\mu_\ell)/\mathbb{Q})$. The field $E$ lies in the cyclotomic field of conductor $N_E \leq h_{\mathrm{gap}}^2 < \ell$, which is prime to $\ell$ and so unramified at $\ell$. So $\gamma$ fixes $E$ and lies in $G$. Since $0 < a < t \leq h_{\mathrm{gap}}^2 \leq \ell - 1$, the exponent $a$ is positive and less than the order $\ell - 1$ of $b$. So $b^a \neq 1$, and $\mathrm{cyc}(\gamma)^a - 1$ is nonzero modulo $\ell$, so a unit. $\square$

**Lemma (All primes).** There is $\varphi \in G$ such that $\mathrm{cyc}(\varphi)^a - 1$ divides $\ell^{v}$ in $\mathbb{Z}_\ell$ for every $0 < a < t$.

Lean: `New.Selmer.exists_cyclotomicChar_pow_sub_one_dvd_pow_padicValNat` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* There is a chosen place $v$ above some $p_i$, not above $\ell$, with norm $p_i$ (`New.Selmer.exists_chosen_notMem_placesDividing`). Let $\varphi$ be a Frobenius at $v$. Then $\mathrm{cyc}(\varphi) = p_i$. For $0 < a < t \leq rt$, $p_i^a - 1$ divides $N$, as in the lemma on inertia above $p_0 p_1$. In $\mathbb{Z}_\ell$, the nonzero integer $N$ is a unit times $\ell^{v}$. So $p_i^a - 1 \mid \ell^{v}$. $\square$

**Theorem (The cyclotomic generator).** There are $h \leq v$ with $\ell \leq h_{\mathrm{gap}}^2$ or $h = 0$, and $\gamma \in G$ that generates $G$ modulo the kernel of $\mathrm{cyc}$ (`IsGeneratorModKer`), such that $\mathrm{cyc}(\gamma)^a - 1$ divides $\ell^h$ for every $0 < a < t$.

Lean: `New.Selmer.exists_cyclotomicChar_pow_sub_one_dvd` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* For every $g \in G$, $4 \mid \mathrm{cyc}(g) - 1$ ([first-order deformations](/chapter/first-order-deformations/), `New.Selmer.four_dvd_cyclotomicChar_sub_one`). So the image of $\mathrm{cyc}$ lies in $1 + 4\mathbb{Z}_\ell$ when $\ell = 2$ and in $\mathbb{Z}_\ell^\times$ otherwise. Both groups are procyclic, so the image is procyclic, and some $g_0$ generates it topologically. For such $g_0$ and every $\gamma$, $\mathrm{cyc}(g_0)^a - 1$ divides $\mathrm{cyc}(\gamma)^a - 1$: the second is a limit of the values $\mathrm{cyc}(g_0)^{am} - 1$, each a multiple of $\mathrm{cyc}(g_0)^a - 1$.

If $h_{\mathrm{gap}}^2 < \ell$, take $h = 0$ and the $\gamma$ of the lemma on large primes; then $\mathrm{cyc}(g_0)^a - 1$ divides a unit. Otherwise take $h = v$ and the $\varphi$ of the lemma on all primes. In both cases $g_0$ is the generator. $\square$

The number $h$ is the $h$ of [the cost of the characters](/chapter/denominator-bound/#the-constants): the separation between the characters at the triangle of primes is $\mathrm{sep} = h_{\mathrm{gap}}\, h$. For all $\ell > h_{\mathrm{gap}}^2$, $h = 0$ and $\mathrm{sep} = 0$, so the multiples of $\mathrm{sep}$ cost nothing. The formula for $e_\ell$ keeps the term $((4t+1)h_{\mathrm{gap}}^{22} + h_{\mathrm{gap}})\, v$ for every $\ell$. This is crude but harmless, since $v = 0$ for all $\ell \nmid N$.
