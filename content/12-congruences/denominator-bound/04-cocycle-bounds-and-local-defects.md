---
title: Cocycle bounds and local defects
lean:
  - New/Congruences/FirstOrder/TraceRelations.lean
decls:
  - New.Selmer.length_ribetCocyclesVanishingOn_le
  - New.Selmer.hasTriangleCost_of_isCharacterCocycle
  - New.Selmer.isTameType_of_mem_placesAboveM
  - New.Selmer.crystallineColength_le_sum_dualDefect
  - New.Selmer.hasJumps_localLattice_summandRep
  - New.Selmer.sum_index_mul_defectBound_le
  - New.Selmer.eventually_exists_inClass_sum_dualDefect_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cocycle bounds and local defects

Ribet's element in [Ribet elements](/chapter/ribet-elements/#ribets-element-for-galois-representations) has a coefficient whose valuation is bounded by the lengths of some modules of cocycles. This section bounds those lengths by two kinds of quantities: Selmer lengths, which the hypotheses of the method control, and local defects above $\ell$, which [the local loss at ℓ](/chapter/local-loss/) controls. The first theorem is the cocycle bound that chapter 2 imports. The last theorem is the bound by $\#r \cdot \mathrm{loc}_\ell$, which explains the factor $4f$ in $\mathrm{loc}_\ell$.

Notation is as in the previous section. Write $S_\ell$ for the places of $E$ above $\ell$ and $S_M$ for the places above $p_0 p_1$ (`New.Selmer.placesAboveM`). For a set $A$ of places, $\bar A$ is its conjugate and $A \cup \bar A$ its conjugation closure.

### The cocycle bound

[Ribet's cocycles vanishing on a set](/chapter/ribet-elements/) are the members $z$ of $\mathrm{Coc}(T, \ell^m)$ for the family $u$ that vanish on a given set of elements and at a given element $\gamma$ (`New.Selmer.ribetCocyclesVanishingOn`). The crystalline colength $\mathrm{crysColen}(T, u, m)$ is the relative length of $\mathrm{Coc}(T, \ell^m)$ over the cocycles that obey the crystalline relations above $\ell$ ([crystalline colength](/chapter/main-summands/#cocycles-relations-and-selmer-lengths)). The module $\mathrm{Sel}_m(T, Q, \gamma)$ is the module of [Selmer cocycles](/chapter/main-summands/#cocycles-relations-and-selmer-lengths).

**Theorem (The cocycle bound).** Let $Y$ be finite and let $(w, \tau, \varphi)$ be a tame generator family of level $\nu$, indexed by $K$. Let $Q$ be a finite set of places. Let the $u_x : G \to M_n(O)$, $x \in Y$, be continuous, with $u_x(g) = 1$ for all $x$ and all $g$ in inertia groups above places outside
$$S_\ell \cup S_M \cup (Q \cup \bar Q) \cup (w(K) \cup \overline{w(K)}).$$
Let $T : G \to M_r(O)$ satisfy $T(g) = 1$ for all $g$ in inertia groups above places outside $S_\ell \cup S_M \cup Q \cup \bar Q$. Let $m \in \mathbb{N}$ and $\gamma \in G$. Then the module $Z$ of the members of $\mathrm{Coc}(T, \ell^m)$ that vanish on the doubled family $\mathrm{withConjInv}\,\tau$ and at $\gamma$ satisfies
$$\operatorname{length}_O Z \leq \mathrm{crysColen}(T, u, m) + \operatorname{length}_O \mathrm{Sel}_m(T, Q, \gamma).$$

Lean: `New.Selmer.length_ribetCocyclesVanishingOn_le` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Let $Z_f$ be the module of functions that obey the crystalline relations $\mathrm{crysRel}(T)$.

*Step 1: $Z \cap Z_f \subseteq \mathrm{Sel}_m(T, Q, \gamma)$.* Let $z \in Z \cap Z_f$. By [Ribet's cocycles are Selmer classes](/chapter/denominator-bound/#trace-relations-and-lattices), $z$ lies in the Selmer module of $T$ for the places $S_\ell \cup S_M \cup (Q \cup \bar Q) \cup (w(K) \cup \overline{w(K)})$ and the crystalline relations. The cocycle $z$ vanishes at every $\tau_j$ and every $(\tau_j^c)^{-1}$. These are tame generators at $w_j$ and $\bar w_j$, and $T$ is unramified there. By [the tame generator lemma](/chapter/first-order-deformations/) (`New.Selmer.IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero`), a cocycle of an unramified representation that vanishes at the tame generator of a place prime to $\ell$ is unramified there. So $z$ lies in the Selmer module for $S_\ell \cup S_M \cup Q \cup \bar Q$. With $z(\gamma) = 0$, this says $z \in \mathrm{Sel}_m(T, Q, \gamma)$.

*Step 2: the lengths.* For submodules $Z$ and $Z_f$, $\mathrm{relLen}(Z, Z_f) + \operatorname{length}(Z \cap Z_f) = \operatorname{length} Z$ ([relative lengths](/chapter/fitting-ideals/), `New.relLength_add_length_inf`). Since $Z \subseteq \mathrm{Coc}(T, \ell^m)$, monotonicity of the relative length gives $\mathrm{relLen}(Z, Z_f) \leq \mathrm{crysColen}(T, u, m)$. Step 1 and monotonicity of length give $\operatorname{length}(Z \cap Z_f) \leq \operatorname{length} \mathrm{Sel}_m(T, Q, \gamma)$. $\square$

The theorem puts the two costs of Ribet's method side by side. The Selmer length is global and is bounded by hypothesis. The crystalline colength is local above $\ell$ and is bounded in the second half of this section.

### The triangle cost of the characters

For a character block $O(-e)$ the method uses the triangle of primes of [first-order deformations](/chapter/first-order-deformations/#the-triangle-of-primes). [The triangle cost](/chapter/ribet-elements/) (`New.Selmer.HasTriangleCost`) is the property that lets the Fitting ideal argument separate the characters. [Character cocycles](/chapter/ribet-elements/) (`New.Selmer.IsCharacterCocycle`) are cocycles in $(O/\ell^\nu)(-e)$ that obey the relations of the family, vanish at tame generators $\delta$ of places $q$ and their conjugates, and, if they vanish at $\gamma$, have their value at $g_0$ killed by every $\chi(g)^e - 1$.

**Theorem (Triangle cost of a character).** Let $K$ be finite and linearly ordered. Let $(w, \tau, \varphi)$, with monotone exponents $0 < \mathrm{ty}(j) < t$, form a triangle of primes for $g_0$ up to $\ell^{\mathrm{sep}}$ with constant $c$ (`New.Selmer.IsPrimeTriangle`). Let the $u_x$, $x \in Y$ finite, be continuous and $1$ on inertia outside $S_\ell \cup S_M \cup (Q \cup \bar Q) \cup (w(K) \cup \overline{w(K)})$. Let $(q, \delta, 1)$ be a tame generator family of level $0$ with $S_M \cup Q \cup \bar Q \subseteq S_\ell \cup q(W) \cup \overline{q(W)}$. Let $e < t$, let $\gamma$ lie in inertia above a place not above $\ell$, and let a finite set $s$ detect the Selmer module of the Tate twist $O(-e)$ unramified outside $S_\ell$ (`New.Selmer.IsDetectedBy`). Let every $z \in Z$ be a character cocycle for $\chi^e$, $\mathrm{withConjInv}\,\delta$, $\gamma$ and $g_0$. Then:

1. $Z$ has triangle cost $\mathrm{crysColen}(O(-e), u, \nu) + \operatorname{length} \mathrm{shaOdd}(\ell, E, O, e, \nu)$ along the $j$ with $\mathrm{ty}(j) = e$, for the families $\tau$, $(\tau^c)^{-1}$, $\varphi$, $(\varphi^c)^{-1}$ and the modulus $\ell^{\mathrm{sep}}$;
2. $Z$ is detected by $s \cup \mathrm{withConjInv}\,\tau(K \times \{\mathrm{true}, \mathrm{false}\})$.

Lean: `New.Selmer.hasTriangleCost_of_isCharacterCocycle` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Every member of $Z$ obeys the relations of the family, so $Z \subseteq \mathrm{Coc}(O(-e), \ell^\nu)$. By the hypothesis on $q$, the places $S_M \cup Q \cup \bar Q$ are covered by $S_\ell$ and the places $q$ and their conjugates. A member $z$ vanishes at the tame generators $\delta$ and their conjugate inverses. By [Ribet's cocycles are Selmer classes](/chapter/denominator-bound/#trace-relations-and-lattices) and the tame generator lemma, as in the cocycle bound, $z$ is unramified outside $S_\ell \cup w(K) \cup \overline{w(K)}$.

If $z$ is also unramified at the $w_j$, then $z$ is unramified outside $\ell$. Then $z(\gamma) = 0$, since $\gamma$ is in inertia off $\ell$. The definition of a character cocycle then gives $(\chi(g_0)^e - 1)\, z(g_0) = 0$.

These are the hypotheses of [the triangle cost of a Tate twist](/chapter/tied-traces/#even-classes-and-cocycles-of-tate-twists) (`New.Selmer.hasTriangleCost_tateTwist`), which gives both parts. $\square$

**Remark.** No bound on the even classes enters here, and no hypothesis of Vandiver type is needed. The element $g_0$ and the factor $\chi(g_0)^e - 1$ take the place of such a hypothesis. [The odd classes](/chapter/odd-classes/) bound the remaining part for all $\ell$ at once.

### Local defects

The crystalline colength is a local quantity. [The local loss at ℓ](/chapter/local-loss/) studies it place by place, for a class of local lattices `InClass F C U` at a place $v$ above $\ell$: lattices whose periods are admissible along the filter $F$, whose Hodge-Tate jumps lie in the sets $U$, and on which each inertial $s$ is killed by every polynomial $Q$ with $C(s, Q)$. The *dual defect* of a lattice $L$ in a class ([local duality](/chapter/local-duality/), `New.Lift.dualDefect`) is the length of the crystalline cocycles of the Tate dual of $L$ modulo those that are orthogonal under cup product to the class.

**Lemma (Tame type above $p_0 p_1$).** Let $V$ with type polynomials $c_i$ be a lift setting for a twist $\vartheta$ ([lift settings](/chapter/main-summands/), `New.Selmer.IsLiftSetting`), and let $t \leq D.t$. Let $v$ be a place above $\ell$ and above $p_0$ or $p_1$. Then $\ell = p_k$ for some $k \in \{0, 1\}$, and for every inertial element $s$ at $v$ the polynomials over $O$ that kill $s$ on all conjugate self-dual representations of the type $\mathrm{scaledTypePoly}(V, c, i)\,(X - 1)^t$ (`New.Selmer.IsRepOfType`) satisfy `IsTameType ℓ D.r ((D.r + D.t) * D.r)`. That is, they include $X^e - 1$, with $e$ the least common multiple of the $\ell^i - 1$ for $1 \leq i \leq r$, and a monic polynomial over $\mathbb{Z}_\ell$ of degree at most $(r + t) r$.

Lean: `New.Selmer.isTameType_of_mem_placesAboveM` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* A place above $\ell$ that is also above $p_k$ forces $\ell = p_k$, since both are the characteristic of the residue field. By [the inertia spectrum](/chapter/main-summands/) (`New.Selmer.exists_inertiaGroup_isInertiaSpectrum`) there is a multiset $\mu$ of elements of $\overline{\mathbb{Q}}_\ell$ with at most $\#n \leq (r + t) r$ elements, each a root of $X^{\ell^a - 1} - 1$ for some $1 \leq a \leq r$, such that $\prod_{y \in \mu} (X - y)$ kills $s$ on every representation of the type. So every polynomial that vanishes on $\mu$ kills $s$. The lemma `New.Selmer.isTameType_of_roots` turns such a multiset into the two polynomials of the tame type: $X^e - 1$ vanishes on $\mu$, and so does a monic polynomial over $\mathbb{Z}_\ell$ of degree at most $(r+t)r$. $\square$

**Lemma (Crystalline colength by dual defects).** Let $Y$ be finite. At each place $v$ above $\ell$, let the restrictions of all $u_x$ and of $\rho$ lie in the class $\mathrm{InClass}(F_v, C_v, U_v)$. Then for every $M$,
$$\mathrm{crysColen}(\rho, u, M) \leq \sum_{v \mid \ell} \mathrm{dualDefect}\big(\mathrm{InClass}(F_v, C_v, U_v),\ (\rho|_v)^{\vee}(1)\big).$$

Lean: `New.Selmer.crystallineColength_le_sum_dualDefect` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* The crystalline relations above $\ell$ are the union over $v \mid \ell$ of the local relations. The relative length over an intersection of submodules is at most the sum of the relative lengths (`New.relLength_iInf_le`). At each $v$, [the local loss at ℓ](/chapter/local-loss/) bounds the relative length of Ribet's cocycles over the local crystalline relations by the dual defect of the Tate dual (`New.Selmer.relLength_ribetCocycles_le`). $\square$

**Lemma (Jumps of the summands).** Let $R$ be a main summand with jumps $J$, and let $T$ agree on the decomposition group at $v \mid \ell$ with a lattice $T_0$ in $R$. Let $g \in G_{\mathbb{Q}_\ell}$, and let $\sigma$ be the complex embedding of $E$ that $g$ gives through the chart at $v$. At the embedding of $O$ given by $g$, the summand $T$ has jumps $J(\sigma)$, and the summand $O(-e)$ has the single jump $e$.

Lean: `New.Selmer.hasJumps_localLattice_summandRep` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* On the decomposition group, $T$ is $T_0$, a lattice in $R$, and the jumps of $R$ are $J$ by the definition of a main summand. The character $\chi^e$ has Hodge-Tate weight $e$ at every embedding. $\square$

**Lemma (Sum of the local degrees).** Let $\#r \geq 1$ and $t \leq D.t$. At each $v \mid \ell$ let $d_v$ be the index of the decomposition group in $G_{\mathbb{Q}_\ell}$, the local degree. Then
$$\sum_{i} \sum_{v \mid \ell} d_v \cdot \#\mathrm{idx}(i) \cdot \frac{\mathrm{defect}_\ell}{\varepsilon_i} \leq \#r \cdot \mathrm{loc}_\ell,$$
where $i$ runs over the $t + 1$ summands, $\#\mathrm{idx}(i)$ is $\#r$ for the main summand and $1$ for a character, and $\varepsilon_i$ is $1$ for the main summand and $D.t$ for a character.

Lean: `New.Selmer.sum_index_mul_defectBound_le` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* The sum factors as $\big(\sum_v d_v\big) \cdot \big(\sum_i \#\mathrm{idx}(i)\, \mathrm{defect}_\ell / \varepsilon_i\big)$.

The local degree $d_v$ counts the complex embeddings of $E$ that belong to $v$ through the chart. Each embedding belongs to at most one place, and $E$ has $2f$ embeddings. So $\sum_v d_v \leq 2f$.

The second factor is $\#r\, \mathrm{defect}_\ell + t \cdot \mathrm{defect}_\ell / D.t$. Since $t \leq D.t \leq \#r \cdot D.t$ and $D.t > 0$ ($D.t$ is odd), the second term is at most $\#r\, \mathrm{defect}_\ell$. So the factor is at most $2\#r\, \mathrm{defect}_\ell$. The product is at most $2f \cdot 2 \#r\, \mathrm{defect}_\ell = \#r \cdot 4f\, \mathrm{defect}_\ell = \#r \cdot \mathrm{loc}_\ell$. $\square$

So the factor $4f$ in $\mathrm{loc}_\ell$ is $2f$ for the places above $\ell$ and $2$ for the main summand and the characters together.

**Theorem (The local defects are bounded).** Let $V$ with type polynomials $c_i$ be a lift setting for $\vartheta$. Let $R$ be a main summand of rank $\#r$ with jumps $J$, and let the $\rho_x$, $x \in Y$, be representations of the type $\mathrm{scaledTypePoly}(V, c, i)\,(X-1)^t$ with jumps $J'$ and level $S$. Let $\epsilon$ be an index bijection and $\pi \in Y$. Then for every large coefficient ring $O$ the following holds. Let $T, T_0 : G \to M_r(O)$ and lattices $u_x$ in the $\rho_x$ be given, with $u_\pi$ the reindexed block sum of the summands of $T$, $T_0$ a lattice in $R$, and $T = T_0$ on the decomposition groups above $\ell$. Then there are classes $\mathrm{InClass}(F_v, C_v, U_v)$ at the places $v \mid \ell$ that contain all $u_x|_v$ and all summands of $u_\pi$ at $v$, and
$$\sum_i \sum_{v \mid \ell} \mathrm{normLength}_O\, \mathrm{dualDefect}\big(\mathrm{InClass}(F_v, C_v, U_v),\ (\text{summand } i \text{ at } v)^{\vee}(1)\big) \leq \#r \cdot \mathrm{loc}_\ell.$$

Lean: `New.Selmer.eventually_exists_inClass_sum_dualDefect_le` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* For each $v \mid \ell$, [the local loss at ℓ](/chapter/local-loss/) gives a statement for large $O$ (`New.Selmer.summand_defect_le_at_place`): the defect of a summand of rank $\rho$ in a class with the jumps of a main summand is at most $d_v \cdot \rho \cdot \mathrm{defect}_\ell / \varepsilon$. There are finitely many $v$, so all hold for large $O$ at once.

Define the classes. The jumps $U_v$ at an embedding of $O$ are the jumps $J'$ of the representations of the type at the corresponding complex embedding. Above $p_0 p_1$, $F_v = \bot$ (potentially crystalline), and $C_v(s, Q)$ says that $Q$ kills $s$ on every representation of the type, so the class is tame by the lemma on tame type. At the other places above $\ell$, $F_v = \top$ (crystalline) and $C_v$ is empty.

Each $u_x$ lies in the class at $v$, since $\rho_x$ is of the type and has jumps $J'$ (`New.Selmer.hasJumps_and_inClass_localLattice`). Each summand of $u_\pi$ embeds equivariantly into $u_\pi$ through the block structure, so it lies in the class too. Every jump of $u_\pi$ is a jump of some summand, and the jumps of the summands are known by the lemma on jumps. These are the hypotheses of the bound at one place. Summing over $i$ and $v$ and applying the lemma on local degrees gives the bound $\#r \cdot \mathrm{loc}_\ell$. $\square$

**Remark (Formalization).** The classes $F_v$, $C_v$, $U_v$ are defined in the proof, and the map that reads the jumps at an embedding of $O$ uses a right inverse of a surjection, chosen by `surjInv`. The statement only asserts that some classes exist. The theorem `ribet_columns` of [Ribet elements](/chapter/ribet-elements/#ribets-element-for-galois-representations) uses them only through the two lemmas above, so the choice does not matter. The length is normalized by `normLength`, so that $O/\ell$ has length $1$, which makes the bound independent of the ramification of $O$.
