---
title: The Galois representation
lean:
  - Lib/Shimura/Eigenspace.lean
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/GaloisRep/Main/LocalConditions.lean
  - Lib/GaloisRep/Main/Defs.lean
  - Lib/Cohomology/WoodsHole.lean
  - Lib/Cohomology/Etale/ProperFunctors.lean
  - Lib/PadicComparison/CrystallineFrobenius.lean
decls:
  - New.Variety.Model.exists_galois_rep
  - New.Variety.Model.aeval_heckePoly_eq_zero_of_isEigenQuotient
  - New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient
  - New.Variety.Model.isNullHecke_mul_of_kills_weight
  - New.Variety.Model.jumpsRelAt_of_isEigenQuotient
  - New.Variety.algebraMap_mem_of_isLocalization
  - New.Variety.Model.IsHeckeAction
  - New.Variety.Model.exists_isHeckeAction
  - New.Variety.ellAdicCohom.transfer
  - New.Variety.ellAdicCohom.woods_hole
  - New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel
  - New.Variety.exists_hasHodgeTateWeight
  - New.GaloisRep.IsSphericalAbove
  - New.GaloisRep.IsGoodAt
  - New.GaloisRep.PolyKillsAt
  - New.GaloisRep.JumpsRelAt
  - New.heckePoly
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Galois representation

This section puts the parts together. The cohomology of the base $Z$ of the model carries commuting Hecke operators and an action of $\operatorname{Gal}(\Omega/E)$, where $\Omega$ is the fixed algebraic closure. The eigenquotient of Section 4 cuts out $r$. The congruence relation of Section 2, fed with the relation on points of Section 3, gives the Hecke polynomial. The occurrence of Section 5 gives the jumps.

### The local conditions

The output is described by a list of local conditions, one list for each place $A$ of $\Omega$ above a finite place $w$ of $E$. The chapter [on attached representations](/chapter/attached-representations/) discusses them in detail. Here is what this section needs.

**Definition (Local conditions).** Let $r : \operatorname{Gal}(\Omega/E) \to \mathrm{GL}_m(\bar{\mathbb{Q}}_\ell)$, let $w$ be a finite place, $J$ a multiset of integers for each complex embedding of $E$, and $P$ a polynomial over $\bar{\mathbb{Q}}_\ell$. Then $r$ is *spherical above $w$* (for the relation "each member of $J$ is a jump" and the polynomial $P$) if for every place $A$ of $\Omega$ above $w$:

1. (good) if $\ell$ is a unit at $A$, the inertia group of $A$ acts trivially; and for every $\ell$-adic local datum at $A$, the restriction of $r$ to the decomposition group is crystalline;
2. (jumps) for every $\ell$-adic local datum at $A$ and every embedding $\gamma$ given by an element $g$ of $\operatorname{Gal}(\bar{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$, each $u$ in $J$ at the induced complex embedding is a Hodge-Tate jump of $r$ at $\gamma$;
3. (Frobenius) for every $s$ with $s^{-1}$ a Frobenius element for $q = |k_w|$ at $A$: if $\ell$ is a unit at $A$, then $P(r(s)) = 0$; and for every local datum and every Weil pair $(s, k)$, $P$ kills $(s, k)$ for $r$ on the decomposition group.

Lean: `New.GaloisRep.IsSphericalAbove`, `New.GaloisRep.IsGoodAt`, `New.GaloisRep.JumpsRelAt` and `New.GaloisRep.PolyKillsAt` (Lib/GaloisRep/Main/LocalConditions.lean).

The elements $s$ in clause 3 are the *geometric* Frobenius elements: $s^{-1}$ raises residues to the power $q$. Clause 3 at $\ell$ is the analogue of the classical statement about the crystalline Frobenius on $D_{\mathrm{cris}}$.

### The main theorem

**Theorem.** Let $X$ be a model over $R$ for $\mathrm{GU}$ of rank $a \geq 1$, at a neat level $\mathfrak{N}$, with $\nu$ extra points. Let $\ell$ be a prime. Let $R$ be the localization of $\mathcal{O}_E$ at a submonoid $M$ that meets no safe place. Let $\theta(w, j) \in \mathbb{C}$ for safe $w$ and $j \in \mathbb{N}$. Let $J$ be a multiset of integers $h \geq 0$, and assume that $\theta$ occurs in weight $h$ (with parameter $\nu$) for every $h \in J$. Then there is a continuous representation $\rho : \operatorname{Gal}(\Omega/E) \to \mathrm{GL}_m(\bar{\mathbb{Q}}_\ell)$ such that at every safe place $w$, $\rho$ is spherical above $w$, with the multiset $J$ at the embedding $E \to \mathbb{C}$ given with $E$ and $0$ at the other embeddings, and with the polynomial
$$P_w(X) = \sum_{j = 0}^{a} (-1)^j q^{\binom{j}{2}} \iota_\ell(\theta(w, j)) X^{a - j}, \qquad q = |k_w|.$$

Lean: `New.Variety.Model.exists_galois_rep` ([Eigenspace.lean, line 689](lean:Lib/Shimura/Eigenspace.lean#L689)).

Here $\iota_\ell : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ is the isomorphism that the source fixes once and for all, and $P_w$ is `New.heckePoly`. The textbook form of the classical case is Deligne, *Formes modulaires et représentations l-adiques*, Séminaire Bourbaki 355 (1969), Théorème 4.9, and for unitary Shimura varieties Harris and Taylor (2001), Chapter VII. Both attach a representation of the correct dimension, cut out as an isotypic part. The source states less, as the remarks below explain.

**Example ($a = 2$).** For $a = 2$, $P_w(X) = t_0 X^2 - t_1 X + q t_2$, where $t_j = \iota_\ell \theta(w, j)$. The value $t_0$ is the eigenvalue of $\tau_{w, 0} = [g_0]$, the Hecke element of the zero subspace; for an eigensystem in which $[g_0]$ acts as the identity, $t_0 = 1$. Compare $X^2 - a_p X + p \chi(p)$ for modular curves: $t_1$ plays the part of $a_p$, and $t_2$ the part of the diamond operator.

The proof has four parts: the Hecke operators on cohomology, Eichler-Shimura away from $\ell$, Eichler-Shimura at $\ell$, and the jumps.

### Hecke operators on cohomology

Let $V^n = V^n(Z)$ for $n \leq 2 \dim X$. For each level $i$, the leg $u_1 = p_{[1]} : W_i \to Z$ is a Galois covering. Pull-back along it is injective, and every class on $W_i$ fixed by the deck group is a pull-back (`New.Variety.ellAdicCohom.transfer`). For each safe place $w$ the source fixes, by `choose`, a level $l(w)$ whose legs include all the $u_A = p_{[g_A]}$.

**Proposition (Hecke action).** There are commuting operators $T(w, j)$ on each $V^n$ with
$$u_1^* \circ T(w, j) = \sum_{\dim A = j} u_A^* \quad \text{on } V^n,$$
the pull-backs being to the level $l(w)$, and such that words in the $T$ act on deep levels as the same words in the Hecke elements.

Lean: `New.Variety.Model.exists_isHeckeAction` and `New.Variety.Model.IsHeckeAction` (Lib/Shimura/HeckeTower/Model.lean).

The sum on the right is fixed by the deck group, so it is $u_1^*$ of a unique class. This defines $T(w, j)$. The operators commute with the Galois action, since pull-backs do and $u_1^*$ is injective.

The eigenquotient $(r, F)$ of Section 4 for the family $(V^n)_n$, the operators $T$ and the eigenvalues $\iota_\ell \circ \theta$ then exists. The cohomology is continuous for the Galois action, so $r$ is continuous. The representation $\rho$ of the theorem is $r$.

### Eichler-Shimura away from $\ell$

**Proposition.** In the setting above, let $A$ lie above the safe place $w$, with $R$ integral at $A$ and $\ell$ a unit at $A$. Let $s$ be a geometric Frobenius at $A$. Then $P_w(r(s)) = 0$.

Lean: `New.Variety.Model.aeval_heckePoly_eq_zero_of_isEigenQuotient` (Lib/Shimura/Eigenspace.lean).

*Proof.* Write $q = t^f$ with $t$ the residue characteristic. The congruence field of the model (Section 3) gives the relation on points
$$\sum_A (-1)^{\dim A} q^{\binom{\dim A}{2}} \left[\operatorname{Frob}^{(a - \dim A) f}(u_A(x))\right] = 0$$
modulo the primes of $R$ that are not units at $A$. The theorem of Section 2, with $g = s^{-1}$, gives for every $x \in V^n$
$$\sum_A (-1)^{\dim A} q^{\binom{\dim A}{2}} \, u_A^*\big(s^{a - \dim A} x\big) = 0.$$
Group the terms by $j = \dim A$ and use the Hecke action:
$$u_1^*\Big(\sum_{j = 0}^{a} (-1)^j q^{\binom{j}{2}} \, T(w, j) \, s^{a - j} x\Big) = 0.$$
Since $u_1^*$ is injective, the sum inside is $0$. Apply $F$. It turns $T(w, j)$ into $t_j = \iota_\ell \theta(w, j)$ and $s$ into $r(s)$, so
$$P_w(r(s)) \, F(x) = \sum_j (-1)^j q^{\binom{j}{2}} t_j \, r(s)^{a - j} F(x) = 0.$$
The values $F(x)$ span, so $P_w(r(s)) = 0$. $\square$

The proof uses the theorem of Section 2 with exponents $e_A = a - \dim A$ and Frobenius power $f$. The order of the terms matters: $s^{a - j}$ acts first, then $T$. Since $T$ commutes with the Galois action, the order does not change the result.

### Eichler-Shimura at $\ell$

**Proposition.** In the same setting, let the cohomology be crystalline at $A$, let $s$ be a geometric Frobenius at $A$ in the decomposition group, and let $(s, k)$ be a Weil pair for a local datum at $A$. Then $P_w$ kills $(s, k)$ for $r$ on the decomposition group.

Lean: `New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient` (Lib/Shimura/Eigenspace.lean).

*Proof.* The Weil pair forces $q = \ell^k$, so $w$ lies above $\ell$. The crystalline comparison of [the comparison theorems](/chapter/comparison-theorems/), in the form `isCrystalline_and_linearFrob_rel`, turns the same relation on points into the relation
$$\sum_A (-1)^{\dim A} q^{\binom{\dim A}{2}} \, u_A^* \circ \beta_{s^{a - \dim A}, (a - \dim A) k} = 0 \quad \text{on } B \otimes V^n,$$
with $\beta$ the linear Frobenius of Section 4. After $u_1^*$, which stays injective after the flat base change to $B$, this is the hypothesis of the proposition on Frobenius relations in Section 4, with $t_k = (w, j)$, $m_k = (-1)^j q^{\binom{j}{2}}$ and $d_k = a - j$. That proposition gives the claim. $\square$

**Remark (Formalization).** The cohomology is crystalline at every place above a safe place. The source gets this from the same lemma `isCrystalline_and_linearFrob_rel`, applied to the empty congruence relation. The crystalline clause of "good" for $r$ then follows from the proposition of Section 4. The unramified clause at places prime to $\ell$ follows from the corollary of Section 2: inertia acts trivially on each $V^n$, and so on the span of the values of $F$.

### The jumps

**Lemma (Killing a weight gives null elements).** Let $c$ be a combination of words in the safe Hecke indices, with coefficients in $\bar{\mathbb{Q}}_\ell$, such that $c(T)$ kills every vector of Hodge-Tate weight $h$ in every $\mathbb{C}_\ell \otimes V^n$. Let $\varepsilon : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ be compatible with the place. Then for every Hecke element $b$, the element $b \cdot \sum_L \varepsilon^{-1}(c_L) \tau_L$ is $h$-null.

Lean: `New.Variety.Model.isNullHecke_mul_of_kills_weight` (Lib/Shimura/Eigenspace.lean).

*Proof.* By the Lefschetz lemma of Section 5, it is enough to show that the family of legs over $b \, c(\tau)$, composed with $m_\alpha$, is null in weight $h$ on deep levels. The vanishing half of the Atiyah-Bott formula in the source (`New.Variety.ellAdicCohom.woods_hole`) reduces this to the vanishing of
$$\sum_g (b\, c(\tau))_g \, \lambda_h\big(u_g^* m_\alpha^* x\big)$$
for Hodge classes $x$ of degree $q \leq \dim X$, with $\lambda_h$ the Hodge-Tate map. The Hodge-Tate comparison (`New.Variety.exists_hasHodgeTateWeight`) writes $\lambda_h(u^* m_\alpha^* x) = \Theta(u^* v)$ for a vector $v$ of weight $h$ in degree $q + h$ and a linear $\Theta$. On deep levels a word in the $\tau$ acts through the same word in $T$, so the sum is $\sum_g b_g \Theta(u_g^* c(T) v)$, and $c(T) v = 0$. $\square$

**Proposition (Jumps).** In the setting of the theorem, let $A$ be a place at which $R$ is integral and the cohomology is crystalline. Then each $h \in J$ is a Hodge-Tate jump of $r$ at $A$, for the embedding $E \to \mathbb{C}$ given with $E$.

Lean: `New.Variety.Model.jumpsRelAt_of_isEigenQuotient` (Lib/Shimura/Eigenspace.lean).

*Proof.* Suppose $h \in J$ is not a jump at $\gamma$, where $\gamma$ is given by $g \in \operatorname{Gal}(\bar{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$. The proposition on jumps in Section 4 gives $c$ with $\sum_L c_L \, g(\iota_\ell \theta(L)) = 1$ and $c(T)$ killing weight $h$. Put $\varepsilon = g \circ \iota_\ell$. The condition on the complex embedding says that $\varepsilon$ is compatible with the place. Then $p = \sum_L \varepsilon^{-1}(c_L) \tau_L$ has $p(\theta) = 1$, and by the lemma every $b p$ is $h$-null. This contradicts the occurrence of $\theta$ in weight $h$. $\square$

*Proof of the theorem.* The representation is $r$, continuous by Section 4. Let $w$ be safe and $A$ above $w$. The ring $R$ is integral at $A$, because the denominators in $M$ are units at $w$ (`New.Variety.algebraMap_mem_of_isLocalization`). The cohomology is crystalline at $A$ by the last remark. Clause 1 follows from the remark. Clause 2 is the proposition on jumps. Clause 3 is the two Eichler-Shimura propositions. $\square$

### What the theorem does not say

**Remark (Formalization).** Several points separate the theorem from its textbook form.

* The representation is the eigenquotient of the total cohomology $\bigoplus_{n \leq 2\dim X} V^n$, not an isotypic part of the middle degree. No dimension is stated; $m$ can be $0$, and then every clause holds trivially except the jumps. The jumps force $m \geq 1$ when $J \neq 0$ and some safe place carries an $\ell$-adic local datum; without a local datum the jump clause is void.
* No semisimplicity, no irreducibility and no purity is stated.
* The jumps are controlled at one complex embedding only, the one given with $E$, and only in the direction "each member of $J$ is a jump". Multiplicities are not controlled, and the multiset at other embeddings is $0$, which makes the condition void there.
* The objects $l(w)$, $T$, the descent data for $u_1^*$ and the eigenquotient are chosen by `choose`. The statement does not depend on the choices.
* The jump is a `finrank` and is $0$ for an infinite-dimensional space of forms. For $r$ the space is finite-dimensional, so this junk value does not enter.
* Continuity is proved in the weak form of Section 4: each orbit map is continuous. This gives continuity of the matrix entries, which is what `Continuous ρ.rep` states.

The chapter [on building the representations](/chapter/building-representations/) explains how the source uses these representations for the forms that it needs.
