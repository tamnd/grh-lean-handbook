---
title: Marked sets and full marks
lean:
  - New/UpperBound/Divisibility/MarkedPrimes.lean
decls:
  - New.Data.IsMarked
  - New.Data.IsFullMark
  - New.Data.placesInducing
  - New.Data.placesInducingConj
  - New.Data.exists_isFullMark
  - New.Data.IsMarked.card_le
  - New.Data.IsMarked.neg_pow_mul_mem_placesInducing_iff
  - New.Data.IsMarked.notMem_bPlaces
  - New.Data.IsMarked.cast_weight_eq
  - New.Data.IsMarked.sum_inducedPlace_eq_sum_star
  - New.Data.IsMarked.sum_placesInducing_eq_sum_placesInducingConj
  - New.Data.IsMarked.sum_inducedPlace_sub_star_eq_zero
  - New.Data.IsMarked.valuation_natCast_eq_exp_neg_one
  - New.Data.IsMarked.isSplit
  - New.Data.IsFullMark.collisionSum_placesInducing_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Marked sets and full marks

A marked set is a set of primes above $p$ at which the divisibility argument can apply a Hecke operator. This section defines marked sets and full marks, proves that a full mark exists, and proves the properties that [divisibility prime by prime](/chapter/divisibility/) uses: the places that induce a marked prime have the small weight $a/x_1$, the sums over a marked set and over its conjugate agree, and a full mark leaves no collisions.

### The definitions

Fix a prime $p$ and $\iota_p$ as in Section 2.

**Definition (Marked set).** A finite set $\Lambda$ of primes of $E$ is *marked* if:

1. $\bar{\mathfrak l} \notin \Lambda$ for every $\mathfrak l \in \Lambda$;
2. $p$ is exceptional;
3. each $\mathfrak l \in \Lambda$ is $w_\tau$ for some a-place $\tau$;
4. $p < x_1$ and $\chi_K(p) \ne 1$.

Lean: `New.Data.IsMarked` (New/UpperBound/Divisibility/MarkedPrimes.lean).

**Definition (Full mark).** A marked set $\Lambda$ is a *full mark* if for each a-place $\tau$, $w_\tau \in \Lambda$ or $\bar w_\tau \in \Lambda$.

Lean: `New.Data.IsFullMark` (New/UpperBound/Divisibility/MarkedPrimes.lean).

By condition 1, a full mark contains exactly one of $w_\tau$ and $\bar w_\tau$ for each a-place $\tau$.

**Definition.** For a set $\Lambda$ of primes, $\Phi_\Lambda$ is the set of places $\sigma \in \Phi$ with $w_\sigma \in \Lambda$, and $\bar\Phi_\Lambda$ is the set of places $\sigma$ with $\bar w_\sigma \in \Lambda$.

Lean: `New.Data.placesInducing`, `New.Data.placesInducingConj` (New/UpperBound/Divisibility/MarkedPrimes.lean).

**Remark (Formalization).** Conditions 2 and 4 are conditions on $p$ alone. The source puts them in the structure so that one hypothesis "$\Lambda$ is marked" carries all the facts about $p$ that the later proofs need. An empty set is marked if $p$ is exceptional and small.

**Lemma.** A marked set has at most $f$ primes.

Lean: `New.Data.IsMarked.card_le` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The map $\tau \mapsto w_\tau$ from $\Phi$, a set of $f$ elements, reaches every prime of $\Lambda$. $\square$

### A full mark exists

The next fact is from [short columns and the gain](/chapter/short-columns-gain/): for odd $e$ and an a-place $\tau$, the place $[-p^e]\tau$ is an a-place if and only if $o_0 \mid e$. The reason is that $[-p^e]$ has class $(-p)^e$ modulo $q_0$, and this is $1$ exactly when $o_0 \mid e$.

**Theorem (Full marks exist).** Let $p < x_1$ be exceptional. Then there is a full mark $\Lambda$ of primes above $p$.

Lean: `New.Data.exists_isFullMark` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Choose a linear order $<$ on the primes of $E$. Let $\Lambda$ be the set of primes $w_\tau$, $\tau$ an a-place, with $w_\tau < \bar w_\tau$. We check the conditions. If $\mathfrak l \in \Lambda$, then $\mathfrak l < \bar{\mathfrak l}$, so $\bar{\mathfrak l} < \mathfrak l$ fails, and $\bar{\mathfrak l} \notin \Lambda$. Conditions 2 and 3 hold by construction. Condition 4 holds since $p < x_1$ and $\chi_K(p) = -1$.

Now let $\tau$ be an a-place. Since $o_0$ is odd and $o_0 \mid o_0$, the place $\tau' = [-p^{o_0}]\tau$ is an a-place. By Section 2, $w_{\tau'} = \bar w_\tau$, and $\bar w_\tau \ne w_\tau$. The order is linear, so $w_\tau < \bar w_\tau$ or $\bar w_\tau < w_\tau$. In the first case $w_\tau \in \Lambda$. In the second case $w_{\tau'} = \bar w_\tau < w_\tau = \bar w_{\tau'}$, so $\bar w_\tau = w_{\tau'} \in \Lambda$. $\square$

**Remark (Formalization).** The linear order comes from a choice (`exists_wellFoundedLT`). The full mark depends on it, and no later statement depends on which full mark is taken. The hypothesis $o_0$ odd is used here only: it makes $[-p^{o_0}]$ both a conjugating element and an element of class $1$ modulo $q_0$.

**Example.** Suppose $o_0 = 1$, that is $-p \equiv 1 \pmod{q_0}$. Then $[-p]$ preserves the a-places. The orbit of an a-place under $[-p]$ consists of a-places, and it induces the two primes $w_\tau$ and $\bar w_\tau$. A full mark picks one of the two for each orbit. In general, the a-places of one orbit are the $[-p]^{i}\tau$ with $o_0 \mid i$, and such $i$ have both parities, since $o_0$ is odd and the orbit has even length $o$.

### Conjugation and the b-places

**Lemma.** Let $\Lambda$ be marked and $e$ odd. For $\sigma \in \Phi$:

$$[-p^e]\sigma \in \Phi_\Lambda \iff \sigma \in \bar\Phi_\Lambda, \qquad [-p^e]\sigma \in \bar\Phi_\Lambda \iff \sigma \in \Phi_\Lambda.$$

In particular $w_{[-p]\sigma} = \bar w_\sigma$.

Lean: `New.Data.IsMarked.neg_pow_mul_mem_placesInducing_iff`, `New.Data.IsMarked.neg_pow_mul_mem_placesInducingConj_iff`, `New.Data.IsMarked.inducedPlace_placeOfInt_neg_mul` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* By Section 2, $w_{[-p^e]\sigma} = \bar w_\sigma$, since $p$ is inert and $e$ is odd. Conjugation is an involution. $\square$

**Lemma.** Let $\Lambda$ be marked, and let $\sigma \in \Phi$ with $w_\sigma \in \Lambda$ or $\bar w_\sigma \in \Lambda$. Then $\sigma$ is not a b-place.

Lean: `New.Data.IsMarked.notMem_bPlaces` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The prime of $\Lambda$ that occurs is $w_\tau$ for an a-place $\tau$. So $w_\tau = w_\sigma$ or $w_\tau = \bar w_\sigma$. By Section 2, $\tau = [-p]^i\sigma$ for some $i$. Let $c$ be the class of $[-p]$ in $(\mathbb Z/q_0)^\times$. Suppose that $\sigma$ is a b-place. Then $\sigma$ has class $-1$ modulo $q_0$, and $\tau$ has class $1$. So $-c^i = 1$. Raise this to the odd power $o_0$: $1 = (-c^i)^{o_0} = -(c^{o_0})^i = -1$. But $1 \ne -1$ in $(\mathbb Z/q_0)^\times$: this is the case $n = 0$ of [the lemma](/decl/New.Parameters.d_pow_ne_neg_one/) that no power of $d$ is $-1$ modulo $q_0$. $\square$

The weight of a place is $a/x$ at a b-place and $a/x_1$ at every other place ([Lemma](/decl/New.Data.cast_weight/)). So:

**Corollary.** Let $\Lambda$ be marked, and let $w_\sigma \in \Lambda$ or $\bar w_\sigma \in \Lambda$. Then the weight of $\sigma$ is $\kappa(\sigma) = a/x_1$.

Lean: `New.Data.IsMarked.cast_weight_eq` (New/UpperBound/Divisibility/MarkedPrimes.lean).

### The balance between $\Lambda$ and its conjugate

The weight of lift $j$ at $\tau$ is $\kappa_j(\tau) = \kappa(\tau) + (j + \tfrac12)\Delta$, from [the places and the weights](/chapter/data-and-sizes/#the-places-and-the-weights). The next three statements say that the places inducing $\Lambda$ and those inducing $\bar\Lambda$ look the same to any function of the weight.

**Lemma.** Let $\Lambda$ be marked, $\mathfrak l \in \Lambda$, $j \in \mathbb N$ and $G : \mathbb N \to \mathbb R$. Then

$$\sum_{\tau : w_\tau = \mathfrak l} G(\kappa_j(\tau)) = \sum_{\tau : w_\tau = \bar{\mathfrak l}} G(\kappa_j(\tau)).$$

Lean: `New.Data.IsMarked.sum_inducedPlace_eq_sum_star` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The map $\tau \mapsto [-p]\tau$ is a bijection of $\Phi$. It sends the places inducing $\mathfrak l$ onto those inducing $\bar{\mathfrak l}$, by the last lemma with $e = 1$. For $\tau$ with $w_\tau = \mathfrak l$, both $\tau$ and $[-p]\tau$ have a prime of $\Lambda$ or its conjugate as induced prime. By the corollary both weights are $a/x_1$. So $\kappa_j(\tau) = \kappa_j([-p]\tau)$, and the terms match. $\square$

**Proposition.** Let $\Lambda$ be marked, $j \in \mathbb N$ and $G : \mathbb N \times \{\text{primes of } E\} \to \mathbb R$. Then

$$\sum_{\tau \in \Phi_\Lambda} G(\kappa_j(\tau), w_\tau) = \sum_{\tau \in \bar\Phi_\Lambda} G(\kappa_j(\tau), \bar w_\tau).$$

Lean: `New.Data.IsMarked.sum_placesInducing_eq_sum_placesInducingConj` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Group the left side by $\mathfrak l = w_\tau \in \Lambda$, and the right side by $\mathfrak l = \bar w_\tau \in \Lambda$. Both become sums over $\mathfrak l \in \Lambda$. For a fixed $\mathfrak l$, the left inner sum runs over $\tau$ with $w_\tau = \mathfrak l$ and the right one over $\tau$ with $w_\tau = \bar{\mathfrak l}$, both with the function $c \mapsto G(c, \mathfrak l)$. The lemma gives equality. $\square$

**Corollary.** In the setting of the proposition,

$$\sum_{\tau \in \Phi} \Big( [w_\tau \in \Lambda]\, G(\kappa_j(\tau), w_\tau) - [\bar w_\tau \in \Lambda]\, G(\kappa_j(\tau), \bar w_\tau) \Big) = 0,$$

where $[\,\cdot\,]$ is $1$ if the condition holds and $0$ if not.

Lean: `New.Data.IsMarked.sum_inducedPlace_sub_star_eq_zero` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Split the sum into two sums, and write each as a sum over $\Phi_\Lambda$ or $\bar\Phi_\Lambda$. The proposition says they are equal. $\square$

The valuation at non-split primes in [divisibility prime by prime](/chapter/divisibility/) uses this corollary. There $G$ is the valuation of a Hecke eigenvalue or of a scaling factor at a prime: the gain at $\mathfrak l$ and the loss at $\bar{\mathfrak l}$ cancel in total.

### Local properties of a marked prime

**Lemma.** Let $\Lambda$ be marked and $\mathfrak l \in \Lambda$. Then $p \in \mathfrak l$, and $p$ is a uniformiser at $\mathfrak l$: the $\mathfrak l$-adic valuation of $p$ is $\exp(-1)$ in the multiplicative notation of the source.

Lean: `New.Data.IsMarked.valuation_natCast_eq_exp_neg_one`, `New.Data.IsMarked.natCast_mem_asIdeal` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The prime $\mathfrak l = w_\tau$ lies above $p$. Since $p$ is inert in $K$, it does not divide $q_1 d$. The extension $E/\mathbb Q$ ramifies only at primes dividing $q_1 d$, so $\mathfrak l$ is unramified over $p$, and $\mathrm{ord}_{\mathfrak l}(p) = 1$. $\square$

**Lemma.** Every prime $\mathfrak l$ of a marked set is split: $\bar{\mathfrak l} \ne \mathfrak l$.

Lean: `New.Data.IsMarked.isSplit` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* If $\bar{\mathfrak l} = \mathfrak l$, then $\bar{\mathfrak l} \in \Lambda$, which contradicts condition 1. $\square$

### Collisions

The collision sum comes from [short columns and the gain](/chapter/short-columns-gain/). For a set $S \subseteq \Phi$, a *collision outside* $S$ is a pair $(\tau, e)$ with $e \in I_p$ (that is, $e$ odd, or $p = d$), $\tau$ an a-place not in $S$, and $[-p^e]\tau$ an a-place not in $S$. The collision sum is $\sum_\tau \sum_e a/p^e$ over the collisions outside $S$. For a collision, $p \ne d$, $e$ is odd and $o_0 \mid e$.

**Proposition.** If $\Lambda$ is a full mark, then the collision sum outside $\Phi_\Lambda$ is $0$.

Lean: `New.Data.IsFullMark.collisionSum_placesInducing_eq_zero` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* We show that there is no collision outside $\Phi_\Lambda$. Let $(\tau, e)$ be one. Then $e$ is odd, $\tau$ is an a-place, and $\tau \notin \Phi_\Lambda$. Since $\Lambda$ is full, $\bar w_\tau \in \Lambda$, so $\tau \in \bar\Phi_\Lambda$. By the lemma on conjugation, $[-p^e]\tau \in \Phi_\Lambda$. This contradicts the definition of a collision. So every term of the collision sum is $0$. $\square$

**Remark (Formalization).** The inner sum over $e$ is a `tsum`. Here every term is $0$, so the junk value of a divergent `tsum` plays no role.
