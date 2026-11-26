---
title: Where the argument uses them
lean:
  - New/Derivatives/Sharpness/NearPairs.lean
  - New/Derivatives/Sharpness/Cases.lean
  - New/Derivatives/FormalGroup/ThetaProducts.lean
  - New/Congruences/LocalLoss/Basic.lean
  - New/Congruences/LocalLoss/CrystallineDefect.lean
decls:
  - New.Data.notMem_bPlaces_of_two_partners
  - New.Data.IsNearPair
  - New.Data.IsNearPair.exponent_unique
  - New.Data.IsNearPair.eq_and_eq_of_partner_eq
  - New.Data.IsNearPair.end_ne_start
  - New.Selmer.placeClass_eq_cmSign_mul_pow
  - New.Selmer.notMem_bPlaces_of_short_arc
  - New.Selmer.notMem_bPlaces_of_coefficientEmbedding_eq_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Where the argument uses them

A search of the source for the field `sparse` of the data and for the lemmas built on it finds exactly two uses. Both are in the second half of the argument, far from the construction. The first is in Volume 11, in the proof that [the divisibility is sharp](/chapter/sharpness/), at the primes $p \leq k$ that do not split in $K$. The second is in Volume 12, in [the local loss at ℓ](/chapter/local-loss/), at the primes $\ell \leq kt$. Each use reduces to the definition of sparseness through one short lemma, and this section states and proves these lemmas. The determinant part of the argument does not use sparseness. This section also explains why the two uses need exactly the parameters of the definition: the bound $kt$ on the primes, the range $0 < i < j < l_0$ of the exponents, and the signs.

### Use 1: near pairs at non-split primes

Let $p$ be a prime. For $e \in \mathbb{N}$ and a place $\tau$, the *partner* of $\tau$ at the exponent $e$ is the place $[-p^e]\,\tau$. Volume 11 bounds the $p$-adic valuation of the coefficients of a product of theta series. In that bound the variable $z_\tau$ of a place is coupled with the variable of its partner, through the monomials $z_\tau^{p^e} z_{[-p^e]\tau}$. The exponents $e$ run over a set $I_p$: the odd $e \geq 1$ if $p$ is inert in $K$, all $e \geq 1$ if $p = d$, and no $e$ if $p$ splits.

Lean: `New.Parameters.partner` (New/Derivatives/FormalGroup/ThetaProducts.lean).

The loss in the valuation bound comes from the couplings in which both places have the large weight $b$. The source calls such a coupling a near pair.

**Definition (Near pair).** Let $D$ be data, $p$ a prime, $\tau$ a place and $e \in \mathbb{N}$. The pair $(\tau, e)$ is a *near pair* if $e \in I_p$, $2e < l_0$, $\tau$ is a $b$-place, and its partner $[-p^e]\tau$ is a $b$-place. The place $\tau$ is its start and $[-p^e]\tau$ its end.

Lean: `New.Data.IsNearPair` (New/Derivatives/Sharpness/NearPairs.lean).

For $p = d$ there are no near pairs, because a place and its partner then have different classes modulo $q_0$, while all $b$-places have class $-1$. So near pairs occur only at inert primes, with odd exponents, and then $[-p^e] = [-p]^e$.

**Lemma (Sparseness along the powers of $-p$).** Let $p \leq k$ be a prime with $\chi_K(p) \neq 1$, let $\sigma$ be a place, and let $0 < i < j < l_0$. Then the three places $\sigma$, $[-p]^i\sigma$, $[-p]^j\sigma$, distinct or not, are not all $b$-places.

Lean: `New.Data.notMem_bPlaces_of_two_partners` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Every prime that divides $q_1$ splits in $K$, so $p \nmid q_1$ and $-p$ is prime to $q_0$. The ratio $[-p]^n\sigma/\sigma = [-p]^n$ has class $(-p)^n = (-1)^n p^n$ modulo $q_1^{(p)}$. Since $t = 5r$ is odd, $t \geq 1$ and $p \leq k \leq kt$. So the field `sparse` of the data applies to $\ell = p$, $i$, $j$, the places $\sigma$, $[-p]^i\sigma$, $[-p]^j\sigma$ and the signs $\epsilon = (-1)^i$, $\epsilon' = (-1)^j$. It says that these places are not all in $\Phi_b$. $\square$

The three consequences describe how near pairs can meet. In each, $p \leq k$ is prime with $\chi_K(p) \neq 1$.

**Lemma (One exponent at each start).** If $(\tau, e)$ and $(\tau, e')$ are near pairs, then $e = e'$.

Lean: `New.Data.IsNearPair.exponent_unique` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* Suppose $e < e'$. The places $\tau$, $[-p]^e\tau$ and $[-p]^{e'}\tau$ are $b$-places, and $0 < e < e' < l_0/2 < l_0$. This contradicts the previous lemma. $\square$

**Lemma (One start at each end).** If $(\tau, e)$ and $(\tau', e')$ are near pairs with the same end, $[-p^e]\tau = [-p^{e'}]\tau'$, then $\tau = \tau'$ and $e = e'$.

Lean: `New.Data.IsNearPair.eq_and_eq_of_partner_eq` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* It suffices to show $e = e'$, since then $\tau = \tau'$ by cancellation. Suppose $e < e'$. Then $\tau = [-p]^{e' - e}\tau'$. The places $\tau'$, $\tau = [-p]^{e' - e}\tau'$ and $[-p]^{e'}\tau'$ are $b$-places, with $0 < e' - e < e' < l_0$. This contradicts the lemma on sparseness along the powers of $-p$. $\square$

**Lemma (An end is not a start).** If $(\tau, e)$ and $(\tau', e')$ are near pairs, then $[-p^e]\tau \neq \tau'$.

Lean: `New.Data.IsNearPair.end_ne_start` (New/Derivatives/Sharpness/NearPairs.lean).

*Proof.* If $\tau' = [-p]^e\tau$, then $[-p]^{e'}\tau' = [-p]^{e + e'}\tau$ is a $b$-place. So $\tau$, $[-p]^e\tau$ and $[-p]^{e + e'}\tau$ are $b$-places, with $0 < e < e + e'$ and $e + e' < l_0/2 + l_0/2 = l_0$. This contradicts the same lemma. $\square$

These three lemmas are the only facts about $b$-places that the sharpness bound at $p \leq k$ needs. In `New/Derivatives/Sharpness/Cases.lean` the set $\Phi_0$ of starts of near pairs is fixed, with one exponent $e(\tau)$ for each start by the first lemma. The second lemma makes the near pairs a *coupling family*: no end is reached from two starts. The third lemma shows that the degrees at starts and at ends do not overlap. Then the couplings $z_\tau^{p^{e(\tau)}} z_{[-p^{e(\tau)}]\tau}$, each used $\lfloor l_\tau/p^{e(\tau)} \rfloor$ times, fit inside the degree $l$, and the bound $v(l!) + \operatorname{val}_{12}(l) \leq S_p + 2\sum_\tau v(B_\tau)$ follows. Without sparseness, a chain $\tau \to [-p]^e\tau \to [-p]^{e+e'}\tau$ of $b$-places would make one place both an end and a start, and the counting of degrees would fail.

**Remark (Formalization).** The partner is defined through `P.placeOfInt s (-p ^ e)`, the place of the class of $-p^e$ modulo $q_1$. If this class is not a unit, the place is the identity by the convention of `placeOfInt`, and the partner of $\tau$ is $\tau$ itself. This junk value does not arise for the primes of this section: the proof of the lemma on sparseness along the powers of $-p$ first shows $p \nmid q_1$, so the class is a unit.

**Remark (Formalization).** The use needs sparseness only for $\ell \leq k$, but the data require it for $\ell \leq kt$. The larger range is for the second use. For the exponents, the use needs $0 < i < j$ with $j < l_0$, and near pairs have $2e < l_0$, so the sum of two exponents of near pairs stays below $l_0$. This is why the condition $2e < l_0$ appears in the definition of a near pair.

### Use 2: the local loss at ℓ

Volume 12 compares the Galois representations of the argument with crystalline lattices at a prime $\ell$. The bound for the loss at $\ell$ uses integral $p$-adic Hodge theory in the form of Kummer charts, with $p = \ell$. Each $g \in G_\ell$ has a *letter* $g\zeta$, the image under $g$ of a root of unity $\zeta$ of order $\ell^f - 1$ in a ring $O$ of coefficients (in Lean, `coefficientEmbedding O g ζ`). Frobenius acts on the letters by $z \mapsto z^\ell$. A letter is a *b-letter* if it is the letter of some $g$ whose complex embedding $\sigma_g$, defined below, lies over a $b$-place. The estimate `New.Lift.KummerChart.hasCupExponent_sparse_thick` of Volume 12 gives an explicit exponent of $\ell$ that makes the crystalline cocycles orthogonal under cup product. One of its hypotheses is that no three $b$-letters follow one another along the orbits of $z \mapsto z^\ell$ with both gaps between $1$ and a bound $J$.

The bridge between Galois elements and places is the following lemma. Fix an isomorphism $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. For an embedding $e \colon E \to \overline{\mathbb{Q}}_\ell$ and $g \in G_\ell = \operatorname{Gal}(\overline{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$, put $\sigma_g = \iota^{-1} \circ g^{-1} \circ e$, a complex embedding of $E$. Let $\operatorname{sgn}(\sigma) \in \{\pm 1\}$ be $1$ if $\sigma$ is the embedding of the CM type at its place and $-1$ otherwise.

**Lemma (Ratios of places from Galois elements).** Let $e \colon E \to \overline{\mathbb{Q}}_\ell$, let $g, g' \in G_\ell$, and let $a, n \in \mathbb{N}$. Suppose that $g' g^{-1}$ sends $e(\zeta_{q_1})^{\ell^a}$ to its $\ell^n$-th power. Let $y$ be the place with $\operatorname{pl}(\sigma_{g'})\, y = \operatorname{pl}(\sigma_g)$, where $\operatorname{pl}$ is the place of an embedding. Then for every $q \mid q_1$ prime to $\ell^a$,
$$\operatorname{cl}_q(y) = \operatorname{sgn}(\sigma_g)\operatorname{sgn}(\sigma_{g'})\, \ell^n.$$

Lean: `New.Selmer.placeClass_eq_cmSign_mul_pow` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* A place acts on $\zeta = \zeta_{q_1}$ as the power given by its class. The embedding of the CM type at the place of $\sigma$ sends $\zeta$ to $\sigma(\zeta)^{\operatorname{sgn}(\sigma)}$, since complex conjugation inverts $\zeta$. Compare the places of $\sigma_g$ and $\sigma_{g'}$ on $\zeta$ and carry the identity to $\overline{\mathbb{Q}}_\ell$ by $\iota$ and $g'$. With $z = e(\zeta)$, a primitive $q_1$-th root of unity, this gives $(g'g^{-1})(z)^{s} = z^{s' c}$, where $s, s'$ are the two signs and $c$ is the class of $y$ modulo $q_1$. Raise to the power $\ell^a$ and use the hypothesis: $z^{\ell^n s \ell^a} = z^{s' c \ell^a}$. So $q_1$ divides $(\ell^n s - s' c)\ell^a$. For $q \mid q_1$ prime to $\ell^a$, this gives $s' c \equiv \ell^n s \pmod q$, and multiplication by $s' = \pm 1$ gives $c \equiv s s' \ell^n$. $\square$

The power $\ell^a$ removes the $\ell$-part of $\zeta_{q_1}$, on which Galois acts in a way that is not a power of $\ell$. This is why the definition of sparseness reads the classes modulo $q_1^{(\ell)}$ and not modulo $q_1$. The signs come from complex conjugation, and this is why the definition allows the signs $\epsilon, \epsilon'$.

**Lemma (No three $b$-places on a short arc).** Let $\ell \leq kt$ be a prime, $e \colon E \to \overline{\mathbb{Q}}_\ell$, $g, g', g_1 \in G_\ell$, $a \in \mathbb{N}$, and $0 < i < n < l_0$. Suppose that $g'g^{-1}$ and $g' g_1^{-1}$ send $e(\zeta_{q_1})^{\ell^a}$ to its $\ell^n$-th and its $\ell^i$-th power. If the places of $\sigma_g$ and $\sigma_{g'}$ are $b$-places, then the place of $\sigma_{g_1}$ is not.

Lean: `New.Selmer.notMem_bPlaces_of_short_arc` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* Suppose that it is. Apply the previous lemma with $q = q_1^{(\ell)}$, which is prime to $\ell^a$. The ratio of the place of $\sigma_{g_1}$ to that of $\sigma_{g'}$ has class $\pm\ell^i$, and the ratio of the place of $\sigma_g$ to that of $\sigma_{g'}$ has class $\pm\ell^n$. So the three $b$-places $\operatorname{pl}(\sigma_{g'})$, $\operatorname{pl}(\sigma_{g_1})$, $\operatorname{pl}(\sigma_g)$ form a configuration that the field `sparse` excludes, with $\sigma = \operatorname{pl}(\sigma_{g'})$, $i$ and $j = n$. $\square$

The lemma that Volume 12 applies is phrased with letters.

**Lemma (No three close $b$-letters).** Let $\ell \leq kt$ be a prime. Let $j \colon \Gamma \to G_\ell$ identify $\Gamma$ with the group of elements of $G_\ell$ that fix $e(E)$, let $F$ in the image of $j$ be a Frobenius for $\ell^f$, and let $\zeta \in O$ be a primitive $(\ell^f - 1)$-th root of unity. Let $h = \Delta/2 = r^8$ be the half gap of the data, and let $1 \leq a, c \leq \lfloor \log_\ell(h^3) \rfloor$. Let $g_0, g_1, g_2 \in G_\ell$ with $g_1\zeta = (g_0\zeta)^{\ell^a}$ and $g_2\zeta = (g_0\zeta)^{\ell^{a+c}}$. If the places of $\sigma_{g_0}$ and $\sigma_{g_2}$ are $b$-places, then the place of $\sigma_{g_1}$ is not.

Lean: `New.Selmer.notMem_bPlaces_of_coefficientEmbedding_eq_pow` (New/Congruences/LocalLoss/CrystallineDefect.lean). Lean names the second gap `b`; here it is $c$, to keep $b$ for the weight.

*Proof.* Let $\xi$ be the part of $e(\zeta_{q_1})$ of order prime to $\ell$, that is, $e(\zeta_{q_1})^{\ell^{v}}$ with $v = v_\ell(q_1)$. The Frobenius $F$ fixes $e(E)$, so $\xi^{\ell^f - 1} = 1$, and $\xi$ is a power of the letter root. From $g_2\zeta = (g_0\zeta)^{\ell^{a+c}}$ and $g_2 \zeta = (g_1\zeta)^{\ell^c}$ it follows that $g_2 g_0^{-1}$ and $g_2 g_1^{-1}$ raise $\xi$ to the powers $\ell^{a+c}$ and $\ell^c$. The half gap satisfies $h^3 \leq (2^s)^{12}$ in the data, so $\lfloor \log_\ell(h^3) \rfloor \leq 12 s$. Hence $0 < c < a + c \leq 24 s \leq 27 s < l_0$. The lemma on short arcs, with $g = g_0$, $g' = g_2$, $g_1$, $i = c$ and $n = a + c$, gives the claim. $\square$

In Lean, $h$ is `D.halfGap`. The next lemma of the source, `New.Selmer.eventually_exists_lettersReadThick`, packs this into the clause of the Kummer chart that no three $b$-letters follow one another at distances at most $\lfloor \log_\ell(h^3) \rfloor$ along $z \mapsto z^\ell$, for $\ell \leq kt$. That is the hypothesis `h_sparse` of `New.Lift.KummerChart.hasCupExponent_sparse_thick` with $J = \lfloor \log_\ell(h^3) \rfloor$.

**Remark (Formalization).** The three parameters of sparseness are fixed by this use. The primes run up to $kt$ because the clause on close $b$-letters in `New.Selmer.eventually_exists_lettersReadThick` is asserted for $\ell \leq Q$ with $Q = kt$. The exponents run up to $l_0 > 27s$ because the gaps run up to $J \leq 12 s$ and two gaps sum to at most $24 s$. The signs are free because complex conjugation can change the sign at each step, through $\operatorname{sgn}(\sigma_g)$. So this use needs $l_0 > 27 s$, and $l_0$ is defined as the least power of $3$ above $27 s$.

### Why the uses need a large set

Neither use needs $\Phi_b$ to be large. An empty set of $b$-places is sparse. The size enters in a third place: in [the main inequality](/chapter/main-inequality/), where the ratio of the numbers of places of the two weights enters the final bound, as Section 1 explains. So the argument asks for two things that pull in opposite directions. The main inequality needs many $b$-places, and the local analysis at the primes $p \leq k$ and $\ell \leq kt$ needs that the $b$-places do not crowd along the orbits of Frobenius. A set of Behrend's type meets both demands. It has $\#\Phi_b \geq \operatorname{towerDeg}(s)/\log b$. This is far from a positive proportion of the $\operatorname{towerDeg}(s)$ places of class $-1$, as the theorem of Roth forces, but it is only a factor $\log b$ below it, and the main inequality can absorb that factor.
