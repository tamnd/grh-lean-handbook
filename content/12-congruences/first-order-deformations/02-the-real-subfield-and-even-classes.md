---
title: The real subfield and even classes
lean:
  - New/Congruences/FirstOrder/KummerMaps.lean
  - New/Congruences/FirstOrder/EvenClasses.lean
  - New/Congruences/FirstOrder/TrianglePrimes.lean
decls:
  - New.Selmer.IsNuSplitPlace
  - New.Selmer.IsNuSplitPlace.prime_pow_dvd_q_sub_one
  - New.Selmer.isConjApart_of_injective_primeBelowPlus
  - New.Selmer.ofGalPlus
  - New.Selmer.ofGalPlus_mul_eq_or
  - New.Selmer.inertiaGroup_le_range_toGalPlus
  - New.Selmer.cyclotomicPlus
  - New.Selmer.tateTwistPlus
  - New.Selmer.evenClasses
  - New.Selmer.comp_ofGalPlus_mem_Z1
  - New.Selmer.four_dvd_cyclotomicChar_sub_one
  - New.Selmer.IsTameGeneratorFamily
  - New.Selmer.withConjInv
  - New.Selmer.IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero
  - New.Selmer.eq_zero_of_forall_mem_Z1_of_mem_evenClasses
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The real subfield and even classes

The Greenberg-Wiles count works best over a totally real field, where complex conjugation acts on each twist by a sign. This section moves from the CM field $E$ to its maximal real subfield $F$. It defines the places used as auxiliary places, the character $\mathrm{cyc}^+$ of $G_F$, and the even classes. The notation is that of [the first section](/chapter/first-order-deformations/#what-the-chapter-proves). For CM fields and their real subfields, see [CM fields](/chapter/cm-fields/).

### Split places

**Definition ($\nu$-split place).** A Frobenius datum $x$, with prime $w$ and Frobenius element $\varphi$, is *$\nu$-split* if $w$ does not lie above $\ell$ and $\varphi$ fixes the $\ell^\nu$-th roots of unity, that is, $\varphi \in G_\nu$.

Lean: `New.Selmer.IsNuSplitPlace` (New/Congruences/FirstOrder/KummerMaps.lean).

**Lemma.** If $x$ is $\nu$-split and its prime has norm $q$, then $\ell^\nu$ divides $q - 1$.

Lean: `New.Selmer.IsNuSplitPlace.prime_pow_dvd_q_sub_one` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The inverse $\varphi^{-1}$ is an arithmetic Frobenius element at a place off $\ell$. It acts on the $\ell^\nu$-th roots of unity by $\zeta \mapsto \zeta^q$. Since $\varphi^{-1} \in G_\nu$, it fixes them, so $q \equiv 1 \pmod{\ell^\nu}$. $\square$

So a $\nu$-split place is a Taylor-Wiles place of level $\ell^\nu$ in the sense of [building the representations](/chapter/building-representations/): its norm is $1$ modulo $\ell^\nu$. For a prime $w$ of $E$, write $w^+$ for the prime of $F$ below $w$.

**Lemma.** Let $x_j$ be Frobenius data of prime norm, with primes $w_j$, such that the primes $w_j^+$ of $F$ are distinct. Then the $w_j$ are distinct, and no $w_j$ is the complex conjugate of any $w_i$.

Lean: `New.Selmer.isConjApart_of_injective_primeBelowPlus` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* If $w_i = w_j$ or $w_i = \bar{w}_j$, then $w_i^+ = w_j^+$, so $i = j$. It remains to see that $w_j \neq \bar{w}_j$. A prime of $E$ of prime norm has residue degree $1$ over $\mathbb{Q}$, so also over $F$. If $w_j = \bar{w}_j$, then $w_j^+$ is inert or ramified in $E$. Ramification is excluded by the lemma on inertia below, and an inert prime has residue degree $2$ over $F$. So $w_j^+$ splits, and $w_j \neq \bar{w}_j$. $\square$

### From $G_F$ back to $G$

The group $G$ has index $2$ in $G_F$, and $G_F = G \cup Gc$. Each $\sigma \in G_F$ is either some $g \in G$ or some $gc$ with $g \in G$.

**Definition (The map back to $G$).** The map $G_F \to G$ sends $g$ and $gc$ to $g$, for $g \in G$. Write it $\sigma \mapsto \sigma^\flat$.

Lean: `New.Selmer.ofGalPlus` (New/Congruences/FirstOrder/KummerMaps.lean).

**Remark (Formalization).** The source defines $\sigma^\flat$ by a choice. It first proves that some $g \in G$ maps to $\sigma$ if $\sigma \in G$, and to $\sigma c$ if not. It then takes the element that the axiom of choice gives. The element is unique because the inclusion of $G$ in $G_F$ is injective. So the choice does not change the meaning of any statement.

The map is continuous, and it is a left inverse of the inclusion of $G$. It is not a homomorphism.

**Lemma.** For $g, h \in G_F$, either $(gh)^\flat = g^\flat h^\flat$ or $(gh)^\flat = g^\flat (h^\flat)^c$.

Lean: `New.Selmer.ofGalPlus_mul_eq_or` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Write $g = a c^{i}$ and $h = b c^{k}$ with $a, b \in G$ and $i, k \in \{0, 1\}$. Then $gh = a c^i b c^k$. If $i = 0$, then $gh = ab\, c^k$, so $(gh)^\flat = ab$. If $i = 1$, then $gh = a b^c c^{1+k}$, and $c^2 = 1$, so $(gh)^\flat = a b^c$. $\square$

**Lemma.** Let $A$ be a place of $\Omega$ above a finite prime $v$ of $F$. Then the inertia group of $A$ in $G_F$ lies in $G$. So $E/F$ is unramified at all finite places.

Lean: `New.Selmer.inertiaGroup_le_range_toGalPlus` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Let $\sigma$ be in the inertia group and suppose $\sigma \notin G$. Then $\sigma$ acts on $E$ as complex conjugation. Since $E$ contains the $5040$-th roots of unity, there is an integer $y$ of $E$ such that $y - \bar{y}$ is a unit ([CM fields](/chapter/cm-fields/)). The inertia condition gives $|\sigma(\bar{y}) - \bar{y}|_A < 1$, that is, $|y - \bar{y}|_A < 1$. So the unit $y - \bar{y}$ lies in the prime below $A$, a contradiction. $\square$

### The character $\mathrm{cyc}^+$

The cyclotomic character of $G_F$ is not the right extension of $\mathrm{cyc}$ for this argument, since its value at $c$ is $-1$.

**Definition ($\mathrm{cyc}^+$).** The character $\mathrm{cyc}^+ \colon G_F \to \mathbb{Z}_\ell^\times$ is the cyclotomic character of $G_F$ times the quadratic character that cuts out $E$. It is $\mathrm{cyc}$ on $G$ and $1$ at $c$.

Lean: `New.Selmer.cyclotomicPlus` (New/Congruences/FirstOrder/KummerMaps.lean).

The character $\mathrm{cyc}^+$ is unramified off $\ell$, by the lemma on inertia, and it is $1$ at every complex conjugation.

**Definition (The twist over $F$).** For $\nu, e \geq 0$, the module $\mathbb{Z}/\ell^\nu$ with $G_F$ acting by $(\mathrm{cyc}^+)^{-e}$ is written $(\mathbb{Z}/\ell^\nu)(-e)^+$.

Lean: `New.Selmer.tateTwistPlus` (New/Congruences/FirstOrder/KummerMaps.lean).

### Even classes

**Definition (Even classes).** Let $O$ be a coefficient ring, $S$ a set of primes of $E$, and $\nu, e \geq 0$. The set of *even classes* of exponent $e$ for $S$ is the set of functions $z \colon G \to O/\ell^\nu$ with these properties.

1. $z$ is a locally constant cocycle for the action $\mathrm{cyc}^{-e}$: $z(gh) = z(g) + \mathrm{cyc}(g)^{-e} z(h)$.
2. $z$ is unramified outside the primes above $\ell$, the primes in $S$, and their complex conjugates: it vanishes on the inertia groups at all other primes.
3. $z(g^c) = z(g)$ for all $g \in G$.
4. $z$ vanishes at every element of a decomposition group above $\ell$ with $\mathrm{cyc} = 1$.

Lean: `New.Selmer.evenClasses` (New/Congruences/FirstOrder/EvenClasses.lean).

The textbook object is the Selmer group of the Tate twist, a subgroup of $H^1(G, (O/\ell^\nu)(-e))$ cut out by local conditions ([local duality](/chapter/local-duality/)). Complex conjugation acts on $H^1$, and the even part is the $+1$ eigenspace. The source works with cocycles, not with classes.

**Remark (Formalization).** An even class in the source is a cocycle, not a cohomology class. A coboundary $g \mapsto (\mathrm{cyc}(g)^{-e} - 1) b$ lies in the set when it satisfies the four conditions, and it is not identified with $0$. The statements of this chapter are about values $z(g)$ at given elements, so they hold for each cocycle. Condition 4 asks more than a local condition on classes: it asks the cocycle itself to vanish on $\ker \mathrm{cyc}$ in each decomposition group above $\ell$. The values lie in vectors of length one over $O/\ell^\nu$. This is a matrix form of the scalar module, and it does not change the meaning.

Condition 3 is the meaning of "even" here. Over $F$, the element $c$ acts on $(O/\ell^\nu)(-e)^+$ by $\mathrm{cyc}^+(c)^{-e} = 1$. So conjugation by $c$ sends a cocycle $z$ to $g \mapsto z(cgc)$, and an even class is a fixed point of this action.

**Lemma.** Let $z \colon G \to \mathbb{Z}/\ell^\nu$ be a cocycle for $\mathrm{cyc}^{-e}$ with $z(g^c) = z(g)$ for all $g$. Then $z^+ = z \circ \flat$, the function $z^+(\sigma) = z(\sigma^\flat)$ on $G_F$, is a cocycle for $(\mathbb{Z}/\ell^\nu)(-e)^+$.

Lean: `New.Selmer.comp_ofGalPlus_mem_Z1` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Let $g, h \in G_F$. If $(gh)^\flat = g^\flat h^\flat$, then $z^+(gh) = z(g^\flat) + \mathrm{cyc}(g^\flat)^{-e} z(h^\flat)$, and $\mathrm{cyc}(g^\flat) = \mathrm{cyc}^+(g)$ since $\mathrm{cyc}^+(c) = 1$. If $(gh)^\flat = g^\flat (h^\flat)^c$, the same holds because $z((h^\flat)^c) = z(h^\flat)$. Continuity holds because $\flat$ is continuous. $\square$

The next lemma is used for the divisibility of $\mathrm{cyc}(\gamma)^a - 1$ in the triangle of primes.

**Lemma.** For every $a \in G$, $4$ divides $\mathrm{cyc}(a) - 1$ in $\mathbb{Z}_\ell$.

Lean: `New.Selmer.four_dvd_cyclotomicChar_sub_one` (New/Congruences/FirstOrder/EvenClasses.lean).

*Proof.* If $\ell$ is odd, $4$ is a unit of $\mathbb{Z}_\ell$. If $\ell = 2$, then $E$ contains the $16$-th roots of unity, since $16$ divides $5040$. The element $a$ fixes them, so $\mathrm{cyc}(a) \equiv 1 \pmod{16}$. $\square$

### Tame generator families

**Definition (Tame generator family).** Let $w_j$ be primes of $E$ and $\tau_j, \varphi_j \in G$, indexed by $j \in J$. They form a *tame generator family* of level $\nu$ if, for each $j$, the prime $w_j$ is not above $\ell$, $\varphi_j \in G_\nu$, and $\tau_j$ is the chosen tame generator at some place of $\Omega$ above $w_j$.

Lean: `New.Selmer.IsTameGeneratorFamily` (New/Congruences/FirstOrder/EvenClasses.lean).

**Definition (Doubled family).** For a family $\tau_j$, the *doubled family* is indexed by $J \times \{\mathrm{true}, \mathrm{false}\}$. Its value at $(j, \mathrm{true})$ is $\tau_j$, and its value at $(j, \mathrm{false})$ is $(\tau_j^c)^{-1}$.

Lean: `New.Selmer.withConjInv` (New/Congruences/FirstOrder/EvenClasses.lean).

The element $(\tau_j^c)^{-1}$ generates tame inertia at the conjugate place $\bar{w}_j$. So the doubled family has one generator at each $w_j$ and one at each $\bar{w}_j$.

**Lemma (Killing tame generators removes ramification).** Let $w_j, \tau_j, \varphi_j$ be a tame generator family. Let $\rho$ be a representation of $G$ that is trivial on the elements of inertia groups off a set $S$ that have $\mathrm{cyc} = 1$. Let $z$ be a locally constant cocycle of $\rho$ modulo $\ell^e$ that is unramified off a set $T \subseteq S \cup \{w_j\} \cup \{\bar{w}_j\}$ and obeys a set $L$ of linear relations. If $z$ vanishes on the doubled family of the $\tau_j$, then $z$ is unramified off $S$, and it still obeys the relations $L$.

Lean: `New.Selmer.IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero` (New/Congruences/FirstOrder/EvenClasses.lean).

*Proof.* Only the primes $w_j$ and $\bar{w}_j$ that are not in $S$ must be removed. Fix such a prime, off $\ell$. On its inertia group the elements with $\mathrm{cyc} = 1$ act trivially through $\rho$, and the cyclotomic character is trivial on inertia off $\ell$. So $z$ is a homomorphism on that inertia group. It is locally constant with values in a group killed by a power of $\ell$, so it factors through the maximal pro-$\ell$ quotient of inertia. That quotient is a quotient of tame inertia, which the tame generator $\tau_j$ generates topologically. So $z(\tau_j) = 0$ makes $z$ vanish on the inertia at $w_j$. At $\bar{w}_j$ the element $(\tau_j^c)^{-1}$ plays the same part. The relations $L$ do not depend on the set of primes. $\square$

**Lemma (Testing with maps to $\mathbb{Z}/\ell^\nu$).** Let $z$ be an even class of exponent $e$, and let $b \in O/\ell^\nu$. Suppose that $u(b) = 0$ for every additive map $u \colon O/\ell^\nu \to \mathbb{Z}/\ell^\nu$ such that $u \circ z$ is a cocycle for $\mathrm{cyc}^{-e}$ modulo $\ell^\nu$. Then $b = 0$.

Lean: `New.Selmer.eq_zero_of_forall_mem_Z1_of_mem_evenClasses` (New/Congruences/FirstOrder/EvenClasses.lean).

*Proof.* The group $O/\ell^\nu$ is a free $\mathbb{Z}/\ell^\nu$-module, since $O$ is free over $\mathbb{Z}_\ell$. So the additive maps to $\mathbb{Z}/\ell^\nu$ separate its points. Every additive map $u$ commutes with multiplication by the integer $\mathrm{cyc}(g)^{-e}$ modulo $\ell^\nu$, so $u \circ z$ is a cocycle for every $u$. $\square$

The lemma reduces statements about even classes with values in $O/\ell^\nu$ to statements about cocycles with values in $\mathbb{Z}/\ell^\nu$. The reciprocity law of the next section is proved in this way.
