---
title: Kummer maps and the reciprocity law
lean:
  - New/Congruences/FirstOrder/KummerMaps.lean
decls:
  - New.Selmer.familyPrimes
  - New.Selmer.kummerSetting
  - New.Selmer.IsKummerMap
  - New.Selmer.HasKummerType
  - New.Selmer.IsKummerMap.hasKummerType
  - New.Selmer.two_nsmul_comp_ofGalPlus_mem_cocycles
  - New.Selmer.IsKummerMap.sum_eq_zero
  - New.Selmer.exists_isTameGeneratorFor_toGalPlus
  - New.Selmer.exists_apply_eq_nsmul_of_mem_evenClasses
  - New.Selmer.IsKummerMap.nsmul_apply_tameGenerator_eq_zero
  - New.Selmer.kummerReductions
  - New.Selmer.exists_card_lt_finrank_kummerReductions
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kummer maps and the reciprocity law

The places of the triangle are chosen one at a time. At each step the argument needs a function on $G$ that pairs with every even class and that sees a new place. These functions are the Kummer maps. They are the restrictions to $G$ of the relations of the Greenberg-Wiles count over $F$. This section defines them, proves the reciprocity law that they satisfy, and counts them modulo $\ell$. The even classes come from the later chapter [tied traces and even classes](/chapter/tied-traces/), and this section uses them in the form of [the previous section](/chapter/first-order-deformations/#the-real-subfield-and-even-classes).

The notation is that of [the real subfield and even classes](/chapter/first-order-deformations/#the-real-subfield-and-even-classes). In particular $x \mapsto x^\flat$ is the map $G_F \to G$, $\mathrm{cyc}^+$ is the extension of $\mathrm{cyc}$ that is $1$ at $c$, and $w^+$ is the prime of $F$ below a prime $w$ of $E$.

### The setting over $F$

Let $x_i$, for $i$ in a finite set $I$, be $\nu$-split places. Each prime $u$ of $F$ gets a chosen place of $\Omega$ above it. If $u = x_i^+$ for some $i$, the chosen place is the place of such an $x_i$. Otherwise it is any place above $u$. The source makes these choices with the axiom of choice. Since all places above $u$ are conjugate, the choice changes the local groups only by conjugation.

**Definition (The primes $S_0$).** The set $S_0$ is the finite set of primes of $F$ that lie above $\ell$ or below one of the $x_i$.

Lean: `New.Selmer.familyPrimes` (New/Congruences/FirstOrder/KummerMaps.lean).

**Definition (Kummer setting).** For an exponent $e$, the *Kummer setting* is the relation setting over $F$ with these data.

1. The module is $(\mathbb{Z}/\ell^\nu)(-e)^+$.
2. The subgroup is the kernel of $\mathrm{cyc}^+$ modulo $\ell^\nu$. It acts trivially on the module.
3. The local primes are the primes in $S_0$, with the chosen places above them.
4. The local condition at $u \in S_0$ is the set of functions on the decomposition group that vanish on its part in $\ker \mathrm{cyc}^+$ if $u$ lies above $\ell$, and that vanish everywhere if not.

Lean: `New.Selmer.kummerSetting` (New/Congruences/FirstOrder/KummerMaps.lean).

The setting is a case of the general count in [local duality](/chapter/local-duality/). At a prime $u = x_i^+$ off $\ell$, the decomposition group lies in the kernel of $\mathrm{cyc}^+$ modulo $\ell^\nu$, because its inertia does and a Frobenius element in $G_\nu$ generates the rest. So the module is trivial there, the coboundaries vanish on the decomposition group, and the zero condition contains them.

A *relation* off a finite set $T$ of primes of $F$, in the sense of [local duality](/chapter/local-duality/), is a locally constant homomorphism $y$ from the subgroup to the Cartier dual of the module. It is extended by $0$ to $G_F$. It satisfies $y(g a g^{-1}) = \mathrm{cyc}^+(g)\, y(a) \circ g^{-1}$ and vanishes on inertia at the primes outside $T$. It also satisfies a reciprocity condition. For every finite family of distinct primes $p \notin T$ of $F$, with Frobenius elements $\varphi_p$ in the subgroup and tame generators $\gamma_p$, and for every cocycle $z$ that satisfies the local conditions at $S_0$, vanishes at complex conjugations, and is unramified off $S_0$ and the $p$, it gives
$$\sum_p y(\varphi_p)(z(\gamma_p)) = 0.$$
A relation stands in place of a dual Selmer class. The condition is what global duality gives for a dual class, and the count of relations in [local duality](/chapter/local-duality/) is proved in this form.

**Definition (Kummer map).** A function $\psi \colon G \to \mathbb{Z}/\ell^\nu$ is a *Kummer map* of exponent $e$ off $T$ for the family $x$ if there is a relation $y$ off $T$ in the Kummer setting with
$$y(g)(a) = a\,\psi(g)/\ell^\nu \in \mathbb{Q}/\mathbb{Z}$$
for all $g \in G$ and $a \in \mathbb{Z}/\ell^\nu$.

Lean: `New.Selmer.IsKummerMap` (New/Congruences/FirstOrder/KummerMaps.lean).

A Kummer map vanishes outside $G_\nu$, since the relation does.

### The type of a Kummer map

**Definition (Kummer type).** A function $\psi \colon G \to \mathbb{Z}/\ell^\nu$ has *Kummer type* of exponent $e$ if these hold.

1. $\psi$ is locally constant.
2. $\psi(ab) = \psi(a) + \psi(b)$ for $a, b \in G_\nu$.
3. $\psi(a^c) = -\psi(a)$ for $a \in G_\nu$.
4. $\psi(g a g^{-1}) = \mathrm{cyc}(g)^{e+1} \psi(a)$ for $g \in G$ and $a \in G_\nu$, with $\mathrm{cyc}$ taken modulo $\ell^\nu$.

Lean: `New.Selmer.HasKummerType` (New/Congruences/FirstOrder/KummerMaps.lean).

**Theorem.** Every Kummer map of exponent $e$ off $T$ has Kummer type of exponent $e$.

Lean: `New.Selmer.IsKummerMap.hasKummerType` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Let $y$ be the relation of $\psi$. Then $\psi(g)/\ell^\nu = y(g)(1)$. The relation is locally constant and a homomorphism on the subgroup, which gives 1 and 2. For $g \in G_F$ and $a \in G_\nu$, the equivariance of $y$ gives
$$y(g a g^{-1})(1) = \mathrm{cyc}(g)\,\mathrm{cyc}^+(g)^{e}\, y(a)(1),$$
since $g^{-1}$ acts on the module by $\mathrm{cyc}^+(g)^{e}$ and on $\mathbb{Q}/\mathbb{Z}$-valued duals through the cyclotomic character of $G_F$. For $g \in G$ both characters are $\mathrm{cyc}(g)$, which gives 4. For $g = c$, the cyclotomic character of $G_F$ is $-1$ and $\mathrm{cyc}^+(c) = 1$, which gives 3. $\square$

So a Kummer map is odd under $c$ and has weight $e + 1$ under conjugation. This is the twist dual to $(\mathbb{Z}/\ell^\nu)(-e)$. For $e = 0$, a Kummer character $a \mapsto a(\alpha^{1/\ell^\nu})/\alpha^{1/\ell^\nu}$ on $G_\nu$, with $\alpha \in E^\times$, has the same weight $1$ under conjugation, and this is the reason for the name.

### Even classes as cocycles over $F$

An even class lives on $G$, and a relation lives on $G_F$. The next lemma moves an even class to $G_F$. It needs the factor $2$.

**Lemma.** Let $x$ be a finite family of $\nu$-split places, and let $P$ be a set of primes of $F$ disjoint from $S_0$. Let $z \colon G \to \mathbb{Z}/\ell^\nu$ be a cocycle for $\mathrm{cyc}^{-e}$ modulo $\ell^\nu$ with these properties:

1. $z(g^c) = z(g)$ for all $g \in G$;
2. $z$ vanishes on inertia above every prime of $F$ that is not above $\ell$ and not in $P$;
3. $z$ vanishes on the elements of $\ker \mathrm{cyc}$ in decomposition groups above $\ell$;
4. $z(\varphi_i) = 0$ for the Frobenius element $\varphi_i$ of each $x_i$.

Then $2 z^+$, where $z^+(\sigma) = z(\sigma^\flat)$, is a cocycle of the Kummer setting that is unramified off $S_0 \cup P$, satisfies the local conditions at $S_0$, and vanishes at complex conjugations.

Lean: `New.Selmer.two_nsmul_comp_ofGalPlus_mem_cocycles` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* By [the lemma on $z \circ \flat$](/chapter/first-order-deformations/#the-real-subfield-and-even-classes), $z^+$ is a cocycle for $(\mathbb{Z}/\ell^\nu)(-e)^+$. It vanishes on inertia off $\ell$ and $P$ because $\flat$ maps such inertia into inertia of $G$. For $g \in \ker \mathrm{cyc}^+$ the cocycle rule gives
$$2 z^+(g) = z^+(g) + \mathrm{cyc}^+(g)^{-e} z^+(g) = z^+(g^2).$$
For a complex conjugation $c'$, $\mathrm{cyc}^+(c') = 1$ and $c'^2 = 1$, so $2 z^+(c') = z^+(1) = 0$. Above $\ell$, let $g$ be in the decomposition group with $\mathrm{cyc}^+(g) = 1$. Since $G$ has index $2$ in $G_F$, $g^2 \in G$. It lies in the decomposition group and has $\mathrm{cyc}(g^2) = 1$, so condition 3 gives $2 z^+(g) = z(g^2) = 0$. At $u = x_i^+$ off $\ell$, the decomposition group of the chosen place is generated topologically by inertia and the Frobenius element of $x_i$. The class $z^+$ vanishes on inertia there by condition 2, and $2z^+$ is a homomorphism on the group, because the module is trivial on it. Condition 4 kills it at the Frobenius element. $\square$

Without the factor $2$ the lemma fails at $c$: the value $z^+(c) = z(1)$ is $0$, but a general complex conjugation is $g c$ with $g \in G$, and $z^+(gc) = z(g)$ need not vanish. The square removes this.

### The reciprocity law

**Theorem (Reciprocity law).** Let $x$ and $w$ be finite families of $\nu$-split places, indexed by $I$ and $J$. Let $T$ be a finite set of primes of $F$ that contains $S_0$. Suppose that the primes $w_j^+$ are distinct and not in $T$. For each $j$, let $\gamma_j \in G$ be a tame generator at the place of $w_j$, normalized over $F$ for $\ell^\nu$. Let $\psi$ be a Kummer map of exponent $e$ off $T$ for $x$. Let $O$ be a coefficient ring, and let $z$ be an even class in $(O/\ell^\nu)(-e)$ for the set of primes $w_j$ that vanishes at the Frobenius elements of $x$. Then
$$\sum_{j \in J} \psi(\varphi_j) \cdot 2 z(\gamma_j) = 0,$$
where $\varphi_j$ is the Frobenius element of $w_j$.

Lean: `New.Selmer.IsKummerMap.sum_eq_zero` (New/Congruences/FirstOrder/KummerMaps.lean).

Here a tame generator $\gamma$ at a place $A$ is *normalized over $F$ for $m$* if $\gamma$ lies in inertia of $G_F$ at $A$ and moves an $m$-th root of a uniformizer of $F$ by the fixed primitive $m$-th root of unity.

*Proof.* By [testing with maps to $\mathbb{Z}/\ell^\nu$](/chapter/first-order-deformations/#the-real-subfield-and-even-classes), it is enough to prove the identity after an additive map $u \colon O/\ell^\nu \to \mathbb{Z}/\ell^\nu$. So assume that $z$ has values in $\mathbb{Z}/\ell^\nu$. By the lemma above with $P = \{w_j^+\}$, the function $2 z^+$ is a cocycle of the Kummer setting, unramified off $S_0$ and the $w_j^+$. The primes $w_j^+$ are distinct and not in $T$. Their Frobenius elements $\varphi_j$ lie in $G_\nu$, and the $\gamma_j$ are tame generators for them over $F$. The reciprocity condition of the relation $y$ of $\psi$ gives
$$\sum_j y(\varphi_j)(2 z^+(\gamma_j)) = 0.$$
Since $\varphi_j, \gamma_j \in G$, we have $z^+(\gamma_j) = z(\gamma_j)$ and $y(\varphi_j)(a) = a \psi(\varphi_j)/\ell^\nu$. So $\sum_j \psi(\varphi_j)\, 2 z(\gamma_j) / \ell^\nu = 0$ in $\mathbb{Q}/\mathbb{Z}$, which is the claim in $\mathbb{Z}/\ell^\nu$. $\square$

### One term left

The law becomes useful when $\psi$ vanishes at all Frobenius elements but one. Then it bounds the value of $z$ at one tame generator.

**Lemma.** At each $\nu$-split place $w$, and for each $m > 0$, there is $\gamma \in G$ that is a tame generator at the place of $w$, normalized over $F$ for $m$.

Lean: `New.Selmer.exists_isTameGeneratorFor_toGalPlus` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Such a generator exists in $G_F$ by local class field theory for the prime $w^+$. It lies in inertia, and inertia lies in $G$ by [the lemma on inertia](/chapter/first-order-deformations/#the-real-subfield-and-even-classes). $\square$

**Lemma.** Let $w$ be a Frobenius datum off $\ell$, and let $\gamma \in G$ be a tame generator at its place, normalized over $F$ for $\ell^\nu$. Let $z$ be an even class in $(O/\ell^\nu)(-e)$ for a set $S$. Then for every $\tau$ in the inertia group of $G$ at that place there is $n \in \mathbb{N}$ with $z(\tau) = n z(\gamma)$.

Lean: `New.Selmer.exists_apply_eq_nsmul_of_mem_evenClasses` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* The cyclotomic character is $1$ on inertia off $\ell$, so the cocycle $z$ is a homomorphism on inertia. So is $z^+$ on the inertia of $G_F$. It is locally constant with values killed by $\ell^\nu$. A normalized tame generator for $\ell^\nu$ generates the inertia group modulo the kernel of every such homomorphism, so $z^+(\tau) = n z^+(\gamma)$. $\square$

**Theorem (Reciprocity with one term).** Keep the hypotheses of the reciprocity law, but let $z$ be an even class for the primes $w_i$ of the whole family. Suppose that $\psi(\varphi_i) = 0$ for all $i \neq j$. If $2 \psi(\varphi_j)$ divides $n$ in $\mathbb{Z}/\ell^\nu$, then $n z(\tau_j) = 0$, where $\tau_j$ is the chosen tame generator at $w_j$.

Lean: `New.Selmer.IsKummerMap.nsmul_apply_tameGenerator_eq_zero` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* Choose normalized generators $\gamma_i$ by the lemma above. The law has one term left: $\psi(\varphi_j)\, 2 z(\gamma_j) = 0$. The chosen tame generator $\tau_j$ lies in inertia, so $z(\tau_j) = m z(\gamma_j)$ for some $m$. Write $n = 2 \psi(\varphi_j) a$. Then $n z(\tau_j) = m a \cdot 2 \psi(\varphi_j) z(\gamma_j) = 0$. $\square$

So if $\psi(\varphi_j)$ is a unit times $\ell^k$, then $2 \ell^k$ kills $z(\tau_j)$ for every even class. A Kummer map that is nearly a unit at one new place and zero at all old places is what the triangle needs.

### Many Kummer maps modulo $\ell$

**Definition (Reductions of Kummer maps).** For $\psi \colon G \to \mathbb{Z}/\ell^\nu$, its *reduction* is the map $G_\nu \to \mathbb{F}_\ell$ given by $\psi$ modulo $\ell$. The space $K_e(x, T)$ is the $\mathbb{F}_\ell$-span of the reductions of the Kummer maps of exponent $e$ off $T$ for $x$.

Lean: `New.Selmer.kummerReductions` (New/Congruences/FirstOrder/KummerMaps.lean).

**Theorem (Many Kummer maps).** Let $\nu > 0$ and $e \geq 0$. Suppose that $E$ has at least four infinite places. Let $x_i$, for $i \in I$, be $\nu$-split places such that the primes $x_i^+$ are distinct. Then there is a finite set $T$ of primes of $F$ with $S_0 \subseteq T$ and
$$\# I < \dim_{\mathbb{F}_\ell} K_e(x, T).$$

Lean: `New.Selmer.exists_card_lt_finrank_kummerReductions` (New/Congruences/FirstOrder/KummerMaps.lean).

*Proof.* The count of relations in [local duality](/chapter/local-duality/) applies to the Kummer setting. Its hypotheses hold here. The kernel of $\mathrm{cyc}^+$ lies in $G_\nu \cup G_\nu c$. The $\ell$-torsion of $\mathbb{Z}/\ell^\nu$ has $\ell$ elements. The number $4$ divides $\mathrm{cyc}(a) - 1$ for $a \in G$ ([even classes](/chapter/first-order-deformations/#the-real-subfield-and-even-classes)). The field $F$ has as many infinite places as $E$, so at least four. The local condition above $\ell$ is the one that the count expects. The count gives a finite $T \supseteq S_0$ such that the relations off $T$, reduced modulo $\ell$, number at least $\ell^{s + 1}$, where $s$ is the number of primes in $S_0$ off $\ell$. Two relations with the same reduction on $G_\nu$ differ by $\ell$ times a relation, so the reductions of relations inject into $K_e(x, T)$. The primes $x_i^+$ are distinct and lie in $S_0$ off $\ell$, so $\# I \leq s$. Hence $\ell^{\# I + 1} \leq \ell^{\dim K_e(x, T)}$. $\square$

The theorem is the engine of the next section. With $\# I$ places chosen, the reductions of Kummer maps span more than $\# I$ dimensions. So some Kummer map is not in the span of any $\# I$ given maps, and the next step can use it.
