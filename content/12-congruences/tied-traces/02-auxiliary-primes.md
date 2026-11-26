---
title: Auxiliary primes
lean:
  - New/Congruences/Selmer/AuxiliaryPrimes.lean
decls:
  - New.Selmer.AuxPrimeData
  - New.IsAuxPrimeDataAt
  - New.IsAuxiliary
  - New.Selmer.exists_discreteLog
  - New.Selmer.valuation_pow_sub_one_lt_one_of_isFrob
  - New.Selmer.exists_ideleClassChar_of_local
  - New.Selmer.exists_anticyclotomicChar_of_frob_fixes_roots
  - New.Selmer.mem_ker_inf_stabilizer_of_mem_normalClosure
  - New.Selmer.exists_isAuxPrimeDataAt
  - New.Selmer.unionWithConj
  - New.Selmer.pointChar
  - New.Selmer.reduceModPow
  - New.Selmer.IsTiedPrimes
  - New.Selmer.IsTiedPrimes.apply_idOrConjInv_of_slope_ne_zero
  - New.Selmer.tieRelations
  - New.Selmer.idOrConjInv_mem_inertiaAbove
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Auxiliary primes

An auxiliary prime is a prime $P$ of $E$, not equal to its conjugate, at which the argument allows new ramification. It carries four pieces of data: a place of $\Omega$ above it, a tame generator of inertia, a Frobenius element and a character of $G$ to $\mathbb{Z}/q$ that is ramified at $P$. This section defines these data and proves that Chebotarev's theorem gives them, with the Frobenius element near a prescribed element of $G$. At the end it defines sets of tied primes and the tie relations.

Background used: Chebotarev's theorem in existence form, the Artin map, the existence theorem and the $S$-unit theorem, all from [class field theory](/chapter/class-field-theory/). Characters that come from the norm-one torus are defined in [Building the representations](/chapter/building-representations/).

### The data at one prime

**Definition (Auxiliary prime data).** For a number $q$, *auxiliary prime data* consist of a place $A$ of $\Omega$, two elements $\gamma$ (the tame generator) and $\varphi$ (the Frobenius element) of $G$, and a homomorphism $\chi \colon G \to \mathbb{Z}/q$, written multiplicatively.

Lean: `New.Selmer.AuxPrimeData` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

The structure only holds the data. The next definition states what they must satisfy.

A character $\chi \colon G \to C$ *comes from the norm-one torus* for sets $T$ and $I$ of places (`New.IsFromU1 T I χ`) if it is locally constant and there is a character $\eta$ of the finite ideles with three properties: $\eta$ is trivial on $E^\times$; $\eta$ is trivial on the ideles that are units off $T \cup \bar T$ and congruent to $1$ at the places of $I$ off $T \cup \bar T$; and $\chi(\mathrm{Art}(x)) = \eta(x/\bar x)$ for every idele $x$.

**Definition.** Let $T$ be a set of finite places of $E$ and $P$ a finite place. Data $(A, \gamma, \varphi, \chi)$ for $q$ are *auxiliary prime data at $P$ for $T$* if these conditions hold.

1. $\chi$ comes from the norm-one torus for $T$ and $\{P\}$.
2. The norm of $P$ is congruent to $1$ modulo $q$.
3. $A$ lies over $P$.
4. $\varphi$ is an arithmetic Frobenius at $A$: it fixes $A$ and acts on the residue field as $x \mapsto x^{\mathrm{N}P}$.
5. $P \notin T$ and $\bar P \neq P$.
6. $\gamma$ lies in the inertia group of $A$, $\chi(\gamma) = 1 \in \mathbb{Z}/q$, and $\gamma$ is the chosen tame generator at $A$.

Lean: `New.IsAuxPrimeDataAt` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

**Remark (Formalization).** The tame generator at a place $A$ is chosen once by `choose` in the definition `New.IsPlaceOver.tameGenerator`, from the existence of an element of inertia that generates tame inertia. Condition 6 asks that $\gamma$ is this chosen element, not only some generator. So two statements about tame generators at the same place refer to the same element of $G$.

**Definition (Auxiliary set).** A finite set $I$ of places is *auxiliary* for a finite set $S$ if, for each $v \in I$, the norm of $v$ is a prime number, $v \notin S$, $\bar v \notin S$ and $\bar v \notin I$.

Lean: `New.IsAuxiliary` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

### A discrete logarithm at $P$

**Lemma (Discrete logarithm).** Let $P$ be a place of prime norm $\mathrm{N}P = 1 + qk$. Let $u$ be a unit of $E_P$ whose residue generates the units of the residue field. Then there is a homomorphism $\lambda \colon E_P^\times \to \mathbb{Z}/q$ with $\lambda(u) = 1$ that is trivial on every $t$ with $t \equiv 1$ modulo $P$ and on every $t$ with $t^k \equiv 1$ modulo $P$.

Lean: `New.Selmer.exists_discreteLog` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* Divide $t$ by the power of a uniformizer that makes it a unit, and take its residue $\bar t$. This is a homomorphism to the residue units, which form a cyclic group of order $qk$ with generator $\bar u$. Write $\bar t = \bar u^m$ and put $\lambda(t) = m \bmod q$. This is well defined because $q$ divides the order $qk$. Then $\lambda(u) = 1$. If $t \equiv 1$, then $\bar t = 1$ and $\lambda(t) = 0$. If $t^k \equiv 1$, then $\bar u^{mk} = 1$, so $qk$ divides $mk$ and $q$ divides $m$. $\square$

**Lemma.** Let $\sigma$ be a Frobenius element at a place $A$ over $P$, with $\mathrm{N}P = 1 + nk$. Let $u$ be a unit at all places off a set $T \not\ni P$, and let $y \in \Omega$ with $y^n = u$ and $\sigma(y) = y$. Then $u^k \equiv 1$ modulo $P$.

Lean: `New.Selmer.valuation_pow_sub_one_lt_one_of_isFrob` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* The element $y$ is a unit at $A$, because $u$ is a unit at $P$. Since $\sigma$ is a Frobenius element, $\sigma(y) \equiv y^{\mathrm{N}P} = y \cdot y^{nk} = y u^k$ modulo $A$. As $\sigma(y) = y$ and $y$ is a unit, $u^k \equiv 1$ modulo $A$, hence modulo $P$. $\square$

### From a local character to a Galois character

**Lemma.** Suppose that the principal ideles and the ideles that are units off $T$ generate the finite ideles. Let $\lambda$ be a continuous character of $E_P^\times$ that is trivial at the $P$-components of the $T$-units. Then there is a continuous character $\theta$ of the finite ideles that is trivial on $E^\times$ and equal to $\lambda$ of the $P$-component on the ideles that are units off $T$.

Lean: `New.Selmer.exists_ideleClassChar_of_local` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* The ideles that are units off $T$ map onto the idele classes, by hypothesis. The kernel of this map consists of the principal ideles of $T$-units. The character $a \mapsto \lambda(a_P)$ is trivial on this kernel, so it descends to the idele classes. Call the result $\theta$. It agrees with a continuous map on the open subgroup of ideles that are units off $T$, so it is continuous. $\square$

**Lemma (An anticyclotomic character ramified at $P$).** Let $T$ be a set of places such that the $T$-ideles and the principal ideles generate the finite ideles, and let a finite set $s$ generate the $T$-units. Let $P \notin T$ have prime norm $1 + qk$, with $\bar P \neq P$. Let $\sigma$ be a Frobenius element at a place $A$ over $P$ that fixes a $q$-th root of each element of $s$. Then there are a continuous character $\chi \colon G \to \mathbb{Z}/q$ and a character $\theta$ of the finite ideles with these properties:

1. $\chi(\gamma_A) = 1$ at the chosen tame generator $\gamma_A$;
2. $\theta$ is trivial on $E^\times$, and on the $T$-ideles that are congruent to $1$ at $P$;
3. $\chi(\mathrm{Art}(x)) = \theta(x / \bar x)$ for every idele $x$.

Lean: `New.Selmer.exists_anticyclotomicChar_of_frob_fixes_roots` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* Take a unit $u_0$ of $E_P$ whose Artin symbol at $A$ is $\gamma_A$ and whose residue generates the residue units. Let $\lambda$ be its discrete logarithm. By the last lemma and the hypothesis on $\sigma$, each $u \in s$ satisfies $u^k \equiv 1$ at $P$, so $\lambda(u) = 0$. Since $s$ generates, $\lambda$ kills all $T$-units. Its kernel has finite index, so $\lambda$ is continuous. The previous lemma extends $\lambda$ to $\theta$. The character $x \mapsto \theta(x / \bar x)$ is continuous and trivial on $E^\times$, so the existence theorem gives $\chi$ with property 3. For property 1, let $x$ be the idele with component $u_0$ at $P$ and $1$ elsewhere. Its conjugate $\bar x$ has component $1$ at $P$ (because $\bar P \neq P$) and is a $T$-idele, so $\theta(\bar x) = 1$. Hence $\chi(\gamma_A) = \theta(x) = \lambda(u_0) = 1$. $\square$

### Chebotarev with a prescribed Frobenius element

**Lemma.** Let $q$ be a unit at the places off $T$, and let the places of $R$ be off $T$. Fix $q$-th roots $y(x)$ of the elements $x \in E$. Then every element of the normal closure of the inertia groups above $R$ fixes the $q$-th roots of unity and the roots $y(u)$ of the $T$-units $u$ in a finite set $s$.

Lean: `New.Selmer.mem_ker_inf_stabilizer_of_mem_normalClosure` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* Let $U$ be the subgroup of elements that fix the $q$-th roots of unity and the $y(u)$. An inertia group above a place $w \in R$ fixes both. The roots of unity are unramified at $w$ because $q$ is a unit there. The roots $y(u)$ are unramified because $u$ is a unit there. This holds for all conjugate places too, so the inertia groups lie in the normal core of $U$. This core is normal, so it contains the normal closure. $\square$

**Theorem (Auxiliary primes exist).** Let $\ell$ be a prime and $N \geq 0$. Let $S$ and $R$ be finite sets of places of $E$. Let $z$ lie in the normal closure of the inertia groups at the places of $R$ that are not in $S \cup \bar S$ and not above $\ell$, and let $W$ be a neighbourhood of $z$ in $G$. Then there are a place $P \notin R \cup \bar R$ of prime norm and auxiliary prime data $(A, \gamma, \varphi, \chi)$ for $\ell^N$ with these properties:

1. $\varphi \in W$ and $\chi(\varphi) = 1$;
2. the data are auxiliary prime data at $P$ for every $T \subseteq S \cup \{v \mid \ell\}$.

Lean: `New.Selmer.exists_isAuxPrimeDataAt` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* Choose a finite set $T$ that contains $S$, $\bar S$ and the places above $\ell$, that contains no other place of $R$, and whose ideles generate the idele classes together with the principal ideles. Such $T$ exists by the finiteness of the class group. The $T$-units are finitely generated by the $S$-unit theorem; let $s$ generate them. Let $U$ be the open subgroup of $G$ that fixes the $\ell^N$-th roots of unity and fixed $\ell^N$-th roots of the elements of $s$. By the last lemma, $z \in U$.

Chebotarev's theorem, applied to the open set $U \cap W'$ with $W'$ the interior of $W$, gives a place $P$ of prime norm outside $T \cup R \cup \bar R$ and outside the finitely many places with $\bar P = P$ of prime norm. It also gives a place $A$ over $P$ and a Frobenius element $\sigma \in U$, and every Frobenius element at $A$ lies in $W$. Since $\sigma$ fixes the $\ell^N$-th roots of unity, $\mathrm{N}P \equiv 1$ modulo $\ell^N$. Write $\mathrm{N}P = 1 + \ell^N k$. The previous lemma gives $\chi$.

The element $\sigma$ need not satisfy $\chi(\sigma) = 1$. Put $\varphi = \sigma\,\gamma_A^{m}$ with $m$ a representative of $\chi(\sigma^{-1})$. Then $\varphi$ is again a Frobenius element at $A$, because $\gamma_A$ is in inertia, and $\chi(\varphi) = \chi(\sigma) + m = 0$. So $\varphi \in W$ and $\chi(\varphi) = 1$ in multiplicative notation. For $T' \subseteq S \cup \{v \mid \ell\}$, the set $T' \cup \bar T'$ lies in $T$, so an idele that is a unit off $T' \cup \bar T'$ and congruent to $1$ at $P$ is killed by $\theta$. This gives condition 1 of auxiliary prime data for $T'$. The other conditions hold by construction. $\square$

**Example.** Let $R = \emptyset$. Then the normal closure is trivial and $z = 1$. The theorem gives a prime $P$ of norm $\equiv 1$ modulo $\ell^N$ with a Frobenius element as close to $1$ as wanted. The character $\chi$ then sends $\gamma_A$ to $1$ and $\varphi$ to $0$ in $\mathbb{Z}/\ell^N$. So $\chi$ sees the tame inertia at $P$ and nothing at the Frobenius element. This is the shape that the tie relations use.

### Tied primes

Three helper definitions appear with the tied primes. The set $S \cup J \cup \bar J$ of places, for finite sets $S$ and $J$, is `New.Selmer.unionWithConj`. For characters $h_j \colon G \to \mathbb{Z}/q$ and $q$-th roots of unity $y_j$, the character $g \mapsto \prod_j y_j^{h_j(g)}$ is `New.Selmer.pointChar`. For a matrix representation $\rho$ over $O$, its reduction modulo $\ell^M$ is `New.Selmer.reduceModPow`.

Lean: `New.Selmer.unionWithConj`, `New.Selmer.pointChar`, `New.Selmer.reduceModPow` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

**Definition (Tied primes).** Let $S_0$ be a finite set of places, $U_i$ a condition on elements of $G$ for each datum $i$ in an index set, $W \subseteq G$, $N \geq 0$, $P_0$ a place and $J$ a finite set of places. For each $v$, let $x_v = (d_v, s_v)$ consist of auxiliary prime data $d_v = (A_v, \gamma_v, \varphi_v, \chi_v)$ for $\ell^N$ and slopes $s_v(i) \in O$. These form *tied primes* if:

1. $J$ is auxiliary for $S_0$, and $P_0 \in J$;
2. for each $v \in J$, $d_v$ is auxiliary prime data at $v$ for the places above $\ell$;
3. for $v \neq P_0$ in $J$ and every $w \in J$, $\chi_w(\varphi_v) = 1$ if $w = P_0$ and $\chi_w(\varphi_v) = 0$ otherwise;
4. $\varphi_{P_0} \in W$, and $s_{P_0} = 0$;
5. no place of $S_0$ and no place $v \neq P_0$ of $J$ divides the norm of $P_0$;
6. if $s_v(i) \neq 0$, then $U_i$ holds at $\varphi_v$ and at $(\varphi_v^c)^{-1}$.

Lean: `New.Selmer.IsTiedPrimes` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

Condition 3 makes the matrix of values $\chi_w(\varphi_v)$ simple: the character of the first prime is $1$ at all later Frobenius elements, and the other characters vanish there. Condition 5 lets [the Greenberg-Wiles count](/chapter/tied-selmer-groups/) choose its extra primes away from $P_0$.

**Lemma.** For tied primes, if $s_v(i) \neq 0$, then $U_i$ holds at $\iota_b(\varphi_v)$ for both values of $b$.

Lean: `New.Selmer.IsTiedPrimes.apply_idOrConjInv_of_slope_ne_zero` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* This is condition 6, split into the cases $b = \text{true}$ and $b = \text{false}$. $\square$

**Definition (Tie relations).** For tied primes and a datum $i$, the *tie relations* are the formal combinations
$$[\iota_b(\gamma_v)] - s_v(i)\,[\iota_b(\varphi_v)], \qquad v \in J,\ b \in \{\text{true}, \text{false}\},$$
with matrix coefficients $1$ and $s_v(i) \cdot 1$.

Lean: `New.Selmer.tieRelations` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

A cocycle $z$ obeys these relations when $z(\gamma_v) = s_v(i)\, z(\varphi_v)$ and $z((\gamma_v^c)^{-1}) = s_v(i)\, z((\varphi_v^c)^{-1})$ for all $v \in J$. At the first prime the slope is $0$, so the relation says that $z$ is unramified at $P_0$ and $\bar P_0$.

**Lemma.** Let $\tau$ lie in the inertia group of a place $A$ over $P$, and let $S$ contain $P$ and $\bar P$. Then $\iota_b(\tau)$ lies in an inertia group above $S$ for both $b$.

Lean: `New.Selmer.idOrConjInv_mem_inertiaAbove` (New/Congruences/Selmer/AuxiliaryPrimes.lean).

*Proof.* For $b = \text{true}$ this is the hypothesis. For $b = \text{false}$, the element $\tau^c$ lies in the inertia group of the conjugate place $cA$, which lies over $\bar P$, and so does its inverse. $\square$
