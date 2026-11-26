---
title: Relations in place of the dual Selmer group
lean:
  - Lib/ClassField/GreenbergWiles/Relations.lean
  - Lib/ClassField/GreenbergWiles/RelationsModL.lean
decls:
  - New.SplitPrime
  - New.RelationSetting
  - New.RelationSetting.cocycles
  - New.RelationSetting.localCocycles
  - New.RelationSetting.IsRelation
  - New.RelationSetting.relations
  - New.RelationSetting.Avoids
  - New.RelationSetting.avoids_one
  - New.RelationSetting.exists_splitPlaces_forall_exists_mem_relations
  - New.RelationSetting.exists_card_cocycles_le
  - New.RelationSetting.reductions
  - New.RelationSetting.exists_pow_le_card_reductions
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Relations in place of the dual Selmer group

The last section ended with a lower bound for a set of linear forms on the values of Selmer cocycles at tame generators. This section packs these forms into a module of *relations*, which the source uses in the place of the dual Selmer group. It then gives the two global counts that the rest of the source uses. The first is a case of the Greenberg-Wiles formula over a totally complex field, as one inequality. The second is a weaker count for the reductions modulo $\ell$ of the relations, over a field with real places.

### Why relations

Recall the cocycle form of the Greenberg-Wiles formula from the section [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula). For a totally complex field $K$ with $r_2$ complex places, it reads

$$\#Z^1_{\mathcal{L}}(M) \cdot \#M^{\#S + r_2} = \#Z^1_{\mathcal{L}^*}(M^*) \cdot \prod_{v \in S} \#Z_v,$$

because $\#Z^1_{\mathcal{L}^*}(M^*) = \#H^1_{\mathcal{L}^*}(M^*) \cdot \#M/\#H^0(K, M^*)$. Here $Z^1_{\mathcal{L}^*}(M^*)$ is the group of dual Selmer cocycles. Let $U$ be an open normal subgroup that acts trivially on $M$ and on $\mu_m$. A dual cocycle $y$ restricted to $U$ is a homomorphism $U \to M^* = \mathrm{Hom}(M, \mathbb{Q}/\mathbb{Z})$. It has three properties.

1. It is equivariant up to the cyclotomic character: $y(g u g^{-1})(a) = \chi(g) \, y(u)(g^{-1} a)$.
2. It is unramified outside a finite set $T$ that contains $S$ and the primes above $m$.
3. It satisfies a reciprocity law. Let $z$ be a Selmer cocycle that may ramify at split primes $v_j$ outside $T$. The sum over all places of the local invariants of $y \cup z$ is $0$, by the reciprocity law for the Brauer group of a number field (Cassels and Fröhlich, *Algebraic Number Theory*, Chapter VII, by Tate). At the primes of $S$ the local terms are $0$, because $L_v^*$ is the annihilator of $L_v$. At the other places outside the $v_j$ both cocycles are unramified, and the local terms are $0$. At a split prime $v_j$ the local term is $y(\varphi_j)(z(\gamma_j))$, up to a sign, where $\varphi_j$ is a Frobenius and $\gamma_j$ a tame generator. So $\sum_j y(\varphi_j)(z(\gamma_j)) = 0$.

The cocycles $y$ that vanish on $U$ are inflated from $G/U$. In the source's count these give a factor of at most $\#M$. So the classical formula implies

$$\#Z^1_{\mathcal{L}}(M) \cdot \#M^{\#S + r_2} \leq \#\{\text{functions on } U \text{ with properties 1 to 3}\} \cdot \#M \cdot \prod_{v \in S} \#Z_v.$$

The source proves this inequality directly. It defines a relation as a function with properties 1 to 3. So the reciprocity law of property 3 is part of the definition, not a theorem about dual cocycles. The source does not prove that dual Selmer cocycles give relations, and it does not need this. It needs only the lower bound for the number of relations.

### Split primes and the setting

**Definition (Split prime).** For $m \neq 0$ and an open normal subgroup $U$, a `SplitPrime m U` is a prime $v$ of $K$, a place of $\Omega$ above it, an arithmetic Frobenius $\varphi$ at that place with $\varphi \in U$, and a tame generator $\gamma$ of inertia modulo $m$ at that place.

Lean: `New.SplitPrime` (Lib/ClassField/GreenbergWiles/Relations.lean).

**Definition (Relation setting).** A `RelationSetting M m` for a discrete module $M$ of $\mathrm{Gal}(\Omega/K)$ consists of the following data and conditions. The module $M$ is killed by $m$. There is an open normal subgroup $U$ that fixes $M$ and the $m$-th roots of unity and contains no complex conjugation. Complex conjugations act trivially on $M$. There is a finite set $S$ of primes (`localPrimes`) outside which $M$ is unramified. For each prime $v$ there is a place of $\Omega$ above $v$ and a submodule $L_v$ (`allowed`) of the functions on its decomposition group. For $v \in S$ the submodule $L_v$ contains the local coboundaries.

Lean: `New.RelationSetting` (Lib/ClassField/GreenbergWiles/Relations.lean).

The docstring adds that $m$ need not be a prime power, that $S$ need not contain the primes above $m$, and that a local condition is a module of functions. The two conditions on complex conjugation are the fields `notMem_of_isComplexConj` and `ρ_eq_one_of_isComplexConj`. Over a totally complex field there are no complex conjugations in $\mathrm{Gal}(\Omega/K)$, and both fields hold for every $U$ and $M$. But the setting is also used over a field with real places, as the last part of this section shows. There the two fields have content.

**Definition (The groups $Z(P)$ and $A_v$).** For a setting $D$ and a set $P$ of primes, `D.cocycles P` is `selmerZ1 M S A L P`: the cocycles that lie in $L_v$ at $v \in S$, vanish at complex conjugations, and are unramified outside $S \cup P$. The group `D.localCocycles v` is $A_v = L_v \cap Z^1(D_v, M)$, the allowed local cocycles.

Lean: `New.RelationSetting.cocycles` (Lib/ClassField/GreenbergWiles/Relations.lean).

Lean: `New.RelationSetting.localCocycles` (Lib/ClassField/GreenbergWiles/Relations.lean).

### Relations

**Definition (Relation).** Let $T$ be a finite set of primes. A function $y : \mathrm{Gal}(\Omega/K) \to \mathrm{Hom}(M, \mathbb{Q}/\mathbb{Z})$ is a relation off $T$ if it satisfies the following. (a) It is locally constant. (b) It is $0$ outside $U$. (c) It is a homomorphism on $U$. (d) $y(g u g^{-1})(a) = \chi_m(g) \cdot y(u)(g^{-1} a)$ for $u \in U$, with $\chi_m$ the cyclotomic character modulo $m$. (e) It is $0$ on the inertia groups above primes outside $T$. (f) For every finite family $p_j$ of split primes with distinct primes outside $T$, and every cocycle $z \in Z(\{p_j\})$, $\sum_j y(\varphi_j)(z(\gamma_j)) = 0$.

Lean: `New.RelationSetting.IsRelation` (Lib/ClassField/GreenbergWiles/Relations.lean).

**Definition (Module of relations).** `D.relations T` is the submodule of the functions $y$ with `D.IsRelation T y`. It is finite if $M$ is finite.

Lean: `New.RelationSetting.relations` (Lib/ClassField/GreenbergWiles/Relations.lean).

The finiteness follows from `New.finite_cocycles_unramified_outside`, applied to $U$ with the trivial action on $\mathrm{Hom}(M, \mathbb{Q}/\mathbb{Z})$: a relation restricted to $U$ is a homomorphism unramified outside the primes above $T$. The docstring of `relations` says that it "takes the place of the group $Z^*$ of dual cocycles: only the restrictions to $U$ of dual cocycles are used, and only through the properties in `IsRelation`".

### One family of split primes for all

**Definition (Avoidable numbers).** A natural number $p$ can be avoided if it is prime to $m$, no prime of $S$ divides it, and the primes dividing it are unramified in the fixed field of $U$. The number $1$ can always be avoided.

Lean: `New.RelationSetting.Avoids` (Lib/ClassField/GreenbergWiles/Relations.lean).

Lean: `New.RelationSetting.avoids_one` (Lib/ClassField/GreenbergWiles/Relations.lean).

**Theorem (Split primes for relations).** Let $p$ be avoidable. There are a level $q$, a finite family $s$ of split places with Frobenius elements $\varphi_i$ and tame generators $\gamma_i$, and a finite set $T$ of primes, with the following properties. (a) The primes of $S$ divide $q$. (b) $T \supseteq S$. (c) No prime of $T$ divides $p$. (d) The Frobenii of $s$ detect roots. (e) Each $\gamma_i$ is a tame generator at the $i$-th place. (f) Every family $\nu$ of linear forms $M \to \mathbb{Q}/\mathbb{Z}$ that kills the values at the $\gamma_i$ of all cocycles in $Z(\{v_i\})$ is the family of values at the $\varphi_i$ of a relation off $T$.

Lean: `New.RelationSetting.exists_splitPlaces_forall_exists_mem_relations` (Lib/ClassField/GreenbergWiles/Relations.lean).

The docstring says that the proof "rests on Artin's reciprocity law for Kummer characters of units, in place of the reciprocity law for local pairings". The proof takes $q$ large and an open normal subgroup $O$ such that elements in one coset of $O$ act alike on the $m$-th roots of the $q$-units fixed by $U$. By Chebotarev (`New.selmerZ1.exists_splitPlaces_frob_mem_coset`), it takes one split prime for each coset of $O$, with Frobenius in that coset when the coset meets $U$. The set $T$ is the primes dividing $q$ and the split primes. For a family $\nu$, the relation is $g \mapsto \nu(gO)$ on $U$ and $0$ outside $U$ (`isRelation_ite_form`).

### The global count

**Theorem (A case of the Greenberg-Wiles formula).** Let $K$ be totally complex, let $\ell$ be prime and $r \neq 0$, and let $D$ be a relation setting for a finite module $M$ with $m = \ell^r$. Let $\sigma$ have $\ell$-adic cyclotomic character $1$, let $\sigma g \sigma^{-1} g^{-1} \in U$ for all $g$, and let $\sigma$ fix no nonzero element of $M$. Let $p$ be avoidable. Then there is a finite set $T \supseteq S$ of primes not dividing $p$ with

$$\#Z(\emptyset) \cdot \#M^{\#S + r_2} \leq \#\mathrm{relations}(T) \cdot \#M \cdot \prod_{v \in S} \#A_v.$$

Lean: `New.RelationSetting.exists_card_cocycles_le` (Lib/ClassField/GreenbergWiles/Relations.lean).

*Proof.* Take $q$, $s$, $\gamma$ and $T$ from the theorem on split primes for relations. The element $\sigma$ satisfies the hypotheses of `hasFewCocycles_of_central`, and the Frobenii detect roots. So $M$ has at most $\#M^{\#\iota + 1}$ trivialised cocycles. Each cocycle of $Z(\emptyset)$ is unramified at the split primes, so it lies in $Z(\{v_i\})$ and vanishes at each $\gamma_i$. Now `card_relations_ge` gives

$$\#Z(\emptyset) \cdot \#M^{\#S + r_2} \leq \#F \cdot \#M \cdot \prod_{v \in S} \#A_v,$$

where $F$ is the set of families $\nu$ that kill the values at the $\gamma_i$ of the cocycles in $Z(\{v_i\})$. By (f), each $\nu \in F$ comes from a relation off $T$, and different $\nu$ come from different relations. So $\#F \leq \#\mathrm{relations}(T)$. $\square$

The docstring calls this "a case of the formula of Greenberg and Wiles (Darmon-Diamond-Taylor, Theorem 2.19), giving only a lower bound" for the relations. It says that "the factor $\#M$ comes from the $\#M$ coboundaries, which are the dual cocycles vanishing on $U$". The element $\sigma$ is the classical device that makes $H^1$ of the finite group $\mathrm{Gal}(K(M)/K)$ vanish. The set $T$ depends on the choice of split primes, so the theorem only states that some $T$ exists.

The user is `New/Congruences/Selmer/Count.lean`, which applies the theorem with an auxiliary prime $p$ that $T$ must avoid.

### Relations modulo $\ell$

**Definition (Reductions).** `D.reductions ℓ T` is the image of `D.relations T` in the functions with values in $M^*/\ell M^*$.

Lean: `New.RelationSetting.reductions` (Lib/ClassField/GreenbergWiles/RelationsModL.lean).

**Theorem (Relations modulo $\ell$).** Let $\ell \mid m$ and $\#M[\ell] = \ell$. Let $K$ have at least $4$ infinite places. Let $\kappa : \mathrm{Gal}(\Omega/K) \to \mathbb{Z}_\ell^\times$ be continuous with values in $1 + 4\mathbb{Z}_\ell$, and suppose there is $c$ such that every $g$ with $\kappa(g) = 1$ lies in $U$ or has $g c \in U$. Let the local condition at each prime $v$ be the functions that vanish on the elements $g$ of the decomposition group with $\kappa(g) = 1$ if $v$ lies above $\ell$, and that vanish everywhere otherwise. Then for some $T \supseteq S$,

$$\ell^{\#\{v \in S : v \nmid \ell\} + 1} \leq \#\,\mathrm{reductions}(\ell, T).$$

Lean: `New.RelationSetting.exists_pow_le_card_reductions` (Lib/ClassField/GreenbergWiles/RelationsModL.lean).

The proof uses the same split primes, with $p = 1$. It bounds the cocycles killed by $\ell$ with the count for $M[\ell]$, and it lifts forms on $M[\ell]$ to relations. The docstring says that the result "is weaker than the count given by the formula of Greenberg and Wiles, which grows with the number of infinite places; here only four of these places are used". The field $K$ need not be totally complex here. The user is `New/Congruences/FirstOrder/KummerMaps.lean`, where $K$ is the maximal real subfield $E^+$ of a CM field and $M$ is a Tate twist of $\mathbb{Z}/\ell^\nu$. There the subgroup $U$ is the kernel of a cyclotomic character of $\mathrm{Gal}(\Omega/E^+)$, and the field `notMem_of_isComplexConj` is proved from the fact that complex conjugation is not in the image of $\mathrm{Gal}(\Omega/E)$.

**Remark (Formalization).** The source claims proofs of the two counts. Each is one inequality, and each compares cocycles, not classes. The dual Selmer group does not appear. The module of relations takes its place, and the reciprocity law at split primes is field (f) of `IsRelation`, so it is part of the definition. This is a choice of definition, not an unproved hypothesis: no statement asserts that a given function is a relation without a proof. But it means that a reader cannot read `exists_card_cocycles_le` as the classical formula. The classical formula implies the inequality, as shown at the start of this section, and the source proves the inequality without the classical formula. The conjugation fields of `RelationSetting` hold for every module over a totally complex field, but they have content in the use over $E^+$. If the reported checks hold, Lean accepts both counts with the hypotheses as stated.
