---
title: Selmer groups and the Greenberg-Wiles formula
lean:
  - Lib/ClassField/GreenbergWiles/SelmerLevels.lean
  - Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean
  - Lib/ClassField/GreenbergWiles/CocycleCounts.lean
  - Lib/ClassField/GreenbergWiles/SelmerRelations.lean
decls:
  - New.selmerZ1
  - New.finite_cocycles_unramified_outside
  - New.IsLargeLevel.SplitPlaces
  - New.IsLargeLevel.SplitPlaces.FrobeniiDetectRoots
  - New.DiscreteModule.trivialisedCocycles
  - New.DiscreteModule.HasFewCocycles
  - New.DiscreteModule.trivialisedCocycles.hasFewCocycles_of_isShortExact
  - New.IsLargeLevel.SplitPlaces.PowerResidueSymbols
  - New.IsLargeLevel.SplitPlaces.power_residue_reciprocity
  - New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective
  - New.IsLargeLevel.SplitPlaces.hasFewCocycles_of_central
  - New.selmerZ1.card_mul_pow_le
  - New.selmerZ1.card_relations_ge
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Selmer groups and the Greenberg-Wiles formula

This section moves from local fields to number fields. It states the classical formula of Greenberg and Wiles, which compares a Selmer group with a dual Selmer group. Then it gives the objects of the source: Selmer cocycles, split places, trivialised cocycles and a reciprocity law for power residue symbols. The source does not prove the formula. It proves upper bounds for Selmer cocycles, and it uses reciprocity at split primes in the place of Poitou-Tate duality.

### The textbook form

Let $K$ be a number field, let $\Sigma$ be a finite set of places of $K$ that contains the infinite places, and let $M$ be a finite module for $G_{K,\Sigma}$, the Galois group of the maximal extension of $K$ unramified outside $\Sigma$. Let $M^* = \mathrm{Hom}(M, \mu)$ be the Cartier dual. A *system of local conditions* is a family $\mathcal{L} = (L_v)$ of subgroups $L_v \subseteq H^1(K_v, M)$, with $L_v = H^1_{\mathrm{ur}}(K_v, M)$ for $v \notin \Sigma$. The *Selmer group* is

$$H^1_{\mathcal{L}}(K, M) = \ker\Big(H^1(G_{K,\Sigma}, M) \to \prod_{v \in \Sigma} H^1(K_v, M)/L_v\Big).$$

The *dual Selmer group* $H^1_{\mathcal{L}^*}(K, M^*)$ is defined in the same way, with $L_v^* \subseteq H^1(K_v, M^*)$ the exact annihilator of $L_v$ under local Tate duality.

**Remark (The Greenberg-Wiles formula).** If the order of $M$ is invertible outside $\Sigma$, then

$$\frac{\# H^1_{\mathcal{L}}(K, M)}{\# H^1_{\mathcal{L}^*}(K, M^*)} = \frac{\# H^0(K, M)}{\# H^0(K, M^*)} \prod_{v \in \Sigma} \frac{\# L_v}{\# H^0(K_v, M)}.$$

This is Proposition 1.6 of A. Wiles, "Modular elliptic curves and Fermat's Last Theorem", *Annals of Mathematics* 141 (1995), 443-551. It is also Theorem 2.19 of H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics* (1995). It uses the Poitou-Tate exact sequence (J. S. Milne, *Arithmetic Duality Theorems*, second edition, 2006, Chapter I, Theorem 4.10; see also Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter VIII, §6), Tate's global Euler characteristic formula (Milne, ADT, Chapter I, Theorem 5.1), and the local Euler characteristic formula of the section [Local Tate duality as an inequality](/chapter/local-duality/#local-tate-duality-as-an-inequality).

The formula is used in the Taylor-Wiles method in the following way. If one can choose auxiliary primes so that the dual Selmer group is $0$, then the formula gives the exact order of the Selmer group. In a fixed case, the right side gives an upper bound for $\#H^1_{\mathcal{L}}$ in terms of $\#H^1_{\mathcal{L}^*}$.

### The cocycle form

The source counts cocycles, not classes. The translation is simple. Let $Z^1_{\mathcal{L}}$ be the cocycles whose classes lie in $H^1_{\mathcal{L}}$, and let $Z_v$ be the local cocycles whose classes lie in $L_v$. Then $\#Z^1_{\mathcal{L}} = \#H^1_{\mathcal{L}} \cdot \#M/\#H^0(K, M)$ and $\#Z_v = \#L_v \cdot \#M/\#H^0(K_v, M)$. Put these in the formula, with the product over the finite places $v \in S$ of $\Sigma$ and the infinite places. The result is

$$\#Z^1_{\mathcal{L}} \cdot \#M^{\#S + \#\{\text{infinite places}\}} = \#M \cdot \frac{\# H^1_{\mathcal{L}^*}(K, M^*)}{\# H^0(K, M^*)} \prod_{v} \#Z_v.$$

At a complex place the decomposition group is trivial, so $Z_v = 0$ and $\#Z_v = 1$. At a real place with $c$ trivial on $M$ and $\#M$ odd, $2x(c) = 0$ gives $x(c) = 0$, and again $\#Z_v = 1$. Condition (c) below asks for $x(c) = 0$ directly. So the product can be taken over $S$ only. The factor $\#H^1_{\mathcal{L}^*}/\#H^0(K, M^*)$ is the factor that the source does not compute. It bounds that factor by $\#M^{k-1}$ for a number $k$ of split primes plus one.

### Selmer cocycles in the source

**Definition (Selmer cocycles).** Let $K$ be a number field with $G = \mathrm{Gal}(\Omega/K)$, let $V$ be a discrete $G$-module, let $S$ and $P$ be sets of finite primes, let $A_v$ be a place of $\Omega$ for each $v$, and let $L_v$ be a submodule of the functions on the decomposition group of $A_v$. Then `selmerZ1 V S A L P` is the submodule of continuous cocycles $x : G \to V$ such that (a) $x$ is $0$ on the inertia group of every place over a prime outside $S \cup P$, (b) for $v \in S$, the restriction of $x$ to the decomposition group of $A_v$ lies in $L_v$, and (c) $x(c) = 0$ for each complex conjugation $c$.

Lean: `New.selmerZ1` (Lib/ClassField/GreenbergWiles/SelmerLevels.lean).

The conditions are on cocycles. The set $P$ is a set of extra primes at which ramification is allowed. In the bounds, $P$ is the set of split primes, or the empty set. Condition (c) is the local condition at the real places.

**Theorem (Finiteness).** Let $G$ be a Galois group of $\Omega$ over a number field, let $V$ be a finite discrete $G$-module and let $S$ be a finite set of primes. Then only finitely many continuous cocycles vanish on the inertia groups above all primes outside $S$.

Lean: `New.finite_cocycles_unramified_outside` (Lib/ClassField/GreenbergWiles/SelmerLevels.lean).

The usual proof uses the theorem of Hermite and Minkowski: a number field has only finitely many extensions of bounded degree unramified outside $S$. The docstring says that the proof in the source uses class field theory instead. On an open subgroup that acts trivially and contains no complex conjugation, a cocycle is a homomorphism. An unramified homomorphism is determined by its values on finitely many decomposition groups.

### Split places

**Definition (Split places).** Let $m$ and $N$ be natural numbers, let $U$ be an open normal subgroup of $G$ and let $I \subseteq G$. A term of `SplitPlaces m N I U ι` consists of distinct primes $v_i$ of $K$, for $i \in \iota$, that do not divide $N$, with a place of $\Omega$ above each $v_i$ and a Frobenius element $\varphi_i \in U$ at that place. The data must satisfy these conditions: $U$ fixes the $m$-th roots of unity, $m$ divides $N$, $I$ is the union of the inertia groups above the primes not dividing $N$ other than the $v_i$, the inertia above every prime prime to $N$ lies in $U$, and the primes dividing $N$ generate the class group of every number field between $K$ and the fixed field of $U$.

Lean: `New.IsLargeLevel.SplitPlaces` (Lib/ClassField/GreenbergWiles/SelmerLevels.lean).

The primes $v_i$ play the part of the Taylor-Wiles primes. They split in the fixed field of $U$, because their Frobenius lies in $U$.

**Definition (Frobenii detect roots).** The split places $s$ satisfy `s.FrobeniiDetectRoots` if every $y \in \Omega^\times$ such that $y^m$ is an $N$-unit fixed by $U$, and such that every $\varphi_i$ fixes $y$, is fixed by all of $U$.

Lean: `New.IsLargeLevel.SplitPlaces.FrobeniiDetectRoots` (Lib/ClassField/GreenbergWiles/SelmerLevels.lean).

This is the condition that replaces the vanishing of the dual Selmer group. By Kummer theory, $y$ gives an extension of the fixed field of $U$ of exponent $m$, unramified outside $N$. The condition says that such an extension is trivial if it is split at all $v_i$. The source uses Chebotarev to find primes with this property, in `New.selmerZ1.exists_splitPlaces_frob_mem_coset` (Lib/ClassField/GreenbergWiles/SelmerRelations.lean). In the count of trivialised cocycles below, the condition is a hypothesis.

### Trivialised cocycles

**Definition (Trivialised cocycles).** Let $V$ be a discrete $G$-module, $X$ a $G$-set and $I \subseteq G$. A *trivialised cocycle* is a pair $(f, z)$ of a map $f : X \to V$ and a continuous map $z : G \to V$ such that $g \cdot f(x) = f(g x) + z(g)$ for all $g$ and $x$, and $z(g) = 0$ for $g \in I$. The pairs form a group under addition.

Lean: `New.DiscreteModule.trivialisedCocycles` (Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).

The identity makes $z$ a cocycle. If $x$ is fixed by a subgroup $D$, the identity says that $z$ restricted to $D$ is the coboundary of $f(x)$. So $f$ chooses a trivialisation of $z$ on each stabiliser. The source takes for $X$ the type `PlaceAboveLevel N`, the places of $\Omega$ over $N$ together with the infinite places. A trivialised cocycle is then a cocycle that is a coboundary at every decomposition group above $N$ and $\infty$, with a chosen coboundary at each place.

**Definition (Few cocycles).** `V.HasFewCocycles X I k` says that the number of trivialised cocycles is in the interval $(0, \#V^k]$. In particular, the group is finite.

Lean: `New.DiscreteModule.HasFewCocycles` (Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).

**Lemma (Short exact sequences).** Let $0 \to A \to B \to C \to 0$ be a short exact sequence of discrete modules. If $A$ and $C$ have at most $\#A^k$ and $\#C^k$ trivialised cocycles, then $B$ has at most $\#B^k$. If the count for $B$ is equal to $\#B^k$, then every trivialised cocycle of $C$ lifts to $B$, and the count for $A$ is equal to $\#A^k$.

Lean: `New.DiscreteModule.trivialisedCocycles.hasFewCocycles_of_isShortExact` (Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).

*Proof.* The map to $C$ has as kernel the trivialised cocycles with values in $A$. So $\#\mathrm{tc}(B) \leq \#\mathrm{tc}(A) \cdot \#\mathrm{tc}(C) \leq \#A^k \#C^k = \#B^k$. If equality holds, then each inequality is an equality, which gives both claims. $\square$

The lemma lets the source go from modules killed by a prime to modules killed by a power of the prime, by dévissage.

### Power residue reciprocity

The key global input is a reciprocity law. Fix a tame generator $\gamma_i$ of inertia at the place over $v_i$: an element of inertia that multiplies an $m$-th root of a uniformiser by a fixed primitive $m$-th root of unity $\zeta$ (`New.IsTameGeneratorFor`, Lib/ClassField/GreenbergWiles/SelmerLevels.lean).

**Definition (Power residue symbols).** For split places $s$, tame generators $\gamma$ and a homomorphism $b$ from the $N$-units fixed by $U$ to $(\mathbb{Z}/m)^\iota$, the predicate `PowerResidueSymbols` has four clauses. (a) $\zeta^{b(y)_i} = \varphi_i(r)/r$ whenever $r^m = y$. (b) A trivialised cocycle that vanishes at every $\gamma_i$ vanishes on $U$. (c) For each $N$-unit $y$ and each trivialised cocycle $(f, z)$, $\sum_{i, g} b(g y)_i \cdot g^{-1} z(\gamma_i) = 0$, with $g$ over representatives of $G/U$. (d) If the fixed field of $U$ is totally complex, then each solution $f$ of the relations in (c) and each $a \in V$ give a trivialised cocycle with $z(\gamma_i) = \sum_{g} g (f(i, g) a)$.

Lean: `New.IsLargeLevel.SplitPlaces.PowerResidueSymbols` (Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).

So $b(y)_i$ is the $m$-th power residue symbol of $y$ at $v_i$. Clause (c) is a relation among the values of a cocycle at the tame generators. Clause (d) is the converse. The file says that clauses (c) and (d) are "an explicit substitute for the Poitou-Tate duality".

**Theorem (Power residue reciprocity at split primes).** Let $U$ act trivially on the $\mathbb{Z}/m$-module $V$, and let $\gamma_i$ be tame generators at the places over $v_i$. Then there are power residue symbols $b$ with the four properties above.

Lean: `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity` (Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean).

The docstring says that the proof is by Kummer theory and Artin's reciprocity law, over the fixed field $F$ of $U$. The Kummer step `New.exists_kummer_chars` gives the Kummer characters $\kappa_y$ of the $N$-units $y$, and $b(y)_i$ is the value of $\kappa_y$ at $\varphi_i$. The relations (c) are Artin's law. The converse (d) uses that $F$ is totally complex and the class group condition in `SplitPlaces`. The existence of the symbols is stated first as `New.IsLargeLevel.SplitPlaces.exists_powerResidueSymbols`. The class field theory is in the chapter [Class field theory on finite ideles](/chapter/class-field-theory/).

### The counts

**Theorem (Count for projective modules).** Let $V$ be finite, killed by a prime $l$, fixed by $U$ and projective over $G/U$ in Higman's sense. Let $z \in G$ and $n$ be such that $\rho(z) - n$ is injective on $V$, and such that $U$ fixes $z(r)/r^n$ whenever $r^l$ is an $N$-unit fixed by $U$ and every $\varphi_i$ fixes $r$. Then (a) the number of trivialised cocycles is between $1$ and $\#V^{\#\iota + 1}$, and (b) it is equal to $\#V^{\#\iota + 1}$ if $z$ acts on the $l$-th roots of unity by $n$ and $K$ is totally complex.

Lean: `New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective` (Lib/ClassField/GreenbergWiles/CocycleCounts.lean).

The proof compares the trivialised cocycles with the $G/U$-equivariant maps from the product of the $N$-units with $\mathbb{Z}$ to $V$. It uses `power_residue_reciprocity` and a form of Dirichlet's unit theorem for $N$-units, `New.IsLargeLevel.dirichlet_fixedSUnits`. Part (b) is the only exact count of global cocycles in the folder.

**Theorem (Count for central scalars).** Let $K$ be totally complex, let $r \neq 0$, and let $V$ be finite, killed by $l^r$, fixed by $U$, with $\rho(z) - 1$ injective, for some $z$ with $l$-adic cyclotomic character $1$ and with $z g z^{-1} g^{-1} \in U$ for all $g$. If the Frobenii of $s$ detect roots, then $V$ has at most $\#V^{\#\iota + 1}$ trivialised cocycles.

Lean: `New.IsLargeLevel.SplitPlaces.hasFewCocycles_of_central` (Lib/ClassField/GreenbergWiles/CocycleCounts.lean).

Here `FrobeniiDetectRoots` is a hypothesis. The element $z$ plays the part of the element $\sigma$ in the classical argument that makes $H^1(\mathrm{Gal}(K(M)/K), M) = 0$: a central element that acts on $M$ without fixed points kills this cohomology.

**Theorem (Selmer cocycles against trivialised cocycles).** Let $M$ be finite and unramified outside $S$, let complex conjugations act trivially on $M$, let $A_v$ lie over $v$, and let $L_v$ contain the local coboundaries for $v \in S$. Suppose that $N$ lies in every prime of $S$, and that $M$ has at most $\#M^k$ trivialised cocycles. Then

$$\#\,\mathrm{selmerZ1}(M, S, A, L, \{v_i\}) \cdot \#M^{\#S + \#\{\text{infinite places}\}} \leq \#M^k \prod_{v \in S} \#(L_v \cap Z^1_v).$$

Lean: `New.selmerZ1.card_mul_pow_le` (Lib/ClassField/GreenbergWiles/SelmerRelations.lean).

The docstring says: "It replaces part of the Greenberg-Wiles formula: an upper bound on Selmer cocycles only, with no dual Selmer group." Compare it with the cocycle form above. With $k = 1$, it has the form of the inequality that the formula gives when $\#H^1_{\mathcal{L}^*} \leq \#H^0(K, M^*)$. The Selmer cocycles here may ramify at the split primes, because $P = \{v_i\}$.

**Lemma (Counting relations).** Under the hypotheses of the last theorem with $k = \#\iota + 1$, suppose also that every Selmer cocycle with $P = \emptyset$ lies in the one with $P = \{v_i\}$ and vanishes at every $\gamma_i$. Then the number of families $n_i$ of maps $M \to \mathbb{Q}/\mathbb{Z}$ with $\sum_i n_i(x(\gamma_i)) = 0$ for all Selmer cocycles $x$ with $P = \{v_i\}$, times $\#M \prod_{v \in S} \#Z_v$, is at least $\#M^{\#S + \#\{\text{infinite places}\}}$ times the number of Selmer cocycles with $P = \emptyset$.

Lean: `New.selmerZ1.card_relations_ge` (Lib/ClassField/GreenbergWiles/SelmerRelations.lean).

This is the lower bound for the relations that the next section uses. The families $n$ play the part of the dual Selmer group.

**Remark (Formalization).** The source claims proofs of all statements of this section. The hypotheses with content are these. `FrobeniiDetectRoots` is a hypothesis of `hasFewCocycles_of_central`. `HasFewCocycles` is a hypothesis of `card_mul_pow_le` and of `card_relations_ge`. The only hypothesis on the local conditions $L_v$ is that they contain the coboundaries. The Cartier dual, the dual Selmer group, local Tate duality, the Poitou-Tate sequence and the global Euler characteristic do not appear. Power residue reciprocity takes their place, and it is proved from Artin reciprocity. All counts are of cocycles, and all are upper bounds except part (b) of the count for projective modules. If the reported checks hold, Lean accepts these statements with the hypotheses as stated here.
