---
title: Local Tate duality as an inequality
lean:
  - Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean
  - Lib/ClassField/GaloisCohomology/ShapiroCorestriction.lean
  - Lib/General/Algebra/CartanMap.lean
  - Lib/ClassField/LocalDuality/DualityInequality.lean
decls:
  - New.DiscreteModule.cartierDual
  - New.DiscreteModule.evalCup
  - New.pairingAnnihilator
  - New.DiscreteModule.FiniteKilledFixedInj
  - New.Cohomology.char_eq_zero_of_cyclicClass_eq_zero
  - New.eq_zero_of_evalCup_eq_zero_of_trivialOn
  - New.card_dual_cocycles_le_of_trivial
  - New.card_mul_card_le_of_le_pairingAnnihilator
  - New.card_mul_card_le_of_orthogonal
  - New.DiscreteModule.HoldsCorestrictions
  - New.DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le
  - New.DiscreteModule.local_duality_card_dvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Local Tate duality as an inequality

This section states local Tate duality and the local Euler characteristic formula in their textbook forms. It derives from them a bound on orthogonal groups of cocycles. Then it gives the form that the source proves: the same bound, proved without the two theorems, and a divisibility that takes a maximal orthogonal pair as a hypothesis.

### The textbook form

Let $k$ be a finite extension of $\mathbb{Q}_p$ and let $M$ be a finite discrete $G_k$-module. Its *Cartier dual* is $M^\vee = \mathrm{Hom}(M, \bar k^\times)$, with $(g f)(m) = g f(g^{-1} m)$. If $M$ is killed by $n$, then $M^\vee = \mathrm{Hom}(M, \mu_n)$. The evaluation pairing $M^\vee \times M \to \bar k^\times$ and the cup product give pairings

$$H^i(k, M^\vee) \times H^{2-i}(k, M) \to H^2(k, \bar k^\times) \cong \mathbb{Q}/\mathbb{Z}, \qquad i = 0, 1, 2.$$

*Tate local duality.* These pairings are perfect. That is, each group is the Pontryagin dual of the other (Serre, *Galois Cohomology*, II.5.2, Theorem 2; Milne, *Arithmetic Duality Theorems*, I.2.3; Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter VII, §2).

*The Euler characteristic formula.* Write $h^i = \#H^i(k, M)$. Then $h^0 h^2 / h^1 = 1/\#(\mathcal{O}/\#M \cdot \mathcal{O})$ (Serre, *Galois Cohomology*, II.5.7, Theorem 5; Milne, *ADT*, I.2.8; Neukirch, Schmidt and Wingberg, Chapter VII, §3).

If $\#M$ is prime to $p$, then $\#(\mathcal{O}/\#M) = 1$ and $h^1 = h^0 h^2$. If $\#M = p^s$, then $\#(\mathcal{O}/\#M) = p^{s[k:\mathbb{Q}_p]} = \#M^{[k:\mathbb{Q}_p]}$.

**Remark (The bound from the two theorems).** Let $l$ be a prime with $\#(\mathcal{O}/l) = l^d$, and let $M$ be killed by a power of $l$. Then $\#(\mathcal{O}/\#M) = \#M^d$. Duality in degree $0$ and $2$ gives $h^2(M) = \#H^0(M^\vee)$. With the Euler characteristic formula,

$$\#H^1(M) \cdot \#B^1(M) \cdot \#B^1(M^\vee) = \bigl(h^0(M) h^0(M^\vee) \#M^d\bigr) \cdot \frac{\#M}{h^0(M)} \cdot \frac{\#M}{h^0(M^\vee)} = \#M^{2+d}.$$

Let $X \subseteq Z^1(M^\vee)$ and $W \subseteq Z^1(M)$ be orthogonal: $x \cup w = 0$ in $H^2$ for all $x \in X$, $w \in W$. A coboundary pairs to zero with every cocycle, so the images $\bar X$ and $\bar W$ in $H^1$ are orthogonal. By duality in degree $1$, $\#\bar X \cdot \#\bar W \leq \#H^1(M)$. Since $\#X \leq \#\bar X \cdot \#B^1(M^\vee)$ and $\#W \leq \#\bar W \cdot \#B^1(M)$,

$$\#X \cdot \#W \leq \#M^{2+d}.$$

Equality holds when $\bar X$ and $\bar W$ are annihilators of each other and both groups contain the coboundaries. In the same way, for a group $L \subseteq Z^1(M^\vee)$ with annihilator $L^\perp \subseteq Z^1(M)$, one finds $\#L \cdot \#L^\perp = \#(L \cap B^1(M^\vee)) \cdot \#H^1(M) \cdot \#B^1(M)$. This divides $\#M^{2+d}$.

The source proves the bound and the divisibility of this remark. It does not prove that the pairing is perfect, and it does not prove the Euler characteristic formula.

### The objects of the source

**Definition (Cartier dual).** For a finite discrete $\Gamma$-module $M$, `M.cartierDual` is the discrete $\Gamma$-module of additive maps $f : M \to \Omega^\times$, with $(g f)(m) = g f(g^{-1} m)$.

Lean: `New.DiscreteModule.cartierDual` (Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean).

**Definition (Evaluation cup product).** For finite $M$, `M.evalCup` is the biadditive map $Z^1(M^\vee) \times Z^1(M) \to H^2(\Gamma, \Omega^\times)$ that sends $(x, y)$ to the class of the 2-cocycle $(g, h) \mapsto x(g)\bigl(g\, y(h)\bigr)$.

Lean: `New.DiscreteModule.evalCup` (Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean).

The cup product is defined on cocycles. Its value is a class. With `New.IsLocalGalois.classOfInvariant_bijective` this class is an element of $\mathbb{Q}/\mathbb{Z}$.

**Definition (Annihilator).** For a biadditive map $b : A \times B \to C$ and a subgroup $L$ of $A$, `pairingAnnihilator b L` is the subgroup of the $y \in B$ with $b(x, y) = 0$ for all $x \in L$.

Lean: `New.pairingAnnihilator` (Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean).

So "$X$ and $W$ are orthogonal" is written `X ≤ pairingAnnihilator M.evalCup.flip W` in the source.

**Definition (Finite, killed, fixed, injective).** For a natural number $n$, a subgroup $Q$, an element $z$ and a natural number $m$, `FiniteKilledFixedInj n Q z m A` says that $A$ is finite, that $n A = 0$, that $Q$ acts trivially on $A$, and that $\rho(z) - m$ is injective on $A$.

Lean: `New.DiscreteModule.FiniteKilledFixedInj` (Lib/General/Algebra/CartanMap.lean).

The local inequality uses it with $z = 1$ and $m = 0$. Then $\rho(1) - 0$ is the identity, so the last condition is empty.

### The trivial case

The proof of the inequality is a dévissage. The base case is a trivial module killed by $l$. Three lemmas treat it.

**Lemma (Characters with trivial symbols).** Let `IsLocalGalois Γ k A` hold. A continuous character $\chi : \Gamma \to \mathbb{Q}/\mathbb{Z}$ whose cyclic class $\delta\chi \cup w$ in $H^2(\Gamma, \Omega^\times)$ is zero for every $w \in k^\times$ is zero.

Lean: `New.Cohomology.char_eq_zero_of_cyclicClass_eq_zero` (Lib/ClassField/LocalDuality/DualityInequality.lean).

*Proof.* Fix $g$. The class with invariant $\chi(g)$ dies when it is restricted to the fixed field of $\ker \chi$, because restriction multiplies the invariant by the index, and the index kills $\chi(g)$. By the theory of cyclic classes, a class that dies there is a symbol $\delta\chi \cup w$ for some $w \in k^\times$. By hypothesis this symbol is zero. The invariant map is injective, so $\chi(g) = 0$. $\square$

This is one half of the nondegeneracy of the local Hilbert symbol: a character of $\Gamma$ that pairs to zero with all of $k^\times$ is zero.

**Lemma (Nondegeneracy on the side of $M$).** Let `IsLocalGalois Γ k A` hold, and let $M$ be a finite module killed by the prime $l$ on which all of $\Gamma$ acts trivially. A cocycle $y \in Z^1(M)$ with $x \cup y = 0$ for every $x \in Z^1(M^\vee)$ is zero.

Lean: `New.eq_zero_of_evalCup_eq_zero_of_trivialOn` (Lib/ClassField/LocalDuality/DualityInequality.lean).

*Proof.* It is enough that each coordinate $j \circ y$, for $j : M \to \mathbb{Z}/l$, is zero. This coordinate is a character. For $w \in k^\times$, choose an $l$-th root $a$ of $w$ in $\Omega$. The Kummer cocycle of $a$, twisted by $j$, has values in $M^\vee$. Its cup product with $y$ is minus the symbol of $j \circ y$ and $w$. So all these symbols vanish, and the previous lemma applies. $\square$

**Lemma (Dual cocycles of a trivial module).** Let $M$ be finite, trivial and killed by $l$, and let $\#(\mathcal{O}/l) = l^d$. Then $\#Z^1(M^\vee) \leq \#M^{2+d}$.

Lean: `New.card_dual_cocycles_le_of_trivial` (Lib/ClassField/LocalDuality/DualityInequality.lean).

*Proof.* Choose a basis $e_1, \dots, e_s$ of $M$ over $\mathbb{Z}/l$. A cocycle $x$ with values in $M^\vee$ is fixed by the $s$ cocycles $g \mapsto x(g)(e_i)$, which take values in $\mu_l \subset \Omega^\times$. By the count of Kummer cocycles there are $l^2 \cdot l^d$ of these for each $i$. So $\#Z^1(M^\vee) \leq (l^{2+d})^s = \#M^{2+d}$. $\square$

### The inequality

**Theorem (Inequality of local duality).** Let `IsLocalGalois Γ k A` hold, let $l$ be prime and $\#(\mathcal{O}/l) = l^d$. Let $Q$ be a subgroup of $\Gamma$ such that every $g \in \Gamma$ has a power $g^{l^i}$ in $Q$. Let $M$ be finite, killed by $l^r$ and fixed by $Q$. Let $X \subseteq Z^1(M^\vee)$ and $W \subseteq Z^1(M)$ be orthogonal under `M.evalCup`. Then $\#X \cdot \#W \leq \#M^{2+d}$.

Lean: `New.card_mul_card_le_of_le_pairingAnnihilator`, `New.card_mul_card_le_of_orthogonal` (Lib/ClassField/LocalDuality/DualityInequality.lean).

The two names differ only in the place of the hypothesis `Finite M`. The second takes it from `FiniteKilledFixedInj` inside the statement.

*Proof.* The source proves the bound for all modules with the same conditions at once, by dévissage. A module killed by $l^r$ on which $\Gamma$ acts through elements of $l$-power order modulo $Q$ has a filtration with trivial quotients killed by $l$. For a trivial module killed by $l$, the pairing has no kernel on the side of $Z^1(M)$, by the nondegeneracy lemma. Since $H^2(\Gamma, \Omega^\times) \cong \mathbb{Q}/\mathbb{Z}$, this gives $\#\mathrm{Ann}(W) \cdot \#W = \#Z^1(M^\vee)$. With $X \subseteq \mathrm{Ann}(W)$ and the lemma on dual cocycles, $\#X \cdot \#W \leq \#M^{2+d}$. For an exact sequence $0 \to M' \to M \to M'' \to 0$, the dual sequence $0 \to M''^\vee \to M^\vee \to M'^\vee \to 0$ is exact. From $X$ and $W$ the source builds an orthogonal pair for $M'$ and an orthogonal pair for $M''$, with the product of their sizes at least $\#X \cdot \#W$, and it multiplies the two bounds. Since $\#M = \#M' \cdot \#M''$, the bound for $M$ follows. $\square$

The hypothesis on $Q$ says that $\Gamma/Q$ is an $l$-group in a weak sense. $Q$ need not be open or normal. The case of interest has $Q$ open and $\Gamma/Q$ a finite $l$-group, so the image of $\Gamma$ in $\mathrm{Aut}(M)$ is an $l$-group.

### The divisibility

The second statement of the source descends a maximal orthogonal pair from an open subgroup $U$ to $\Gamma$. It needs a notion of corestriction on cocycles.

**Definition (Holds coboundaries and corestrictions).** Let $U$ be an open subgroup of $\Gamma$, $Y' \subseteq Z^1(U, M)$ and $Y \subseteq Z^1(\Gamma, M)$. The predicate `M.HoldsCorestrictions U Y' Y` says two things. (a) Every coboundary $g \mapsto g m - m$ lies in $Y$. (b) Every $y \in Y'$ is the Shapiro image of a cocycle $F$ with values in the functions $\Gamma/U \to M$, such that the sum of $F$ over $\Gamma/U$ lies in $Y$.

Lean: `New.DiscreteModule.HoldsCorestrictions` (Lib/ClassField/GaloisCohomology/ShapiroCorestriction.lean).

The sum over $\Gamma/U$ of a Shapiro lift is a corestriction of $y$ on the level of cocycles. So (b) says that $Y$ holds a corestriction of each element of $Y'$.

**Lemma (Annihilators descend).** Let `IsLocalGalois Γ k A` hold, let $U$ be open, and let $i \cdot [\Gamma : U]$ act as the identity on $M$. Let $b$ be an equivariant pairing into $\Omega^\times$, and let $X, Y$ hold the coboundaries and corestrictions of $X', Y'$. If $X'$ contains the annihilator of $Y'$ over $U$, then $X$ contains the annihilator of $Y$ over $\Gamma$.

Lean: `New.DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le` (Lib/ClassField/LocalDuality/DualityInequality.lean).

**Theorem (Divisibility form of local duality).** Let `IsLocalGalois Γ k A` hold and let $M$ be finite. Let $U$ be an open subgroup whose index is prime to $\#M$. Let $X' \subseteq Z^1(U, M^\vee)$ and $W' \subseteq Z^1(U, M)$ be orthogonal, and suppose (`h_max`) that $\#X' \cdot \#W' \geq \#Y \cdot \#Z$ for every orthogonal pair $Y, Z$ over $U$. Let $X$ and $W$ hold the coboundaries and corestrictions of $X'$ and $W'$. Then for every group $L$ of cocycles in $Z^1(\Gamma, M^\vee)$,

$$\#L^\perp \cdot \#L \;\Big|\; \#W \cdot \#X,$$

where $L^\perp$ is the annihilator of $L$ in $Z^1(\Gamma, M)$.

Lean: `New.DiscreteModule.local_duality_card_dvd` (Lib/ClassField/LocalDuality/DualityInequality.lean).

*Proof.* Since the index of $U$ is prime to $\#M$, some integer $i$ has $i \cdot [\Gamma : U]$ acting as the identity on $M$ and on $M^\vee$. By `h_max`, each of $X'$ and $W'$ is the whole annihilator of the other over $U$. By the lemma on annihilators, the annihilator of $W$ lies in $X$, and the annihilator of $X$ lies in $W$; the second inclusion uses that the cup product changes sign when its factors are swapped. So the left kernel of the pairing over $\Gamma$ lies in $X$. For any $L$, the source computes $\#L^\perp \cdot \#L = \#Z^1(\Gamma, M) \cdot \#(\ker \cap L)$. This divides $\#Z^1(\Gamma, M) \cdot \#(\ker \cap X) = \#X^\perp \cdot \#X$, which divides $\#W \cdot \#X$. $\square$

The hypothesis `h_max` is not a duality theorem. But it carries the content of one. It says that over $U$ the bound of the inequality is reached by the given pair. The theorem turns this into a statement over $\Gamma$. The next section shows how the source proves `h_max` in the one case where it uses the theorem: it combines the inequality with an exact count of crystalline cocycles.

**Remark (Formalization).** The source has no perfect pairing in local Tate duality and no Euler characteristic formula. What it has is the following. (1) Kummer theory for cocycles, from Hilbert 90. (2) One half of the nondegeneracy of the Hilbert symbol, from the theory of cyclic classes and the invariant map. (3) The inequality $\#X \cdot \#W \leq \#M^{2+d}$ for orthogonal groups of cocycles, for $M$ of $l$-power order on which $\Gamma$ acts through an $l$-group. This is the numerical shadow of duality and the Euler characteristic formula, as the remark above shows. (4) The divisibility `New.DiscreteModule.local_duality_card_dvd`, whose hypothesis `h_max` is a maximal orthogonal pair over an open subgroup of index prime to $\#M$. The hypothesis `h_max` is a hypothesis of the theorem. It is not derived inside the theorem. A user must supply it. The research notes describe local duality in the source as "an inequality and a divisibility". This is accurate, but the divisibility holds only under `h_max`.
