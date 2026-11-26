---
title: Characters, twists and m-fold twists
lean:
  - Lib/ClassField/HeckeCharacter/Basic.lean
  - Lib/ClassField/HeckeCharacter/SplitTameCharacters.lean
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/Reduction/Data/LevelAndTwists.lean
decls:
  - New.AutChar
  - New.AutChar.HasWeight
  - New.AutChar.exists_hasWeight_of_prod_eq_one
  - New.Data.IsChosen
  - New.Data.chiMLocal
  - New.Data.orderOf_chiMLocal
  - New.Data.chiMLocal_apply_eq_one_of_pow_q₁_eq_one
  - New.Data.exists_zeta_pow_eq_of_isIntegral
  - New.Data.prod_phi_zeta_pow_pow_liftWeight_zero_eq_one
  - New.Data.exists_char_hasWeight
  - New.Data.chiZero
  - New.Data.chiM
  - New.Data.TameChar
  - New.Data.Twist
  - New.Data.TameChar.one
  - New.WeilData.hasWeight_upsilonU1_zpow
  - New.Data.untwistedLiftChar
  - New.Data.untwistedLiftChar_hasWeight
  - New.Data.liftChar
  - New.Data.hasWeight_liftChar
  - New.Data.LiftIndex
  - New.Data.TameChar.pow
  - New.Data.MFoldTwist
  - New.Data.chainChar
  - New.Data.MFoldTwist.powTwist
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Characters, twists and m-fold twists

The theta lifts of the argument are twisted by characters of the norm-one adeles of $E$. This section defines these characters, proves that characters with a prescribed weight and tame part exist, and defines the tame characters, twists and $m$-fold twists. The weights $\kappa_j$, the level $N$ and the primes $p_0, p_1$ belong to [the data and its sizes](/chapter/data-and-sizes/). We use only the facts about them stated here.

### Characters with a weight

Let $\mathbb{A}_E$ be the adeles of $E$, and let $U(1)(\mathbb{A}_E) = \{u \in \mathbb{A}_E : u \bar u = 1\}$.

**Definition (Automorphic character).** An automorphic character of $U(1)$ over $E$ is a continuous homomorphism $\mu : U(1)(\mathbb{A}_E) \to S^1$ with $\mu(u) = 1$ for every $u \in E$ with $u \bar u = 1$.

Lean: `New.AutChar` (Lib/ClassField/HeckeCharacter/Basic.lean).

Each infinite place $v$ of $E$ has its chosen embedding $\Phi_v$ (Section 4), and through it the component $u_v$ of $u$ at $v$ is a complex number of absolute value $1$. A finite place $w$ has a residue field $k_w$ with $q_w$ elements.

**Definition (Weight and tame part).** Let $e$ be a function from the infinite places to $\mathbb{Z}$, and for each finite place $w$ let $\psi_w$ be a multiplicative character of $k_w$. The character $\mu$ has weight $e$ and tame part $\psi$ if only finitely many $\psi_w$ are nontrivial, and
$$\mu(u) = \prod_v u_v^{e(v)} \cdot \prod_w \psi_w(u \bmod w)$$
for every $u \in U(1)(\mathbb{A}_E)$ with integral finite part.

Lean: `New.AutChar.HasWeight` (Lib/ClassField/HeckeCharacter/Basic.lean).

**Remark (Formalization).** `HasWeight` is a class, and $e$ and $\psi$ are out-parameters. Lean finds the weight of a character by instance search. The class says nothing about $\mu$ on elements with a nonintegral finite part. Those values are fixed by continuity and by the triviality on $U(1)(E)$, but the class does not record them.

If $\mu$ has weight $e$ and tame part $\psi$, then for every integral $u \in E$ with $u \bar u = 1$ the right side of the formula is $\mu(u) = 1$. The source proves the converse.

**Proposition.** Let $\psi$ be trivial outside a finite set $S$ of finite places. Suppose that
$$\prod_v \Phi_v(u)^{e(v)} \cdot \prod_{w \in S} \psi_w(u \bmod w) = 1$$
for every integral $u \in E$ with $u \bar u = 1$. Then some automorphic character has weight $e$ and tame part $\psi$.

Lean: `New.AutChar.exists_hasWeight_of_prod_eq_one` (Lib/ClassField/HeckeCharacter/Basic.lean).

### The characters $\omega$, $\mu^\flat$ and $\chi$

The data contains two primes $p_0, p_1$ that split in $K$, and an integer $\bar\pi_M$ of $K$ of norm $M = p_0 p_1$. Let $\pi_M$ be its conjugate, seen in $E$. A finite place $w$ of $E$ is chosen if $\pi_M \in w$. A chosen place lies over $p_0$ or $p_1$, and its residue field has $p_i$ elements. The data has $q_2^2 \mid p_i - 1$, with $q_2 = (q_0 d)^{s+6}$.

**Definition (The characters ω).** At a chosen place $w$, fix a character of $k_w^\times$ of order $q_2^2$, and let $\omega_w$ be its $q_2$-th power. At the other places, let $\omega_w = 1$. Then $\omega_w$ has order $q_2$ at every chosen place.

Lean: `New.Data.IsChosen`, `New.Data.chiMLocal`, `New.Data.orderOf_chiMLocal` (New/Derivatives/Field/ChosenPlaces.lean).

**Lemma.** If $x \in k_w$ and $x^{q_1} = 1$, then $\omega_w(x) = 1$.

Lean: `New.Data.chiMLocal_apply_eq_one_of_pow_q₁_eq_one` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* At a place that is not chosen this is clear. At a chosen place, $q_1 \mid q_1 d \mid q_2$, so $x^{q_2} = 1$, and $\omega_w(x)$ is the value of the fixed character at $x^{q_2} = 1$. $\square$

**Lemma.** Let $\gamma \in E$ be integral with $\gamma \bar\gamma = 1$. Then $\gamma = \zeta^k$ for some $k$.

Lean: `New.Data.exists_zeta_pow_eq_of_isIntegral` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* All conjugates of $\gamma$ have absolute value $1$, since $E$ is CM and conjugation commutes with every embedding. By Kronecker's theorem, $\gamma$ is a root of unity. By Section 3, it is a power of $\zeta$. $\square$

Let $\kappa_0(v) = \kappa(v) + r^8$ be the weight of the first lift at $v$, where $\kappa(v)$ is the weight of the data and $r^8$ is half the gap $\Delta = 2r^8$. The data has $q_1 \mid \kappa(v)$ for every $v$.

**Lemma.** For every $k$, $\prod_v \Phi_v(\zeta^k)^{\kappa_0(v)} = 1$.

Lean: `New.Data.prod_phi_zeta_pow_pow_liftWeight_zero_eq_one` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Since $\kappa_0(v) \equiv r^8 \bmod q_1$ and $\zeta^{q_1} = 1$, the product is $\prod_v \Phi_v(\zeta^{k r^8}) = N_{E/K}(\zeta^{k r^8})$, by Section 4. This norm is $1$, by Section 3. $\square$

**Proposition.** For all natural numbers $a$ and $n$, there is an automorphic character with weight $v \mapsto -a\,\kappa_0(v)$ and tame part $\omega^n$.

Lean: `New.Data.exists_char_hasWeight` (New/Derivatives/Field/ChosenPlaces.lean).

*Proof.* Apply the proposition above with $S$ the set of chosen places. Let $\gamma$ be integral with $\gamma\bar\gamma = 1$. By the second lemma, $\gamma = \zeta^k$. By the third lemma, the infinite factor is $\big(\prod_v \Phi_v(\zeta^k)^{\kappa_0(v)}\big)^{-a} = 1$. At a finite place $w$, the residue $x$ of $\gamma$ satisfies $x^{q_1} = 1$, so $\omega_w(x)^n = 1$ by the first lemma. $\square$

**Definition (The characters μ♭ and χ).** Let $\mu^\flat$ be a character given by the proposition with $(a, n) = (1, 0)$, so with weight $-\kappa_0$ and trivial tame part. Let $\chi$ be a character given by it with $(a, n) = (0, 1)$, so with weight $0$ and tame part $\omega$.

Lean: `New.Data.chiZero`, `New.Data.chiM` (New/Derivatives/Field/ChosenPlaces.lean).

**Remark (Formalization).** The three objects $\omega$, $\mu^\flat$ and $\chi$ are chosen with `Classical.choose`. The fixed character of order $q_2^2$ is any one, and $\mu^\flat$ and $\chi$ are any characters with the stated weight and tame part. The source does not claim that they are unique. The later chapters use only the properties stated here, and the choice is made once, in `New.Data`.

### Tame characters and twists

**Definition (Tame character).** A tame character is an automorphic character $\vartheta$ of weight $0$ with a finite set $Q$ of finite places and a tame part $\psi$, such that $\psi_w = 1$ for $w \notin Q$, the conjugate $\bar w$ of each $w \in Q$ is not in $Q$, and $MN$ is prime to $\prod_{w \in Q} q_w$. Here $N$ is the prime level of the data. A twist is a tame character with $\psi_w \neq 1$ for every $w \in Q$. The trivial character, with $Q = \emptyset$, is a twist.

Lean: `New.Data.TameChar`, `New.Data.Twist`, `New.Data.TameChar.one` (New/Reduction/Data/LevelAndTwists.lean).

**Remark (Formalization).** A tame character is a structure. The set $Q$ and the tame part are data in it, not properties of the character. For a tame character, $Q$ may contain places with $\psi_w = 1$. Only a twist excludes them. The condition $\bar w \notin Q$ makes every place of $Q$ split, in the sense of Section 1.

### The characters of the lifts

Let $\upsilon$ be the restriction to $U(1)(\mathbb{A}_E)$ of the splitting character of the Weil data. For every integer $z$, $\upsilon^z$ has constant weight $z$ and trivial tame part.

Lean: `New.WeilData.hasWeight_upsilonU1_zpow` (Lib/ClassField/HeckeCharacter/SplitTameCharacters.lean).

The $j$-th lift of the chain has the weight $\kappa_j = \kappa + (j + \tfrac12)\Delta = \kappa_0 + j\Delta$.

**Definition (Lift characters).** For $j \in \mathbb{N}$ let $\mu^0_j = \mu^\flat\,(\upsilon^{-\Delta}\chi)^j$. For a tame character $\vartheta$, let the lift character be $\mu^0_j \vartheta$.

Lean: `New.Data.untwistedLiftChar`, `New.Data.liftChar` (New/Reduction/Data/LevelAndTwists.lean).

**Lemma.** The character $\mu^0_j$ has weight $-\kappa_j$ and tame part $\omega^j$. For a tame character $\vartheta$ with tame part $\psi$, the character $\mu^0_j\vartheta$ has weight $-\kappa_j$ and tame part $\omega^j \psi$.

Lean: `New.Data.untwistedLiftChar_hasWeight`, `New.Data.hasWeight_liftChar` (New/Reduction/Data/LevelAndTwists.lean).

*Proof.* Weights add and tame parts multiply under products of characters, and powers multiply both by the exponent. So $\upsilon^{-\Delta}\chi$ has weight $-\Delta$ and tame part $\omega$. Its $j$-th power has weight $-j\Delta$ and tame part $\omega^j$. With $\mu^\flat$ the weight is $-\kappa_0 - j\Delta = -\kappa_j$, and the tame part is $\omega^j$. Multiplication by $\vartheta$, of weight $0$, gives the second claim. $\square$

### m-fold twists

Let $m$ be the number of lifts of the data. The lifts are indexed by $1 \le j \le m$.

**Definition (m-fold twist).** For a tame character $\vartheta$ and $n \in \mathbb{N}$, let $\vartheta^n$ be the tame character with the same set $Q$ and tame part $\psi^n$. An $m$-fold twist is a twist with $\psi_w^n \neq 1$ for every $w \in Q$ and every $1 \le n \le m$. For such $\vartheta$ and $1 \le n \le m$, $\vartheta^n$ is a twist. The chain character of index $j$ is $\mu^0_j \vartheta^j$.

Lean: `New.Data.LiftIndex`, `New.Data.TameChar.pow`, `New.Data.MFoldTwist`, `New.Data.MFoldTwist.powTwist`, `New.Data.chainChar` (New/Reduction/Data/LevelAndTwists.lean).

So the $j$-th lift of the chain is twisted by $\vartheta^j$, and the definition makes each of these a twist with the same set $Q$.

**Remark (Formalization).** `TameChar.pow` with $n = 0$ gives a tame character with tame part $1$ and the old set $Q$. It is not a twist if $Q \neq \emptyset$. `MFoldTwist.powTwist` takes its index in `LiftIndex`, so this case does not occur.
