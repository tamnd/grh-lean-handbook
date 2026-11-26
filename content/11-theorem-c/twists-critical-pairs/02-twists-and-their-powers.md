---
title: Twists and their powers
lean:
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Determinant/Twist/FitTwists.lean
decls:
  - New.Data.TameChar
  - New.Data.TameChar.normQ
  - New.Data.Twist
  - New.Data.TameChar.one
  - New.Data.TameChar.pow
  - New.Data.MFoldTwist
  - New.Data.MFoldTwist.powTwist
  - New.Data.Twist.toAutChar_one
  - New.Data.Twist.Q_one
  - New.Data.MFoldTwist.toTwist_one
  - New.Data.toAutChar_one_and_toTwist_one_and_Q_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Twists and their powers

A twist changes the character of a lift by a character of finite order that is ramified away from the level and away from the chosen places. The proof of Theorem C compares the lattice at the trivial twist with the lattice at a twist $\vartheta$. The chain of lifts uses the powers $\vartheta^j$ for $1 \leq j \leq m$, and the chain determinant has factors at the quotients $\vartheta^{j-i}$. So the argument needs a twist whose first $m$ powers are all ramified at every place of the modulus. This section gives the three definitions (tame characters, twists and $m$-fold twists), the powers, and the trivial twist. The definitions are those of [fields, places and twists](/chapter/fields-places-twists/). We repeat them here because every statement of the chapter depends on their exact form.

### Tame characters

Let $D$ be admissible data with CM field $E$, number of lifts $m$, product of the two chosen primes $M$ and level $N$. For a finite place $w$ of $E$ write $k_w$ for the residue field and $q_w = |k_w|$. An automorphic character of $U(1)(\mathbb{A}_E)$ has a weight at each infinite place and a tame part, a family of characters of the residue fields $k_w$. The relation is `New.AutChar.HasWeight` of Volume 1: the character is $u \mapsto \prod_v u_v^{c(v)} \prod_w \psi_w(u \bmod w)$ on the elements with integral finite part.

**Definition (Tame character).** A tame character of $D$ is an automorphic character $\vartheta$ of $U(1)(\mathbb{A}_E)$, a finite set $Q$ of finite places of $E$ and a family $\psi = (\psi_w)$ of characters $\psi_w : k_w^\times \to \mathbb{C}^\times$, such that

1. $\vartheta$ has weight $0$ and tame part $\psi$;
2. $\psi_w = 1$ for $w \notin Q$;
3. for $w \in Q$ the conjugate place $\bar w$ is not in $Q$;
4. $\gcd(MN, \prod_{w \in Q} q_w) = 1$.

The number $\mathrm{Nm}\,Q = \prod_{w \in Q} q_w$ is the norm of the modulus.

Lean: `New.Data.TameChar` (New/Reduction/Data/LevelAndTwists.lean)

Lean: `New.Data.TameChar.normQ` (New/Reduction/Data/LevelAndTwists.lean)

The four conditions have four roles. Weight $0$ means that a twist does not change the weights of the lifts, so the twisted lift lives in the same space of forms of the same weight. The tame part is trivial outside $Q$, so the twist does not change the local data at the level and at the chosen places. The condition $\bar w \notin Q$ is a field of the structure that the later volumes use when they build twists and their levels. No proof in this chapter uses it. The coprimality keeps $Q$ away from the places where the lifts already have ramification.

**Remark (Formalization).** The set $Q$ is a modulus, not the conductor. Condition 2 says that $\psi$ is trivial outside $Q$. It does not say that $\psi_w \neq 1$ inside $Q$. So a tame character may have $\psi_w = 1$ at some $w \in Q$, and then $Q$ is larger than the set of ramified places. The $L$-functions of the chapter omit the Euler factors at all of $Q$, so the difference matters: an unramified place of $Q$ still loses its Euler factor.

### Twists and m-fold twists

**Definition (Twist).** A twist is a tame character with $\psi_w \neq 1$ for every $w \in Q$. The trivial twist $1$ has the trivial character, $Q = \emptyset$ and the trivial tame part. The trivial tame character $\mathbf{1}$ is the tame character of the trivial twist.

Lean: `New.Data.Twist` (New/Reduction/Data/LevelAndTwists.lean)

Lean: `New.Data.TameChar.one` (New/Reduction/Data/LevelAndTwists.lean)

For a twist, $Q$ is exactly the set of places where $\psi$ is not trivial. So the modulus of a twist is its tame conductor.

**Definition (Powers).** For a tame character $\vartheta$ and $n \in \mathbb{N}$, the tame character $\vartheta^n$ has the character $\vartheta^n$ of $U(1)(\mathbb{A}_E)$, the same set $Q$, and the tame part $\psi^n = (\psi_w^n)$.

Lean: `New.Data.TameChar.pow` (New/Reduction/Data/LevelAndTwists.lean)

The power keeps $Q$, so the power of a twist is a tame character, but it need not be a twist: $\psi_w^n$ can be trivial at a place of $Q$.

**Definition ($m$-fold twist).** An $m$-fold twist is a twist with $\psi_w^n \neq 1$ for every $w \in Q$ and every $n$ with $1 \leq n \leq m$. For an $m$-fold twist $\vartheta$ and $n \in [1, m]$, the twist $\vartheta^n$ is the tame character $\vartheta^n$ with this property as its proof that it is a twist.

Lean: `New.Data.MFoldTwist` (New/Reduction/Data/LevelAndTwists.lean)

Lean: `New.Data.MFoldTwist.powTwist` (New/Reduction/Data/LevelAndTwists.lean)

The trivial twist is an $m$-fold twist, because its $Q$ is empty and the condition is vacuous.

**Example (The order condition).** Let $w$ be a place of $E$ and $\psi_w$ a character of the cyclic group $k_w^\times$ of order $q_w - 1$. Let $d$ be the order of $\psi_w$. Then $\psi_w^n = 1$ if and only if $d \mid n$. For $1 \leq n \leq m$ this happens for some $n$ if and only if $d \leq m$. So $\psi_w$ satisfies the condition of an $m$-fold twist if and only if $d > m$. A character of order $d$ exists if and only if $d \mid q_w - 1$. So an $m$-fold twist ramified at $w$ exists only if $q_w - 1$ has a divisor larger than $m$, and it is enough that $q_w > m + 1$, with a generator of the character group. For example, with $m = 3$ and $q_w = 7$ the characters of $\mathbb{F}_7^\times$ of order $6$ qualify, and the characters of order $2$ and $3$ do not. The two characters of order $6$ are a generator and its inverse.

The example shows that the local condition is easy. The difficulty in the existence of $m$-fold twists is global: the tame part must be the tame part of an automorphic character of weight $0$, so it must be trivial on the image of the global units in $\prod_{w \in Q} k_w^\times$. Volume 12 makes this choice ([the twisting theorem](/chapter/twisting-theorem/)).

### The trivial twist

Three equations about the trivial twist hold by definition. The proofs of the chapter use them to identify the denominator of a ratio with the numerator at $\vartheta = 1$.

**Lemma (The trivial twist).** The trivial twist has the trivial character of $U(1)(\mathbb{A}_E)$ and the empty modulus. The twist under the trivial $m$-fold twist is the trivial twist.

Lean: `New.Data.Twist.toAutChar_one` (New/Determinant/Twist/FitTwists.lean)

Lean: `New.Data.Twist.Q_one` (New/Determinant/Twist/FitTwists.lean)

Lean: `New.Data.MFoldTwist.toTwist_one` (New/Determinant/Twist/FitTwists.lean)

Lean: `New.Data.toAutChar_one_and_toTwist_one_and_Q_one` (New/Determinant/Twist/FitTwists.lean)

*Proof.* Each equation holds by the definition of the trivial twist and of the trivial $m$-fold twist. The last declaration is the conjunction of the three. $\square$

**Remark (Formalization).** In Lean the trivial tame character `TameChar.one` is an abbreviation for the tame character under the twist `1`. So a statement about `TameChar.one` unfolds to a statement about `(1 : D.Twist)`, and the three lemmas above apply without a further step. The type of twists has a `One` instance but no group structure: the source defines powers of tame characters, and it never multiplies two different twists. The inverse twist $\vartheta^{-1}$ enters only through the sign $s = -1$ in the ratio of Section 3, as the integer power $\vartheta^{s}$ of the automorphic character.

### Where the powers enter

The lift with index $j \in [1, m]$ has the character $\mu_j^0 \vartheta^j$ (the definition `New.Data.chainChar` of Volume 1). The ratios that the proof of Theorem C controls are the ratios at the twists $\vartheta^j$ for $j \in [1, m]$, with the sign $s = \pm 1$. The sign $-1$ gives the twist $\vartheta^{-j}$, which is ramified at the same places as $\vartheta^j$, since $\psi_w^{-j} \neq 1$ if and only if $\psi_w^j \neq 1$. So the $m$-fold condition covers all the exponents $-m \leq n \leq m$ with $n \neq 0$. The regular families of Section 6 are families of $m$-fold twists, and their conditions are stated for all powers $\vartheta^j$, $j \in [1, m]$.
