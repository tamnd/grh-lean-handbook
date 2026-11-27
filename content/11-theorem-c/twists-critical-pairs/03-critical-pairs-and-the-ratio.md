---
title: Critical pairs and the ratio
lean:
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - Lib/ClassField/Avatar/HeckeBaseChange.lean
decls:
  - New.Data.CriticalPair
  - New.AutChar.L
  - New.AutChar.HasWeight.L_ne_zero
  - New.AutChar.HasWeight.L_inv
  - New.Data.CriticalPair.ratio
  - New.Data.CriticalPair.L_inv_mul
  - New.Data.CriticalPair.one_le_cast_z
  - New.Data.CriticalPair.neg_negWeight_ne_zero
  - New.Data.CriticalPair.L_mul_ne_zero
  - New.Data.CriticalPair.ratio_ne_zero
  - New.Data.CriticalPair.star_ratio
  - New.Data.CriticalPair.ratio_ne_zero_and_real
  - New.Data.CriticalPair.IsRamified
  - New.Data.RankOneIndex
  - New.Data.CriticalPair.IsMainPair
  - New.Data.CriticalPair.IsMainPair.isRamified
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Critical pairs and the ratio

The lattices of Theorem C are built from theta lifts, and the norms of theta lifts are $L$-values (Volume 6). When the twist changes, the $L$-values change. A critical pair records one $L$-value that occurs: a character $\nu$ of $U(1)(\mathbb{A}_E)$ and a point $z$. The ratio of the pair at a twist $\vartheta$ is the factor by which the twist changes the absolute value of this $L$-value. This section defines both and proves that the ratio is a nonzero real number. The proof is one application of the non-vanishing of Hecke $L$-functions on the line $\mathrm{Re}\, s \geq 1$.

### The partial L-function of a character of U(1)

Let $\nu$ be an automorphic character of $U(1)(\mathbb{A}_E)$. The map $x \mapsto x/\bar x$ sends $\mathbb{A}_E^\times$ to $U(1)(\mathbb{A}_E)$, so $\chi = \nu(x/\bar x)$ is a Hecke character of $E$, the base change of $\nu$.

**Definition (Partial $L$-function).** For a set $S$ of finite places of $E$, $L^S(s, \nu)$ is the Euler product of the base change $x \mapsto \nu(x/\bar x)$ over the places outside $S \cup \bar S$, for real $s > 1$. At $s = 1$ it is the limit from the right.

Lean: `New.AutChar.L` (Lib/ClassField/Avatar/HeckeBaseChange.lean)

Two facts from Volume 3 ([class field theory](/chapter/class-field-theory/)) are all that the section uses.

**Theorem (Non-vanishing).** Let $\nu$ have weight $e \neq 0$ and some tame part, and let $S$ be finite. Then $L^S(s, \nu) \neq 0$ for all real $s \geq 1$.

Lean: `New.AutChar.HasWeight.L_ne_zero` (Lib/ClassField/Avatar/HeckeBaseChange.lean)

The idea: the base change has type $2e \neq 0$ at infinity, so its square is not trivial, and a nontrivial Hecke character has an $L$-function without zeros on $\mathrm{Re}\, s \geq 1$.

**Theorem (Inverse character).** Let $\nu$ have weight $e$ and tame part $\psi$, with $\psi_v = 1$ for $v \notin S$. Then $L^S(\cdot, \nu^{-1}) = L^S(\cdot, \nu)$.

Lean: `New.AutChar.HasWeight.L_inv` (Lib/ClassField/Avatar/HeckeBaseChange.lean)

The reason: outside $S \cup \bar S$ the base change is unramified, and the Euler factor of $\nu^{-1}$ at $v$ is the Euler factor of $\nu$ at $\bar v$, because $\nu^{-1}(x/\bar x) = \nu(\bar x/x)$.

### Critical pairs

Let $\Phi$ be the CM type of $E$, which indexes the infinite places. Let $t = 5r$ and let $b$ be the weight scale of the data.

**Definition (Critical pair).** A critical pair $p = (\nu, z)$ consists of an automorphic character $\nu$ of $U(1)(\mathbb{A}_E)$, a function $c : \Phi \to \mathbb{N}$, a tame part $\psi$ and an integer $z$, such that $\nu$ has weight $-c$ and tame part $\psi$, $\psi_w = 1$ at every place $w$ that is not chosen, $1 \leq z \leq t$, and $z \leq c(v) \leq 4b$ for every $v \in \Phi$.

Lean: `New.Data.CriticalPair` (New/Derivatives/Field/ChosenPlaces.lean)

A place $w$ is chosen if $\pi_M \in w$, where $\pi_M$ is the element of norm $M = p_0 p_1$ of the imaginary quadratic field (Volume 1). So a critical pair is ramified at most at the chosen places, and its $L$-function without the chosen places is a complete Euler product of an unramified character. The point $z$ is at most the smallest weight. There are finitely many critical pairs (`New.Data.finite_criticalPair`).

**Definition (Ratio).** For a critical pair $p = (\nu, z)$, a tame character $\vartheta$ with modulus $Q$ and a sign $s \in \{\pm 1\}$ (by default $s = 1$),

$$\mathrm{ratio}(p, \vartheta, s) = \frac{|L^{S \cup Q}(z, (\nu \vartheta^{s})^{-1})|}{|L^{S}(z, \nu^{-1})|} \in \mathbb{C},$$

where $S$ is the set of chosen places.

Lean: `New.Data.CriticalPair.ratio` (New/Determinant/Twist/FitTwists.lean)

At $\vartheta = 1$ the modulus is empty, so the numerator and the denominator are the same number and the ratio is $1$, since the denominator is not zero (Theorem below). The ratio is a quotient of two absolute values, so it is real and nonnegative. The source writes it as a complex number because the heights of Volume 1 are heights of families of complex numbers.

**Remark (Formalization).** The ratio is a quotient in $\mathbb{C}$, and Lean defines $x/0 = 0$. So the definition alone does not exclude the value $0$ when the denominator vanishes. The theorem on non-vanishing below excludes it. The sign $s$ is a unit of $\mathbb{Z}$, and $\vartheta^s$ is the integer power of the automorphic character. Only the character is raised to the power $s$; the modulus $Q$ in the numerator is the modulus of $\vartheta$, the same for both signs.

### The ratio is a nonzero real number

**Lemma (Inverse of the twisted character).** Let $p = (\nu, z)$ be a critical pair and $\vartheta$ a tame character. Then

$$L^{S \cup Q}(\cdot, (\nu\vartheta)^{-1}) = L^{S \cup Q}(\cdot, \nu\vartheta).$$

Lean: `New.Data.CriticalPair.L_inv_mul` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The character $\nu\vartheta$ has weight $-c + 0 = -c$ and tame part $\psi \cdot \psi_\vartheta$. If $w \notin S \cup Q$, then $\psi_w = 1$ because $w$ is not chosen, and $(\psi_\vartheta)_w = 1$ because $w \notin Q$. So the tame part is trivial outside $S \cup Q$, and the theorem on the inverse character applies. $\square$

The same argument with $\vartheta = 1$ gives $L^S(\cdot, \nu^{-1}) = L^S(\cdot, \nu)$ (`New.Data.CriticalPair.L_inv`, in [the chain determinant and its factorization](/chapter/chain-determinant/)). So the inverses in the definition of the ratio do not change its value at $s = 1$. The source keeps them because the inner product formula of Section 4 gives the $L$-value of the inverse character.

**Lemma (The weight of a pair).** For a critical pair, $1 \leq z$ as a real number, and the weight $v \mapsto -c(v)$ is not the zero function.

Lean: `New.Data.CriticalPair.one_le_cast_z` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.neg_negWeight_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The first claim is $z \in [1, t]$. For the second, take any $v \in \Phi$. Then $c(v) \geq z \geq 1$, so $-c(v) \neq 0$. $\square$

**Lemma (Non-vanishing of the twisted value).** For a critical pair $p$ and a tame character $\vartheta$, $L^{S \cup Q}(z, \nu\vartheta) \neq 0$.

Lean: `New.Data.CriticalPair.L_mul_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The character $\nu\vartheta$ has weight $-c \neq 0$. The set $S \cup Q$ is finite, since there are finitely many chosen places and $Q$ is a finite set. And $z \geq 1$. The theorem on non-vanishing applies. $\square$

**Theorem (The ratio is a nonzero real number).** For a critical pair $p$, a tame character $\vartheta$ and a sign $s$,

$$\mathrm{ratio}(p, \vartheta, s) \neq 0 \quad\text{and}\quad \overline{\mathrm{ratio}(p, \vartheta, s)} = \mathrm{ratio}(p, \vartheta, s).$$

Lean: `New.Data.CriticalPair.ratio_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.star_ratio` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.ratio_ne_zero_and_real` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The character $\vartheta^s$ has weight $s \cdot 0 = 0$. So $\nu\vartheta^s$ has weight $-c$, and its inverse has weight $c$. Both weights are nonzero by the lemma on the weight of a pair. The theorem on non-vanishing, with the finite sets $S \cup Q$ and $S$ and the point $z \geq 1$, gives $L^{S \cup Q}(z, (\nu\vartheta^s)^{-1}) \neq 0$ and $L^S(z, \nu^{-1}) \neq 0$. A quotient of two positive real numbers is a nonzero real number, and complex conjugation fixes real numbers. $\square$

**Remark (Formalization).** The planning notes of the handbook derive the non-vanishing of the ratio from the positivity of the algebraic part and from the formula of the ratio as a quotient of algebraic parts (Section 4). The source does not do this. It proves `ratio_ne_zero` directly from `New.AutChar.HasWeight.L_ne_zero`, as above. The direct proof is better for the argument: it holds for both signs and for every critical pair, while the formula of Section 4 holds only for $s = 1$ and for pairs with $z \geq 2$.

**Example (A pair with $z = 1$).** The definition allows $z = 1$. Then the ratio compares the values at $s = 1$, the edge of the region of absolute convergence. The source defines the value at $s = 1$ as the limit from the right of the Euler product, and the theorem on non-vanishing includes $s = 1$. The classical model is $L(1, \chi) \neq 0$ for a nontrivial Dirichlet character, the key step of Dirichlet's theorem on primes in progressions. So the case $z = 1$ is the deepest case of the theorem, and the cases $z \geq 2$ are elementary: there the Euler product converges absolutely and has no zero.

### Ramified pairs and main pairs

The proof of Theorem C does not need all critical pairs. It needs the pairs whose $L$-values occur in the norms of the lifts of the chain. These are the main pairs.

**Definition (Ramified pair).** A critical pair is ramified if $\psi_w \neq 1$ exactly at the chosen places: $\psi_w \neq 1 \iff w$ is chosen, for every finite place $w$.

Lean: `New.Data.CriticalPair.IsRamified` (New/Determinant/Twist/FitTwists.lean)

**Definition (Rank index).** For $z \in \mathbb{N}$, the index type $\mathrm{RankOneIndex}(z)$ is the disjoint union of sets of sizes $12$, $4$, $4$ and $2z \mathbin{\dot-} 20$, where $\dot-$ is the truncated subtraction of $\mathbb{N}$.

Lean: `New.Data.RankOneIndex` (New/Determinant/Twist/FitTwists.lean)

The four blocks are the basis of the definite space $E^{2z}$ to which the character of a main pair is lifted. The block sizes come from the construction of the test form in [Hecke values of character lifts](/chapter/hecke-values/).

**Definition (Main pair).** Let $\omega = (\omega_w)$ be the fixed family of residue characters of the data (`New.Data.chiMLocal`), and let $w_j(v)$ be the weight of the character of the $j$-th lift. A critical pair $p = (\nu, z)$ with weight $-c$ is a main pair for $j$ if

1. $\mathrm{RankOneIndex}(z)$ has $2z$ elements and $z \geq 2$;
2. $m < z \leq r$;
3. $1 \leq j \leq m$;
4. the tame part of $\nu$ is $\omega^j$;
5. $c(v) \leq w_j(v)$ for every $v \in \Phi$;
6. $w_j(v) + r \leq c(v) + t$ for every $v \in \Phi$.

Lean: `New.Data.CriticalPair.IsMainPair` (New/Determinant/Twist/FitTwists.lean)

Conditions 5 and 6 say $w_j(v) - (t - r) \leq c(v) \leq w_j(v)$. Since $t - r = 4r$, the weight of a main pair lies in a window of width $4r$ below the weight of the $j$-th lift.

**Remark (Formalization).** Condition 1 is `HasLiftRank` for the index type $\mathrm{RankOneIndex}(z)$. Its docstring says "$2 \leq z$". The type forces more: it has $20 + (2z \mathbin{\dot-} 20)$ elements, which is $2z$ if $z \geq 10$ and $20 > 2z$ if $z < 10$. So condition 1 holds if and only if $z \geq 10$. The argument loses nothing, because condition 2 gives $z > m \geq \sqrt{x}$, and the sizes of the data make $\sqrt{x}$ much larger than $10$. Condition 6 is written without subtraction, so the truncated subtraction of $\mathbb{N}$ plays no role in it. The planning notes ask whether the bound is $w_j + r - t \leq c$; the Lean form is the form above, which is the same bound over $\mathbb{Z}$.

**Lemma (Main pairs are ramified).** A main pair for some $j$ is ramified.

Lean: `New.Data.CriticalPair.IsMainPair.isRamified` (New/Determinant/Twist/FitTwists.lean)

*Proof.* The tame part is $\omega^j$ with $1 \leq j \leq m$. By a lemma of Volume 9 (`New.Data.chiMLocal_zpow_ne_one_iff_isChosen`), for every integer $n$ with $n \neq 0$ and $|n| \leq 8m$, $\omega_w^n \neq 1$ if and only if $w$ is chosen. The reason is that $\omega_w = 1$ off the chosen places, and at a chosen place $\omega_w$ has order $q_2$, a multiple of $q_1 d > 8m$, so no $n$ with $0 < |n| \leq 8m$ is a multiple of the order. Apply it with $n = j$. $\square$

The lemma is the step that connects main pairs to the regular families of Section 6. The condition on small ratios there is stated for ramified pairs, and the proof of Theorem C applies it to main pairs.
