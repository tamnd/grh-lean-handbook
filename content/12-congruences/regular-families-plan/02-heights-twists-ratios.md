---
title: Heights, twists and ratios
lean:
  - New/Reduction/Lattices/Heights.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/Determinant/Twist/FitTwists.lean
decls:
  - New.PrimePadicIso
  - New.HeightLe
  - New.HeightLe.of_le
  - New.Data.TameChar
  - New.Data.TameChar.normQ
  - New.Data.Twist
  - New.Data.MFoldTwist
  - New.Data.MFoldTwist.powTwist
  - New.Data.CriticalPair
  - New.Data.CriticalPair.ratio
  - New.Data.CriticalPair.IsRamified
  - New.Data.CriticalPair.IsMainPair
  - New.Data.CriticalPair.IsMainPair.isRamified
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Heights, twists and ratios

This section collects the objects in the statement of the theorem that do not involve denominators: heights of families indexed by primes, twists, and the ratios of Hecke $L$-values. All of them come from earlier volumes. The section states them in the form that the theorem uses.

### Families indexed by primes

The theorem treats all primes at once. One twist is chosen for each prime $\ell$ and each isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$, and the sizes of the resulting numbers are measured by one height.

**Definition (Pairs of a prime and an isomorphism).** A *prime isomorphism* $\kappa$ is a prime $\ell$ together with a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$.

Lean: `New.PrimePadicIso` (New/Reduction/Lattices/Heights.lean).

Such isomorphisms exist by the axiom of choice, since both fields are algebraically closed of characteristic $0$ and of the same uncountable cardinality. There are many of them for each $\ell$. The source never uses a particular one. It quantifies over all of them.

**Definition (Height of a family).** Let $c$ be a real number and $y$ a function from prime isomorphisms to $\mathbb{C}$. The family $y$ *has height at most* $c$ if there are a complex number $H \neq 0$, a real number $\alpha$ and real numbers $h_l \geq 0$, one for each natural number $l$, such that:

1. $|\sigma(H)| \leq e^{\alpha}$ for every ring automorphism $\sigma$ of $\mathbb{C}$;
2. $\|\iota(H\, y_\kappa)\| \leq \ell^{h_\ell}$ for every prime isomorphism $\kappa = (\ell, \iota)$;
3. $\alpha + \sum_{l \in T} h_l \log l \leq c$ for every finite set $T$ of primes.

Lean: `New.HeightLe` (New/Reduction/Lattices/Heights.lean).

Here $\|\cdot\|$ is the norm of $\overline{\mathbb{Q}}_\ell$ with $\|\ell\| = 1/\ell$. For an algebraic number $y$ with the constant family $y_\kappa = y$, this is the logarithmic Weil height, in a form that does not need a number field: $H$ clears the denominators, $\alpha$ bounds the archimedean sizes, and $h_\ell \log \ell$ bounds the loss at $\ell$. [Twisted lattices](/chapter/twisted-lattices/) in Volume 1 explains why the source uses this form. The file Heights.lean also proves the product formula for $\mathbb{Q}$ in logarithms, `New.log_product_formula`, which is the reason that a height bound is a real constraint.

**Remark (Formalization).** The multiplier $H$ and the numbers $h_l$ are the same for all isomorphisms $\iota$ at one prime. The family $y$ may still depend on $\iota$, and in the theorem it does, since the twist $\theta(\kappa)$ depends on $\kappa$. So a bound of height for the family is one bound for all choices, with a different twist at each choice. This is the form in which Theorem C uses the bounds of this volume.

The source uses the definition through one simple criterion, the case $H = 1$ and $\alpha = 0$.

**Lemma (Heights from local bounds).** Let $e_l$ be real numbers with $\sum_{l \in T} e_l \leq c$ for every finite set $T$ of primes. Let $\|\iota(y_\kappa)\| \leq \exp(e_\ell)$ for every prime isomorphism $\kappa = (\ell, \iota)$. Then $y$ has height at most $c$.

Lean: `New.HeightLe.of_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* The source applies the more general lemma `New.HeightLe.of_mul_le` with $H = 1$ and $\alpha = 0$. That lemma takes $h_l = e_l^{+}/\log l$, where $e^{+} = \max(e, 0)$. Then $h_l \geq 0$. Condition 1 is $1 \leq e^{0}$. Condition 2 holds because $\|\iota(y_\kappa)\| \leq \exp(e_\ell) \leq \exp(e_\ell^{+}) = \ell^{h_\ell}$. For condition 3, $\sum_{l \in T} h_l \log l = \sum_{l \in T} e_l^{+}$ is the sum of $e_l$ over the primes $l \in T$ with $e_l \geq 0$. This is a sum over a finite set of primes, so it is at most $c$ by the hypothesis. $\square$

The hypothesis asks the sum bound for every finite set $T$, not for the set of all primes. So the lemma never needs a convergent infinite sum. The numbers $e_l$ may have any sign, and the proof of condition 3 uses the bound for the subset of $T$ where $e_l \geq 0$. In the theorem, $e_\ell$ is a multiple of $\log \ell$, so the sum condition is a weighted sum $\sum_{l \in T} e'_l \log l \leq c$.

### Twists

The twists are characters of $U(1)$ over the CM field $E$, with tame ramification on a finite set of places ([fields, places and twists](/chapter/fields-places-twists/)).

**Definition (Tame characters and twists).** A *tame character* $\vartheta$ of the data $D$ is a character of $U(1)(\mathbb{A})$, together with a finite set $Q$ of finite places of $E$ and a tame part $\psi$, a character $\psi_w$ of the residue field at each finite place $w$, with these properties: $\vartheta$ has weight $0$ and tame part $\psi$; $\psi_w = 1$ for $w \notin Q$; $Q$ is disjoint from its complex conjugate; and the product of the norms of the places of $Q$ is prime to $M N$, where $M = p_0 p_1$ and $N$ is the level. The *norm of the modulus* is $\mathrm{Nm}\,Q = \prod_{w \in Q} q_w$. A *twist* is a tame character with $\psi_w \neq 1$ for every $w \in Q$. An *$m$-fold twist* is a twist with $\psi_w^n \neq 1$ for every $w \in Q$ and every $1 \leq n \leq m$. For an $m$-fold twist $\tau$ and $1 \leq j \leq m$, the power $\tau^j$ is a twist, with the same set $Q$ and the tame part $\psi^j$.

Lean: `New.Data.TameChar`, `New.Data.TameChar.normQ`, `New.Data.Twist`, `New.Data.MFoldTwist`, `New.Data.MFoldTwist.powTwist` (New/Reduction/Data/LevelAndTwists.lean).

The index $j$ runs over $\mathrm{LiftIndex} = \{1, \dots, m\}$. The $m$ powers of one $m$-fold twist serve the $m$ single lifts of one chain, and each power must again be a twist, ramified at all places of $Q$. This is the reason for the condition $\psi_w^n \neq 1$. The trivial character, with $Q$ empty, is an $m$-fold twist.

### Critical pairs and ratios of Hecke values

**Definition (Critical pairs).** A *critical pair* $p = (\nu, z)$ of the data $D$ consists of a character $\nu$ of $U(1)(\mathbb{A})$, trivial on rational points, a function $c$ on the infinite places, a tame part $\psi$ and a natural number $z$, such that $\nu$ has weight $-c$ and tame part $\psi$, $\psi_w = 1$ off the chosen places, $1 \leq z \leq t$, and $z \leq c(v) \leq 4b$ at every infinite place $v$.

Lean: `New.Data.CriticalPair` (New/Derivatives/Field/ChosenPlaces.lean).

**Definition (The ratio of Hecke values).** For a critical pair $p = (\nu, z)$, a tame character $\vartheta$ and a sign $s = \pm 1$ (by default $s = 1$), put
$$p.\mathrm{ratio}(\vartheta, s) = \frac{|L^{S \cup Q}(z, (\nu\vartheta^{s})^{-1})|}{|L^{S}(z, \nu^{-1})|} \in \mathbb{C} .$$
Here $S$ is the set of chosen places, and $L^{S}$ omits the Euler factors at the places of $S$ and at their conjugates. The numerator also omits the factors at the places of $Q$ and their conjugates. The pair is *ramified* if $\psi_w \neq 1$ exactly at the chosen places $w$.

Lean: `New.Data.CriticalPair.ratio`, `New.Data.CriticalPair.IsRamified` (New/Determinant/Twist/FitTwists.lean).

**Remark (Formalization).** The ratio is a real number read as a complex number. If $L^{S}(z, \nu^{-1}) = 0$, then the ratio is $0$ by the convention $x/0 = 0$ of Lean, and its inverse is $0$ by the convention $0^{-1} = 0$. Then every bound of the form $\|\iota(\mathrm{ratio}^{-1})\| \leq C$ with $C \geq 0$ holds trivially at this pair. The theorem bounds only inverse ratios, so the junk value never makes a statement false. It can make a statement empty at a pair where the $L$-value vanishes.

The pairs that the lifts of one chain see are the main pairs. For them Volume 11 proves a height bound for the inverse ratios from the second half of the definition of regular families.

**Definition (Main pairs).** A critical pair $p = (\nu, z)$ with weight $-c$ is a *main pair* for $j$ if $2 \leq z$ and the index type `New.Data.RankOneIndex` $z$ has $2z$ elements, $m < z \leq r$, $1 \leq j \leq m$, the tame part of $\nu$ is $\omega^j$ for the fixed family $\omega$ of residue characters, and $w_j + r - t \leq c \leq w_j$ at every infinite place. Here $w_j$ is minus the weight of the character of the $j$-th lift.

Lean: `New.Data.CriticalPair.IsMainPair` (New/Determinant/Twist/FitTwists.lean).

**Lemma (Main pairs are ramified).** A main pair for some $j$ is ramified.

Lean: `New.Data.CriticalPair.IsMainPair.isRamified` (New/Determinant/Twist/FitTwists.lean).

*Proof.* The tame part is $\omega^j$ with $1 \leq j \leq m$. The family $\omega$ is trivial off the chosen places, and at each chosen place it has order above $8m$. So $\omega_w^j \neq 1$ exactly at the chosen places. The source cites this fact as `New.Data.chiMLocal_zpow_ne_one_iff_isChosen`. $\square$

**Remark (Formalization).** The lower bound on $c$ is written $w_j + r \leq c + t$ in Lean, without subtraction. The index type `New.Data.RankOneIndex` $z$ is a sum of four blocks of sizes $12$, $4$, $4$ and $2z - 20$, with truncated subtraction of natural numbers. So it has $20 + (2z - 20)$ elements, which is $2z$ only for $z \geq 10$. The field `hasLiftRank` asks for $2z$ elements and for $2 \leq z$, so it excludes the junk sizes for small $z$. It fixes the rank of the definite space to which the character of the pair is lifted.

### Why the ratios matter

For a main pair $p$, Volume 11 writes the inverse ratio $p.\mathrm{ratio}(\vartheta)^{-1}$, up to a power of $\mathrm{Nm}\,Q$, as a quotient $\|\varphi_1\|^2/\|\varphi_\vartheta\|^2$ of the norms of two rank-one theta lifts, the untwisted and the twisted one ([Hecke values of character lifts](/chapter/hecke-values/)). A test form $\Xi$ that is integral above $\ell$ and orthogonal to the false lifts pairs with $\varphi_\vartheta$. The $\ell$-adic size of the inverse ratio is then controlled by the denominator of the projection of test forms to the line $\mathbb{C}\varphi_\vartheta$. This is why the definition of denominators in the next section has a second clause for main pairs. The resulting bound is `New.Data.heightLe_inv_ratio`: for a regular family and a main pair for $j$, the inverse ratios at $\theta(\kappa)^j$ have height at most $6\,\mathrm{denominatorBudget} - \mathrm{directionAmount}$.

For all ramified pairs, main or not, the theorem bounds the inverse ratios directly, at the powers $\vartheta = \theta(\kappa)^j$ and for both signs $s = \pm 1$. The twisting theorem of Section 6 gives $\|\iota(p.\mathrm{ratio}(\vartheta, s)^{-1})\| \leq \ell^{e'_\ell}$ with an explicit number $e'_\ell$, the twist error. Section 3 turns this into a height bound with the constant $x_1$. The value $s = -1$ is the ratio at the inverse twist.
