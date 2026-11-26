---
title: Twist measures of critical pairs
lean:
  - New/Congruences/Selmer/ClassSums.lean
decls:
  - New.Data.CriticalPair.IsTwistMeasure
  - New.Data.CriticalPair.integralAlgebraicPart_insert
  - New.Data.CriticalPair.isTwistMeasure_integralAlgebraicPart
  - New.Data.CriticalPair.hasWeight_mul_upsilonU1
  - New.Data.CriticalPair.exists_mul_norm_sq_detPeriod_eq
  - New.Data.CriticalPair.detPeriod_mul_upsilonU1_insert
  - New.Data.CriticalPair.exists_isIntegralMeasure_norm_sq_detPeriod
  - New.Data.CriticalPair.exists_isTwistMeasure_of_z_eq_one
  - New.Data.CriticalPair.exists_isTwistMeasure
  - New.Selmer.coprime_prod_q_of_isAuxiliary
  - New.Selmer.tameCharOfAuxiliary
  - New.Selmer.invAvatar_eq_of_artinMap_eq
  - New.Selmer.exists_tameChar_invAvatar_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Twist measures of critical pairs

This section gives the complex input of the $L$-value part. For a ramified critical pair $p = (\nu, z)$, the ratios of twisted to untwisted $L$-values are given by one function $F$ of tame characters, which is an integral measure at each modulus and changes by Euler factors when the modulus grows. The second part turns Galois characters for an auxiliary set into tame characters. All results are in [ClassSums.lean](lean:New/Congruences/Selmer/ClassSums.lean#L1).

Background used: tame characters $\vartheta$ with modulus $Q$, twists and $\mathrm{normQ}$ ([tame characters](/chapter/twists-critical-pairs/#twists-and-their-powers)); critical pairs, the ratio $\mathrm{ratio}(\vartheta)$ and ramified pairs ([critical pairs and the ratio](/chapter/twists-critical-pairs/#critical-pairs-and-the-ratio)); the factorization `New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq` ([products of L-values of a twist](/chapter/twists-critical-pairs/#products-of-l-values-of-a-twist)); the algebraic part for $z \geq 2$ with `New.Data.CriticalPair.integralAlgebraicPart_ne_zero` and `New.Data.CriticalPair.ratio_eq_integralAlgebraicPart_div` ([the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part)); integral measures `New.Data.TameChar.IsIntegralMeasure` and the rank-two period `New.Rows.detPeriod` with `New.Rows.detPeriod_insert` ([Hecke values](/chapter/hecke-values/)); the inverse of the period `New.Rows.exists_mul_stdClassSum_modKernelStdSpace_eq_one` ([the comparison operator, part 2](/chapter/comparison-operator-2/)); the avatar `New.Data.TameChar.invAvatar` ([avatars](/chapter/main-summands/#avatars-and-conjugate-self-duality)); the characters of U(1) of tame level `New.AutChar.exists_mem_tameChars` (Lib/ClassField/HeckeCharacter/Basic.lean).

Recall that $F$ is an *integral measure at the modulus $Q$ of $\vartheta$* if there are finitely many points $u_a$ of $U(1)(\mathbb{A})$ and complex numbers $c_a$ such that $\|j(c_a)\| \leq 1$ for every prime $l$ prime to $\mathrm{normQ}(\vartheta)$ and every ring map $j \colon \mathbb{C} \to \mathbb{C}_l$, and $F(\vartheta') = \sum_a c_a \vartheta'(u_a)$ for every $\vartheta'$ with modulus $Q$.

### Twist measures

**Definition.** Let $p = (\nu, z)$ be a critical pair, $I$ a finite set of natural numbers, $m \in \mathbb{N}$ and $F$ a function from tame characters to $\mathbb{C}$. Then $F$ is a *twist measure* for $p$, $I$ and $m$ if:

1. $F(1) \neq 0$;
2. $F$ is an integral measure at the modulus of every tame character;
3. if $\vartheta'$ is $\vartheta$ with the modulus $Q \cup \{v\}$ in place of $Q$, $v \notin Q$, then
$$F(\vartheta') = F(\vartheta) \prod_{l \in I} \prod_{\epsilon = \pm 1} \Bigl(1 - \frac{a_v^{\epsilon}}{q_v^{l}}\Bigr),$$
with $q_v = \mathrm{N}v$ and $a_v$ the value at a uniformizer at $v$ of the base change $x \mapsto (\nu\vartheta)(x/\bar x)$;
4. for every twist $\vartheta$, $F(\vartheta) = F(1)\, \mathrm{normQ}(\vartheta)^m\, \mathrm{ratio}(\vartheta)^{m+1}$.

Lean: `New.Data.CriticalPair.IsTwistMeasure` (New/Congruences/Selmer/ClassSums.lean).

The set $I$ becomes the list of exponents of a Stickelberger system in the next section, and $m + 1$ becomes the power $i$ of the ratio.

### The case $z \geq 2$

**Lemma.** Let $z \geq 2$ and let $n$ have $2z$ elements. Let $\vartheta'$ be $\vartheta$ with modulus $Q \cup \{v\}$, $v \notin Q$. Then
$$\mathrm{integralAlgebraicPart}(\vartheta') = \mathrm{integralAlgebraicPart}(\vartheta) \prod_{\epsilon = \pm 1} \Bigl(1 - \frac{a_v^{\epsilon}}{q_v^{z}}\Bigr).$$

Lean: `New.Data.CriticalPair.integralAlgebraicPart_insert` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* By `New.Data.CriticalPair.exists_integralAlgebraicPart_eq_mul_L` there is $A \neq 0$ with $\mathrm{integralAlgebraicPart}(\vartheta) = A \cdot L^{S}(z, (\nu\vartheta)^{-1})$, where the Euler factors at $S$, the chosen places and $Q$ with their conjugates, are removed. The place $v$ is not chosen, and $\bar v \notin Q \cup \{v\}$. The tame part of $\nu\vartheta$ is trivial at $v$ and $\bar v$, so the value at a uniformizer at $\bar v$ is $a_v^{-1}$. Going from $\vartheta$ to $\vartheta'$ sets the Hecke coefficients at $v$ and $\bar v$ to zero. By `eulerProd_erase` this multiplies the Euler product by $\prod_{w \in \{v, \bar v\}} (1 - c_w q_w^{-z})$, which is the stated product. $\square$

**Theorem.** If $z \geq 2$ and $n$ has $2z$ elements, then $\mathrm{integralAlgebraicPart}$ is a twist measure for $p$, $\{z\}$ and $m = 0$.

Lean: `New.Data.CriticalPair.isTwistMeasure_integralAlgebraicPart` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* (1) is `integralAlgebraicPart_ne_zero`. (2) is `isIntegralMeasure_integralAlgebraicPart`. (3) is the lemma. (4) follows from $\mathrm{ratio}(\vartheta) = \mathrm{integralAlgebraicPart}(\vartheta)/\mathrm{integralAlgebraicPart}(1)$, since the value at $1$ is not zero. $\square$

### The case $z = 1$

At $z = 1$ there is no lift of rank $2z \geq 4$. The source uses the period $\Lambda(\vartheta) = \mathrm{detPeriod}$ on the unitary group of rank two of the character $\nu\vartheta\upsilon$, with $\upsilon$ the restriction to $U(1)$ of the fixed splitting Hecke character, in weight $c - 1$, at the modulus $\mathrm{twistModulus}(\vartheta, 2)$ (the chosen places to the exponent $2$, times $Q$).

**Lemma.** The character $\nu\vartheta\upsilon$ has weight $-(c - 1)$ and tame part the product of the tame parts of $\nu$ and $\vartheta$.

Lean: `New.Data.CriticalPair.hasWeight_mul_upsilonU1` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* Multiplication by $\upsilon$ raises the weight by $1$ and keeps the tame part. Since $1 \leq z \leq c$, the subtraction $c - 1$ in $\mathbb{N}$ is exact. $\square$

**Lemma.** Let $p$ be ramified. There is a real $C$ such that for every twist $\vartheta$: $\Lambda(\vartheta) \neq 0$, $C \neq 0$, and $C\|\Lambda(\vartheta)\|^2 = \mathrm{lValueProd}(S, (\nu\vartheta)^{-1}, 1)$, with $S$ the chosen places and $Q$.

Lean: `New.Data.CriticalPair.exists_mul_norm_sq_detPeriod_eq` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* `exists_mul_stdClassSum_modKernelStdSpace_eq_one` in rank $2$ gives $C$ and, for each tame datum, an element $\gamma$ with $\gamma\Lambda = 1$ and $\|\gamma\|^2 = C/\mathrm{lValueProd}$. Then $\|\gamma\|\|\Lambda\| = 1$, so $\Lambda \neq 0$, and $C\|\Lambda\|^2 = \mathrm{lValueProd}$. This product is not zero, so $C \neq 0$. $\square$

**Lemma.** Let $\vartheta'$ be $\vartheta$ with modulus $Q \cup \{v\}$, $v \notin Q$. Then $\Lambda(\vartheta') = (1 - X)(1 - q_v X)\Lambda(\vartheta)$, with $X^{-1} = \mathrm{frobValue}$ of $\nu\vartheta\upsilon$ at $v$ in rank two.

Lean: `New.Data.CriticalPair.detPeriod_mul_upsilonU1_insert` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* The tame part is trivial off the places of the modulus, $v$ is not one of them, and the new set of places is the old one with $v$. Then `detPeriod_insert` gives the factor $\mathrm{qPochhammer}(q_v, 2, X) = (1 - X)(1 - q_v X)$. $\square$

**Lemma.** There is $N \neq 0$ such that $\vartheta' \mapsto \|\mathrm{chosenGroupOrder} \cdot N \cdot \Lambda(\vartheta')\|^2$ is an integral measure at the modulus of every tame character.

Lean: `New.Data.CriticalPair.exists_isIntegralMeasure_norm_sq_detPeriod` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* The kernel polynomial $\prod_\tau \det^{c_\tau - 1}$ is homogeneous, so a fixed $N \neq 0$ scales the kernel to integral values at integral points. Fix $\vartheta$ with modulus $Q$. For $\vartheta'$ of modulus $Q$, $\Lambda(\vartheta')$ is a sum over the classes $x$ and the elements $y$ of $GL_2$ of the residue ring of $\vartheta'(\det g)\theta(g)$, with $g = x \cdot \mathrm{lift}(y)$ and $\theta$ the kernel of the trivial twist. The coefficient of the point $\det g$ is $\mathrm{chosenGroupOrder}/\#\mathrm{Aut}(x) \cdot N\theta(g)$. The first factor is an integer by Minkowski's lemma. For a prime $l \nmid \mathrm{normQ}$, a rational point moves $g$ to an integral point at $l$ without a change of $\theta$, so $N\theta(g)$ is integral at $l$. So $N'\Lambda$ is an integral measure, and the squared norm of an integral measure is one (`IsIntegralMeasure.norm_sq`). $\square$

**Theorem.** Let $p$ be ramified with $z = 1$. There is a twist measure $F$ for $p$, $\{0, 1\}$ and $m = 1$.

Lean: `New.Data.CriticalPair.exists_isTwistMeasure_of_z_eq_one` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* Put $F(\vartheta) = \|\mathrm{chosenGroupOrder} \cdot N \cdot \Lambda(\vartheta)\|^2$. (1) holds since $\Lambda(1) \neq 0$ and $N \neq 0$. (2) is the last lemma. (3): the factor of $\Lambda$ is $(1 - X)(1 - q_v X)$, and $\|(1 - X)(1 - q_v X)\|^2$ is the product of $(1 - a_v^{\epsilon}/q_v^{l})$ over $l \in \{0, 1\}$ and $\epsilon = \pm 1$. The source gets this by writing $\|w\|^2 = w \bar w$ and putting in the definitions of `frobValue` and `spaceChar`, then a ring computation. (4): by the factorization with $z = 1$, $\mathrm{lValueProd}(S, (\nu\vartheta)^{-1}, 1) = \mathrm{normQ}(\vartheta)\, \mathrm{lValueProd}(\text{chosen}, \nu^{-1}, 1)\, \mathrm{ratio}(\vartheta)^2$. Divide the identity of the period lemma at $\vartheta$ by the one at $1$, and cancel $C$. This gives $\|\Lambda(\vartheta)\|^2 = \|\Lambda(1)\|^2 \mathrm{normQ}(\vartheta)\mathrm{ratio}(\vartheta)^2$. $\square$

**Theorem.** Let $p$ be ramified. There is $F$ that equals $\mathrm{integralAlgebraicPart}$ whenever $p$ has a lift of rank $2z$, and that is a twist measure for $p$ with $I = \{0, 1\}$ and $m = 1$ if $z = 1$, and $I = \{z\}$ and $m = 0$ otherwise.

Lean: `New.Data.CriticalPair.exists_isTwistMeasure` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* Since $1 \leq z$, either $z \geq 2$ or $z = 1$. In the first case $p$ has a lift of rank $2z$ and the theorem for $z \geq 2$ applies. In the second case there is no lift of rank $2z$, since that needs $z \geq 2$, so the first condition is empty, and the theorem for $z = 1$ applies. $\square$

**Remark (Formalization).** In the case $z = 1$, $F$ is real and positive, a squared norm. The constant $\mathrm{chosenGroupOrder} \cdot N$ is not unique. Only $F(\vartheta)/F(1)$ enters the twisting theorem, so the choice does not change the result.

### From Galois characters to tame characters

**Lemma.** Let $I$ be auxiliary for the bad places of $\ell M N$. Then $\prod_{w \in I} \mathrm{N}w$ is prime to $\ell$ and to $MN$. Each $\chi \in \mathrm{tameChars}(I)$ gives a tame character $\mathrm{tameCharOfAuxiliary}(\chi)$ with modulus $I$.

Lean: `New.Selmer.coprime_prod_q_of_isAuxiliary`, `New.Selmer.tameCharOfAuxiliary` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* Each $\mathrm{N}w$ is a prime. If it divided $\ell MN$, then $w$, which contains $\mathrm{N}w$, would be a bad place. For the tame character, the conditions on the conjugates come from the auxiliary set, and the coprimality from the first claim. $\square$

**Lemma.** If $\mathrm{Art}(x) = g$, then $\tau^{\mathrm{inv}}(g) = \iota_\ell(b)^{-1}$, with $b$ the value at $x$ of the base change of $\tau$.

Lean: `New.Selmer.invAvatar_eq_of_artinMap_eq` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* This is the formula for the avatar. The type of $\tau$ is $0$, so the product over the embeddings is $1$. $\square$

**Lemma.** Let $I$ be auxiliary for the bad places, and $\psi$ a character for $I$. Then there is a tame character $\tau$ with modulus $I$ and $\psi = \tau^{\mathrm{inv}}$.

Lean: `New.Selmer.exists_tameChar_invAvatar_eq` (New/Congruences/Selmer/ClassSums.lean).

*Proof.* Let $\eta$ be the idele character of $\psi$, and $\eta'$ its composite with the map from $U(1)(\mathbb{A})$ to the finite ideles. A rational point of $U(1)$ maps to a principal idele, so $\eta'$ kills it. An integral point $\equiv 1$ modulo $I$ is a unit everywhere and $\equiv 1$ at $I$, so $\eta'$ kills it. So $\iota_\ell^{-1} \circ \eta'$ is a character of $U(1)(\mathbb{A})$ modulo rational points and integral points of level $I$. By `exists_mem_tameChars` it comes from some $\mu \in \mathrm{tameChars}(I)$. Put $\tau = \mathrm{tameCharOfAuxiliary}(\mu^{-1})$. For $g$, choose $x$ with $\mathrm{Art}(x) = g$, and put $u = x/\bar x$. Then $\psi(g) = \eta(u) = \iota_\ell(\mu(u))$, and the last lemma gives $\tau^{\mathrm{inv}}(g) = \iota_\ell(\mu^{-1}(u))^{-1} = \iota_\ell(\mu(u))$. $\square$
