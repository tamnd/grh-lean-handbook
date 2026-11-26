---
title: The algebraic part
lean:
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
decls:
  - New.Data.CriticalPair.HasLiftRank
  - New.Data.CriticalPair.rowLengthSum
  - New.Data.CriticalPair.denomBound
  - New.Data.CriticalPair.lValueData
  - New.Data.CriticalPair.trivialLift
  - New.Data.CriticalPair.algPart
  - New.Data.CriticalPair.integralAlgebraicPart
  - New.LValueData.inner_trivialLift_self_eq_L
  - New.Data.CriticalPair.exists_norm_sq_trivialLift_eq_mul_L
  - New.Data.CriticalPair.cast_chosenGroupOrder_mul_denomBound_sq_ne_zero
  - New.Data.CriticalPair.vacuumScale_pow_mul_pow_rowLengthSum_ne_zero
  - New.Data.CriticalPair.trivialLift_ne_zero
  - New.Data.CriticalPair.algPart_pos
  - New.Data.CriticalPair.exists_ne_zero_algPart_eq_mul_L
  - New.Data.CriticalPair.exists_algPart_eq_mul_L
  - New.Data.CriticalPair.ratio_eq_algPart_div
  - New.Data.CriticalPair.integralAlgebraicPart_ne_zero
  - New.Data.CriticalPair.exists_integralAlgebraicPart_eq_mul_L
  - New.Data.CriticalPair.ratio_eq_integralAlgebraicPart_div
  - New.LValueData.formAction_trivialLift
  - New.Data.CriticalPair.exists_ofAlgForm_trivialLift_eq_smul_lift
  - New.Data.CriticalPair.formAction_trivialLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The algebraic part

The ratio of Section 3 is a quotient of two $L$-values. To bound its height, the proof needs it as a quotient of two numbers with arithmetic meaning. In the model case of Section 1 the meaning comes from the closed formula for $L(2, \chi_5)$. In the source it comes from theta lifts: the squared norm of the theta lift of $\nu\vartheta$ from $U(1)$ to a definite unitary group $U(2z)$ is a constant times $L^{S \cup Q}(z, (\nu\vartheta)^{-1})$. A definite unitary group has a finite set of classes, so a form on it is a finite list of vectors, and its squared norm is a finite sum. The constant does not depend on $\vartheta$, so it cancels in the ratio. This section makes this precise.

All statements of the section fix a finite index set $n$ and assume `HasLiftRank`.

**Definition (Lift rank).** For a critical pair $p = (\nu, z)$ and a finite type $n$, `HasLiftRank` says $|n| = 2z$ and $z \geq 2$.

Lean: `New.Data.CriticalPair.HasLiftRank` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

### The lift of a twisted pair

Let $p = (\nu, z)$ have weight $-c$, and let $\vartheta$ be a tame character with modulus $Q$. The row lengths of the pair are $c(\tau) - z \geq 0$ for $\tau \in \Phi$, and their sum is $\rho(p) = \sum_\tau (c(\tau) - z)$. This is the total order of the derivatives in the lift.

**Definition (Lift data and lift).** Assume $|n| = 2z$ and $z \geq 2$. The lift data of $(p, \vartheta)$ consists of the level places (the chosen places and the places of $Q$), the row lengths $c(\tau) - z$, the character $\nu\vartheta$ of $U(1)(\mathbb{A}_E)$ and the tame part $\psi \cdot \psi_\vartheta$. Its unscaled lift $\Theta$ is the theta lift to the definite $U(n)$ of the constant function $1$ on $U(1)$ for these data, times an index. The lift of $(p, \vartheta)$ is

$$\varphi_\vartheta = \big(v^{|n|} \cdot (\bar\pi_M\, \eta)^{\rho(p)}\big) \cdot \Theta,$$

where $v$ is the vacuum scale and $\eta$ the jet scale of the parameters, at the tower exponent of the data.

Lean: `New.Data.CriticalPair.rowLengthSum` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

Lean: `New.Data.CriticalPair.lValueData` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

Lean: `New.Data.CriticalPair.trivialLift` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

The scale makes the lift integral: the vacuum scale clears the denominators of the vacuum vector, and $\bar\pi_M \eta$ clears the denominators of one derivative. The integrality is proved in [Hecke values of character lifts](/chapter/hecke-values/). This chapter needs only that the scale is not zero.

**Definition (Algebraic part).** The algebraic part of $(p, \vartheta)$ is

$$L^{\mathrm{alg}}(z, \nu\vartheta) = \frac{\|\varphi_\vartheta\|^2}{(\mathrm{Nm}\, Q)^{|n| - 1}} \in \mathbb{C}.$$

The integral algebraic part is $n_L \cdot L^{\mathrm{alg}}(z, \nu\vartheta)$ with the natural number $n_L = |G_S| \cdot n_\nu^2$. Here $|G_S|$ is the product of the orders of the groups $GL_{rt}(k_w)$ over the chosen places $w$ (`chosenGroupOrder`), and $n_\nu = M^{2f \cdot 2z} (Md)^{\rho(p)}$ is a denominator for the values of the lift.

Lean: `New.Data.CriticalPair.algPart` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

Lean: `New.Data.CriticalPair.denomBound` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

Lean: `New.Data.CriticalPair.integralAlgebraicPart` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

The power $(\mathrm{Nm}\, Q)^{2z - 1}$ is the analogue of the conductor in the model case: the norm of the lift grows with the level, and the division removes this growth.

**Remark (Formalization).** The exponent $|n| - 1$ is a subtraction in $\mathbb{N}$. It is $2z - 1 \geq 3$ under `HasLiftRank`, so truncation does not occur. The division is in $\mathbb{C}$, and $\mathrm{Nm}\, Q \geq 1$ since it is a product of norms of places, so the junk value of $x/0$ does not occur. The algebraic part is a complex number. Its positivity below is in the order on $\mathbb{C}$ (`ComplexOrder`), in which $0 < x$ means that $x$ is a positive real number.

### The norm of the lift

The analytic input is the Rallis inner product formula for the dual pair $(U(1), U(2z))$, in the form of Volume 6 ([the Rallis inner product formula](/chapter/rallis-inner-product/)). Chapter 10 of this volume evaluates it for the lift of a character. We state the result in full.

**Theorem (Norm of the lift of a character).** Let $X$ be lift data with rank $|n| = 2k$ and $1 < k$, whose character $\mu$ has weight $-(\text{row length}(\tau) + k)$ at every $\tau$ and tame part trivial off the places of $X$. Let

$$C = \frac{\mathrm{vol}([U(n)]) \cdot \mathrm{vol}([U(1)])}{\zeta_F(2k)},$$

where $F$ is the maximal real subfield of $E$ and $\zeta_F(2k)$ is the Euler product at $k$ of the signs. Then $C \neq 0$ and

$$\langle \Theta_X, \Theta_X\rangle = C \cdot \prod_{w \text{ chosen}} (q_w - 1) \cdot h(\kappa) \cdot \dim(\kappa) \cdot L^{X}(k, \mu^{-1}) \cdot \Big(\prod_{w \in Q} q_w\Big)^{|n| - 1},$$

where $h(\kappa)$ is the hook number and $\dim(\kappa)$ the number of Weyl indices of the weight $\kappa$ of the descent pair, and $L^X$ omits the places of $X$ and their conjugates.

Lean: `New.LValueData.inner_trivialLift_self_eq_L` (New/OneLift/HeckeValues/CharacterLiftNorm.lean)

The proof is in [Hecke values of character lifts](/chapter/hecke-values/). Its idea: the inner product formula writes the squared norm of the theta lift of $1$ as a sum of coefficients of the vacuum. This sum is the Euler product $L^X(k, \mu^{-1})/\zeta_F(2k)$ without the places of $X$, and the missing factors of $\zeta_F(2k)$ at the places of $Q$ combine with the index of the level and the mean square of the block datum into $(\mathrm{Nm}\, Q)^{2k-1}$.

For a critical pair the character $\nu\vartheta$ has weight $-c = -((c - z) + z)$. So the theorem applies with $k = z$, and only the $L$-value and the power of $\mathrm{Nm}\,Q$ depend on $\vartheta$.

**Lemma (The norm as an $L$-value).** Assume $|n| = 2z$ and $z \geq 2$. There is $C \in \mathbb{C}$ with $C \neq 0$ such that for every tame character $\vartheta$ with modulus $Q$,

$$\|\Theta_\vartheta\|^2 = C \cdot L^{S \cup Q}(z, (\nu\vartheta)^{-1}) \cdot (\mathrm{Nm}\,Q)^{|n| - 1},$$

where $\Theta_\vartheta$ is the unscaled lift of the lift data of $(p, \vartheta)$.

Lean: `New.Data.CriticalPair.exists_norm_sq_trivialLift_eq_mul_L` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* Apply the theorem with $k = z$, so $2k = |n|$ and $k > 1$. Take for $C$ the product of the constant of the theorem, the product of the $q_w - 1$ over the chosen places, the hook number and the number of Weyl indices. These four factors depend only on the masses, the chosen places and the weight $\kappa$ of the descent pair. The weight is the column count of the row lengths $c(\tau) - z$, and it does not depend on $\vartheta$. So $C$ is the same for all $\vartheta$. Each factor is nonzero: the constant by the theorem, the factors $q_w - 1$ because $q_w \geq 2$, and the two counts because they are positive. The places of the lift data are the chosen places and $Q$, and the product over the twist places is $\mathrm{Nm}\,Q$. Finally $\langle \Theta, \Theta \rangle = \|\Theta\|^2$. $\square$

### Positivity and the ratio

**Lemma (Nonzero scales).** The factor $n_L = |G_S| \cdot n_\nu^2$ is nonzero in $\mathbb{C}$, and the scale $v^{k}(\bar\pi_M \eta)^{\rho(p)}$ is nonzero for every $k$.

Lean: `New.Data.CriticalPair.cast_chosenGroupOrder_mul_denomBound_sq_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.vacuumScale_pow_mul_pow_rowLengthSum_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The orders of finite groups are positive, $M \geq 1$ and $d \geq 1$, so $n_L \neq 0$. The vacuum scale, $\bar\pi_M$ and the jet scale are nonzero by their definitions, and a power of a nonzero number is nonzero. $\square$

**Lemma (The lift is not zero).** Assume `HasLiftRank`. For every tame character $\vartheta$, $\varphi_\vartheta \neq 0$.

Lean: `New.Data.CriticalPair.trivialLift_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* By the lemma on the norm and by $L^{S\cup Q}(\cdot, (\nu\vartheta)^{-1}) = L^{S\cup Q}(\cdot, \nu\vartheta)$ (Section 3), $\|\Theta_\vartheta\|^2 = C \cdot L^{S \cup Q}(z, \nu\vartheta) \cdot (\mathrm{Nm}\,Q)^{2z-1}$. Here $C \neq 0$, the $L$-value is nonzero by Section 3, and $\mathrm{Nm}\,Q \neq 0$. So $\Theta_\vartheta \neq 0$. The lift $\varphi_\vartheta$ is a nonzero multiple of $\Theta_\vartheta$. $\square$

So the non-vanishing of an $L$-value, a statement about the line $\mathrm{Re}\,s \geq 1$, gives the non-vanishing of a theta lift. This is the direction of the argument that the source uses. The classical theory often goes the other way: one proves that a lift is nonzero by local means and deduces that an $L$-value does not vanish.

**Theorem (Algebraic part).** Assume `HasLiftRank`. Then:

1. $L^{\mathrm{alg}}(z, \nu\vartheta) > 0$ for every tame character $\vartheta$;
2. there is $A \in \mathbb{C}$ with $A \neq 0$ such that $L^{\mathrm{alg}}(z, \nu\vartheta) = A \cdot L^{S \cup Q}(z, \nu\vartheta)$ for every tame character $\vartheta$ with modulus $Q$;
3. there is $A \in \mathbb{C}$ such that for every $\vartheta$ both the equation of 2 and the positivity of 1 hold.

Lean: `New.Data.CriticalPair.algPart_pos` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.exists_ne_zero_algPart_eq_mul_L` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.exists_algPart_eq_mul_L` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* 1. The norm $\|\varphi_\vartheta\|$ is positive by the last lemma, and $\mathrm{Nm}\,Q$ is a positive integer, so the quotient $\|\varphi_\vartheta\|^2/(\mathrm{Nm}\,Q)^{2z-1}$ is a positive real number.

2. Let $\sigma$ be the scale of the lift and $C$ the constant of the lemma on the norm. Put $A = |\sigma|^2 C$. Then $A \neq 0$, and

$$L^{\mathrm{alg}}(z, \nu\vartheta) = |\sigma|^2 \frac{\|\Theta_\vartheta\|^2}{(\mathrm{Nm}\,Q)^{2z-1}} = |\sigma|^2 C \cdot L^{S \cup Q}(z, \nu\vartheta),$$

by the lemma on the norm and Section 3, after cancelling $(\mathrm{Nm}\,Q)^{2z-1} \neq 0$.

3. Combine 1 and 2. $\square$

**Theorem (The ratio as a quotient of algebraic parts).** Assume `HasLiftRank`. For every tame character $\vartheta$, with the default sign $s = 1$,

$$\mathrm{ratio}(p, \vartheta) = \frac{L^{\mathrm{alg}}(z, \nu\vartheta)}{L^{\mathrm{alg}}(z, \nu)} = \frac{n_L L^{\mathrm{alg}}(z, \nu\vartheta)}{n_L L^{\mathrm{alg}}(z, \nu)}.$$

The integral algebraic part is nonzero, and there is $A \neq 0$ with $n_L L^{\mathrm{alg}}(z, \nu\vartheta) = A \cdot L^{S \cup Q}(z, (\nu\vartheta)^{-1})$ for every $\vartheta$.

Lean: `New.Data.CriticalPair.ratio_eq_algPart_div` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.integralAlgebraicPart_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.exists_integralAlgebraicPart_eq_mul_L` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.ratio_eq_integralAlgebraicPart_div` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* Take $A$ from part 3 of the last theorem. Then $A \neq 0$, since $A$ is a factor of the positive number $L^{\mathrm{alg}}(z, \nu\vartheta)$. At the trivial tame character the modulus is empty and the character is $\nu$ (Section 2). So

$$\frac{L^{\mathrm{alg}}(z, \nu\vartheta)}{L^{\mathrm{alg}}(z, \nu)} = \frac{A\, L^{S \cup Q}(z, \nu\vartheta)}{A\, L^{S}(z, \nu)} = \frac{L^{S \cup Q}(z, (\nu\vartheta)^{-1})}{L^{S}(z, \nu^{-1})}.$$

The left side is a quotient of two positive real numbers, so it is a positive real number and it is equal to its absolute value. The absolute value of the right side is the ratio by definition. This proves the first equation. The second follows because $n_L \neq 0$ cancels. For the integral algebraic part, $n_L \neq 0$ and the algebraic part is positive, so the product is not zero, and the constant is $n_L A$, with the $L$-value of $(\nu\vartheta)^{-1}$ from Section 3. $\square$

**Remark (Formalization).** The theorem holds only for the sign $s = 1$ and only under `HasLiftRank`, so only for pairs with $z \geq 2$. The non-vanishing of the ratio for all pairs and both signs is the direct theorem of Section 3. The proof of positivity uses `trivialLift_ne_zero`, which uses the non-vanishing of the $L$-value. So the order of the proofs in Lean is: $L$-value nonzero, then lift nonzero, then algebraic part positive, then the formula for the ratio. The planning notes reverse this order for the non-vanishing of the ratio. That is not what the source does.

**Example (A consequence for the $L$-values).** Part 2 of the theorem on the algebraic part, at $\vartheta$ and at $1$, gives

$$\frac{L^{S \cup Q}(z, \nu\vartheta)}{L^S(z, \nu)} = \frac{L^{\mathrm{alg}}(z, \nu\vartheta)}{L^{\mathrm{alg}}(z, \nu)} > 0.$$

So under `HasLiftRank` the quotient of the two $L$-values is already a positive real number, without absolute values. In the model case this is the statement that $L(2, \chi_5)/\zeta(2) = 24/(25\sqrt 5)$ is positive. For a real character the Euler product at a real point $s > 1$ is a product of positive factors, so positivity is clear there. For a complex character the individual $L$-values need not be real, and the positivity of the quotient is a consequence of the formula: the constant $A$ absorbs the common phase.

### The lift is a theta lift of the constant function

Two more facts about the lift are used in [false lifts](/chapter/false-lifts/), where the test forms are built from it.

**Proposition (The lift as a theta lift).** Assume `HasLiftRank`, and let $O$ be the descent pair of the lift data of $(p, \vartheta)$. The function on $U(2z)(\mathbb{A})$ that `ofAlgForm` attaches to $\varphi_\vartheta$ (its matrix coefficient against the highest vector of the parameter of $O$) is $c$ times the theta lift by the theta kernel of $O$, at the Schwartz function made from the highest vector, of the constant function $1$ on $U(1)(\mathbb{A})$, for some $c \neq 0$.

Lean: `New.Data.CriticalPair.exists_ofAlgForm_trivialLift_eq_smul_lift` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The unscaled lift is the theta lift of $1$ times the index of the chosen level (Chapter 10). Take $c$ to be the scale of the lift times this index. Both are nonzero. $\square$

**Proposition (Invariance).** The product of the groups $GL_1(k_w)$ over the chosen places acts on algebraic forms, and it fixes the unscaled lift $\Theta$ of any lift data and the lift $\varphi_\vartheta$ of $(p, \vartheta)$.

Lean: `New.LValueData.formAction_trivialLift` (New/OneLift/HeckeValues/TwistedRatio.lean)

Lean: `New.Data.CriticalPair.formAction_trivialLift` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* The group fixes the constant function $1$ on $U(1)$, and the theta lift commutes with the action. The lift $\varphi_\vartheta$ is a scalar multiple of $\Theta$, and the action is linear. $\square$
