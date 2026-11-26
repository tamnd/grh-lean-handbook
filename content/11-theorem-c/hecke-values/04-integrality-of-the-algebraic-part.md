---
title: Integrality of the algebraic part
lean:
  - New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean
decls:
  - New.Data.TameChar.IsIntegralMeasure
  - New.Data.TameChar.IsIntegralMeasure.norm_sq
  - New.Data.CriticalPair.pointDatum
  - New.Data.CriticalPair.pointKernel
  - New.Data.CriticalPair.smul_kernelForm_apply
  - New.Data.CriticalPair.trivialLift_apply
  - New.Data.CriticalPair.weylGauge_denomBound_smul_pointKernel_le_one
  - New.Data.CriticalPair.denomBound_smul_trivialLift_mem_integralForms
  - New.Data.CriticalPair.integralAlgebraicPart_mem_integralAway
  - New.Data.CriticalPair.norm_integralAlgebraicPart_one_le_one
  - New.Data.CriticalPair.TrivialLiftIndex
  - New.Data.CriticalPair.liftPoint
  - New.Data.CriticalPair.trivialLift_apply_eq_sum_smul
  - New.Data.CriticalPair.kernelPairing
  - New.Data.CriticalPair.norm_sq_trivialLift_eq_sum
  - New.Data.CriticalPair.mul_kernelPairing_mem_embValRing
  - New.Data.CriticalPair.isIntegralMeasure_integralAlgebraicPart
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integrality of the algebraic part

Let $p = (\nu, z)$ be a critical pair, $n$ an index set with `H : p.HasLiftRank n` (so $\#n = 2z$ and $z \geq 2$), and $\vartheta$ a tame character with modulus $Q$ and norm $N(Q) = $ `ϑ.normQ`. The scaled lift $\varphi_\vartheta = $ `trivialLift H ϑ` and the integral algebraic part

$$n_L\,L^{\mathrm{alg}}(\vartheta) = \mathrm{chosenGroupOrder}\cdot n_\nu^2\cdot\frac{\|\varphi_\vartheta\|^2}{N(Q)^{2z-1}}, \qquad n_\nu = \mathrm{denomBound} = M^{4fz}(Md)^j,$$

are defined in [the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part), with $j = $ `p.rowLengthSum`. That chapter says that $n_\nu$ clears the denominators of the lift and defers the proof to this chapter. This section gives the proof. It then shows that $\vartheta' \mapsto n_L L^{\mathrm{alg}}(\vartheta')$, on the characters with the same modulus $Q$, is the evaluation of one element of the group ring of $U(1)(\mathbb{A})$ whose coefficients are integral away from $Q$. Volume 12 calls this an integral measure and uses it in [twist measures](/chapter/twisting-theorem/#twist-measures-of-critical-pairs).

### Integral measures

**Definition (Integral measure).** A function $F$ on tame characters is an integral measure at the modulus $Q$ of $\vartheta$ if there are a finite set $A$, points $u_a \in U(1)(\mathbb{A})$ and numbers $c_a \in \mathbb{C}$ such that:

1. each $c_a$ is integral away from $N(Q)$: $\|j(c_a)\| \leq 1$ for every prime $l \nmid N(Q)$ and every ring map $j : \mathbb{C} \to \mathbb{C}_l$ (`Seesaw.integralAway`);
2. $F(\vartheta') = \sum_a c_a\,\vartheta'(u_a)$ for every tame $\vartheta'$ with $Q(\vartheta') = Q$.

Lean: `New.Data.TameChar.IsIntegralMeasure` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

**Lemma (Squares of measures).** If $F$ is an integral measure at $Q$, so is $\vartheta' \mapsto |F(\vartheta')|^2$.

Lean: `New.Data.TameChar.IsIntegralMeasure.norm_sq` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* Take the index set $A\times A$, the points $u_x u_y^{-1}$ and the coefficients $c_x\,\overline{c_y}$. Then $|F|^2 = F\bar F = \sum_{x,y}c_x\overline{c_y}\,\vartheta'(u_x)\overline{\vartheta'(u_y)}$, and $\overline{\vartheta'(u_y)} = \vartheta'(u_y^{-1})$ since the values lie on the circle. For integrality, $\overline{c_y}$ is integral at $j$ because $c_y$ is integral at $j\circ\mathrm{conj}$, which is again a ring map to $\mathbb{C}_l$. A product of integral numbers is integral. $\square$

### The lift as a sum of kernel values

**Definition (Point datum and point kernel).** Let $X = $ `lValueData H ϑ`. The point datum is

$$f^{\mathrm{pt}} = \mathrm{vacuumScale}^{\#n}\cdot\mathrm{vacuumDatum}\big(\mathfrak{m}_1, \mathbf{1}^{\mathrm{blk}}\big),$$

the vacuum off the chosen places and the places of $Q$, and at these places the indicator `identityBlockIndicator` modulo $\mathfrak{m}_1 = $ `levelModulus 1` of the columns that reduce to $e_{i_0}$ at the chosen places and have the entry $1$ at $i_0$ at the places of $Q$. The point kernel is the jet vector

$$\kappa^{\mathrm{pt}}(g, h) = \mathrm{kernelValue}_X\big(b, f^{\mathrm{pt}}\big)(g, h), \qquad b = \bar\pi_M\cdot\mathrm{jetScale},$$

with one coordinate for each index of the Weyl basis of the weight.

Lean: `New.Data.CriticalPair.pointDatum` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean), `New.Data.CriticalPair.pointKernel` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

Here $\pi_M = $ `D.piMBar` is an integer of the imaginary quadratic field with norm $M$, and $\mathrm{jetScale} = $ `P.jetScale D.towerExp` is the period scale of the Taylor series ([theta kernels and gauges](/chapter/theta-kernels-gauges/)).

**Lemma (Kernel form and point kernel).** For $g \in U(1)(\mathbb{A}_f)$ and $h \in G_f$,

$$\mathrm{vacuumScale}^{\#n}\,b^{\,j}\cdot\theta_X(g)(h) = \sum_{A\in\mathrm{TwistGL}}\kappa^{\mathrm{pt}}\big(g\cdot\mathrm{twistResidueLift}(A), h\big),$$

where $A$ runs over the families of units of the residue fields at the places of $Q$ and `twistResidueLift A` is an integral lift of $A^{-1}$.

Lean: `New.Data.CriticalPair.smul_kernelForm_apply` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The block datum of $X$ is a sum over $A$ of translates of the vacuum datum by `twistResidueLift A` (`blockDatum_eq_sum_modDatum`). So $\theta_X(g)(h)$ is the sum over $A$ of the unscaled kernel values at $g\cdot\mathrm{twistResidueLift}(A)$. The scalar $\mathrm{vacuumScale}^{\#n}$ is linear in the datum. By the scale lemma of [the data, the kernel and the lift](/chapter/character-lifts/#the-data-the-kernel-and-the-lift) (`schurJet_jetSeries_eq_smul`), scaling the variables by $b$ multiplies the jet vector by $b^{\,\mathrm{boxes}}$, and the number of boxes of the weight is the row length sum $j$. $\square$

**Lemma (The lift as a finite sum).** For $h \in G_f$,

$$\varphi_\vartheta(h) = \sum_{(c, A)}\kappa^{\mathrm{pt}}\big(c_{\mathrm{out}}\cdot\mathrm{twistResidueLift}(A), h\big),$$

over the classes $c$ of $U(1)$ at the level `D.chosenLevel` and the families $A$.

Lean: `New.Data.CriticalPair.trivialLift_apply` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The classes of $U(1)$ at this level have trivial stabilisers (`classAut_eq_bot_of_le_chosenLevel`), since the level is small enough by the size bounds of the data. So the class sum $\varphi_X$ is the plain sum $\sum_c\theta_X(c_{\mathrm{out}})$. The scaled lift is $\mathrm{vacuumScale}^{\#n}b^{\,j}\varphi_X$. Apply the previous lemma to each term. $\square$

### Integrality

**Lemma (Integral kernel values).** Let $l$ be a prime with $\gcd(l, N(Q)) = 1$ and $j$ an embedding $\mathbb{C} \to \mathbb{C}_l$. For all $g$, $h$, the vector $n_\nu\cdot\kappa^{\mathrm{pt}}(g, h)$ has gauge at most $1$ at $h$ with respect to $j$.

Lean: `New.Data.CriticalPair.weylGauge_denomBound_smul_pointKernel_le_one` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* Put $d_0 = M^{2f\cdot\#n} = M^{4fz}$. Step 1: $d_0\cdot f^{\mathrm{pt}}$ lies in the standard data of level $M$ (`smul_vacuumDatum_mem_standardData`). This uses that $N(Q)M$ lies in the modulus, that the indicator takes the values $0$ and $1$, and that $l$ is prime to $N(Q)$. Step 2: $d_0\,(Md)^j$ divides $n_\nu$, by the definition $n_\nu = M^{4fz}(Md)^j$ and $\#n = 2z$. Step 3: $|\bar\pi_M| \leq 1$ at every place (`norm_star_piMBar_le_one`). By the integrality lemma for theta kernels of [data from functions modulo an ideal](/chapter/theta-kernels-gauges/#data-from-functions-modulo-an-ideal) (`smul_mem_raises_of_dvd`), $n_\nu f^{\mathrm{pt}}$ raises gauges by at most $1$ for the kernel at scale $b$. The weight of $U(1)$ is trivial, so the vector $1$ has gauge $1$, and the kernel value at $(g, h)$ applied to it has gauge at most $1$. $\square$

**Theorem (Integrality of the scaled lift).** For $l \nmid N(Q)$ and every embedding $j$, the form $n_\nu\varphi_\vartheta$ is integral at $j$.

Lean: `New.Data.CriticalPair.denomBound_smul_trivialLift_mem_integralForms` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The determinant exponent of the descent pair is $0$. By the finite sum, $n_\nu\varphi_\vartheta(h)$ is a sum of vectors of gauge at most $1$ at $h$. The gauge is ultrametric (`weylGauge_sum_le`). $\square$

**Theorem (Integrality of the algebraic part).** $n_L L^{\mathrm{alg}}(\vartheta)$ is integral away from $N(Q)$.

Lean: `New.Data.CriticalPair.integralAlgebraicPart_mem_integralAway` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* Let $\phi = n_\nu\varphi_\vartheta$. Then $n_L L^{\mathrm{alg}} = \mathrm{chosenGroupOrder}\cdot\langle\phi, \phi\rangle/N(Q)^{\#n-1}$. The inner product is a class sum of Gram pairings weighted by $1/\#\mathrm{Aut}$. The orders of all stabilisers divide `chosenGroupOrder` (`card_classAut_dvd_chosenGroupOrder`). So $\|j(\mathrm{chosenGroupOrder}\cdot\langle\phi, \phi\rangle)\| \leq 1$ when $\phi$ is integral at $j$ and at $j\circ\mathrm{conj}$ (`norm_nsmul_inner_le_one`), which holds by the previous theorem. Since $l \nmid N(Q)$, $\|j(N(Q))\| = 1$. $\square$

**Corollary (No twist).** For every $l$ and every $\iota : \mathbb{C} \cong \overline{\mathbb{Q}}_l$, $|\iota(n_L L^{\mathrm{alg}}(1))| \leq 1$.

Lean: `New.Data.CriticalPair.norm_integralAlgebraicPart_one_le_one` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The trivial character has empty modulus, so $N(Q) = 1$ and every $l$ is allowed. The norm of $\overline{\mathbb{Q}}_l$ is the restriction of the norm of $\mathbb{C}_l$ (`PadicComplex.norm_extends`). $\square$

### One group ring element for all twists

**Definition (Index and points).** `TrivialLiftIndex ϑ` is the product of the classes of $U(1)$ at `D.chosenLevel` and the families of units at the places of $Q$. For an index $a = (c, A)$, $g_a = $ `liftPoint ϑ a` $= c_{\mathrm{out}}\cdot\mathrm{twistResidueLift}(A)$.

Lean: `New.Data.CriticalPair.TrivialLiftIndex` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean), `New.Data.CriticalPair.liftPoint` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

Both depend on the modulus $Q$ only, not on the character $\vartheta$.

**Lemma (Twisting moves to a scalar).** Let $\vartheta'$ have the same modulus as $\vartheta$, and let $\vartheta^0 = $ `ϑ.pow 0`, the trivial character regarded as tame of modulus $Q$. Then

$$\varphi_{\vartheta'}(h) = \sum_a\vartheta'\big(\det(1, g_a)\big)^{-1}\cdot\kappa^{\mathrm{pt}}_{\vartheta^0}(g_a, h).$$

Lean: `New.Data.CriticalPair.trivialLift_apply_eq_sum_smul` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The character of the lift data is $\nu\vartheta'$, and it enters the twisted Weil action as a scalar factor at the point of $U(1)$ (`pairWeil_apply`). The point datum and the points $g_a$ depend on $Q$ only. So the term for $\vartheta'$ is the term for $\vartheta^0$ times $\vartheta'(\det(1, g_a))^{-1}$. $\square$

**Definition (Kernel pairing).** For indices $a$, $b$,

$$\mathrm{kp}(a, b) = \sum_{[k]}\frac{1}{\#\mathrm{Aut}(k)}\,G\big(\kappa^{\mathrm{pt}}_{\vartheta^0}(g_b, k), \kappa^{\mathrm{pt}}_{\vartheta^0}(g_a, k)\big),$$

the class sum over $U(2z)$ at the level of the lift of the Gram pairing $G$ = `gramForm`.

Lean: `New.Data.CriticalPair.kernelPairing` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

**Remark (Formalization).** A single term $k \mapsto \kappa^{\mathrm{pt}}(g_a, k)$ need not be invariant under the level, so the summand of $\mathrm{kp}$ need not be a function on classes. The class sum `classSum` is taken at the fixed representatives `out` of the classes. The sum over $a$ and $b$ is invariant, and only this sum is used.

**Proposition (The norm as a double sum).** If $Q(\vartheta') = Q$, then

$$\|\varphi_{\vartheta'}\|^2 = \sum_a\sum_b\vartheta'\big(\det((1, g_b)/(1, g_a))\big)\cdot\mathrm{kp}(a, b).$$

Lean: `New.Data.CriticalPair.norm_sq_trivialLift_eq_sum` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* The level of the lift data depends on $Q$ only. The squared norm is the class sum of $G(\varphi_{\vartheta'}(k), \varphi_{\vartheta'}(k))$. Insert the previous lemma in both arguments. $G$ is conjugate linear in the first argument, and $\overline{c^{-1}} = c$ for $c$ on the circle. So the coefficient of $\mathrm{kp}(a, b)$ is $\vartheta'(\det(1, g_a))^{-1}\vartheta'(\det(1, g_b))$, which is the value at the quotient. $\square$

**Lemma (Integral pairings).** For $l \nmid N(Q)$ and every embedding $j$, $\mathrm{chosenGroupOrder}\cdot n_\nu^2\cdot\mathrm{kp}(a, b)$ is integral at $j$.

Lean: `New.Data.CriticalPair.mul_kernelPairing_mem_embValRing` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* Move $n_\nu$ into both arguments of $G$. Each scaled kernel value has gauge at most $1$ by the lemma on integral kernel values, applied to $\vartheta^0$. The Gram pairing of two vectors of gauge at most $1$ at the same point is integral (`gramForm_mem_embValRing`). The orders of the stabilisers divide `chosenGroupOrder` (`smul_classSum_mem`). $\square$

**Theorem (The algebraic part is an integral measure).** $\vartheta' \mapsto n_L L^{\mathrm{alg}}(\vartheta')$ is an integral measure at the modulus of $\vartheta$.

Lean: `New.Data.CriticalPair.isIntegralMeasure_integralAlgebraicPart` (New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean).

*Proof.* Take the index set of pairs $(a, b)$, the points $u_{(a,b)} = \det((1, g_b)/(1, g_a))$, and the coefficients

$$c_{(a,b)} = \mathrm{chosenGroupOrder}\cdot n_\nu^2\cdot\mathrm{kp}(a, b)\cdot N(Q)^{-(\#n-1)}.$$

Condition 1: the first factor is integral by the previous lemma, and $N(Q)^{-1}$ is an $l$-adic unit for $l \nmid N(Q)$. Condition 2: for $\vartheta'$ of modulus $Q$, $N(Q(\vartheta')) = N(Q)$. Insert the double sum in the definition of $n_L L^{\mathrm{alg}}$, and distribute the constant factors. $\square$

The points $u$ and the coefficients $c$ do not depend on $\vartheta'$. This is the point of the theorem: the twisted algebraic parts for all characters of modulus $Q$ are the values of one finite combination of characters with integral coefficients. In the model case of [character-lifts](/chapter/character-lifts/#the-lift-of-a-character) with $Q = \varnothing$ the sum has one class and no families, and the theorem says only that $n_L L^{\mathrm{alg}}(1)$ is integral.

**Remark (Formalization).** The representatives $c_{\mathrm{out}}$ of the classes are chosen by `Quotient.out`, and `twistResidueLift` is a chosen lift. The points $u$ and the coefficients $c$ depend on these choices, but the values $F(\vartheta')$ do not. The coefficients are integral only away from $N(Q)$. At primes dividing $N(Q)$ the theorem says nothing.
