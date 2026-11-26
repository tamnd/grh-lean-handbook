---
title: The size of the untwisted operator
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.card_prod_mul_card_tightFrameIndex_mul_sq_le
  - New.Data.normSqAt_comparisonOp_le
  - New.Data.isComparisonOperator_comparisonOp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The size of the untwisted operator

This section proves property 5 of a comparison operator for $U_1$: it multiplies the squared norm at every $\sigma \in \mathrm{Aut}(\mathbb{C})$ by at most $\exp(6A)$, with $A = f m b\log^2 b$. Then it collects the five properties into the theorem that $U_\vartheta$ is a comparison operator.

The bound is not a bound for an operator norm at $\sigma = 1$ alone. The operator $U_1$ is defined by an adjoint, and an automorphism $\sigma$ of $\mathbb{C}$ does not commute with adjoints. So the proof uses the rank one decomposition of Section 4, in which $U_1\varphi$ is a sum of explicit forms with coefficients that are inner products. Each coefficient is bounded at $\sigma$ by a Cauchy-Schwarz inequality for conjugate pairings.

### Inputs for the size bound

Let $N$ be the number of pairs $b = (i, c)$ of a choice and a class of $V^\circ$, and $F$ the number of fillings of $\mu^-$ with increasing columns. So the frame index set has $N F$ elements. Let $n_{\mathrm{Aut}} \geq 1$ be the chosen group order and $h_j \geq 1$ the hook number of $\mu^-$. We use the following results of [the comparison operator, part 2](/chapter/comparison-operator-2/), of Volume 4 and of Volume 5, one line each.

- *Classes and denominators.* $(M^{l_1})^2\cdot e^b\,\big(N\,e^b\,n_{\mathrm{Aut}}\big)^2 \leq e^A$, where $M \geq 1$ is the modulus of the level and $l_1$ the denominator exponent of the splitting of $V_j$ at the trivial twist (`New.Rows.M_pow_denominatorExponent_sq_mul_le_exp`).
- *Fillings.* $F \leq \exp(x^{999})$ (`New.Rows.card_columnFilling_colsMinus_le`).
- *Hook number.* $h_j \leq \exp(x^{999})$ (`New.Rows.hookNumberMinus_le`).
- *Gluing at the trivial twist.* For every tuple $\zeta$ and every $\sigma$, $\|\mathrm{glue}_1\zeta\|_\sigma^2 \leq e^{2A}\,\|\zeta\|_\sigma^2$ (`New.Rows.normSqAt_glue_le`).
- *Cauchy-Schwarz for conjugates.* For forms $\varphi'$, $\varphi$ of one level and $\sigma \in \mathrm{Aut}(\mathbb{C})$, $|\sigma\langle\varphi', \varphi\rangle| \leq \|\varphi\|_\sigma\,\|\varphi'\|_{\sigma'}$ with $\sigma' = \mathrm{conj}\circ\sigma\circ\mathrm{conj}$ (`New.LevelPlaces.LevelForm.norm_map_inner_le`, [PAdicGauge.lean](lean:Lib/Adelic/AutomorphicForms/PAdicGauge.lean#L673)).
- *Triangle inequality.* For vectors $\xi_a$ of the Weyl module, $\|\sigma(\sum_a\xi_a)\| \leq \sum_a\|\sigma(\xi_a)\|$ for the Gram norm (`New.sqrt_weylNormSq_sum_le`, [MatrixNormBounds.lean](lean:Lib/General/LinearAlgebra/MatrixNormBounds.lean#L155)).

### Counting the frame

**Lemma (The size of the frame).** With $N$, $F$, $n_{\mathrm{Aut}}$ and $h_j$ as above,

$$N\cdot\big(N F\cdot n_{\mathrm{Aut}}\,h_j^2\big)^2 \leq \exp(2A).$$

Lean: `New.Data.card_prod_mul_card_tightFrameIndex_mul_sq_le` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The input on classes has extra factors $(M^{l_1})^2$, $e^b$ and $e^b$, each at least $1$. Replace each by $1$. This gives $(N n_{\mathrm{Aut}})^2 \leq e^A$, so $N n_{\mathrm{Aut}} \leq e^{A/2}$, as both sides are positive. Since $n_{\mathrm{Aut}} \geq 1$, also $N \leq e^{A/2}$. Now rearrange:

$$N\cdot(N F n_{\mathrm{Aut}}h_j^2)^2 = N\cdot(N n_{\mathrm{Aut}})^2\cdot(F h_j^2)^2 \leq e^{A/2}\cdot e^A\cdot\big(e^{x^{999}}\,e^{2x^{999}}\big)^2 = \exp\big(\tfrac32 A + 6x^{999}\big).$$

The size inequality $6x^{999} \leq A/2$ holds, since $A \geq b$ and $b \geq x_1^{10^6} \geq x^{10^{12}}$ ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)). The source proves it by `D.le_of_hasLogBound`, the comparison of logarithmic bounds of the data. So the right side is at most $\exp(2A)$. $\square$

### The bound for the untwisted operator

**Theorem (The untwisted operator is short).** For every form $\varphi \in \mathcal{F}_1$ and every $\sigma \in \mathrm{Aut}(\mathbb{C})$,

$$\|U_1\varphi\|_\sigma^2 \leq \exp(3A)^2\,\|\varphi\|_\sigma^2 .$$

Lean: `New.Data.normSqAt_comparisonOp_le` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Take the tight frame $(f_a)$ of tuples of Section 4 for $\delta = 1$. We use only its claims 1 and 3: $\sum_a\langle f_a, \zeta\rangle f_a = h_j^2\zeta$, and $\|f_a\|_\tau^2 \leq h_j^2$ for every $a$ and every $\tau \in \mathrm{Aut}(\mathbb{C})$. Write $n = n_{\mathrm{Aut}}$, $h = h_j$, and

$$c_a = n\,\langle\mathrm{glue}_1 f_a, \varphi\rangle, \qquad S = e^{2A}\,\|\varphi\|_\sigma^2 \geq 0 .$$

*Step 1: the coefficients.* By Cauchy-Schwarz for conjugates, then the gluing bound at $\sigma'$, then claim 3 at $\sigma'$,

$$|\sigma(c_a)| = n\,|\sigma\langle\mathrm{glue}_1 f_a, \varphi\rangle| \leq n\,\|\varphi\|_\sigma\,\|\mathrm{glue}_1 f_a\|_{\sigma'} \leq n\,\|\varphi\|_\sigma\sqrt{e^{2A}h^2} = n\,h\sqrt S .$$

This is where the frame must be short at every automorphism, not only at $1$: the pairing moves $\sigma$ to $\sigma'$.

*Step 2: one value of the sum.* Let $\zeta = \sum_a c_a f_a$, and fix a pair $b$. The value $\zeta_b$ is $\sum_a c_a\,(f_a)_b$. For one term, $\|\sigma(c_a (f_a)_b)\| = |\sigma(c_a)|\,\|\sigma((f_a)_b)\|$. The Gram norm of one value is at most the norm of the whole tuple, so $\|\sigma((f_a)_b)\| \leq \|f_a\|_\sigma \leq h$. So each term has Gram norm at most $n h^2\sqrt S$ after $\sigma$. By the triangle inequality, with $NF$ terms,

$$\|\sigma(\zeta_b)\| \leq N F\,n h^2\sqrt S .$$

*Step 3: the whole tuple.* Square and add over the $N$ pairs $b$:

$$\|\zeta\|_\sigma^2 = \sum_b\|\sigma(\zeta_b)\|^2 \leq N\,(N F\,n h^2)^2\,S .$$

*Step 4: back to forms.* By the rank one decomposition of Section 4 and the linearity of $\mathrm{glue}_1$, $U_1\varphi = \sum_a c_a\,\mathrm{glue}_1 f_a = \mathrm{glue}_1\zeta$. The gluing bound at $\sigma$, step 3 and the lemma on the size of the frame give

$$\|U_1\varphi\|_\sigma^2 \leq e^{2A}\,\|\zeta\|_\sigma^2 \leq e^{2A}\cdot e^{2A}\cdot S = e^{6A}\,\|\varphi\|_\sigma^2 = \exp(3A)^2\,\|\varphi\|_\sigma^2 . \qquad\square$$

The three factors $e^{2A}$ have three sources: the gluing map in the coefficient, the size of the frame, and the gluing map in the sum. The bound $\exp(3A)^2$ in property 5 is exactly their product.

### The theorem

**Theorem (The operator of the source is a comparison operator).** For every $1 \leq j \leq m$ the family $U_\vartheta = n_{\mathrm{Aut}}h_j^2\,\mathrm{glue}_\vartheta\mathrm{glue}_\vartheta^*$ is a comparison operator for $j$.

Lean: `New.Data.isComparisonOperator_comparisonOp` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* We check the five properties of Section 3.

*Property 1.* By the lemma on the ratio, $\rho_j(\vartheta) = |c'_1|^2/|c'_\vartheta|^2$. Both twist factors are nonzero, so the quotient is nonzero.

*Property 2.* Let

$$s = \frac{n_{\mathrm{Aut}}\,h_j^2}{|c'_1|^2}, \qquad U^\circ = s\,(\Theta^\circ)^*\Theta^\circ .$$

The number $s$ is real and positive: $n_{\mathrm{Aut}} \geq 1$, $h_j > 0$ and $c'_1 \neq 0$. For a good form $y \neq 0$, $\langle y, U^\circ y\rangle = s\,\|\Theta^\circ y\|^2$, and $\Theta^\circ y \neq 0$ because $\Theta^\circ$ is injective. So $\langle y, U^\circ y\rangle > 0$. For a twist $\vartheta$ and good forms $y'$, $y$, the lemma on inner products of Section 3 gives

$$\langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle = \frac{n_{\mathrm{Aut}}h_j^2}{|c'_\vartheta|^2}\langle\Theta^\circ y', \Theta^\circ y\rangle = \frac{|c'_1|^2}{|c'_\vartheta|^2}\cdot s\,\langle y', (\Theta^\circ)^*\Theta^\circ y\rangle = \rho_j(\vartheta)\,\langle y', U^\circ y\rangle .$$

*Property 3.* This is the lemma on orthogonality to the false lifts of Section 3.

*Property 4.* This is the integrality lemma of Section 4.

*Property 5.* This is the theorem above. $\square$

**Remark (Formalization).** Property 1 is the field that answers F-072 of [the register of findings](/chapter/register-of-findings/). It is proved here from $c'_\vartheta \neq 0$, and that fact rests on the injectivity of $\Theta^\circ$ and the existence of a nonzero good form (`New.Rows.twistFactor_ne_zero`). The operator $U^\circ$ is not unique. The proof takes the one positive multiple of $(\Theta^\circ)^*\Theta^\circ$ that makes the identity of property 2 hold.

### What the theorem gives

In the model case of Section 1 the positive number $\langle\Theta_\vartheta y, U_\vartheta\Theta_\vartheta y\rangle$ was $\rho\,u_0$. The theorem says the same in rank $d$, with $U^\circ$ in place of $u_0$. The ratio $\rho_j(\vartheta)$ is a quotient of Hecke values, and [Hecke values of character lifts](/chapter/hecke-values/) bounds the height of its inverse. The operator $U^\circ$ does not depend on $\vartheta$, so it cancels in the quotient $Z_j(1)/Z_j(\xi)$ (Section 7).
