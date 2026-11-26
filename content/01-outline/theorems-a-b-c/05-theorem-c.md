---
title: Theorem C, long forms
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Determinant/Twist/FitTwists.lean
decls:
  - New.Data.integral_forms_long
  - New.TwistedLattice.covolume_add_index_nonneg
  - New.Data.IsAuxiliaryForm
  - New.Data.exists_span_isAuxiliaryForm_eq_top
  - New.Data.mul_completion_cost_le
  - New.Data.HasSmallRatios
  - New.Data.IsRegularFamily
  - New.exists_isRegularFamily
  - New.Data.heightLe_liftDeterminant_ratio
  - New.Data.heightLe_chainDeterminant_one_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theorem C, long forms

Theorems A and B give an upper bound for the covolume of many short integral forms. Theorem C gives the lower bound. It says that a family of target forms of small index that spans almost all of the target cannot have a small covolume. The lower bound is about $d_T\,\mathrm{mainAmount}$, the same main term as in Theorem A. The volume of the lattice changes with the twist, and ratios of Hecke $L$-values measure the change.

### The statement of Theorem C

**Theorem (Theorem C, integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2)\,d_T$. Suppose that $y$ has index at most $\delta$ and covolume at most $c$ in the target lattice. Then

$$d_T\bigl(\mathrm{mainAmount} - 3 f a \log^4 b\bigr) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

Here $\mathrm{mainAmount} = m k \cdot \mathrm{directionAmount}$, and the direction amount is the sum over the infinite places $\sigma$ of $s_\infty(\kappa_\sigma) - s_{\mathrm{fin}}(\kappa_\sigma, \sigma)$. The size of a derivative of order $\kappa$ is $s_\infty(\kappa) = \log\kappa! + \kappa\log(M/\Omega)$, and $s_{\mathrm{fin}}$ is the prime sum that measures its divisibility ([the prime sums](/chapter/prime-sums/)). The hypothesis on $n$ comes from Theorem B, and the bounds $c$ and $\delta$ come from Theorem A.

### The lower bound in a twisted lattice

The model case of Section 1 gives $c + 2\delta \geq 0$ for a basis of $\mathbb{Z}^d$. In general the family $y$ is completed to a basis by auxiliary forms $z$. The integrality of $y$ is tested on the lifts $\Theta_\xi y$ for many twists $\xi$, and the lattice has a volume $Z(\xi) = \det(\Theta_\xi^*\Theta_\xi)$ that depends on $\xi$. At each $\iota$ above a prime $\ell$, the proof picks one twist $\xi_\iota$ whose modulus is prime to $\ell$.

**Theorem (A twist for each prime).** Let $L$ be a twisted lattice on $V$ whose maps $\Theta_\xi$ are all injective. Let $y_1, \dots, y_n, z_1, \dots, z_{n'}$ be a basis of $V$, and let $\xi_\iota$ be a twist allowed at the prime of $\iota$, for each $\iota$. Suppose that:

1. $y$ has covolume at most $c$ and index at most $\delta$;
2. $\gamma(\xi) \neq 0$ for every twist $\xi$, and $\gamma(\xi)\,\Theta_\xi z_i$ is integral at $\iota$ whenever $\xi$ is allowed at the prime of $\iota$;
3. every conjugate of $\Theta_1 z_i$ has squared norm at most $e^{b_{\mathrm{short}}}$;
4. the family $|\gamma(\xi_\iota)|^{-2}$ has height at most $b_{\mathrm{denom}}$, and the family $Z(1)/Z(\xi_\iota)$ has height at most $b_{\mathrm{volume}}$.

Then $0 \leq c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}}$.

Lean: `New.TwistedLattice.covolume_add_index_nonneg` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Let $G(\xi)$ be the Gram determinant of the family $\Theta_\xi(y, z)$. Then $G(\xi) = Z(\xi)\cdot G_0$, where $G_0$ is the Gram determinant of $(y, z)$ in $V$. For each $\iota$ write

$$G(1) = |\gamma(\xi_\iota)|^{2n'} G(\xi_\iota)\cdot |\gamma(\xi_\iota)|^{-2n'}\cdot \frac{Z(1)}{Z(\xi_\iota)}.$$

This uses $\gamma(\xi_\iota) \neq 0$ and $Z(\xi_\iota) \neq 0$, which holds as $\Theta_{\xi_\iota}$ is injective. The first factor has height at most $2\delta$: at $\iota$ the matrix of the index carries $y$ to integral forms, $\gamma$ makes $z$ integral, and the Gram matrix uses $\iota$ and its conjugate. The second factor has height at most $n' b_{\mathrm{denom}}$, and the third at most $b_{\mathrm{volume}}$. So the constant family $G(1)$ has height at most $2\delta + n' b_{\mathrm{denom}} + b_{\mathrm{volume}}$. It is not zero, because $(y, z)$ is a basis and $\Theta_1$ is injective. By Hadamard's inequality for the conjugates, $|\sigma G(1)| \leq e^{c + n' b_{\mathrm{short}}}$ for every $\sigma$. The product formula, in the form `New.HeightLe.neg_le_of_norm_map_le`, says that a nonzero number of height at most $h$ whose conjugates are at most $e^{c'}$ has $-h \leq c'$. This is the inequality. $\square$

So Theorem C needs auxiliary forms, twists $\xi_\iota$ with small ratios, and a height bound for $Z(1)/Z(\xi_\iota)$. The injectivity of the lifts is `New.Data.injective_lift_targetLattice`, and the volume of the target lattice at $\vartheta$ is $Z(\vartheta)$ (`New.Data.volume_targetLattice`).

### The three inputs

**Definition (Auxiliary forms).** Let $\gamma(\vartheta) \in \mathbb{C}$ for each $m$-fold twist $\vartheta$. A target form $y$ is *auxiliary for* $\gamma$ if $\gamma(\vartheta)\,\Theta_\vartheta y$ is integral at $\iota$ whenever $\mathrm{Nm}\,Q(\vartheta)$ is prime to the prime of $\iota$, and every conjugate of $\Theta_1 y$ has squared norm at most $\exp(2x_1^2b^2)$.

Lean: `New.Data.IsAuxiliaryForm` (New/Determinant/Twist/LongForms.lean).

**Theorem (Auxiliary forms).** There are an integer $e$ and numbers $\gamma(\vartheta) \neq 0$ with $\gamma(1) = 1$ and

$$|\gamma(\vartheta)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{i, j < m}\mathrm{turnRatio}_{ij}(\vartheta),$$

such that the target is spanned by the forms auxiliary for $\gamma$.

Lean: `New.Data.exists_span_isAuxiliaryForm_eq_top` (New/Determinant/Twist/LongForms.lean).

The turn ratios are products of ratios of Hecke values. Their logarithmic sizes are at most $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$.

**Lemma (The cost of completion).** If $n \geq (1 - 4/b^2)\,d_T$ and $d_T = n + n'$, then $n'(2x_1^2b^2 + b) \leq d_T\, b$.

Lean: `New.Data.mul_completion_cost_le` (New/Determinant/Twist/LongForms.lean).

*Proof.* We have $n' \leq (4/b^2)\,d_T$, so $n'(2x_1^2b^2 + b) \leq d_T\cdot 4(2x_1^2 + b^{-1})$. The sizes of the data give $4(2x_1^2 + b^{-1}) \leq b$. $\square$

The twists come from Volume 12. A family $\theta$ of $m$-fold twists, one for each $\iota$, *has small ratios* if $\mathrm{Nm}\,Q(\theta(\iota))$ is prime to the prime of $\iota$, and if for $1 \leq j \leq m$, each ramified critical pair and each sign $s = \pm 1$, the inverse ratios of Hecke $L$-values at the $j$-th power of $\theta(\iota)$ form a family of height at most $x_1$. It is *regular* if in addition the $j$-th powers have denominators within the budget $\mathrm{denominatorBudget}$, for each $j$.

Lean: `New.Data.HasSmallRatios`, `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean).

**Theorem (Twists with few congruences).** Every admissible data $D$ has a regular family of $m$-fold twists.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

**Theorem (The cost of one lift).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then the family $Z_j(1)/Z_j(\theta(\iota)^j)$, the quotient of the Gram determinants of the $j$-th single lift, has height at most $d_T\, k\,(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$.

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

The budget is chosen so that $k\log b\cdot\mathrm{denominatorBudget} = f a \log^4 b/m$. So the theorem gives the height $d_T(f a\log^4 b/m - k\,\mathrm{directionAmount})$ for each $j$ (`New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div`). The chain determinant factors as the product of the $m$ single lift determinants times the $d_T$-th power of a scalar: a power of $\mathrm{Nm}\,Q$ times quotient ratios of Hecke values (`New.Data.exists_chainDeterminant_one_div_eq`). The inverse scalar has height at most $m^2 t x_1 \leq b$. The $m$ single lifts add up to $d_T(f a\log^4 b - m k\,\mathrm{directionAmount})$, and $m k\,\mathrm{directionAmount} = \mathrm{mainAmount}$.

**Lemma (The inverse ratio).** Let $\theta$ have small ratios, and let each single lift quotient have height at most $d_T(f a\log^4 b/m - k\,\mathrm{directionAmount})$. Then $Z(1)/Z(\theta(\iota))$ has height at most $d_T(b + f a\log^4 b - \mathrm{mainAmount})$.

Lean: `New.Data.heightLe_chainDeterminant_one_div` (New/Determinant/Twist/LongForms.lean).

The sign is the point. The height bound for $Z(1)/Z(\xi_\iota)$ is negative, about $-d_T\,\mathrm{mainAmount}$. In the inequality of a twist for each prime, a negative $b_{\mathrm{volume}}$ forces $c + 2\delta$ to be large.

### The proof of Theorem C

*Proof.* Take $\theta$ with small ratios and the single lift bounds, and take $e$ and $\gamma$ from the theorem on auxiliary forms. The forms auxiliary for $\gamma$ span the target, so $y$ extends by auxiliary forms $z_1, \dots, z_{n'}$ to a basis, with $d_T = n + n'$. Apply the theorem on a twist for each prime with $\xi_\iota = \theta(\iota)$, which is allowed at the prime of $\iota$ by the coprimality.

1. Short: $b_{\mathrm{short}} = 2x_1^2b^2$, by the definition of auxiliary forms.
2. Denominator: $|\gamma(\theta(\iota))|^{-2}$ is the square of the inverse of a power of $\mathrm{Nm}\,Q$ times $m^2$ turn ratios. Its height is at most $2m^2tx_1 \leq b$. So $b_{\mathrm{denom}} = b$.
3. Volume: $b_{\mathrm{volume}} = d_T(b + f a\log^4 b - \mathrm{mainAmount})$, by the lemma on the inverse ratio.

The theorem gives $0 \leq c + 2\delta + n'(2x_1^2b^2 + b) + d_T(b + f a\log^4 b - \mathrm{mainAmount})$. The cost of completion bounds the third term by $d_T b$. As $b \leq f a\log^4 b$, both terms $d_T b$ are at most $d_T f a\log^4 b$. So $d_T(\mathrm{mainAmount} - 3 f a\log^4 b) \leq c + 2\delta$. $\square$

### What Theorem C costs

The error $3 f a\log^4 b$ per dimension has three parts. One is the budget of the denominators, $f a\log^4 b/m$ for each of the $m$ single lifts. One is the term $b$ from the quotient ratios in the chain determinant. One is the term $b$ from the completion by auxiliary forms. In the units of Section 1, $\mathrm{denominatorBudget} = \mathrm{errorUnit}/(mk)$, so each single lift costs $k\log b\cdot\mathrm{denominatorBudget} = \log b\cdot\mathrm{errorUnit}/m$ per dimension.

**Remark (Formalization).** The family $\theta$ is a function on all pairs $\iota$, and the height of a family of complex numbers indexed by $\iota$ is defined with one multiplier $H \neq 0$ for all $\iota$. So the theorem uses a different twist at each prime, but one common bound.

### The plan in Volumes 11 and 12

Volume 11 proves the inputs, and Volume 12 proves the existence of regular families. [Theorem C and the height argument](/chapter/theorem-c-plan/) gives the overview, and [the proof of Theorem C](/chapter/proof-of-theorem-c/) is this section in full. [Twists, critical pairs and regular families](/chapter/twists-critical-pairs/) defines the ratios of Hecke values and states the existence of regular families. [Single theta lifts and their norms](/chapter/single-theta-lifts/) computes the norm of one lift. [The exchange identity, part 1](/chapter/exchange-identity-1/) and [part 2](/chapter/exchange-identity-2/) compare the lifts for two orders of the chain. [Seesaw squares](/chapter/seesaw-squares/) explains why the constant of the seesaw identity may vanish, while the scalars of the squares in a triangle of lifts do not (`New.Exchange.IsTriangle.ne_zero_of_squareCommutes`), and [the chain determinant](/chapter/chain-determinant/) factors $Z(\vartheta)$ into single lifts. [Grids, paths and turns](/chapter/grids-paths-turns/) and [deep level Poincaré series](/chapter/deep-level-poincare/) build the auxiliary forms, and [Hecke values of character lifts](/chapter/hecke-values/) computes the ratios. [The divisibility is sharp](/chapter/sharpness/), [false lifts](/chapter/false-lifts/) and the comparison operator ([part 1](/chapter/comparison-operator-1/), [part 2](/chapter/comparison-operator-2/)) lead to [the height of one lift determinant](/chapter/lift-volume-height/). In Volume 12, [regular families: the plan](/chapter/regular-families-plan/) explains the denominator budget, and [the proof](/chapter/proof-of-regular-families/) constructs the family by Ribet's method and Selmer groups. The hard part is the cost of one lift: the lift at a good twist must be shown to have no unexpected congruences, so that its denominators stay within $f a\log^4 b/m$.
