---
title: The statement of Theorem C
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/IntegralTargetForms.lean
decls:
  - New.Data.integral_forms_long
  - New.TwistedLattice.IndexLe
  - New.TwistedLattice.CovolumeLe
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The statement of Theorem C

This section states Theorem C as the source states it, with every size explicit. It then shows how the four inputs of Section 4 give the theorem, so that the reader sees the arithmetic of the error terms before the inputs.

### The sizes

The data $D$ fix the scales of the argument. They are defined in [the data and its sizes](/chapter/data-and-sizes/). The scales satisfy

$$(\log b)^{100} \leq x, \qquad x^{10^6} \leq x_1, \qquad x_1^{10^6} \leq b.$$

Here $x$ is the length of the prime sum, $x_1$ is a second cut-off, and $b$ is the weight scale. The other sizes are $a = xb$; the number of lifts $m \in [\sqrt{x}, 2\sqrt{x}]$; the rank $r \in [x^5, 3x^5]$ of the hermitian spaces $W_j$; $k = r + 1 - m$; and $t = 5r$. The number of infinite places of the CM field $E$ is $f$. The error unit is $\mathrm{errorUnit} = f a \log^3 b$.

The main term is built from the direction amount

$$\mathrm{directionAmount} = \sum_{\sigma} \bigl(s_\infty(\kappa_\sigma) - s_{\mathrm{fin}}(\kappa_\sigma, \sigma)\bigr),$$

a sum over the infinite places $\sigma$ in the set $\Phi$ of the data. Here $\kappa_\sigma$ is the order of the derivative at $\sigma$, $s_\infty(\kappa) = \log\kappa! + \kappa\log(M/\Omega)$ is its archimedean size (`New.Data.jetSize`), and $s_{\mathrm{fin}}$ is the prime sum that measures its divisibility ([the prime sums](/chapter/prime-sums/)). Then

$$\mathrm{mainAmount} = m\,k\cdot\mathrm{directionAmount}.$$

Let $d = \dim_{\mathbb{C}}$ of the target forms. This is `New.Data.targetDim`.

### Index and covolume

The target forms carry the structure of a twisted lattice ([the integral target forms](/chapter/integral-target-forms/)). For each $m$-fold twist $\vartheta$ there is a lift $\Theta_\vartheta$, the lower chain of $m$ theta lifts at the level of the data, restricted to the target forms. A form $y$ is integral at $\iota$ if $\Theta_\vartheta y$ has integral values at $\iota$ for every twist $\vartheta$ whose modulus has norm prime to the prime of $\iota$. Two numbers measure a finite family $y = (y_k)_{k \in S}$ of target forms.

**Definition (Index at most δ).** The family $y$ has *index at most $\delta$* if there are real numbers $\delta_\ell \geq 0$, one for each $\ell \in \mathbb{N}$, with $\sum_{\ell \in U}\delta_\ell\log\ell \leq \delta$ for every finite set $U$ of primes, such that for every $\iota$ some square matrix $u$ over the valuation ring $\mathcal{O}_\iota$, indexed by $S$, carries $y$ into the vectors integral at $\iota$ with loss $\delta_\ell$, where $\ell$ is the prime of $\iota$. The matrix does not depend on the twist.

Lean: `New.TwistedLattice.IndexLe` (New/Reduction/Lattices/TwistedLattice.lean).

To carry $y$ with loss $a$ means: $\|\iota\det u\| \geq \ell^{-a}$, and $\sum_k u_{ik}y_k$ is integral at $\iota$ for each $i$. So $\delta$ is the logarithm of a common denominator of the family, summed over the primes.

**Definition (Covolume at most c).** The family $y$ has *covolume at most $c$* if for every automorphism $\sigma$ of $\mathbb{C}$ the Gram determinant of the conjugate coordinate vectors $\sigma\Theta_1 y_k$, taken with the rational Gram matrix of the lattice, has absolute value at most $e^c$.

Lean: `New.TwistedLattice.CovolumeLe` (New/Reduction/Lattices/TwistedLattice.lean).

The covolume uses only the untwisted lift $\Theta_1$. The twists enter only through the integrality, and so only through the index.

### The theorem

**Theorem (Theorem C, integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with

$$\Bigl(1 - \frac{4}{b^2}\Bigr) d \leq n.$$

Suppose that $y$ has index at most $\delta$ and covolume at most $c$ in the target lattice. Then

$$d\bigl(\mathrm{mainAmount} - 3 f a \log^4 b\bigr) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

The hypotheses are exactly four: linear independence, the lower bound for $n$, the index bound and the covolume bound. The family need not be integral. Its failure to be integral is the index $\delta$. The hypothesis on $n$ is the conclusion of Theorem B, and the bounds $c$ and $\delta$ come from Theorem A.

The error is $3 f a\log^4 b = 3\log b\cdot\mathrm{errorUnit}$ per dimension. The main term is much larger.

### The proof from the inputs

The proof is short once the inputs are known. Each step names the input of Section 4 that it uses.

*Proof.* Step 1: twists. Take a family $\theta$ of $m$-fold twists with small ratios such that, for each $1 \leq j \leq m$, the family $Z_j(1)/Z_j(\theta(\iota))$ has height at most $d\,(f a\log^4 b/m - k\cdot\mathrm{directionAmount})$. Such a family exists by `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div`. That lemma takes the regular family of [the existence theorem](/decl/New.exists_isRegularFamily/) and applies [the height of one lift](/decl/New.Data.heightLe_liftDeterminant_ratio/). It uses the identity $k\log b\cdot\mathrm{denominatorBudget} = f a\log^4 b/m$, which holds as $\mathrm{denominatorBudget} = f a\log^3 b/(mk)$.

Step 2: auxiliary forms. Take $e$ and $\gamma$ from [the theorem on auxiliary forms](/decl/New.Data.exists_span_isAuxiliaryForm_eq_top/). The auxiliary forms span the target, so $y$ extends by auxiliary forms $z_1, \dots, z_{n'}$ to a basis, with $n + n' = d$.

Step 3: the three bounds.

1. Each $z_i$ has $\|\Theta_1 z_i\|_\sigma^2 \leq \exp(2x_1^2b^2)$ for every $\sigma$. So $b_{\mathrm{short}} = 2x_1^2b^2$.
2. The family $|\gamma(\theta(\iota))|^{-2}$ is the square of the inverse of $\mathrm{Nm}\,Q^{e/2}$ times $m^2$ turn ratios. The family of the inverse has height at most $m\cdot m\cdot(t x_1)$, by `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio`. The square has height at most $2m^2tx_1$, and $2m^2tx_1 \leq b$ by the sizes. So $b_{\mathrm{denom}} = b$.
3. The volume of the target lattice at $\vartheta$ is $Z(\vartheta)$ (`New.Data.volume_targetLattice`). [The inverse ratio lemma](/decl/New.Data.heightLe_chainDeterminant_one_div/) gives the height $d\,(b + f a\log^4 b - \mathrm{mainAmount})$ for $Z(1)/Z(\theta(\iota))$. So $b_{\mathrm{volume}} = d\,(b + f a\log^4 b - \mathrm{mainAmount})$.

Step 4: the frame. The lifts $\Theta_\vartheta$ of the target lattice are injective (`New.Data.injective_lift_targetLattice`). The modulus of $\theta(\iota)$ has norm prime to the prime of $\iota$. So [the theorem on a twist for each prime](/decl/New.TwistedLattice.covolume_add_index_nonneg/) applies and gives

$$0 \leq c + 2\delta + n'(2x_1^2b^2 + b) + d\,(b + f a\log^4 b - \mathrm{mainAmount}).$$

Step 5: the cost of completion. By [the lemma on the cost of completion](/decl/New.Data.mul_completion_cost_le/), $n'(2x_1^2b^2 + b) \leq d\,b$. The sizes give $b \leq f a\log^4 b$, so both terms $d\,b$ are at most $d f a\log^4 b$. The inequality becomes $0 \leq c + 2\delta + 3d f a\log^4 b - d\cdot\mathrm{mainAmount}$. This is the claim. $\square$

### The three errors

The error $3 f a\log^4 b$ per dimension has three parts, one for each term above.

| Part | Source of the error | Size per dimension |
|---|---|---|
| Denominators | $m$ single lifts, each with budget $f a\log^4 b/m$ | $f a\log^4 b$ |
| Quotient ratios | the scalar of the chain factorization | $b$ |
| Completion | $n' \leq 4d/b^2$ auxiliary forms, each with two costs: squared length $b_{\mathrm{short}} = 2x_1^2b^2$ in logarithm, and denominators $b_{\mathrm{denom}} = b$ | $b$ |

The completion is cheap although an auxiliary form is very long: there are few of them. The completion costs $n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) = n'(2x_1^2b^2 + b)$. The factor $b^2$ in their squared length cancels the factor $4/b^2$ in their number, and the constant $4(2x_1^2 + b^{-1})$ is at most $b$ by the sizes.

**Remark (Formalization).** The family $\theta$ is a function on all pairs $\iota$, and $\theta$ is produced by `choose` in the proof of the existence of regular families (Section 4). So the twist at a prime is not given by a formula. The theorem does not need one. The height of a family uses one multiplier for all $\iota$, so the bounds at the different primes are added in one sum, whatever the twists are.
