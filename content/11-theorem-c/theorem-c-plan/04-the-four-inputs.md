---
title: The four inputs
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/Congruences/FitTwistsExist.lean
  - New/Determinant/Chain/NormOfChain.lean
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.IsAuxiliaryForm
  - New.Data.exists_span_isAuxiliaryForm_eq_top
  - New.Data.CriticalPair.ratio
  - New.Data.HasSmallRatios
  - New.Data.ClearsProjection
  - New.Data.HasDenominatorsLe
  - New.Data.IsDenominatorBound
  - New.Data.IsRegularFamily
  - New.exists_isRegularFamily
  - New.Data.exists_chainDeterminant_one_div_eq
  - New.Data.IsComparisonOperator
  - New.Data.isComparisonOperator_comparisonOp
  - New.Data.heightLe_liftDeterminant_ratio
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The four inputs

This section states the four inputs of Theorem C in full, with links to the chapters that prove them. The order follows the proof in Section 3.

### Input 1: auxiliary forms

For each $m$-fold twist $\vartheta$, let $\mathrm{Nm}\,Q(\vartheta)$ be the product of the norms of the places in the set $Q$ of $\vartheta$, and let $\Theta_\vartheta$ be the lift of the target lattice.

**Definition (Auxiliary forms).** Let $\gamma(\vartheta) \in \mathbb{C}$ for each $m$-fold twist $\vartheta$. A target form $y$ is *auxiliary for $\gamma$* if two conditions hold. First, $\gamma(\vartheta)\,\Theta_\vartheta y$ is integral at $\iota$ for every $\iota$ and every $\vartheta$ such that the prime of $\iota$ is prime to $\mathrm{Nm}\,Q(\vartheta)$. Second, $\|\Theta_1 y\|_\sigma^2 \leq \exp(2x_1^2b^2)$ for every automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Data.IsAuxiliaryForm` (New/Determinant/Twist/LongForms.lean).

**Theorem (Auxiliary forms).** There are an integer $e$ and numbers $\gamma(\vartheta) \in \mathbb{C}$, one for each $m$-fold twist $\vartheta$, such that $\gamma(\vartheta) \neq 0$ for every $\vartheta$, $\gamma(1) = 1$,

$$|\gamma(\vartheta)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{i=0}^{m-1}\prod_{j=0}^{m-1}\mathrm{turnRatio}_{ij}(\vartheta)$$

for every $\vartheta$, and the forms auxiliary for $\gamma$ span the target forms.

Lean: `New.Data.exists_span_isAuxiliaryForm_eq_top` (New/Determinant/Twist/LongForms.lean).

The turn ratio $\mathrm{turnRatio}_{ij}(\vartheta)$ is the product over $1 \leq s \leq t$ of ratios of Hecke values of the character $\chi_{i+1}\chi_{j+1}$ at the twist $\vartheta^{j+1}$, where $\chi_i$ is the character of the $i$-th lift at the trivial twist. The proof projects spanning forms of deep level with short lifts to the target. The chapters [grids, columns and turns](/chapter/grids-paths-turns/) and [deep level Poincaré series and spanning forms](/chapter/deep-level-poincare/) give the proof.

### Input 2: regular twists

The twists are tested by ratios of $L$-values. A critical pair $p = (\nu, z)$ is a Hecke character $\nu$ of $U(1)$ with a point $z$. Let $S$ be the set of chosen places of the data.

**Definition (The ratio of a pair).** For a critical pair $p = (\nu, z)$, a tame character $\vartheta$ and a sign $s = \pm 1$,

$$p.\mathrm{ratio}(\vartheta, s) = \frac{|L^{S \cup Q(\vartheta)}(z, (\nu\vartheta^s)^{-1})|}{|L^{S}(z, \nu^{-1})|} \in \mathbb{C},$$

where $L^T$ omits the Euler factors at the places of $T$ and at their conjugates. The default sign is $s = 1$.

Lean: `New.Data.CriticalPair.ratio` (New/Determinant/Twist/FitTwists.lean).

The definition is a quotient in $\mathbb{C}$, and in Lean $x/0 = 0$. Section 5 explains why the denominator is not $0$.

**Definition (Small ratios).** A family $\theta$ of $m$-fold twists, one for each $\iota$, *has small ratios* if two conditions hold. First, the prime of $\iota$ is prime to $\mathrm{Nm}\,Q(\theta(\iota))$, for every $\iota$. Second, for every $1 \leq j \leq m$, every critical pair $p$ that is ramified (its tame part is nontrivial exactly at the chosen places), and every sign $s$, the family $\iota \mapsto p.\mathrm{ratio}(\theta(\iota)^j, s)^{-1}$ has height at most $x_1$.

Lean: `New.Data.HasSmallRatios` (New/Determinant/Twist/FitTwists.lean).

The denominators are measured by two conditions at one $\iota$ above $\ell$, for a twist $\vartheta$, an index $j$ and a bound $\beta$. Let $Z$ be the space of lifts of good forms from $W_j$ at $\vartheta$, the range of the good lift $\Theta_{j,\vartheta}$, and let $\mathrm{pr}$ be the orthogonal projection onto $Z$.

**Definition (Clearing the projection).** The projection is *cleared with loss $\beta$ at $\iota$* if there is an operator $\Lambda$ on $Z$ with $\exp(-(\dim Z)\,r\beta) \leq \|\iota\det\Lambda\|$ such that $\Lambda(\mathrm{pr}\,y)$ is integral at $\iota$ for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts.

Lean: `New.Data.ClearsProjection` (New/Determinant/Twist/FitTwists.lean).

**Definition (Denominators at most β).** The twist $\vartheta$ *has denominators at most $\beta$* at $\iota$ for the index $j$ if the projection is cleared with loss $\beta$ at $\iota$, and if for every main pair $p$ for $j$ and all test forms $\Xi$, $\Xi'$ on the definite space of the pair, the inner product of the projections of $\Xi$ and $\Xi'$ to the line of the lift of $\nu\vartheta$ has $\|\iota(\cdot)\| \leq e^\beta$.

Lean: `New.Data.HasDenominatorsLe` (New/Determinant/Twist/FitTwists.lean).

**Definition (A denominator bound).** Let $\theta$ be a family of $m$-fold twists, $1 \leq j \leq m$, and $\gamma(\ell) \in \mathbb{R}$ for each $\ell \in \mathbb{N}$. Then $\gamma$ is a *denominator bound* for $\theta$ and $j$ if $\sum_{\ell \in T}\gamma(\ell) \leq \mathrm{denominatorBudget}$ for every finite set $T$ of primes, and if $\theta(\iota)^j$ has denominators at most $\gamma(\ell)$ at $\iota$ for the index $j$, for every $\iota$, where $\ell$ is the prime of $\iota$.

Lean: `New.Data.IsDenominatorBound` (New/Determinant/Twist/FitTwists.lean).

**Definition (Regular family).** A family $\theta$ of $m$-fold twists is *regular* if it has small ratios and, for every $1 \leq j \leq m$, some $\gamma$ is a denominator bound for $\theta$ and $j$.

Lean: `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean).

Here $\mathrm{denominatorBudget} = \mathrm{errorUnit}/(mk) = f a\log^3 b/(mk)$. Now the existence theorem can be stated in full.

**Theorem (Twists with few congruences).** Let $D$ be data. There is a family $\theta$ of $m$-fold twists, one for each $\iota$, such that:

1. for every $\iota$, the prime $\ell$ of $\iota$ is prime to $\mathrm{Nm}\,Q(\theta(\iota))$;
2. for every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s$, the family $\iota \mapsto p.\mathrm{ratio}(\theta(\iota)^j, s)^{-1}$ has height at most $x_1$;
3. for every $1 \leq j \leq m$ there are real numbers $\gamma(\ell)$ with $\sum_{\ell \in T}\gamma(\ell) \leq f a\log^3 b/(mk)$ for every finite set $T$ of primes, such that for every $\iota$ above $\ell$ the twist $\theta(\iota)^j$ has denominators at most $\gamma(\ell)$ at $\iota$ for the index $j$.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

*Proof.* The theorem is the subject of Volume 12; see [regular families: the plan](/chapter/regular-families-plan/) and [the proof of the existence of regular families](/chapter/proof-of-regular-families/). The last step is this. For each $\iota$ above $\ell$, `New.Selmer.exists_mFoldTwist_hasDenominatorsLe` gives a twist $\tau$ with $\ell$ prime to $\mathrm{Nm}\,Q(\tau)$, with $\|\iota(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e_\ell\log\ell)$ for the ramified pairs, where $e_\ell = (4f + 3)\,r\,v_\ell(n_{\mathrm{Aut}}) + 2^{-\ell}$ and $n_{\mathrm{Aut}}$ is the chosen group order, and with denominators at most $\beta_\ell$ for every $j$, where $e^{\beta_\ell}$ is $\ell$ to the power of a clearing bound, times the $\ell$-part of the number of classes of $U(1)$ at the chosen level. The proof takes $\theta(\iota) = \tau$ by `choose`. The sum $\sum_\ell e_\ell\log\ell$ is at most $x_1$, and the sum of the $\beta_\ell$ is within the budget. $\square$

### Input 3: the chain determinant factorization

Let $Z(\vartheta) = \det(\Theta_\vartheta^*\Theta_\vartheta)$ be the chain determinant, and let $Z_j(\vartheta)$ be the Gram determinant of the $j$-th single good lift at the twist $\vartheta^j$. Both are positive real numbers (`New.Data.chainDeterminant_pos`, `New.Data.liftDeterminant_pos`).

**Theorem (The chain determinant factors).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$

$$\frac{Z(1)}{Z(\vartheta)} = \Bigl(\mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{0 < i < j \leq m}\mathrm{quotientRatio}_{ij}(\vartheta)\Bigr)^{-d}\prod_{j=1}^m\frac{Z_j(1)}{Z_j(\vartheta)}.$$

Lean: `New.Data.exists_chainDeterminant_one_div_eq` (New/Determinant/Twist/LongForms.lean).

The quotient ratio $\mathrm{quotientRatio}_{ij}(\vartheta)$ is the product of $t$ ratios of Hecke $L$-values of the character $\chi_j/\chi_i$ at the twist $\vartheta^{j-i}$. The proof rests on an operator identity: on the target forms $\Theta_\vartheta^*\Theta_\vartheta$ is a scalar times the product of the $m$ series of Rallis' inner product formula. The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) proves it. The scalar has height at most $m^2tx_1$ for a family with small ratios, which is at most $b$.

### Input 4: the height of one lift

For the single lifts the source introduces an operator that compares the lift at $\vartheta$ with the lift at $1$. Let $\Theta_{j,\vartheta}$ be the good lift from $W_j$ at $\vartheta$, and let $\rho_j(\vartheta)$ be the ratio of the products of Hecke values of three pairs, at $\vartheta$ and at $1$.

**Definition (Comparison operator).** Let $1 \leq j \leq m$. A family of operators $U_\vartheta$ on the forms on $V_j$, one for each twist $\vartheta$, is a *comparison operator* if it has these five properties.

1. The ratio $\rho_j(\vartheta)$ is not $0$, for every $\vartheta$.
2. There is an operator $U^\circ$ on the good forms on $W_j$ with $\langle y, U^\circ y\rangle > 0$ for $y \neq 0$, such that $\langle\Theta_{j,\vartheta}y', U_\vartheta\Theta_{j,\vartheta}y\rangle = \rho_j(\vartheta)\,\langle y', U^\circ y\rangle$ for all $\vartheta$ and all good forms $y'$, $y$.
3. For every $\vartheta$ and every $z$ in the range of $\Theta_{j,\vartheta}$, the form $U_\vartheta z$ is orthogonal to the false lifts.
4. For every $\vartheta$, every prime $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$ and every place $\iota$ above $\ell$, $U_\vartheta$ maps forms integral at $\iota$ to forms integral at $\iota$.
5. For every form $\varphi$ and every $\sigma$, $\|U_1\varphi\|_\sigma^2 \leq \exp(3 f m b\log^2 b)^2\,\|\varphi\|_\sigma^2$.

Lean: `New.Data.IsComparisonOperator` (New/OneLift/LiftVolumeHeight.lean).

**Theorem (A comparison operator exists).** For every $1 \leq j \leq m$ the operators $U_\vartheta = n_{\mathrm{Aut}}\,h_j^2\;\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*$ form a comparison operator. Here $\mathrm{glue}_\vartheta$ builds a form on $V_j$ from a tuple of forms on a smaller space $V^\circ$, $h_j$ is a hook number, and $n_{\mathrm{Aut}}$ is the chosen group order.

Lean: `New.Data.isComparisonOperator_comparisonOp` (New/OneLift/LiftVolumeHeight.lean).

The proof is the content of [false lifts](/chapter/false-lifts/) and of the two chapters on the comparison operator ([part 1](/chapter/comparison-operator-1/), [part 2](/chapter/comparison-operator-2/)).

**Theorem (The height of one lift determinant).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most

$$d\,k\,\bigl(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}\bigr).$$

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Let $\Delta(\vartheta)$ be the determinant of the compression of $U_\vartheta$ to the range of $\Theta_{j,\vartheta}$. Property 2 gives a constant $C \neq 0$ with $Z_j(\vartheta)\,\Delta(\vartheta) = C\rho_j(\vartheta)^d$. As $\rho_j \neq 0$ by property 1, $\Delta(\vartheta) \neq 0$. So

$$\frac{Z_j(1)}{Z_j(\vartheta)} = \frac{\Delta(\vartheta)}{\Delta(1)}\,\rho_j(\vartheta)^{-d}.$$

Property 5 bounds the conjugates of $\Delta(1)$ by $\exp(3 d f m b\log^2 b)$. Properties 3 and 4, with the clearing of the projection from the regular family, bound $\Delta(\theta(\iota)^j)$ at $\iota$ by $\exp(d\,r\gamma(\ell))$. So $\Delta(\theta(\iota)^j)/\Delta(1)$ has height at most $3dfmb\log^2 b + d\,r\cdot\mathrm{denominatorBudget}$. The inverse ratio $\rho_j^{-1}$ has height at most $10 m x_1 + k(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$, by the chapter [Hecke values of character lifts](/chapter/hecke-values/). Add $d$ times this, and use the sizes to bound the sum by $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$. $\square$

The main term $-k\cdot\mathrm{directionAmount}$ comes from the Hecke values: their ratio is large and has no denominator. The rest is error. The chapter [the height of one lift determinant](/chapter/lift-volume-height/) gives the proof in full.
