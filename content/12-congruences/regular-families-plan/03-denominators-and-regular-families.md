---
title: Denominators and regular families
lean:
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/TestedForms.lean
  - New/Congruences/FitTwistsExist.lean
  - New/OneLift/LiftVolumeHeight.lean
  - New/Determinant/Twist/LongForms.lean
decls:
  - New.Data.goodLift
  - New.Selmer.DenominatorLe
  - New.Data.ClearsProjection
  - New.Selmer.DenominatorLe.clearsProjection
  - New.Data.HasDenominatorsLe
  - New.Data.denominatorBudget
  - New.Data.IsDenominatorBound
  - New.Data.IsNegligible
  - New.Data.HasSmallRatios
  - New.Data.IsRegularFamily
  - New.exists_isRegularFamily
  - New.Data.heightLe_liftDeterminant_ratio
  - New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Denominators and regular families

This section defines the denominator of a projection to a space of lifts, the budget, and regular families. Then it states the theorem of the volume and the two results of Volume 11 that use it.

### Lifts and integral forms

Fix the data $D$, an index $1 \leq j \leq m$ and a twist $\vartheta$. The lift datum `D.descentPair` $\vartheta$ $j$ describes a theta lift from the hermitian space $W_j$ of rank $r$ to a definite space $V$ of rank $r + t$ ([single theta lifts](/chapter/single-theta-lifts/)). The *good forms* on $W_j$ are the forms fixed by the principal congruence subgroup at the chosen places that lie in the image of an idempotent $e_0$ of the group algebra of $\prod_{w} \mathrm{GL}_r(k_w)$, the product over the chosen places $w$.

**Definition (The lift of good forms).** The map $\mathrm{goodLift}(\vartheta, j)$ is the theta lift $\mathrm{singleLift}(\vartheta, j)$, restricted to the good forms on $W_j$. Its range $Z = Z(\vartheta, j)$ is a finite dimensional subspace of the forms on $V$.

Lean: `New.Data.goodLift` (New/Determinant/Twist/FitTwists.lean).

A form on $V$ is a function on a finite set of classes, so it is a vector in a finite dimensional hermitian space. A form is *integral at* $\iota$ if all its values lie in the closed unit ball of $\mathbb{C}_\ell$ after the map $\iota$. Let $\mathrm{pr}_Z$ be the orthogonal projection to $Z$. Only some integral forms are tested. A form $y$ is *orthogonal to the false lifts* if it is orthogonal to the forms in $Z^{\perp}$ that lie in the image of $e_0$ and are killed by the Hecke polynomial at its test value at some split place off the level. Volume 11 treats these forms in [false lifts](/chapter/false-lifts/).

### Denominators of projections

The source uses two forms of the same notion. The first is the general one, for any descent pair $O$ and any subspace $Z$.

**Definition (Denominators of a projection).** Let $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$, let $O$ be a descent pair whose source has the index type $r$, let $e_0$ be an element of the group algebra, $Z$ a subspace of the forms, and $\beta$ real. The projection to $Z$ *has denominator at most* $\exp \beta$ per dimension and per row if there is a linear map $\Lambda : Z \to Z$ such that:

1. $\|\iota(\det \Lambda)\| \geq \exp(-\dim Z \cdot \#r \cdot \beta)$;
2. for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts, the form $\Lambda(\mathrm{pr}_Z\, y)$ is integral at $\iota$, and $\|\iota\langle y', \Lambda(\mathrm{pr}_Z\, y)\rangle\| \leq 1$ for every form $y'$ that is integral at every embedding $\mathbb{C} \to \mathbb{C}_\ell$.

Lean: `New.Selmer.DenominatorLe` (New/OneLift/TestedForms.lean).

The second is the special case for the spaces of lifts, with the rank $r$ of the data in place of $\#r$ and without the clause on inner products.

**Definition (An operator clears the projection).** For $\iota$, a twist $\vartheta$, an index $j$ and a real $\beta$, an operator *clears the projection* if there is a linear map $\Lambda$ on $Z = Z(\vartheta, j)$ with $\exp(-\dim Z \cdot r \cdot \beta) \leq \|\iota(\det \Lambda)\|$ such that $\Lambda(\mathrm{pr}_Z\, y)$ is integral at $\iota$ for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts.

Lean: `New.Data.ClearsProjection` (New/Determinant/Twist/FitTwists.lean).

The determinant condition is the point of the definition. If $\Lambda$ were multiplication by a scalar $\ell^{e}$, the condition would say that $e \log \ell \leq r\beta$, and the projection would have denominator at most $\ell^{e}$. A general $\Lambda$ allows the denominator to be large in a few directions if it is small in the others. Only the total, the valuation of $\det \Lambda$, enters the Gram determinant of the lifts. In logarithms, at most $\dim Z \cdot r \cdot \beta$ is lost to the projection.

**Lemma (From the general form to the special form).** If the projection to the range of $\mathrm{goodLift}(\vartheta, j)$ has denominator at most $\exp \beta$ in the sense of `DenominatorLe` for the descent pair of $(\vartheta, j)$ and the idempotent $e_0$, and $\beta \leq \beta'$, then an operator clears the projection with the constant $\beta'$.

Lean: `New.Selmer.DenominatorLe.clearsProjection` (New/Congruences/FitTwistsExist.lean).

*Proof.* Take the same $\Lambda$. The integrality of $\Lambda(\mathrm{pr}_Z\, y)$ is the first half of the second clause. For the determinant, the index type of the rows of the data has $r$ elements (`New.Data.card_rowIndex`). Since $\dim Z \cdot r \geq 0$ and $\beta \leq \beta'$, we have $\exp(-\dim Z \cdot r \cdot \beta') \leq \exp(-\dim Z \cdot r \cdot \beta) \leq \|\iota(\det \Lambda)\|$. $\square$

**Definition (Denominators at a twist).** For $\iota$, a twist $\vartheta$, an index $j$ and a real $\beta$, the twist *has denominators at most* $\beta$ if two conditions hold.

1. An operator clears the projection to $Z(\vartheta, j)$ with the constant $\beta$.
2. For every main pair $p$ for $j$ and every two test forms $\Xi, \Xi'$ on the space of the rank-one lift of $\nu\vartheta$, let $\mathrm{pr}$ be the orthogonal projection to the line $\mathbb{C}\,\varphi$ of the lifted form $\varphi$ (the `trivialLift` of the datum `p.lValueData`). Then $\|\iota\langle \mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle\| \leq \exp \beta$.

Lean: `New.Data.HasDenominatorsLe` (New/Determinant/Twist/FitTwists.lean).

A test form is integral above $\ell$ and orthogonal to the false lifts in the kernel of the adjoint of the lift. The second clause is a denominator for a projection to a line. If $\varphi$ is integral and $\|\iota\langle \varphi, \varphi\rangle\| = \ell^{e}$ with $e > 0$, the projection $\langle \Xi, \varphi\rangle \varphi/\langle\varphi,\varphi\rangle$ of an integral $\Xi$ can have a denominator, and the clause bounds it.

### The budget and the bound

**Definition (The budget).** The *denominator budget* of the data is
$$\mathrm{denominatorBudget} = \frac{\mathrm{errorUnit}}{m k} = \frac{f\, a \log^3 b}{m k},$$
where $f$ is the number of infinite places of $E$, $a = x b$, $m$ is the number of lifts, and $k = r + 1 - m$.

Lean: `New.Data.denominatorBudget` (New/Determinant/Twist/FitTwists.lean).

With the sizes of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes), $m$ is about $\sqrt{x}$ and $k$ is about $r$, of size $x^5$. So the budget is about $f\, b \log^3 b \cdot x^{-4.5}$. It is a large number, since $b \geq x^{10^{12}}$. The product $m k \log b \cdot \mathrm{denominatorBudget}$ is $f a \log^4 b$, which is the size of the error term $3 f a \log^4 b$ of Theorem C.

**Definition (Denominator bounds for a family).** Let $\theta$ be a family of $m$-fold twists, one for each prime isomorphism, and $1 \leq j \leq m$. Real numbers $\gamma_\ell$, one for each natural number $\ell$, form a *denominator bound* for $\theta$ at $j$ if:

1. $\sum_{\ell \in T} \gamma_\ell \leq \mathrm{denominatorBudget}$ for every finite set $T$ of primes;
2. for every prime isomorphism $\kappa = (\ell, \iota)$, the twist $\theta(\kappa)^j$ has denominators at most $\gamma_\ell$ at $\iota$.

Lean: `New.Data.IsDenominatorBound` (New/Determinant/Twist/FitTwists.lean).

The number $\gamma_\ell$ depends on $\ell$ only, not on $\iota$. The twist depends on $\kappa$.

**Definition (Negligible numbers).** Real numbers $e_\ell$ are *negligible with the exponent* $C$ if $e_\ell \geq 0$ for every $\ell$ and $\sum_{\ell \in T} e_\ell \log \ell \leq x^{C}$ for every finite set $T$ of primes.

Lean: `New.Data.IsNegligible` (New/Determinant/Twist/FitTwists.lean).

Here $x$ is the length of the prime sum, the smallest scale of the data. Since $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, a negligible number with an exponent below $10^6$ fits under $x_1$, and every negligible number of this volume fits far under the budget.

### Regular families

**Definition (Small ratios).** A family $\theta$ of $m$-fold twists *has small ratios* if:

1. for every prime isomorphism $\kappa = (\ell, \iota)$, the norm $\mathrm{Nm}\,Q$ of the modulus of $\theta(\kappa)$ is prime to $\ell$;
2. for every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s = \pm 1$, the family $\kappa \mapsto p.\mathrm{ratio}(\theta(\kappa)^j, s)^{-1}$ has height at most $x_1$.

Lean: `New.Data.HasSmallRatios` (New/Determinant/Twist/FitTwists.lean).

**Definition (Regular families).** A family $\theta$ of $m$-fold twists is *regular* if it has small ratios and, for every $1 \leq j \leq m$, there is a denominator bound $\gamma$ for $\theta$ at $j$.

Lean: `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean).

**Theorem (Twists with few congruences).** For all data $D$ there is a regular family $\theta$ of $m$-fold twists, one for each pair $\kappa = (\ell, \iota)$ of a prime $\ell$ and a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

*Proof.* This is the summary of the proof. Section 6 gives each step with its exact statement. For each $\kappa = (\ell, \iota)$, the result for one prime (Section 6) gives an $m$-fold twist $\tau$ with three properties: $\mathrm{Nm}\,Q$ is prime to $\ell$; for every $j$, every ramified pair $p$ and every sign $s$,
$$\|\iota(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e'_\ell \log \ell), \qquad e'_\ell = \mathrm{twistError}(\ell);$$
and for every $j$ the twist $\tau^j$ has denominators at most
$$\gamma_\ell = \mathrm{clearingBound}(\ell) \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell,$$
where $h_{\mathrm{std}}$ is the number of classes `StdClasses` of $U(1)$ at the level `D.chosenLevel`. Choose such a $\tau = \theta(\kappa)$ for every $\kappa$. The numbers $e'_\ell$ are negligible with the exponent $999$ (Section 5). So $\sum_{\ell \in T} e'_\ell \log \ell \leq x^{999} \leq x_1$ for every finite set $T$ of primes. The lemma on heights from local bounds of Section 2, with $e_\ell = e'_\ell \log \ell$, gives the height bound $x_1$ for the inverse ratios. The sum of $\gamma_\ell$ over any finite set of primes is at most the budget (Section 5). $\square$

**Remark (Formalization).** The family $\theta$ comes from the axiom of choice (the tactic `choose`). The source does not construct the twists. It proves for each $\kappa$ that a twist exists. So $\theta(\kappa)$ is not a definite twist, and no property of $\theta$ holds beyond those in the definition of regular families.

**Remark (Formalization).** The constant $\gamma_\ell$ in the proof has the extra term $v_\ell(h_{\mathrm{std}}) \log \ell$. It comes from the second clause. There the bound for the projection to a line costs the $\ell$-part of the class number of $U(1)$ at the chosen level (`New.Selmer.DenominatorLe.norm_inner_starProjection_le`). In the first clause it is only slack. The number of these classes is at most $\exp(x^{30})$ (`New.Data.card_stdClasses_le_exp`). So the extra terms are negligible with the exponent $30$.

### How Volume 11 uses the theorem

The first use is in the proof of the bound for one lift determinant. For a twist $\vartheta$, let $Z_j(\vartheta)$ be the Gram determinant `D.liftDeterminant` of the lift of the good forms on $W_j$ at $\vartheta$ ([the height of one lift determinant](/chapter/lift-volume-height/)).

**Theorem (The cost of one lift).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then the family $\kappa \mapsto Z_j(1)/Z_j(\theta(\kappa))$ has height at most
$$d_T \cdot k \cdot (\log b \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount}).$$
Here $d_T$ is the dimension of the good forms, and $\mathrm{directionAmount}$ is the sum over the infinite places $\sigma$, of weight $\kappa_\sigma$, of the size $\log \kappa_\sigma! + \kappa_\sigma \log(M/\Omega)$ of a derivative of order $\kappa_\sigma$, less the prime sum that measures its divisibility.

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

The proof is in Volume 11. It writes the ratio as a quotient of the determinants of two projected comparison operators, times the $d_T$-th power of an inverse ratio of Hecke values. The first clause of the denominator bound controls the operators, and the second clause controls the Hecke values through `New.Data.heightLe_inv_ratio`.

**Theorem (Single lifts at good twists).** There is a family $\theta$ of $m$-fold twists with small ratios such that, for every $1 \leq j \leq m$, the family $\kappa \mapsto Z_j(1)/Z_j(\theta(\kappa))$ has height at most
$$d_T \Big(\frac{f\, a \log^4 b}{m} - k \cdot \mathrm{directionAmount}\Big).$$

Lean: `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take a regular family $\theta$ by the theorem on twists with few congruences. It has small ratios by definition. Since $\mathrm{denominatorBudget} = f a \log^3 b/(m k)$ and $k \neq 0$, we have $k \cdot \log b \cdot \mathrm{denominatorBudget} = f a \log^4 b/m$. Then the bound of the cost of one lift is $d_T(f a \log^4 b/m - k \cdot \mathrm{directionAmount})$. $\square$

This explains the shape of the budget. The bound for one lift has the factor $k$, and a chain has $m$ lifts. The factor $1/(m k)$ in the budget cancels both. With the factor $\log b$ of the bound for one lift, the cost of the denominators of the whole chain is $d_T f a \log^4 b$, which is of the size of the error term $3 f a \log^4 b$ per dimension in [the statement of Theorem C](/chapter/theorems-a-b-c/#theorem-c-long-forms).
