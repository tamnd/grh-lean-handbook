---
title: A twist for each prime and the inverse ratio
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/Congruences/FitTwistsExist.lean
  - New/OneLift/LiftVolumeHeight.lean
  - New/Determinant/Chain/Moduli.lean
  - New/Determinant/Chain/NormOfChain.lean
decls:
  - New.Data.denominatorBudget
  - New.Data.IsDenominatorBound
  - New.Data.IsRegularFamily
  - New.exists_isRegularFamily
  - New.Data.heightLe_liftDeterminant_ratio
  - New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div
  - New.Data.quotientRatio
  - New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq
  - New.Data.exists_chainDeterminant_one_div_eq
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio
  - New.Data.heightLe_chainDeterminant_one_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A twist for each prime and the inverse ratio

This section supplies the twists $\theta(\iota)$ of the frame and the bound $b_{\mathrm{volume}}$ for the family $Z(1)/Z(\theta(\iota))$. It has two parts. The first part takes a regular family and bounds the single lift determinants. The second part inverts the factorization of the chain determinant and adds the heights.

### Regular families

**Definition (The denominator budget).** $\mathrm{denominatorBudget} = \mathrm{err}_0/(m k) = f a\log^3 b/(m k)$.

Lean: `New.Data.denominatorBudget` (New/Determinant/Twist/FitTwists.lean).

**Definition (A denominator bound).** Let $\theta$ be a family of $m$-fold twists, $1 \leq j \leq m$, and $\beta(\ell) \in \mathbb{R}$ for every $\ell \in \mathbb{N}$. Then $\beta$ is a *denominator bound* for $\theta$ and $j$ if $\sum_{\ell \in T}\beta(\ell) \leq \mathrm{denominatorBudget}$ for every finite set $T$ of primes, and if for every $\iota$ with prime $\ell$ the twist $\theta(\iota)^j$ has denominators at most $\beta(\ell)$ at $\iota$ for the index $j$.

Lean: `New.Data.IsDenominatorBound` (New/Determinant/Twist/FitTwists.lean).

"Denominators at most $\beta$" means two bounds: an operator with determinant at least $\exp(-(\dim Z)\,r\beta)$ at $\iota$ clears the denominators of the projection to the space $Z$ of lifts, and the projections of test forms to the line of a lift of a main pair have inner products at most $e^\beta$ at $\iota$. The chapter [twists, critical pairs and regular families](/chapter/twists-critical-pairs/#regular-families-of-twists) states the two bounds in full.

**Definition (Regular family).** A family $\theta$ of $m$-fold twists, one for each $\iota$, is *regular* if it has small ratios and, for every $1 \leq j \leq m$, there is a denominator bound for $\theta$ and $j$.

Lean: `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean).

**Theorem (Twists with few congruences).** For all data $D$ there is a regular family $\theta$ of $m$-fold twists.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

*Proof.* This theorem is the subject of Volume 12; see [regular families: the plan](/chapter/regular-families-plan/#the-chain-of-the-proof). The last step is this. For each $\iota$ with prime $\ell$, `New.Selmer.exists_mFoldTwist_hasDenominatorsLe` gives an $m$-fold twist $\tau$ such that $\ell$ is prime to $\mathrm{Nm}\,Q(\tau)$, such that $\|\iota(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e_\ell\log\ell)$ for every $j$, every ramified pair $p$ and every sign $s$, and such that $\tau^j$ has denominators at most $\beta_\ell$ at $\iota$ for every $j$. Here $e_\ell = (4f + 3)\,r\,v_\ell(n_{\mathrm{Aut}}) + 2^{-\ell}$ with $n_{\mathrm{Aut}}$ the chosen group order, and $\beta_\ell$ is a clearing bound times $\log\ell$ plus $v_\ell$ of the number of classes at the chosen level times $\log\ell$. The proof takes $\theta(\iota) = \tau$ by `choose`. The numbers $e_\ell$ are negligible, so $\sum_{\ell \in T}e_\ell\log\ell \leq x_1$ for every finite set $T$ of primes. So the inverse ratios have height at most $x_1$, with $H = 1$ (`New.HeightLe.of_le`). The sum of the $\beta_\ell$ is within the budget by `New.Selmer.sum_clearingBound_add_padicValNat_le`. $\square$

**Remark (Formalization).** The family $\theta$ comes from `choose`, so the twist at $\iota$ is not given by a formula. It may differ for two $\iota$ with the same prime. The proof of Theorem C does not need a formula. It uses only the properties of a regular family, and a height uses one multiplier for all $\iota$.

### The height of one lift

**Theorem (The height of one lift determinant).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most

$$d\,k\,\bigl(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}\bigr).$$

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The chapter [the height of one lift determinant](/chapter/lift-volume-height/#the-height-bound) gives the proof. In short: let $U$ be the comparison operator and $\Delta(\vartheta)$ the determinant of its compression to the lifts. There is $C \neq 0$ with $Z_j(\vartheta)\Delta(\vartheta) = C\rho_j(\vartheta)^d$, where $\rho_j$ is a ratio of Hecke values and $d$ is the dimension of the good forms on $W_j$. This dimension is $d = D.\mathtt{targetDim}$ (`New.Data.targetDim_eq_finrank_goodForms_spaceW`). So $Z_j(1)/Z_j(\theta(\iota)) = (\Delta(\theta(\iota)^j)/\Delta(1))\,\rho_j(\theta(\iota)^j)^{-d}$. The first factor has height at most $d(3A + rB)$ with $A = fmb\log^2 b$ and $B = \mathrm{denominatorBudget}$, by the archimedean bound for $U_1$ and the clearing of denominators. The second has height at most $d(10mx_1 + k(6B - \mathrm{directionAmount}))$ by the chapter [Hecke values](/chapter/hecke-values/#heights-of-inverse-ratios). The sizes give $3A + rB + 10mx_1 + 6kB \leq kB\log b$. $\square$

**Theorem (Single lifts at good twists).** There is a family $\theta$ of $m$-fold twists with small ratios such that for every $j$ with $1 \leq j \leq m$ the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most

$$d\,\Bigl(\frac{f a\log^4 b}{m} - k\cdot\mathrm{directionAmount}\Bigr).$$

Lean: `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take a regular family $\theta$ by the theorem on twists with few congruences. It has small ratios. We have $k > 0$, and

$$k\,\bigl(\log b\cdot\mathrm{denominatorBudget}\bigr) = k\log b\cdot\frac{f a\log^3 b}{m k} = \frac{f a\log^4 b}{m}.$$

So $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}) = d(fa\log^4 b/m - k\cdot\mathrm{directionAmount})$, and the theorem on the height of one lift gives the bound for each $j$. $\square$

The statement forgets that $\theta$ is regular. The rest of the proof uses only small ratios.

### The factorization inverted

**Definition (The quotient ratio).** For $i, j \in \mathbb{N}$,

$$\mathrm{quotientRatio}_{ij}(\vartheta) = \mathrm{lRatioProd}\bigl(\chi_j/\chi_i,\ t,\ \vartheta^{j-i}\bigr),$$

with truncated subtraction $j - i$.

Lean: `New.Data.quotientRatio` (New/Determinant/Chain/Moduli.lean).

**Theorem (Factorization of the determinant).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$: $Z(\vartheta) > 0$; $Z_j(\vartheta) > 0$ for every $1 \leq j \leq m$; and

$$\frac{Z(\vartheta)}{Z(1)} = \Bigl(\mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{0<i\leq m}\ \prod_{i<j\leq m}\mathrm{quotientRatio}_{ij}(\vartheta)\Bigr)^{d}\ \prod_{j=1}^{m}\frac{Z_j(\vartheta)}{Z_j(1)}.$$

Lean: `New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` (New/Determinant/Chain/NormOfChain.lean).

The chapter [the chain determinant](/chapter/chain-determinant/#good-forms-and-the-factorization) proves this theorem. The positivity comes from the injectivity of the chains and of the single lifts.

**Lemma (The inverted factorization).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$

$$\frac{Z(1)}{Z(\vartheta)} = \Bigl(\mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{0<i\leq m}\ \prod_{i<j\leq m}\mathrm{quotientRatio}_{ij}(\vartheta)\Bigr)^{-d}\ \prod_{j=1}^{m}\frac{Z_j(1)}{Z_j(\vartheta)}.$$

Lean: `New.Data.exists_chainDeterminant_one_div_eq` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take $e$ from the factorization. Then $Z(1)/Z(\vartheta) = (Z(\vartheta)/Z(1))^{-1}$. Insert the factorization. The inverse of a product is the product of the inverses, $(s^d)^{-1} = (s^{-1})^d$, and $(Z_j(\vartheta)/Z_j(1))^{-1} = Z_j(1)/Z_j(\vartheta)$. $\square$

**Remark (Formalization).** In Lean, $x/0 = 0$ and $0^{-1} = 0$, so these identities also hold if a factor is $0$. The proof does not need the positivity. The positivity matters for the meaning: by it, $Z(1)/Z(\vartheta)$ is a true quotient. The inverted lemma is at [line 162](lean:New/Determinant/Twist/LongForms.lean#L162) of its file.

**Lemma (The scalar of the chain).** Let $\theta$ have small ratios and $e \in \mathbb{Z}$. Then the family

$$\iota \mapsto \Bigl(\mathrm{Nm}\,Q(\theta(\iota))^{e/2}\prod_{0<i\leq m}\ \prod_{i<j\leq m}\mathrm{quotientRatio}_{ij}(\theta(\iota))\Bigr)^{-1}$$

has height at most $m\cdot m\cdot(t x_1)$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Each quotient ratio with $0 < i < j \leq m$ is a ramified ratio (`New.Data.isRamifiedRatio_of_mem_sigma`). Apply the theorem on inverse products of ramified ratios (Section 3) to the set of these pairs. It has at most $m^2$ elements (`New.Data.card_sigma_Ioc_le`), and a height bound may be raised. $\square$

### The inverse ratio

**Lemma (The inverse ratio).** Let $\theta$ have small ratios, and suppose that for every $1 \leq j \leq m$ the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most $d(fa\log^4 b/m - k\cdot\mathrm{directionAmount})$. Then the family $\iota \mapsto Z(1)/Z(\theta(\iota))$ has height at most

$$d\,\bigl(b + f a\log^4 b - \mathrm{mainAmount}\bigr).$$

Lean: `New.Data.heightLe_chainDeterminant_one_div` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take $e$ from the inverted factorization, and let $s(\vartheta)$ be the scalar in it. There are three steps.

1. The scalar. By the lemma on the scalar of the chain, the family $s(\theta(\iota))^{-1}$ has height at most $m\,m\,t\,x_1$. The sizes give $m\,m\,t\,x_1 \leq b$. So it has height at most $b$. Its $d$-th power has height at most $d\,b$.
2. The single lifts. The product over $j \in \{1, \dots, m\}$ of the $m$ families has height at most the sum of the $m$ bounds. The set has $m$ elements, so the sum is
$$\begin{aligned} m\cdot d\Bigl(\frac{fa\log^4 b}{m} - k\cdot\mathrm{directionAmount}\Bigr) &= d\,\bigl(fa\log^4 b - m k\cdot\mathrm{directionAmount}\bigr) \\ &= d\,\bigl(fa\log^4 b - \mathrm{mainAmount}\bigr), \end{aligned}$$
as $m \neq 0$ and $\mathrm{mainAmount} = m k\cdot\mathrm{directionAmount}$.
3. The product. The product of the two families has height at most $d\,b + d(fa\log^4 b - \mathrm{mainAmount}) = d(b + fa\log^4 b - \mathrm{mainAmount})$. By the inverted factorization at $\vartheta = \theta(\iota)$, this product is the family $Z(1)/Z(\theta(\iota))$.

$\square$

This gives $b_{\mathrm{volume}} = d(b + fa\log^4 b - \mathrm{mainAmount})$. The main term $-d\cdot\mathrm{mainAmount}$ comes from the $m$ single lifts. Each contributes $-d\,k\cdot\mathrm{directionAmount}$, which is the full size of the term $\mathrm{directionAmount}$ by the sharpness of chapter 13. The two errors are $d\,b$ for the scalar and $d\,fa\log^4 b$ for the denominators of the $m$ lifts.
