---
title: Auxiliary forms and the cost of completion
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Determinant/Chain/Moduli.lean
  - New/Determinant/AuxiliaryForms/Turns.lean
  - New/Determinant/AuxiliaryForms/SpanningForms.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
  - New/Determinant/Twist/FitTwists.lean
decls:
  - New.Data.lRatioProd
  - New.Data.IsRamifiedRatio
  - New.Data.turnRatio
  - New.Data.isRamifiedRatio_turnRatio
  - New.Data.HasAbsUpToNormPower
  - New.Data.HasAbsUpToNormPower.exists_norm_div_eq
  - New.Data.exists_span_short_lifts_eq_top
  - New.Data.goodProjTranslate_mem_integralForms
  - New.Data.normSqAt_goodProjTranslate_le
  - New.Data.IsAuxiliaryForm
  - New.Data.exists_span_isAuxiliaryForm_eq_top
  - New.Data.HasSmallRatios
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio
  - New.Data.mul_completion_cost_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Auxiliary forms and the cost of completion

This section supplies the forms $z_i$ of the frame and the two bounds $b_{\mathrm{short}}$ and $b_{\mathrm{denom}}$. It proves the theorem on auxiliary forms from the spanning forms of chapter 11, and it computes the cost of the completion. All statements are in New/Determinant/Twist/LongForms.lean, except the inputs in the first two subsections.

### Ratios of Hecke values

**Definition (The product of ratios).** For a character $\nu$, an integer $s$ and a tame character $\vartheta$ with modulus $Q$,

$$\mathrm{lRatioProd}(\nu, s, \vartheta) = \prod_{z=1}^{s}\frac{|L^{MQ}(z, (\nu\vartheta)^{-1})|}{|L^{M}(z, \nu^{-1})|},$$

where $L^M$ omits the chosen places, and $L^{MQ}$ also omits the places of $Q$.

Lean: `New.Data.lRatioProd` (New/Determinant/Chain/Moduli.lean).

**Definition (A ramified ratio).** A function $F$ of the $m$-fold twists is a *ramified ratio* if there are a ramified critical pair $p = (\nu, z)$ and $1 \leq n \leq m$ such that $F(\vartheta) = \mathrm{lRatioProd}(\nu, z, \vartheta^n)$ for every $\vartheta$.

Lean: `New.Data.IsRamifiedRatio` (New/Determinant/Chain/Moduli.lean).

A ramified ratio is nonnegative, and its value at the trivial twist is $1$ (`New.Data.IsRamifiedRatio.nonneg`, `New.Data.IsRamifiedRatio.apply_one`). The chapter [the chain determinant](/chapter/chain-determinant/#moduli-and-ratios-of-hecke-values) proves both.

**Definition (The turn ratio).** For $i, j \in \mathbb{N}$,

$$\mathrm{turnRatio}_{ij}(\vartheta) = \mathrm{lRatioProd}\bigl(\chi_{i+1}\chi_{j+1},\ t,\ \vartheta^{j+1}\bigr),$$

where $\chi_i = D.\mathtt{untwistedLiftChar}\ i$ is the character of the $i$-th lift at the trivial twist.

Lean: `New.Data.turnRatio` (New/Determinant/AuxiliaryForms/Turns.lean).

**Lemma (Turn ratios are ramified).** For $i, j < m$ the turn ratio $\mathrm{turnRatio}_{ij}$ is a ramified ratio.

Lean: `New.Data.isRamifiedRatio_turnRatio` (New/Determinant/AuxiliaryForms/Turns.lean).

*Proof.* Take the critical pair of the square $(i, j)$: the character $\chi_{i+1}\chi_{j+1}$, with $z = t$, and $n = j + 1$. Then $1 \leq n \leq m$. The tame part of the pair is the power $\omega^{i+j+2}$ of the fixed family $\omega = D.\mathtt{chiMLocal}$ of residue characters. The exponent is not $0$ and is small against the order of $\omega$, so this power is nontrivial exactly at the chosen places (`New.Data.chiMLocal_zpow_ne_one_iff_isChosen`). So the pair is ramified. The equation holds by definition. $\square$

**Definition (Absolute value up to a norm power).** A complex function $c$ of the $m$-fold twists *has absolute value $f$ up to a norm power* if there are $C \in \mathbb{R}$ and $k \in \mathbb{Z}$ with $|c(\vartheta)|^2 = C\,\mathrm{Nm}\,Q(\vartheta)^k f(\vartheta)^2$ for every $\vartheta$.

Lean: `New.Data.HasAbsUpToNormPower` (New/Determinant/Chain/Moduli.lean).

**Remark (Formalization).** The constant $C$ may be $0$. Then $c$ vanishes at every twist. The next lemma excludes this case by its hypothesis $c(1) \neq 0$.

**Lemma (Normalizing at the trivial twist).** Let $c$ have absolute value $f$ up to a norm power. Suppose that $f \geq 0$, $f(1) = 1$ and $c(1) \neq 0$. Then there is an integer $e$ with $|c(\vartheta)/c(1)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}f(\vartheta)$ for every $\vartheta$.

Lean: `New.Data.HasAbsUpToNormPower.exists_norm_div_eq` (New/Determinant/Chain/Moduli.lean).

*Proof.* The trivial twist has $\mathrm{Nm}\,Q(1) = 1$, so $|c(1)|^2 = C$. Take $e = k$. Then $|c(\vartheta)/c(1)|^2 = \mathrm{Nm}\,Q(\vartheta)^k f(\vartheta)^2$, and both sides of the claim are nonnegative, so the claim follows by taking square roots. $\square$

### The spanning forms and the good part

**Theorem (Spanning forms with short lifts).** There are units $c(\vartheta) \in \mathbb{C}^\times$, one for each $m$-fold twist, such that $c$ has absolute value $\prod_{i<m}\prod_{j<m}\mathrm{turnRatio}_{ij}$ up to a norm power, and such that the forms of principal level on $Y_0$ are spanned by the forms $y$ with two properties:

1. for every $\vartheta$, every prime $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$ and every place above $\ell$, the form $(c(\vartheta)/c(1))\cdot\Theta_\vartheta y$ is integral at that place;
2. for every automorphism $\sigma$ of $\mathbb{C}$ and every $g$, the squared Weyl norm of $\sigma$ applied to the value at $g$ of the chain of lifts of $y$ at the trivial twist is at most $\exp(x^{202}b^2)$.

Lean: `New.Data.exists_span_short_lifts_eq_top` (New/Determinant/AuxiliaryForms/SpanningForms.lean).

The chapter [deep level Poincaré series](/chapter/deep-level-poincare/#denominators-sizes-and-spanning-forms) proves this theorem, with the turns of [grids, columns and turns](/chapter/grids-paths-turns/#turns-off-the-diagonal). The forms of this theorem lie in the forms of principal level, not in the target. The next two lemmas move them to the target. Let $\mathsf{G}$ be the finite group $D.\mathtt{chosenGL}$ and $e_0$ the central idempotent that cuts out the good part. For $s \in \mathsf{G}$ the map $\mathrm{goodProjTranslate}(s)$ is the translation by $s$ followed by $|\mathsf{G}|\,e_0$. Its values are target forms.

**Lemma (The good part keeps integrality).** Let $c \in \mathbb{C}$ and $z$ a form of principal level on $Y_0$. If $c\cdot\Theta_\vartheta z$ is integral at a place $j$, then $c\cdot\Theta_\vartheta(\mathrm{goodProjTranslate}(s)\,z)$ is integral at $j$, for every $s \in \mathsf{G}$.

Lean: `New.Data.goodProjTranslate_mem_integralForms` (New/UpperBound/Size/ArchimedeanSize.lean).

**Lemma (The size of the good part).** Let $z$ be a form of principal level on $Y_0$ and $B \in \mathbb{R}$. If every value of the chain of lifts of $z$ at the trivial twist, conjugated by $\sigma$, has squared Weyl norm at most $e^B$, then $\|\Theta_1(\mathrm{goodProjTranslate}(s)\,z)\|_\sigma^2 \leq \exp(x^{99} + B)$.

Lean: `New.Data.normSqAt_goodProjTranslate_le` (New/UpperBound/Size/ArchimedeanSize.lean).

The chapter [the archimedean size](/chapter/archimedean-size/#the-good-part) of Volume 9 proves both lemmas. The first holds because $|\mathsf{G}|\,e_0$ has coefficients that are algebraic integers. The second holds because the coefficients of $\sigma e_0$ have absolute value at most $1$, and the factor $e^{x^{99}}$ bounds the effect of the sum over $\mathsf{G}$.

### Auxiliary forms

**Definition (Auxiliary forms).** Let $\gamma(\vartheta) \in \mathbb{C}$ for every $m$-fold twist $\vartheta$. A target form $y$ is *auxiliary for $\gamma$* if two conditions hold.

1. For every $\iota$ and every $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to the prime of $\iota$, the form $\gamma(\vartheta)\,\Theta_\vartheta y$ is integral at the place of $\iota$.
2. For every automorphism $\sigma$ of $\mathbb{C}$, $\|\Theta_1 y\|_\sigma^2 \leq \exp(2x_1^2b^2)$.

Lean: `New.Data.IsAuxiliaryForm` (New/Determinant/Twist/LongForms.lean).

**Theorem (Auxiliary forms).** There are an integer $e$ and numbers $\gamma(\vartheta) \in \mathbb{C}$, one for each $m$-fold twist $\vartheta$, such that:

1. $\gamma(\vartheta) \neq 0$ for every $\vartheta$;
2. $\gamma(1) = 1$;
3. for every $\vartheta$,
$$|\gamma(\vartheta)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{i=0}^{m-1}\prod_{j=0}^{m-1}\mathrm{turnRatio}_{ij}(\vartheta);$$
4. the target forms are spanned by the forms auxiliary for $\gamma$.

Lean: `New.Data.exists_span_isAuxiliaryForm_eq_top` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take the units $c(\vartheta)$ and the spanning set of the theorem on spanning forms. Let $F = \prod_{i<m}\prod_{j<m}\mathrm{turnRatio}_{ij}$. Each factor is a ramified ratio, so $F \geq 0$ and $F(1) = 1$. As $c(1)$ is a unit, the lemma on normalizing gives an integer $e$ with $|c(\vartheta)/c(1)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}F(\vartheta)$. Put $\gamma(\vartheta) = c(\vartheta)/c(1)$. Then $\gamma(\vartheta) \neq 0$, $\gamma(1) = 1$, and part 3 holds.

For part 4, consider $\mathrm{goodProjTranslate}(1)$. It is $|\mathsf{G}|$ times the restriction of $e_0$ to its range, and $|\mathsf{G}| \neq 0$, so it maps onto the target. So it maps the span of the spanning set onto the target, and the target is spanned by the images of the spanning forms. It is enough to show that each image is auxiliary for $\gamma$. Let $\psi$ be a spanning form. Condition 1 of an auxiliary form holds by the lemma on integrality, applied with $c = \gamma(\vartheta)$ and $s = 1$, at the place of $\iota$. For condition 2, the lemma on the size gives $\|\Theta_1(\mathrm{goodProjTranslate}(1)\,\psi)\|_\sigma^2 \leq \exp(x^{99} + x^{202}b^2)$. The sizes give $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$ (`New.Data.le_of_hasLogBound`), as $x^{202} \leq x_1^2$ and $x^{99} \leq x_1^2b^2$. $\square$

**Remark (Formalization).** The numbers $\gamma(\vartheta)$ come from the units of the theorem on spanning forms by an `obtain`, so they are not given by a formula. The proof of Theorem C uses only the four properties. Part 2, $\gamma(1) = 1$, is not used in the proof of Theorem C.

### The height of the scalar

**Definition (Small ratios).** A family $\theta$ of $m$-fold twists, one for each $\iota$, *has small ratios* if two conditions hold.

1. For every $\iota$, the prime of $\iota$ is prime to $\mathrm{Nm}\,Q(\theta(\iota))$.
2. For every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s = \pm 1$, the family $\iota \mapsto p.\mathrm{ratio}(\theta(\iota)^j, s)^{-1}$ has height at most $x_1$.

Lean: `New.Data.HasSmallRatios` (New/Determinant/Twist/FitTwists.lean).

**Theorem (Inverse products of ramified ratios).** Let $\theta$ have small ratios, let $e \in \mathbb{Z}$, and let $F_a$, for $a$ in a finite set $s$, be ramified ratios. Then the family

$$\iota \mapsto \Bigl(\mathrm{Nm}\,Q(\theta(\iota))^{e/2}\prod_{a \in s}F_a(\theta(\iota))\Bigr)^{-1}$$

has height at most $\#s\cdot(t x_1)$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod` (New/Determinant/Chain/Moduli.lean).

*Proof.* Each $F_a(\vartheta)$ is a product of $z \leq t$ ratios of a ramified pair, and the inverse of each ratio has height at most $x_1$ by small ratios. So $F_a(\theta(\iota))^{-1}$ has height at most $t x_1$, and the product over $s$ has height at most $\#s\cdot(tx_1)$. The power $\mathrm{Nm}\,Q(\theta(\iota))^{-e/2}$ has absolute value $1$ at $\iota$, because its base is prime to the prime of $\iota$ (`New.HeightLe.rpow_mul`). So it does not raise the height. $\square$

**Lemma (The scalar of the auxiliary forms).** Let $\theta$ have small ratios and $e \in \mathbb{Z}$. Then the family

$$\iota \mapsto \Bigl(\mathrm{Nm}\,Q(\theta(\iota))^{e/2}\prod_{i=0}^{m-1}\prod_{j=0}^{m-1}\mathrm{turnRatio}_{ij}(\theta(\iota))\Bigr)^{-1}$$

has height at most $m\cdot m\cdot(t x_1)$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio` (New/Determinant/Twist/LongForms.lean).

*Proof.* Apply the theorem on inverse products to the set $s = \{0, \dots, m-1\}^2$, with $F_{(i,j)} = \mathrm{turnRatio}_{ij}$. These are ramified ratios by the lemma on turn ratios, and $\#s = m\cdot m$. The double product is the product over $s$. $\square$

In the proof of Theorem C the family $(|\gamma(\theta(\iota))|^2)^{-1}$ is the square of this family, by part 3 of the theorem on auxiliary forms. So it has height at most $2\,m\,m\,t\,x_1$. The sizes give $2\,m\,m\,t\,x_1 \leq b$: here $m^2 \leq 4x$ and $t \leq 15x^5$, so the left side is at most $120\,x^6x_1$, which is much smaller than $b$. This gives $b_{\mathrm{denom}} = b$.

### The cost of completion

**Lemma (The cost of completion).** Let $n, n' \in \mathbb{N}$ with $(1 - 4/b^2)\,d \leq n$ and $d = n + n'$. Then

$$n'\,(2x_1^2b^2 + b) \leq d\,b.$$

Lean: `New.Data.mul_completion_cost_le` (New/Determinant/Twist/LongForms.lean).

*Proof.* We have $b > 0$. From $d = n + n'$ and the hypothesis, $n' = d - n \leq (4/b^2)\,d$. So

$$n'(2x_1^2b^2 + b) \leq \frac{4}{b^2}\,d\,(2x_1^2b^2 + b) = d\cdot 4\,(2x_1^2 + b^{-1}).$$

The sizes give $4(2x_1^2 + b^{-1}) \leq b$ (`New.Data.le_of_hasLogBound`), since $x_1^{10^6} \leq b$. So the left side is at most $d\,b$. $\square$

The forms $z_i$ are very long: each has squared length up to $\exp(2x_1^2b^2)$. They are cheap in total because there are few of them. The factor $4/b^2$ in their number cancels the factor $b^2$ in the logarithm of their squared length. The bound $b_{\mathrm{denom}} = b$ for each form is smaller than $2x_1^2b^2$, and it adds only $n'b \leq 4d/b$.
