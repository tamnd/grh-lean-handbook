---
title: Products of L-values of a twist
lean:
  - Lib/SiegelWeil/Tower/FiniteTateIntegral.lean
  - New/Reduction/Lattices/Heights.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
decls:
  - New.Exchange.lValueProd
  - New.PrimePadicIso
  - New.HeightLe
  - New.HeightLe.rpow_mul
  - New.Data.IsRegularFamily.heightLe_of_eq_zpow_mul
  - New.Data.CriticalPair.lowerPoint
  - New.Data.TameChar.disjoint_isChosen_Q
  - New.Data.CriticalPair.ratio_lowerPoint
  - New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Products of L-values of a twist

The norms of the lifts in the chain are not single $L$-values. The tower of Volume 6 gives, for a lift of rank $2e$, a product of the $L$-values at all points $1, \dots, e$, together with a power of the norms of the level places. When the twist changes, this product changes, and the change has two parts: a power of $\mathrm{Nm}\, Q$ and a product of squared ratios. This section proves the factorization and the fact that makes the power of $\mathrm{Nm}\,Q$ harmless.

### The product L-star

**Definition (Product of $L$-values).** For a set $S$ of finite places, a character $\chi$ of $U(1)(\mathbb{A}_E)$ and $e \in \mathbb{N}$,

$$L_*(S, \chi, e) = \Big(\prod_{w \in S} q_w\Big)^{e^2} \prod_{z = 1}^{e} |L^S(z, \chi)|^2.$$

Lean: `New.Exchange.lValueProd` (Lib/SiegelWeil/Tower/FiniteTateIntegral.lean)

This is the definition of [the Rallis inner product formula](/chapter/rallis-inner-product/). The factor $(\prod q_w)^{e^2}$ is the normalization at the level places that makes the tower of lifts work.

**Remark (Formalization).** The product over $S$ is a `finprod` over a set. In Mathlib a `finprod` over an infinite support is $1$, a junk value. In this section $S$ is the set of chosen places or its union with a modulus $Q$, which is finite, so the junk value does not occur.

### Lower points of a pair

The factorization has one ratio for each point $1 \leq z' \leq z$ of a pair $p = (\nu, z)$. Each such point gives a pair with the same character.

**Definition (Lower point).** For a critical pair $p = (\nu, z)$ and $z' \in \mathbb{N}$, the pair $p_{\downarrow z'}$ has the character, the weight and the tame part of $p$ and the point $\max(1, \min(z', z))$.

Lean: `New.Data.CriticalPair.lowerPoint` (New/OneLift/HeckeValues/TwistedRatio.lean)

For $1 \leq z' \leq z$ the point is $z'$. The point $\max(1, \min(z', z))$ is in $[1, z] \subseteq [1, t]$ and it is at most every $c(v)$, so $p_{\downarrow z'}$ is a critical pair for every $z'$. The clamp makes the definition total, and its value outside $[1, z]$ is never used. Since the tame part does not change, $p_{\downarrow z'}$ is ramified if $p$ is ramified. This is the property that the small ratios of Section 6 need.

**Lemma (Ratio at a lower point).** For $1 \leq z' \leq z$, a tame character $\vartheta$ and a sign $s$,

$$\mathrm{ratio}(p_{\downarrow z'}, \vartheta, s) = \frac{|L^{S \cup Q}(z', (\nu\vartheta^s)^{-1})|}{|L^S(z', \nu^{-1})|}.$$

Lean: `New.Data.CriticalPair.ratio_lowerPoint` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* For $1 \leq z' \leq z$ we have $\min(z', z) = z'$ and $\max(1, z') = z'$. Substitute in the definition of the ratio. $\square$

**Lemma (The modulus avoids the chosen places).** For a tame character $\vartheta$, no place of $Q$ is chosen.

Lean: `New.Data.TameChar.disjoint_isChosen_Q` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* Let $w \in Q$. The ideal $w$ contains $q_w$, a factor of $\mathrm{Nm}\,Q$, so $\mathrm{Nm}\,Q \in w$. If $\pi_M \in w$, then $M = \pi_M \bar\pi_M \in w$. Since $M$ and $\mathrm{Nm}\,Q$ are coprime integers, this gives $1 \in w$, which is not possible. So $w$ is not chosen. The source takes this from the lemma `New.Data.normQ_mem_and_notMem_of_mem_Q` of Volume 9. $\square$

### The factorization

**Theorem (Factorization of $L_*$ at a twist).** Let $p = (\nu, z)$ be a critical pair, $\vartheta$ a tame character with modulus $Q$, and $s$ a sign. Then

$$L_*\big(S \cup Q, (\nu\vartheta^s)^{-1}, z\big) = (\mathrm{Nm}\,Q)^{z^2} \cdot L_*\big(S, \nu^{-1}, z\big) \cdot \prod_{z' = 1}^{z} \mathrm{ratio}(p_{\downarrow z'}, \vartheta, s)^2,$$

where $S$ is the set of chosen places.

Lean: `New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* There are two steps, one for each factor of $L_*$.

The norm factor. The sets $S$ and $Q$ are disjoint by the last lemma, and both are finite. So

$$\prod_{w \in S \cup Q} q_w = \Big(\prod_{w \in S} q_w\Big) \cdot \mathrm{Nm}\, Q,$$

and the $z^2$-th power is $(\prod_{w \in S} q_w)^{z^2} (\mathrm{Nm}\,Q)^{z^2}$.

The $L$-value factor. Fix $1 \leq z' \leq z$. The ratio of $p_{\downarrow z'}$ is not zero (Section 3), so its denominator $|L^S(z', \nu^{-1})|$ is not zero. By the lemma on lower points,

$$|L^{S \cup Q}(z', (\nu\vartheta^s)^{-1})|^2 = |L^S(z', \nu^{-1})|^2 \cdot \mathrm{ratio}(p_{\downarrow z'}, \vartheta, s)^2.$$

Take the product over $z' \in [1, z]$, multiply by the norm factor and rearrange. $\square$

The theorem is an identity of real numbers, and its proof uses nothing about the size of the ratios. The content is the bookkeeping: every Euler factor at $Q$ that the twist removes is accounted for by the ratio, and the normalization at the level contributes exactly $(\mathrm{Nm}\,Q)^{z^2}$.

**Example (The smallest case).** Take $z = 1$. Then the theorem says

$$\Big(\prod_{w \in S \cup Q} q_w\Big) |L^{S \cup Q}(1, (\nu\vartheta^s)^{-1})|^2 = \mathrm{Nm}\,Q \cdot \Big(\prod_{w \in S} q_w\Big) |L^S(1, \nu^{-1})|^2 \cdot \mathrm{ratio}(p, \vartheta, s)^2,$$

which is the definition of the ratio, squared, multiplied by the norms. For $z = 2$ the power of $\mathrm{Nm}\,Q$ is $4 = 2^2$, while the number of squared ratios is $2$. The exponent $z^2$ grows faster than the number $z$ of ratios: it is the exponent of the normalization in the tower, and it has no relation to the ratios.

### Powers of the norm of the modulus do not change heights

The factor $(\mathrm{Nm}\, Q)^{z^2}$ is not small. It is harmless for a different reason: the heights of the source are heights of families indexed by pairs $\iota = (\ell, \iota)$ of a prime and an isomorphism, and the modulus of the twist at $\iota$ is chosen prime to $\ell$. A number prime to $\ell$ is an $\ell$-adic unit.

**Definition (Height of a family).** Let $\mathcal{I}$ be the set of pairs $\iota$ of a prime $\ell$ and a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$. A family $y : \mathcal{I} \to \mathbb{C}$ has height at most $c$ if there are $H \in \mathbb{C}$ with $H \neq 0$, a real number $\alpha$ and real numbers $h_\ell \geq 0$ such that

1. $|\sigma(H)| \leq e^\alpha$ for every automorphism $\sigma$ of $\mathbb{C}$;
2. $|\iota(H y_\iota)|_\ell \leq \ell^{h_\ell}$ for every $\iota$, with $\ell$ the prime of $\iota$;
3. $\alpha + \sum_{\ell \in T} h_\ell \log \ell \leq c$ for every finite set $T$ of primes.

Lean: `New.PrimePadicIso` (New/Reduction/Lattices/Heights.lean)

Lean: `New.HeightLe` (New/Reduction/Lattices/Heights.lean)

This is the definition of [twisted lattices](/chapter/twisted-lattices/). The rule we need is proved there.

**Lemma (Powers of units).** Let $y$ have height at most $c$, let $c \leq c'$, let $N : \mathcal{I} \to \mathbb{N}$ with $N_\iota$ prime to the prime of $\iota$ for every $\iota$, and let $e : \mathcal{I} \to \mathbb{Q}$. Then $\iota \mapsto N_\iota^{e_\iota} y_\iota$ has height at most $c'$.

Lean: `New.HeightLe.rpow_mul` (New/Reduction/Lattices/Heights.lean)

**Proposition (Powers of the norm of the modulus).** Let $\theta$ be a regular family of $m$-fold twists (Section 6). Let $y$ have height at most $c$, let $c \leq c'$, and let $y'$ be a family such that for every $\iota$ with $y'_\iota \neq 0$ there is $k \in \mathbb{Z}$ with $y'_\iota = (\mathrm{Nm}\,Q_{\theta(\iota)})^k y_\iota$. Then $y'$ has height at most $c'$.

Lean: `New.Data.IsRegularFamily.heightLe_of_eq_zpow_mul` (New/OneLift/HeckeValues/TwistedRatio.lean)

*Proof.* Choose the integer $k_\iota$ for each $\iota$ with $y'_\iota \neq 0$, and put $k_\iota = 0$ otherwise. A regular family has small ratios, and the first condition of small ratios is that the prime of $\iota$ is prime to $\mathrm{Nm}\,Q_{\theta(\iota)}$. So the lemma on powers of units applies with $N_\iota = \mathrm{Nm}\,Q_{\theta(\iota)}$ and $e_\iota = k_\iota$. It gives the height bound $c'$ for the family $(\mathrm{Nm}\,Q_{\theta(\iota)})^{k_\iota} y_\iota$. Condition 1 of the height does not involve the family. Condition 2 for $y'$ follows from condition 2 for this family, because $|\iota(H y'_\iota)|_\ell \leq |\iota(H (\mathrm{Nm}\,Q)^{k_\iota} y_\iota)|_\ell$: the two sides are equal if $y'_\iota \neq 0$, and the left side is $0$ if $y'_\iota = 0$. $\square$

**Remark (Formalization).** The proposition assumes that $\theta$ is a regular family, but its proof uses only the coprimality field of `HasSmallRatios`. The hypothesis "$y'_\iota = 0$ or $y'_\iota$ is a power times $y_\iota$" lets the source treat the indices where a quantity vanishes without a case split at the call site. The integers $k_\iota$ are chosen by `choose!`, which gives a value also at the indices where no $k$ exists. These values are never used.

### How the two results are used

The later chapters meet products $L_*$ at a twisted character $(\nu\vartheta^s)^{-1}$ in the norms of the lifts, and they divide them by the same product at the trivial twist. By the factorization, the quotient is $(\mathrm{Nm}\,Q)^{z^2}$ times a product of squared ratios. The proposition removes the power of $\mathrm{Nm}\,Q$, and the small ratios of Section 6 bound the height of the inverse ratios. The two steps are combined in [the chain determinant and its factorization](/chapter/chain-determinant/), where the following theorem is proved.

**Theorem (Heights of products of ratios).** Let $\theta$ be a family of $m$-fold twists with small ratios, let $e \in \mathbb{Z}$, and let $s$ be a finite set. For each $a \in s$, let $F_a$ be a ramified ratio: there are a ramified pair $p$ and $n \in [1, m]$ with $F_a(\vartheta) = \prod_{z'=1}^{z} \mathrm{ratio}(p_{\downarrow z'}, \vartheta^n)$ for every $m$-fold twist $\vartheta$. Then the family

$$\iota \mapsto \Big((\mathrm{Nm}\,Q_{\theta(\iota)})^{e/2} \prod_{a \in s} F_a(\theta(\iota))\Big)^{-1}$$

has height at most $|s| \cdot t \cdot x_1$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod` (New/Determinant/Chain/Moduli.lean)

In Lean the product $F_a$ is written with `New.Data.lRatioProd`, and the ratio in it is the quotient of the absolute values at the points $1, \dots, z$. The proof takes one factor $\mathrm{ratio}(p_{\downarrow z'}, \vartheta^n)^{-1}$ for each $z' \leq z \leq t$, each of height at most $x_1$ by the condition on small ratios applied to the ramified pair $p_{\downarrow z'}$, and multiplies. The exponent $e/2$ is rational, and the lemma on powers of units allows rational exponents, which is why it is stated with $e : \mathcal{I} \to \mathbb{Q}$.
