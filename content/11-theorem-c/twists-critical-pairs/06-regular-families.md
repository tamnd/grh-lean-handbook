---
title: Regular families of twists
lean:
  - New/Determinant/Twist/FitTwists.lean
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Data.goodLift
  - New.Data.denominatorBudget
  - New.Data.ClearsProjection
  - New.Data.HasDenominatorsLe
  - New.Data.IsDenominatorBound
  - New.Data.IsNegligible
  - New.Data.HasSmallRatios
  - New.Data.IsRegularFamily
  - New.exists_isRegularFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Regular families of twists

Sections 3 to 5 work with one twist. The height argument works with families. A height bound for a nonzero algebraic number $y$ is a statement about all places at once: the archimedean size of $y$ and the $\ell$-adic sizes for all primes $\ell$. The source does not pick one twist for all primes. For each pair $\iota$ of a prime $\ell$ and an isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$ it picks a twist $\theta(\iota)$ that is good at $\ell$, and it bounds the height of the family $\iota \mapsto y(\theta(\iota))$ in the sense of Section 5. This works because the quantities of Theorem C at the trivial twist do not depend on the twist, and the height argument at $\iota$ only needs the twisted quantity at the one prime of $\iota$.

A family is regular if it satisfies two groups of conditions. The first group, small ratios, controls the inverse ratios of Sections 3 to 5. The second group, small denominators, controls the denominators of the orthogonal projections to the spaces of lifts. The denominators must be small in total over all primes, and the total is the denominator budget.

### The budget

**Definition (Denominator budget).** With the error unit $f a \log^3 b$ of the data (Volume 1), where $f$ is the number of infinite places of $E$ and $a = x b$,

$$\mathrm{denominatorBudget} = \frac{f a \log^3 b}{m k}, \qquad k = r + 1 - m.$$

Lean: `New.Data.denominatorBudget` (New/Determinant/Twist/FitTwists.lean)

**Example (Why this size).** The height of one lift determinant ([the height of one lift determinant](/chapter/lift-volume-height/)) is bounded by $d \cdot k \cdot (\log b \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount})$, where $d$ is the dimension of the good forms. The budget is the size for which the first term is

$$k \cdot \log b \cdot \mathrm{denominatorBudget} = \frac{f a \log^4 b}{m}.$$

There are $m$ lifts. Summed over them, these first terms give $d f a \log^4 b = d \cdot \mathrm{errorUnit} \cdot \log b$. So the division by $m k$ in the budget cancels the factor $k$ of one lift and the number $m$ of lifts.

**Remark (Formalization).** All sizes are real numbers and $m k > 0$ by the sizes of the data, since $m \geq \sqrt x$ and $k = r + 1 - m \geq x^5 + 1 - 2\sqrt x > 0$. So the division by $m k$ is a true division, not the junk value $x/0 = 0$. The subtraction in $k$ is in $\mathbb{N}$, and it does not truncate, for the same reason.

### Small denominators

The spaces of lifts are defined with the theta lift of [single theta lifts and their norms](/chapter/single-theta-lifts/). For a tame character $\vartheta$ and $j \in \mathbb{N}$, the single lift takes forms on the hermitian space $W_j$ of rank $r$ to forms on the definite space $V$ of rank $r + t$ of the lift datum $(\vartheta, j)$.

**Definition (Good lift).** The good lift is the single lift restricted to the good forms: the forms fixed by the principal congruence subgroup at the chosen places that lie in the image of the idempotent $e_0$. Its range $Z$ is the space of lifts from $W_j$ for $\vartheta$.

Lean: `New.Data.goodLift` (New/Determinant/Twist/FitTwists.lean)

Let $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$ be a ring isomorphism. A form on $V$ is integral at $\iota$ if all its values lie in the unit ball of the $\ell$-adic absolute value after $\iota$. A form is orthogonal to the false lifts if it is orthogonal to the forms in $Z^\perp \cap \mathrm{im}(e_0)$ that are killed by the Hecke polynomial at its test value at some split place off the level ([false lifts](/chapter/false-lifts/)). Denominators are written with norms: "$v_\iota(y) \geq -\beta_\ell$" reads $|\iota(y)|_\ell \leq e^{\beta}$ with $\beta = \beta_\ell \log \ell$.

**Definition (Clearing the projection).** Let $\vartheta$ be a twist, $j \in \mathbb{N}$, $\beta \in \mathbb{R}$, and let $\mathrm{pr}$ be the orthogonal projection to $Z$. The twist clears the projection with $\beta$ at $\iota$ if there is a linear map $\Lambda : Z \to Z$ such that

1. $|\iota(\det \Lambda)|_\ell \geq \exp(-\dim Z \cdot r \beta)$;
2. for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts, $\Lambda(\mathrm{pr}\, y)$ is integral at $\iota$.

Lean: `New.Data.ClearsProjection` (New/Determinant/Twist/FitTwists.lean)

The map $\Lambda$ multiplies the projection by an operator whose determinant has $\ell$-adic valuation at most $\dim Z \cdot r \beta/\log \ell$. If $\Lambda$ were a scalar $\lambda$, condition 1 would say $|\iota\lambda|_\ell \geq e^{-r\beta}$, so the projection would have denominators at most $e^{r\beta}$. A general $\Lambda$ allows different denominators in different directions, with the same total.

**Definition (Denominators at most $\beta$).** The twist $\vartheta$ has denominators at most $\beta$ for $j$ at $\iota$ if

1. it clears the projection with $\beta$ at $\iota$;
2. for every main pair $p$ for $j$ and every two test forms $\Xi, \Xi'$ on the definite space of rank $2z$ of the lift data of $(p, \vartheta)$, with $L$ the complex line spanned by the unscaled lift $\Theta_\vartheta$ of Section 4,
$$\big|\iota\langle \mathrm{pr}_L\, \Xi, \mathrm{pr}_L\, \Xi'\rangle\big|_\ell \leq e^\beta.$$

Lean: `New.Data.HasDenominatorsLe` (New/Determinant/Twist/FitTwists.lean)

A test form is a form that is integral above $\ell$ and orthogonal to the false lifts in the kernel of the adjoint of the lift. The second condition makes sense because a main pair satisfies `HasLiftRank` (Section 3), so the lift data exist.

**Definition (Denominator bound).** Let $\theta$ be a family of $m$-fold twists and $j \in [1, m]$. Real numbers $(\gamma_\ell)$, one for each prime, are a denominator bound for $\theta$ and $j$ if

1. $\sum_{\ell \in T} \gamma_\ell \leq \mathrm{denominatorBudget}$ for every finite set $T$ of primes;
2. for every $\iota$, with prime $\ell$, the twist $\theta(\iota)^j$ has denominators at most $\gamma_\ell$ for $j$ at $\iota$.

Lean: `New.Data.IsDenominatorBound` (New/Determinant/Twist/FitTwists.lean)

**Remark (Formalization).** The numbers $\gamma_\ell$ are not required to be nonnegative. The sum condition over every finite $T$ is then a condition on the positive parts: take $T$ to be the primes with $\gamma_\ell > 0$ among any finite set. One $\gamma_\ell$ serves all isomorphisms $\iota$ with the prime $\ell$, while the twist $\theta(\iota)$ may depend on $\iota$.

### Small ratios

**Definition (Small ratios).** A family $\theta$ of $m$-fold twists, one for each $\iota$, has small ratios if

1. $\gcd(\ell, \mathrm{Nm}\,Q_{\theta(\iota)}) = 1$ for every $\iota$, with $\ell$ the prime of $\iota$;
2. for every $j \in [1, m]$, every ramified critical pair $p$ and every sign $s$, the family
$$\iota \mapsto \mathrm{ratio}\big(p, \theta(\iota)^j, s\big)^{-1}$$
has height at most $x_1$.

Lean: `New.Data.HasSmallRatios` (New/Determinant/Twist/FitTwists.lean)

The inverse is well defined in the honest sense, since the ratio is not zero (Section 3). Condition 2 is a condition at the infinite places and at all primes at once. It covers both signs, so it bounds both $\vartheta^j$ and $\vartheta^{-j}$, and it covers all ramified pairs, not only the main pairs. The lower points $p_{\downarrow z'}$ of a ramified pair are ramified (Section 5), so condition 2 applies to each factor of the product in the factorization of $L_*$.

The size $x_1$ is the second cut-off of the data: $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$. So $x_1$ is large compared with the prime sum length $x$ and small compared with the weight scale $b$. In the factorization of Section 5 there are at most $t$ ratios, so their product has height at most $t x_1$, which is still small compared with $b$.

**Definition (Negligible numbers).** For $C \in \mathbb{N}$, numbers $(e_\ell)$ are negligible with exponent $C$ if $e_\ell \geq 0$ for all $\ell$ and $\sum_{\ell \in T} e_\ell \log \ell \leq x^C$ for every finite set $T$ of primes.

Lean: `New.Data.IsNegligible` (New/Determinant/Twist/FitTwists.lean)

The proof of Theorem C does not use this notion. It is used in the proof of the existence of regular families in Volume 12, for the error of the twisting theorem, for an error of the denominators, for the valuations of a bound for class numbers and for the valuations of the number of standard classes, with the exponents $999$, $4000$, $2000$ and $30$.

### Regular families

**Definition (Regular family).** A family $\theta$ of $m$-fold twists, one for each $\iota$, is regular if it has small ratios and if for every $j \in [1, m]$ there is a denominator bound $\gamma$ for $\theta$ and $j$.

Lean: `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean)

**Theorem (Existence of regular families).** For all admissible data $D$ there is a regular family $\theta$ of $m$-fold twists.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean)

The proof is the subject of Volume 12 ([the proof of the existence of regular families](/chapter/proof-of-regular-families/)). Its plan, in the form of the source: for each $\iota$ with prime $\ell$ it finds one $m$-fold twist $\tau$ with three properties. The norm $\mathrm{Nm}\,Q_\tau$ is prime to $\ell$. For every $j \in [1, m]$, every ramified pair $p$ and every sign $s$, $|\iota(\mathrm{ratio}(p, \tau^j, s)^{-1})|_\ell \leq \exp(\varepsilon_\ell \log \ell)$, with an error $\varepsilon_\ell$ of the twisting theorem ([the twisting theorem](/chapter/twisting-theorem/)). And for every $j$, $\tau^j$ has denominators at most $\beta_\ell$ for $j$ at $\iota$, with $\beta_\ell$ made of a clearing bound times $\log \ell$ and the $\ell$-adic valuation of the number of standard classes times $\log \ell$ ([the denominator bound](/chapter/denominator-bound/)). The family $\theta$ is then the choice of one such $\tau$ for each $\iota$. The sums over $\ell$ of the errors are bounded by the statements that these errors are negligible.

**Remark (Formalization).** The family of the theorem is not unique, and the source does not construct a particular one: it is obtained by `choose` from an existence statement for each $\iota$. Every use of the theorem in the source takes some regular family and uses only the properties in the definition. So the junk values of `choose` play no role. The name of the theorem has the namespace `New`, not `New.Data`.

### What the later chapters prove from regularity

The definitions of this chapter are the interface between the proof of Theorem C and Volume 12. Three theorems of the later chapters use them. We state them in full.

**Theorem (Height of the inverse ratio at a main pair).** Let $\theta$ be a regular family, $j \in [1, m]$, and $p$ a main pair for $j$. Then the family $\iota \mapsto \mathrm{ratio}(p, \theta(\iota)^j)^{-1}$ has height at most $6 \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount}$.

Lean: `New.Data.heightLe_inv_ratio` (New/OneLift/HeckeValues/TwistedValueHeights.lean)

The proof is in [Hecke values of character lifts](/chapter/hecke-values/). Up to a power of $\mathrm{Nm}\,Q$, the inverse ratio is $\|\varphi_1\|^2/\|\varphi_\vartheta\|^2$ by Section 4. With test forms $\Xi, \Xi'$ it is written as a product of an inner product of projections, bounded by the second condition of small denominators, and of factors with known divisibility. 
**Theorem (Height of one lift determinant).** Let $\theta$ be a regular family and $j \in [1, m]$. Then the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ of quotients of lift determinants has height at most $d \cdot k \cdot (\log b \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount})$, with $d$ the dimension of the good forms.

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean)

The proof is in [the height of one lift determinant](/chapter/lift-volume-height/).

**Theorem (Single lifts at good twists).** There is a family $\theta$ of $m$-fold twists with small ratios such that for every $j \in [1, m]$ the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most $d\,(f a \log^4 b / m - k \cdot \mathrm{directionAmount})$.

Lean: `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (New/Determinant/Twist/LongForms.lean)

*Proof.* Take a regular family by the theorem on existence. It has small ratios. Apply the theorem on the height of one lift determinant and the identity $k \cdot \log b \cdot \mathrm{denominatorBudget} = f a \log^4 b/m$ of the example on the budget. $\square$

The file of this theorem belongs to [the proof of Theorem C](/chapter/proof-of-theorem-c/). The proof above is a place where the existence theorem, and with it Volume 12, enters the proof of Theorem C.
