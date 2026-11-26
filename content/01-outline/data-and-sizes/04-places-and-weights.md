---
title: The places and the weights
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/PrimeSums.lean
decls:
  - New.Data.bPlaces
  - New.Parameters.IsSparse
  - New.Data.aPlaces
  - New.Data.card_aPlaces
  - New.Data.weight
  - New.Data.cast_weight
  - New.Data.weight_mem_Icc
  - New.Data.liftWeight
  - New.Data.shiftedWeight_mem_Icc
  - New.Data.totalRemainder_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The places and the weights

The field $E$ has $f$ infinite places, and the theta lifts of the argument carry one weight at each place. This section defines two sets of places, $\Phi_a$ and $\Phi_b$, and the weight $\kappa(\tau)$ of a place $\tau$. The choice of the weights is the device that makes the prime remainder $R_{q_0}(x)$ appear in the covolume of the lattice, with a coefficient that one can control. The section ends with the identity that shows this.

### The group of places

Recall from [fields, places and twists](/chapter/fields-places-twists/) that the infinite places of $E = K(\zeta_{q_1})$ form a group $\Phi$, and that the action on $\zeta_{q_1}$ gives an isomorphism $\Phi \cong (\mathbb{Z}/q_1)^\times$ (`New.Parameters.placeMulEquiv`). For a divisor $q$ of $q_1$, the class of a place $\tau$ modulo $q$ is the image of $\tau$ in $(\mathbb{Z}/q)^\times$ (`New.Parameters.placeClass`). For an integer $\nu$, the place $\nu \cdot 1$ is the place with class $\nu$ if $\nu$ is prime to $q_1$, and the identity place otherwise (`New.Parameters.placeOfInt`).

**Definition (The $a$-places).** The set $\Phi_a$ of $a$-places is the set of places $\tau$ with class $1$ modulo $q_0$.

Lean: `New.Data.aPlaces` (New/Reduction/Data/AdmissibleData.lean).

**Lemma (The number of $a$-places).** One has $\#\Phi_a = \operatorname{towerDeg}(s) = q_1/q_0$, and $f = \#\Phi_a \cdot \varphi(q_0)$.

Lean: `New.Data.card_aPlaces`, `New.Data.f_eq_card_aPlaces_mul` (New/Reduction/PrimeSums.lean).

*Proof.* The reduction map $(\mathbb{Z}/q_1)^\times \to (\mathbb{Z}/q_0)^\times$ is onto, since $q_0 \mid q_1$. Its kernel has $\varphi(q_1)/\varphi(q_0)$ elements. Every prime factor of $\operatorname{towerDeg}(s) = 3 l_0 2^s$ is $2$ or $3$, and both divide $q_0$, since $18480 \mid q_0$. So $q_1 = q_0 \operatorname{towerDeg}(s)$ has the same prime factors as $q_0$, and $\varphi(q_1) = \operatorname{towerDeg}(s)\,\varphi(q_0)$. The kernel is $\Phi_a$, so $\#\Phi_a = \operatorname{towerDeg}(s)$. The second claim is $f = \operatorname{towerDeg}(s)\varphi(q_0)$. $\square$

### The $b$-places

**Definition (The $b$-places).** The data contain a finite set $\Phi_b \subseteq \Phi$ with these properties:

1. every $\sigma \in \Phi_b$ has class $-1$ modulo $q_0$;
2. $\operatorname{towerDeg}(s) \leq \#\Phi_b \cdot \log b$;
3. $\Phi_b$ is sparse for the primes up to $k t$, in the sense of the next definition.

Lean: `New.Data.bPlaces`, `New.Data.placeClass_of_mem_bPlaces`, `New.Data.towerDeg_le_card_bPlaces_mul`, `New.Data.sparse` (New/Reduction/Data/AdmissibleData.lean).

Since $q_0 > 2$, the classes $1$ and $-1$ modulo $q_0$ differ, so $\Phi_a$ and $\Phi_b$ are disjoint. There are $\operatorname{towerDeg}(s)$ places with class $-1$ modulo $q_0$, by the argument of the lemma above applied to the coset of $-1$. So property 2 says that $\Phi_b$ contains at least the fraction $1/\log b$ of the places in its coset. Property 3 limits the multiplicative structure of $\Phi_b$. A set with both properties is of Behrend type.

**Definition (Sparse sets of places).** Let $L \in \mathbb{N}$ and let $T$ be a finite set of places of $E(s)$. The set $T$ is sparse for the primes up to $L$ if the following holds. Let $\ell \leq L$ be a prime, let $q_1'$ be the part of $q_1$ prime to $\ell$, and let $\phi$ be the class map $\Phi \to (\mathbb{Z}/q_1')^\times$. Then for all integers $i$, $j$ with $0 < i < j < l_0$, there are no places $\sigma, \tau, \rho \in T$ and no signs $\varepsilon, \varepsilon' \in \{\pm 1\}$ with
$$\phi(\tau/\sigma) = \varepsilon \ell^i \quad\text{and}\quad \phi(\rho/\sigma) = \varepsilon' \ell^j \qquad\text{in } \mathbb{Z}/q_1' .$$

Lean: `New.Parameters.IsSparse` (New/Reduction/Data/AdmissibleData.lean).

In words: seen from any place $\sigma$ of $T$, at most one power $\ell^i$ with $0 < i < l_0$, up to sign, leads from $\sigma$ to a place of $T$. The places $\sigma$, $\tau$, $\rho$ need not be distinct, and the two signs are independent. So the condition also restricts the order of $\ell$ modulo $q_1'$: with $\sigma = \tau = \rho$ it says that $\ell^i$ and $\ell^j$ are not both $\pm 1$ in $\mathbb{Z}/q_1'$.

**Remark (Formalization).** The condition is stated with the values in $\mathbb{Z}$ of the units: $(\phi(\tau/\sigma)).\mathrm{val} = \varepsilon \ell^i$ is an equation in $\mathbb{Z}/q_1'$, between the residue and the cast of the integer $\varepsilon\ell^i$. The empty set is sparse. The data cannot use it, since property 2 and $\operatorname{towerDeg}(s) > 0$ force $\Phi_b \neq \emptyset$. The sparse condition is used in the bounds for near pairs of derivatives (New/Derivatives/Sharpness/NearPairs.lean) and for the local loss of the congruences (New/Congruences/LocalLoss/Basic.lean). The construction of a set with properties 1 to 3 is in [the data exist](/chapter/data-exist/).

### The weights

**Definition (The weights).** Put $a = x b$. The data contain a weight $\kappa : \Phi \to \mathbb{N}$ with
$$\kappa(\tau) = \begin{cases} b & \text{if } \tau \in \Phi_b, \\ a / x_1 & \text{otherwise.} \end{cases}$$
The number $a/x_1$ is the off weight. For $i, j \in \mathbb{N}$ put
$$\kappa^{(i)}(\sigma) = \kappa(\sigma) + (i + 1)\tfrac12\Delta, \qquad \kappa_j(\sigma) = \kappa^{(2j)}(\sigma) = \kappa(\sigma) + (j + \tfrac12)\Delta .$$
The number $\kappa_j(\sigma)$ is the weight of the character of the $j$-th lift at $\sigma$.

Lean: `New.Data.weight`, `New.Data.weight_eq`, `New.Data.a`, `New.Data.offWeight`, `New.Data.shiftedWeight`, `New.Data.liftWeight` (New/Reduction/Data/AdmissibleData.lean); `New.Data.liftWeight_eq` (New/Reduction/Data/Magnitudes.lean).

The source writes the off weight as $x b / x_1$ in natural numbers, with the division of $\mathbb{N}$, which rounds down.

**Remark (Formalization).** The division $x b / x_1$ in $\mathbb{N}$ is exact. The data ask $q_1 x_1 \mid b$ (`New.Data.dvd_natB`), so $q_1 x_1 \mid x b = a$ (`New.Data.q₁_mul_natX₁_dvd_a`). Hence the off weight equals the real quotient $a/x_1$ (`New.Data.cast_offWeight`), and no rounding error enters. The same divisibility gives $q_1 \mid \kappa(\tau)$ for every place (`New.Data.q₁_dvd_weight`). The identity $\kappa_j = \kappa + j\Delta + \tfrac12\Delta$ is `New.Data.liftWeight_eq`; it holds in $\mathbb{N}$, since $\Delta = 2 \cdot \tfrac12\Delta$ by definition.

**Lemma (The size of the weights).** For every place $\sigma$:

1. $\kappa(\sigma) = a / x$ if $\sigma \in \Phi_b$, and $\kappa(\sigma) = a / x_1$ otherwise, as real numbers;
2. $a/x_1 \leq \kappa(\sigma) \leq a/x = b$;
3. $x^{999} \leq a / x_1 \leq b / x^{999}$;
4. $\kappa(\sigma) + x^{42} \leq 2b$.

Lean: `New.Data.cast_weight` (New/Reduction/Data/Magnitudes.lean); `New.Data.weight_mem_Icc`, `New.Data.weight_le_b`, `New.Data.weight_add_x_pow_le_two_mul_b` (New/Reduction/Data/LevelAndTwists.lean); `New.Data.a_div_x₁_mem_Icc` (New/Reduction/Data/Sizes.lean).

*Proof.* Part 1 is the definition, with $b = a/x$ and the remark above. Part 2 follows from part 1 and $x \leq x_1$. For part 3, $\log(a/x_1) = \log x + \log b - \log x_1$. The lower bound $x^{999}$ needs $998 \log x + \log x_1 \leq \log b$, which follows from (S3) and (S4). The upper bound $b/x^{999}$ needs $1000 \log x \leq \log x_1$, which is (S3). For part 4, $x^{42} \leq b$, since $42 \log x \leq \log b$ by (S3) and (S4), and $\kappa(\sigma) \leq b$. $\square$

So every weight lies between $x^{999}$ and $b$. On the logarithmic scale, $\log \kappa(\sigma)$ is $\log b$ on $\Phi_b$ and $\log b - (\log x_1 - \log x)$ elsewhere. Both are $\log b$ up to a relative error of $10^{-6}$.

**Lemma (The shifted weights).** Let $i \leq 4m$ and $j \leq 2m$. For every place $\sigma$:

1. $\kappa(\sigma) \leq \kappa^{(i)}(\sigma) \leq \kappa(\sigma) + x^{42}$;
2. $\log \kappa^{(i)}(\sigma) \leq \log \kappa(\sigma) + 1/x$;
3. $\kappa_j(\sigma) \leq \kappa(\sigma) + x^{42}$ and $\kappa_j(\sigma) \leq 2b$;
4. $\log \kappa_j(\sigma) \leq \log\kappa(\sigma) + 1/x$.

For every $j \in \mathbb{N}$ one also has $\kappa(\sigma) \leq \kappa_j(\sigma) - \tfrac12\Delta$.

Lean: `New.Data.shiftedWeight_mem_Icc`, `New.Data.log_shiftedWeight_le`, `New.Data.liftWeight_le_weight_add`, `New.Data.liftWeight_le_two_mul_b`, `New.Data.log_liftWeight_le`, `New.Data.weight_le_liftWeight_sub` (New/Reduction/Data/LevelAndTwists.lean).

*Proof.* Part 1: $(i + 1)\tfrac12\Delta \leq (4m + 1) r^8 \leq (8\sqrt x + 1)(3x^5)^8 \leq x^{42}$, since $3^8 \cdot 9 \leq x^{3/2}$. Part 2: by part 1, $\log\kappa^{(i)} \leq \log \kappa + \log(1 + x^{42}/\kappa) \leq \log\kappa + x^{42}/\kappa$. Since $\kappa \geq x^{999} \geq x^{43}$, this is at most $\log\kappa + 1/x$. Parts 3 and 4 are parts 1 and 2 with $i = 2j \leq 4m$, together with part 4 of the previous lemma. The last claim is $\kappa_j = \kappa + j\Delta + \tfrac12\Delta$. $\square$

So on the logarithmic scale the weights $\kappa_0, \dots, \kappa_{2m}$ at one place equal $\kappa$ up to $1/x$.

### Why two weights

The weights are chosen for one identity. The prime sum of the data at a place $\sigma$ is
$$s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu) \Bigl(\frac{y}{\nu} - \kappa(-\nu\sigma)\Bigr)^{+},$$
where $\Lambda_K(\nu) = \Lambda(\nu)(1 - \chi_K(\nu))$ and $-\nu\sigma$ is the product of $\sigma$ with the place of $-\nu$ (`New.Data.primeSum`). At $y = a$, the term of $\nu$ is positive only if $\nu < a/\kappa(-\nu\sigma)$, that is, $\nu < x$ if $-\nu\sigma \in \Phi_b$, and $\nu < x_1$ otherwise. For an $a$-place $\sigma$, the place $-\nu\sigma$ has class $-\nu$ modulo $q_0$. So it can lie in $\Phi_b$ only if $\nu \equiv 1 \pmod {q_0}$. The two weights cut the prime sum at the two lengths $x$ and $x_1$, and the residue class $1$ modulo $q_0$ is separated at length $x$.

**Theorem (The total remainder).** Let $s_{\mathrm{main}} = a\bigl(\log a - \tfrac1f \sum_{\tau} \log\kappa(\tau) + c_1\bigr)$ where $c_1$ is the constant $c_q$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/) for $q = 1$, and let $\operatorname{rem} = \sum_{\tau \in \Phi_a}\bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr)$. Then
$$\operatorname{rem} = a\Bigl(\#\Phi_b \bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a\, R_1(x_1)\Bigr),$$
where $R_q$ is the weighted prime remainder.

Lean: `New.Data.mainPrimeSum`, `New.Data.totalRemainder`, `New.Data.totalRemainder_eq` (New/Reduction/PrimeSums.lean).

The proof is in [prime sums and the total remainder](/chapter/prime-sums/). The identity shows the role of each field of this section. The coefficient of $R_{q_0}(x)$ is $a\,\#\Phi_b$, and property 2 of the $b$-places gives $\#\Phi_a = \operatorname{towerDeg}(s) \leq \#\Phi_b \log b$. So the terms at scale $x_1$, where the prime number theorem makes $R_q$ small, have weight at most $\log b$ times the weight of $R_{q_0}(x)$. A lower bound for the total remainder then gives a lower bound for $R_{q_0}(x)$, after division by $a\,\#\Phi_b$.
