---
title: The supersingular coefficient
lean:
  - New/Derivatives/FormalGroup/FrobeniusCongruence.lean
decls:
  - New.CMLattice.derivative_pow_mul_derivative_taylorVia_translatedX
  - New.CMLattice.norm_coeff_pow_taylorVia_translatedX_recursion_lt_one
  - New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The supersingular coefficient

At an inert prime $p$, Section 4 finds the exponent $\Xi \equiv \lambda Y^{p+1}$ modulo $p$. It needs that $\lambda$ is a unit. Step 4 of Section 4 reduces this to one coefficient of the series $x$: the coefficient of $z^{p-1}$. This section proves that this coefficient is a unit. The proof is independent of the Frobenius congruence. It uses only the differential equation of $x$ and the integrality of $\mathfrak{o}[[y]]$ below the degree $q_p = p^2$.

We keep the setting of Section 2: a prime $d \equiv 7 \bmod 8$, a CM lattice $C$ for $d$, and the coordinates $x$ and $y$ of [Volume 3](/decl/New.CMLattice.weierstrass_equation/), with $y^2 + a_1xy = x^3 + x$, $x = z^2 + \cdots$ and $x' = 2y + a_1x$. Write $h_n$ for the coefficient of $z^{p-1}$ in $x^n$.

### The differential equation of x

**Lemma (Derivatives of x).** Let $\iota$ be a ring homomorphism from $\mathbb{C}$ to a field $F$ of characteristic $0$, and let $x$ be the Taylor series of $\wp(z + t) - \wp(t)$ with coefficients mapped by $\iota$. Then
$$x'^2 = 4x^3 + a_1^2x^2 + 4x, \qquad x'' = 6x^2 + a_1^2x + 2,$$
and for every $n \in \mathbb{N}$,
$$\bigl(x^n x'\bigr)' = (4n + 6)\,x^{n+2} + (n+1)\,a_1^2\,x^{n+1} + (4n + 2)\,x^n,$$
where $a_1$ means $\iota(a_1)$.

Lean: `New.CMLattice.derivative_pow_mul_derivative_taylorVia_translatedX` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean), with `New.CMLattice.derivative_taylorVia_translatedX_sq` and `New.CMLattice.derivative_derivative_taylorVia_translatedX`.

*Proof.* From $x' = 2y + a_1x$ we get $x'^2 = 4y^2 + 4a_1xy + a_1^2x^2 = 4(x^3 + x) + a_1^2x^2$ by the cubic. For the second identity, differentiate $x' = 2y + a_1x$ and use the formula for $y'$ of Volume 3. For the third,
$$\bigl(x^nx'\bigr)' = n x^{n-1}x'^2 + x^n x'' = n x^{n-1}\bigl(4x^3 + a_1^2x^2 + 4x\bigr) + x^n\bigl(6x^2 + a_1^2x + 2\bigr),$$
and the terms collect as stated. For $n = 0$ the first term is absent, and the formula reads $x'' = 6x^2 + a_1^2x + 2$. $\square$

The lemma holds over any field of characteristic $0$. The source applies it with $F = \mathbb{C}_p$ and $\iota = \iota_p$.

### A recursion modulo the maximal ideal

**Lemma (Recursion).** Let $\chi_K(p) = -1$. For every $n \in \mathbb{N}$,
$$\bigl|(4n+6)\,h_{n+2} + (n+1)\,a_1^2\,h_{n+1} + (4n+2)\,h_n\bigr| < 1.$$

Lean: `New.CMLattice.norm_coeff_pow_taylorVia_translatedX_recursion_lt_one` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* By the last lemma, the number in the bars is the coefficient of $z^{p-1}$ in $F'$, where $F = x^nx'$. For any series, $[z^{p-1}]F' = p\,[z^p]F$. The series $x$ lies in $\mathfrak{o}[[y]]$, and so does $x'$, since the ring $\mathfrak{o}[[y]]$ is closed under the derivative (`New.CMLattice.derivative_mem_integralSeriesRing`). So $F \in \mathfrak{o}[[y]]$. Its coefficients below the degree $q_p = p^2$ are integral (Section 2), and $p < p^2$. Hence $|[z^p]F| \le 1$ and $|p\,[z^p]F| \le 1/p < 1$. $\square$

The proof uses $p < q_p$ in an essential way. At $p = d$ we have $q_p = p$, the coefficient $[z^p]F$ need not be integral, and the lemma is not claimed.

### The coefficient is a unit

**Theorem (Supersingular coefficient).** Let $\chi_K(p) = -1$. Then the coefficient of $z^{p-1}$ in $x$ has norm $1$:
$$|h_1| = \bigl|[z^{p-1}]\,x\bigr| = 1.$$

Lean: `New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean), with `New.CMLattice.norm_coeff_pow_taylorVia_translatedX_lt_one` and `New.CMLattice.coeff_two_mul_taylorVia_translatedX_pow`.

*Proof.* The prime $p$ is odd. Write $p = 2m + 1$. Since $p - 1 < q_p$, the coefficient $h_1$ is integral, so $|h_1| \le 1$. Assume $|h_1| < 1$. We show by induction that $|h_n| < 1$ for all $n \le m$.

For $n = 0$, $h_0$ is the coefficient of $z^{p-1}$ in $1$, which is $0$ since $p > 1$. For $n = 1$ this is the assumption. Let $n + 2 \le m$, and assume $|h_n| < 1$ and $|h_{n+1}| < 1$. The factor $4n + 6 = 2(2n + 3)$ is a unit, since $p$ is odd and $0 < 2n + 3 \le 2m - 1 < p$. The factors $n + 1$, $4n + 2$ and $a_1^2$ are integral; for $a_1$ this is the [bound on $a_1$](/decl/New.CMLattice.norm_a₁_le_one/) of Volume 3. By the recursion and the ultrametric inequality,
$$|h_{n+2}| = |(4n+6)h_{n+2}| \le \max\Bigl(\bigl|(4n+6)h_{n+2} + (n+1)a_1^2h_{n+1} + (4n+2)h_n\bigr|,\ \bigl|(n+1)a_1^2h_{n+1} + (4n+2)h_n\bigr|\Bigr) < 1.$$
This proves $|h_m| < 1$.

But $x = z^2u$ with $u(0) = 1$, since $x = z^2 + \cdots$. So $x^m = z^{2m}u^m$, and the coefficient of $z^{2m} = z^{p-1}$ in $x^m$ is $u(0)^m = 1$. Thus $h_m = 1$, a contradiction. $\square$

The recursion is a three-term relation, and it would allow $h_1 \equiv 0$ if the chain did not end at $h_m = 1$. The chain runs over $n + 2 \le m$, exactly the range where $4n + 6$ is prime to $p$. At $n + 2 = m + 1$ the factor is $4(m - 1) + 6 = 2p$, and the recursion stops carrying information.

### Small cases

**Example.** Let $p = 3$. Then $m = 1$, and the theorem says $|[z^2]x| = 1$. This is direct: $[z^2]x = 1$. The recursion is not needed.

**Example.** Let $p = 5$. This prime is inert for $d = 7$, since the squares modulo $7$ are $1$, $2$ and $4$. Here $m = 2$, and the recursion at $n = 0$ reads $6h_2 + a_1^2h_1 + 2h_0 \equiv 0$ modulo the maximal ideal. With $h_0 = 0$ and $h_2 = [z^4]x^2 = 1$, it gives
$$a_1^2\,h_1 \equiv -6 \equiv -1 \pmod{\mathfrak{m}}.$$
So $h_1$ is a unit, and so is $a_1$. For $p = 5$ the proof gives more than the theorem: it determines $h_1$ modulo $\mathfrak{m}$ as $-a_1^{-2}$.

**Example.** For $p = 7$ the recursion at $n = 0$ and $n = 1$ gives $6h_2 \equiv -a_1^2h_1$ and $10h_3 \equiv -2a_1^2h_2 - 6h_1$, with $h_3 = 1$. If $h_1 \equiv 0$, the first relation gives $h_2 \equiv 0$, and then the second gives $10 \equiv 0$ modulo $7$, which is false. The prime $7$ is ramified for $d = 7$, but it is inert for other $d$, for example $d = 23$, where the squares modulo $23$ are $1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18$ and $7$ is not among them.

**Remark (Formalization).** The theorem is stated with norms: "$|h_1| = 1$" in place of "$h_1$ is a unit of $\mathfrak{o}$". The source does not mention the reduction of the curve or its Hasse invariant. The name "supersingular" is only a guide to the reader: an inert prime is a prime of supersingular reduction for a curve with complex multiplication by $\mathcal{O}_K$. The source uses the theorem once, in the proof that the coefficient of $z^{p+1}$ in the exponent is a unit (Section 4). The lemma on the derivatives of $x$ is stated for every field $F$ of characteristic $0$ and every $\iota : \mathbb{C} \to F$. The other two results use the instance $\iota_p$ of `New.PadicPlace p`.
