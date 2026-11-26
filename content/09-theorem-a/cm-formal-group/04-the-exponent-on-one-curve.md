---
title: The exponent on one curve
lean:
  - New/Derivatives/FormalGroup/Exponent.lean
decls:
  - New.leastFlatDegree
  - New.CMLattice.negLogThetaPart
  - New.CMLattice.exponentSeries
  - New.ramified_or_inert
  - New.CMLattice.expSubst_negLogThetaPart_sub_mem
  - New.CMLattice.exists_rescale_theta_eq_mul_expSubst
  - New.CMLattice.exists_smul_negLogThetaPart_sub_rescale_eq
  - New.CMLattice.exists_functional_equation_exponentSeries
  - New.CMLattice.norm_coeff_exponentSeries_sub_le
  - New.CMLattice.exists_seriesToCp_eq_exponentSeries_of_inert
  - New.CMLattice.exists_seriesToCp_eq_exponentSeries_of_ramified
  - New.C_dvd_pow_sub_primePowerSeries_odd_mul_even
  - New.CMLattice.norm_coeff_exponentSeries_eq_one
  - New.CMLattice.exists_eq_exponentSeries_dvd_sub_tsum_of_inert
  - New.CMLattice.exists_exponentSeries_tsum_of_ramified
  - New.CMLattice.exists_exponent_tsum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The exponent on one curve

This section proves the main result on one curve. At a nonsplit prime $p$ there is a scale $\varpi$ of valuation $\rho_p$ such that $\theta(\varpi z)$ is an integral series times $\exp(c_\varpi\Xi)$, where $\Xi$ is integral and is known modulo $\pi_p$. The result is used in Section 6, where the exponents of the factors of a theta product are added.

The proof has four steps. Step 1 averages $g = -\log\theta$ over roots of unity. Step 2 derives a functional equation from the Frobenius congruence of Section 2. Step 3 solves the equation modulo $\pi_p$. Step 4 shows that the leading coefficient is a unit at an inert prime, with the theorem of Section 3.

We keep the setting of Section 2, and we write $\pi = \iota_p(\pi_p)$, $q = q_p$, $\rho = \rho_p$, and $c_\varpi = \varpi^{p+1}/p$.

### The degrees that matter

**Definition (Least flat degree, flat part, exponent).** Let $d$ and $p$ be natural numbers.

1. The *least flat degree* is $i_0 = 2$ if $p = d$, and $i_0 = p + 1$ otherwise.
2. The *flat part* $g^\flat$ of $g = -\log\theta$ is its part in the degrees $n \equiv p + 1 \bmod q - 1$: the coefficient of $z^n$ in $g^\flat$ is $g_n$ if $n \equiv p + 1 \bmod q - 1$, and $0$ otherwise.
3. For $\varpi \in \mathbb{C}_p$, the *exponent* is $\Xi_1 = -c_\varpi^{-1}\, g^\flat(\varpi z)$.

Lean: `New.leastFlatDegree`, `New.CMLattice.negLogThetaPart`, `New.CMLattice.exponentSeries` (New/Derivatives/FormalGroup/Exponent.lean), with `New.congruencePart`.

**Lemma (Ramified or inert).** Let $\chi_K(p) \ne 1$. Then either $p = d$ and $q = p$, or $p \ne d$, $\chi_K(p) = -1$ and $q = p^2$. In both cases:

1. $i_0 < q - 1$, and $p + 1 \equiv i_0 \bmod q - 1$;
2. if $\varpi \ne 0$ and $|\varpi|^{q-1} = |\pi|$, then $\bigl|\pi\varpi^{i_0}/(q\,c_\varpi)\bigr| = 1$;
3. $|\pi^n/q| \le |\pi|$ for every $n > 2$.

Lean: `New.ramified_or_inert`, `New.leastFlatDegree_lt`, `New.add_one_modEq_leastFlatDegree`, `New.norm_piPrime_mul_pow_leastFlatDegree_div`, `New.norm_piPrime_pow_div_le` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* The cases come from $\chi_K(p) \in \{0, -1\}$. (1) If $p = d$, then $q - 1 = p - 1 \ge 6$ since $d \equiv 7 \bmod 8$, and $p + 1 = (p - 1) + 2$. If $p$ is inert, $p + 1 < p^2 - 1$ since $p \ge 3$. (2) If $p$ is inert, $\pi\varpi^{p+1}/(p^2\varpi^{p+1}/p) = 1$. If $p = d$, the number is $\pi/\varpi^{p-1}$, and $|\varpi|^{p-1} = |\pi|$. (3) The number $\pi^n/q$ is $p^{n-2}$ if $p$ is inert, and $-\pi^{n-2}$ if $p = d$, since then $\pi^2 = -p$. $\square$

So the degree $p + 1$ of the coupling $z^p\cdot z$ is the least positive degree $\equiv p + 1$ at an inert prime. At $p = d$ the least such degree is $2$, and $z^2$ is the coupling with $e = 0$.

### Step 1: averaging

The averaging uses the following result of Volume 3, from [the chapter on CM elliptic curves](/chapter/cm-elliptic-curves/): if $\zeta^{q-1} = 1$, then $\exp\bigl(\zeta^{-(p+1)}g(\zeta z) - g(z)\bigr) \in \mathfrak{o}[[y]]$ (`New.CMLattice.expSubst_rescale_sub_mem_of_pow_eq_one`).

**Lemma (Averaging).** The series $\exp(g^\flat - g) = \theta\,\exp(g^\flat)$ lies in $\mathfrak{o}[[y]]$.

Lean: `New.CMLattice.expSubst_negLogThetaPart_sub_mem` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* Let $\zeta$ be a primitive $(q-1)$-th root of unity in $\mathbb{C}_p$. The part of a series in the degrees $\equiv r \bmod m$ is the mean of $\eta^{-r}f(\eta z)$ over the $m$-th roots of unity $\eta$ (`New.congruencePart_eq_sum`). So
$$(q - 1)(g^\flat - g) = \sum_{i=0}^{q-2}\Bigl(\zeta^{-i(p+1)}g(\zeta^i z) - g(z)\Bigr),$$
and $\exp(g^\flat - g)^{q-1}$ is the product of the exponentials of the terms. Each factor lies in $\mathfrak{o}[[y]]$ by the result of Volume 3. The number $q - 1$ is prime to $p$. A series $b$ with $b(0) = 1$ and $b^m \in \mathfrak{o}[[y]]$, with $m$ prime to $p$, lies in $\mathfrak{o}[[y]]$, since $(1 + X)^{1/m}$ has integral coefficients (`New.IsSeriesGenerator.expSubst_mem_of_pow_mem`). $\square$

**Lemma (Splitting off the exponential).** Let $\varpi \ne 0$ with $|\varpi| \le p^{-\rho}$. There is an integral series $W$ with
$$\theta(\varpi z) = W\,\exp\bigl(c_\varpi\,\Xi_1\bigr).$$

Lean: `New.CMLattice.exists_rescale_theta_eq_mul_expSubst` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* We have $\theta = \exp(-g) = \exp(g^\flat - g)\exp(-g^\flat)$. Every element of $\mathfrak{o}[[y]]$ stays integral after the substitution $z \mapsto \varpi z$ with $|\varpi| \le p^{-\rho}$ (`New.CMLattice.rescale_mem_range_seriesToCp`, a consequence of the [theorem on the formal parameter](/decl/New.CMLattice.exists_scaled_formalParam/)). So $W = \exp(g^\flat - g)(\varpi z)$ is integral, by the last lemma. The other factor is $\exp(-g^\flat(\varpi z)) = \exp(c_\varpi\Xi_1)$ by the definition of $\Xi_1$. $\square$

### Step 2: the functional equation

**Lemma (Frobenius congruence for the flat part).** Let $\chi_K(p) \ne 1$. There are $\lambda \in \mathfrak{o}$ and $H \in \mathfrak{o}[[y]]$ with
$$q\,g^\flat(z) - g^\flat(\pi z) = \pi\Bigl(\lambda\,T^{i_0} + T^{\,i_0 + q - 1}H\Bigr),$$
where $T$ is the formal parameter of Volume 3.

Lean: `New.CMLattice.exists_smul_negLogThetaPart_sub_rescale_eq` (New/Derivatives/FormalGroup/Exponent.lean), with `New.CMLattice.exists_congruencePart_eq_smul_formalParam_pow_add`.

*Proof.* By the [logarithmic form](/decl/New.CMLattice.exists_negLogTheta_frobenius_congruence/) of the Frobenius congruence, $qg - g(\pi z) = \pi G$ with $G \in \mathfrak{o}[[y]]$. Taking the part in the degrees $\equiv p + 1$ commutes with $f \mapsto qf - f(\pi z)$, since this map acts on each coefficient alone. So the left side is $\pi$ times the part of $G$ in the degrees $\equiv p + 1 \equiv i_0$. Write $G = \sum_k b_kT^k$ with $b_k \in \mathfrak{o}$. The series $T$ has only terms in the degrees $\equiv 1 \bmod q - 1$. So the part of $G$ in the degrees $\equiv i_0$ is $\sum_{k \equiv i_0} b_kT^k$. Since $0 < i_0 < q - 1$, this is $b_{i_0}T^{i_0} + T^{i_0 + q - 1}H$. $\square$

**Lemma (Functional equation).** Let $\chi_K(p) \ne 1$, let $|\varpi| = p^{-\rho}$, and let $Y$ be an integral series with $T(\varpi z) = \varpi Y$. There is $\lambda \in \mathfrak{o}$ such that for every $n$,
$$\Bigl|\bigl(1 - \pi^n/q\bigr)\,[z^n]\,\Xi_1 - \lambda\,[z^n]\,Y^{i_0}\Bigr| \le |\pi|.$$

Lean: `New.CMLattice.exists_functional_equation_exponentSeries` (New/Derivatives/FormalGroup/Exponent.lean), with `New.CMLattice.exists_smul_rescale_negLogThetaPart_sub_rescale_eq`.

*Proof.* Substitute $\varpi z$ for $z$ in the last lemma. Then $T(\varpi z) = \varpi Y$, and $H(\varpi z) = V$ is integral, as in Step 1. So
$$q\,g^\flat(\varpi z) - g^\flat(\pi\varpi z) = \pi\varpi^{i_0}\Bigl(\lambda_0 Y^{i_0} + \varpi^{q-1}R\Bigr), \qquad R = Y^{i_0 + q - 1}V.$$
The left side is $-c_\varpi\bigl(q\,\Xi_1 - \Xi_1(\pi z)\bigr)$, and its coefficient of $z^n$ is $-c_\varpi(q - \pi^n)[z^n]\Xi_1$. Divide by $-q\,c_\varpi$. With $u = -\pi\varpi^{i_0}/(q\,c_\varpi)$ we get
$$\bigl(1 - \pi^n/q\bigr)[z^n]\Xi_1 = u\lambda_0\,[z^n]Y^{i_0} + u\,\varpi^{q-1}\,[z^n]R.$$
By item 2 of the first lemma, $|u| = 1$, since $|\varpi|^{q-1} = p^{-(q-1)\rho} = |\pi|$. So $\lambda = u\lambda_0$ lies in $\mathfrak{o}$, and the last term has norm at most $|\pi|$. $\square$

For inert $p$ the unit is $u = -1$. At $p = d$ it is $-\pi/\varpi^{p-1}$, which depends on the choice of $\varpi$.

### Step 3: solving the equation

**Lemma (Solving degree by degree).** Let $\chi_K(p) \ne 1$, and let $a \in \mathfrak{o}$ with $\bigl|(1 - \pi^n/q)[z^n]\Xi_1 - a\bigr| \le |\pi|$. If $n < i_0$ or $n > 2$, then $\bigl|[z^n]\Xi_1 - a\bigr| \le |\pi|$. For $n < i_0$, the coefficient $[z^n]\Xi_1$ is $0$.

Lean: `New.CMLattice.norm_coeff_exponentSeries_sub_le` (New/Derivatives/FormalGroup/Exponent.lean), with `New.CMLattice.coeff_exponentSeries_eq_zero_of_lt`.

*Proof.* If $0 \le n < i_0$, then $n \not\equiv p + 1 \bmod q - 1$, since $i_0 < q - 1$ is the least such degree. So $[z^n]g^\flat = 0$ and $[z^n]\Xi_1 = 0$, and the claim is the hypothesis. If $n > 2$, put $t = \pi^n/q$, so $|t| \le |\pi| < 1$ and $|1 - t| = 1$. Then $|(1-t)[z^n]\Xi_1| \le 1$, so $[z^n]\Xi_1$ is integral, and $|[z^n]\Xi_1 - a| \le \max\bigl(|(1-t)[z^n]\Xi_1 - a|, |t\,[z^n]\Xi_1|\bigr) \le |\pi|$. $\square$

At an inert prime $i_0 = p + 1 \ge 4$, and every $n$ satisfies $n < i_0$ or $n > 2$. At $p = d$ the degree $n = 2$ is left. There $1 - \pi^2/q = 1 + p/p = 2$.

**Proposition (Solution at an inert prime).** Let $\chi_K(p) = -1$, let $|\varpi| = p^{-\rho}$, and let $Y$ be integral with $T(\varpi z) = \varpi Y$. There are an integral series $\Xi$ and $\lambda \in \mathfrak{o}$ with $\Xi = \Xi_1$ and $\Xi \equiv \lambda\,Y^{p+1}$ modulo $\pi$.

Lean: `New.CMLattice.exists_seriesToCp_eq_exponentSeries_of_inert` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* The last two lemmas give $|[z^n]\Xi_1 - \lambda[z^n]Y^{p+1}| \le |\pi|$ for all $n$. So $\Xi_1$ is integral, and it is $\equiv \lambda Y^{p+1}$ modulo $\pi$ (`New.exists_seriesToCp_eq_and_C_dvd_sub`). $\square$

**Proposition (Solution at the ramified prime).** Let $p = d$, let $|\varpi| = p^{-\rho}$, let $Y$ be integral with $T(\varpi z) = \varpi Y$ and $[z^2]Y^2 \equiv 1$ modulo $\pi$, and let $\frac12 \in \mathfrak{o}$ be the inverse of $2$. There are an integral series $\Xi$ and $\lambda \in \mathfrak{o}$ with $\Xi = \Xi_1$ and
$$\Xi \equiv \lambda\Bigl(Y^2 - \tfrac12 z^2\Bigr) \pmod{\pi}.$$

Lean: `New.CMLattice.exists_seriesToCp_eq_exponentSeries_of_ramified` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* For $n \ne 2$ argue as in the inert case. For $n = 2$ the functional equation gives $|2x - \lambda c| \le |\pi|$, where $x = [z^2]\Xi_1$ and $c = [z^2]Y^2$. Then
$$x - \lambda\bigl(c - \tfrac12\bigr) = \tfrac12\Bigl((2x - \lambda c) + \lambda(1 - c)\Bigr),$$
and both terms in the bracket have norm at most $|\pi|$. The coefficient of $z^2$ in $Y^2 - \frac12 z^2$ is $c - \frac12$. $\square$

### Reduction modulo the prime

The ring $\mathfrak{o}/\pi\mathfrak{o}$ is nonzero, since $|\pi| < 1$, and it has characteristic $p$, since $\pi$ divides $p$. By the [theorem on the formal parameter](/decl/New.CMLattice.exists_scaled_formalParam/), $Y \equiv \sum_{j \ge 0} z^{q^j}$ modulo $\pi$. In characteristic $p$ the series $\sum_{i \in I} z^{p^i}$ is the [prime power series](/decl/New.primePowerSeries/) $P_I$ of Volume 7, and $P_I^{\,p} = P_{I + 1}$.

**Lemma (Reduction of the powers of Y).** Assume $Y \equiv \sum_{j} z^{q^j}$ modulo $\pi$. If $q = p^2$, then $Y^{p+1} \equiv P_{\mathrm{odd}}\,P_{\mathrm{even}}$ modulo $\pi$. If $q = p$, then $Y^2 \equiv P_{\mathbb{N}}^{\,2}$ modulo $\pi$.

Lean: `New.C_dvd_pow_sub_primePowerSeries_odd_mul_even`, `New.C_dvd_sq_sub_primePowerSeries_univ_sq` (New/Derivatives/FormalGroup/Exponent.lean), with `New.map_reducePiPrime_eq_primePowerSeries`.

*Proof.* If $q = p^2$, the powers of $q$ are the $p^i$ with $i$ even, so $Y \equiv P_{\mathrm{even}}$. Then $Y^{p+1} = Y^p\cdot Y \equiv P_{\mathrm{even}}^{\,p}P_{\mathrm{even}} = P_{\mathrm{odd}}P_{\mathrm{even}}$. If $q = p$, then $Y \equiv P_{\mathbb{N}}$. $\square$

The products expand into couplings. For $p \ne 2$,
$$P_{\mathrm{odd}}P_{\mathrm{even}} = \sum_{e \text{ odd}}\sum_{j \ge 0}\bigl(z^{p^e}z\bigr)^{p^j}, \qquad P_{\mathbb{N}}^{\,2} - \tfrac12 z^2 = \tfrac12 z^2 + \sum_{j \ge 1}\bigl(z^2\bigr)^{p^j} + 2\sum_{e \ge 1}\sum_{j \ge 0}\bigl(z^{p^e}z\bigr)^{p^j}.$$
The first identity holds because $z^{p^a + p^b}$ with $a$ odd and $b$ even is $(z^{p^e}z)^{p^j}$ with $e = |a - b|$ and $j = \min(a, b)$, and this pair is unique: $a \ne b$, and the base-$p$ expansion of $p^a + p^b$ has the digit $1$ in the places $a$ and $b$ and $0$ elsewhere. For the second, $P_{\mathbb{N}}^2 = \sum_a z^{2p^a} + 2\sum_{a < b}z^{p^a + p^b}$. These are `New.hasSum_primePowerSeries_odd_mul_even` and `New.hasSum_primePowerSeries_univ_sq_sub` of Lib.

### Step 4: the unit

**Lemma (Unit coefficient).** Let $\chi_K(p) = -1$ and $\varpi \ne 0$. Then $\bigl|[z^{p+1}]\,\Xi_1\bigr| = 1$.

Lean: `New.CMLattice.norm_coeff_exponentSeries_eq_one` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* The degree $p + 1$ is $\equiv p + 1$, so $[z^{p+1}]\Xi_1 = -c_\varpi^{-1}\varpi^{p+1}g_{p+1} = -p\,g_{p+1}$. The [lemma on the logarithm of theta](/decl/New.CMLattice.derivative_derivative_negLogTheta/) gives $x_{p-1} = (p+1)p\,g_{p+1}$. The factor $p + 1$ is a unit. So $|[z^{p+1}]\Xi_1| = |x_{p-1}| = 1$ by the [theorem of Section 3](/decl/New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one/). $\square$

The value of $\varpi$ cancels. The unit comes from the curve alone: it is the coefficient of $z^{p-1}$ in $x$, up to the unit $-(p+1)^{-1}$.

### The theorems

**Theorem (Exponent at an inert prime).** Let $\chi_K(p) = -1$, let $|\varpi| = p^{-\rho}$, and let $Y$ be integral with $T(\varpi z) = \varpi Y$ and $Y \equiv \sum_j z^{q^j}$ modulo $\pi$. There are an integral series $\Xi$ and a unit $\lambda$ of $\mathfrak{o}$ with $\Xi = \Xi_1$ and
$$\Xi \equiv \sum_{e \text{ odd}}\sum_{j \ge 0}\lambda\,\bigl(z^{p^e}z\bigr)^{p^j} \pmod{\pi}.$$

Lean: `New.CMLattice.exists_eq_exponentSeries_dvd_sub_tsum_of_inert` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* Combine the solution at an inert prime, the reduction of $Y^{p+1}$, and the first expansion. The coefficient of $z^{p+1}$ on the right is $\lambda$ ($e = 1$, $j = 0$). So $\lambda \equiv [z^{p+1}]\Xi$, which is a unit by Step 4. A number congruent to a unit modulo $\pi$ is a unit. $\square$

**Theorem (Exponent at the ramified prime).** Let $p = d$, let $|\varpi| = p^{-\rho}$, let $Y$ be as in the last theorem, and let $\frac12$ be the inverse of $2$ in $\mathfrak{o}$. There are an integral series $\Xi$ and $\lambda \in \mathfrak{o}$ with $\Xi = \Xi_1$ and
$$\Xi \equiv \sum_{e \ge 0}\sum_{j \ge 0}\lambda_{ej}\bigl(z^{p^e}z\bigr)^{p^j} \pmod{\pi}, \qquad \lambda_{00} = \tfrac12\lambda,\quad \lambda_{0j} = \lambda\ (j \ge 1),\quad \lambda_{ej} = 2\lambda\ (e \ge 1).$$

Lean: `New.CMLattice.exists_exponentSeries_tsum_of_ramified` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* The congruence $Y^2 \equiv P_{\mathbb{N}}^2$ gives $[z^2]Y^2 \equiv 1$. Apply the solution at the ramified prime and the second expansion. $\square$

**Theorem (The exponent on one curve).** Let $d \equiv 7 \bmod 8$ be a prime, $C$ a CM lattice for $d$, and $p$ a prime with $\chi_K(p) \ne 1$. There are $\varpi \in \mathbb{C}_p$, integral series $\Xi$ and $W$, and numbers $\lambda_{ej} \in \mathfrak{o}$ for $e, j \in \mathbb{N}$, such that:

1. $|\varpi| = p^{-\rho_p}$;
2. $\Xi(0) = 0$;
3. $\theta(\varpi z) = W\,\exp\bigl(c_\varpi\,\Xi\bigr)$ with $c_\varpi = \varpi^{p+1}/p$;
4. $\Xi \equiv \sum_{e \in I_p^\circ}\sum_{j \ge 0}\lambda_{ej}\bigl(z^{p^e}z\bigr)^{p^j}$ modulo $\pi_p$;
5. if $\chi_K(p) = -1$, then $\lambda_{e0}$ is a unit for every odd $e$.

Lean: `New.CMLattice.exists_exponent_tsum` (New/Derivatives/FormalGroup/Exponent.lean).

*Proof.* Take $\varpi$ and $Y$ from the [theorem on the formal parameter](/decl/New.CMLattice.exists_scaled_formalParam/), and $W$ from Step 1. If $p = d$, then $I_p^\circ = \mathbb{N}$; take $\Xi$ and $\lambda_{ej}$ from the theorem at the ramified prime, and item 5 is void. If $p$ is inert, $I_p^\circ$ is the set of odd numbers; take $\Xi$ and $\lambda$ from the theorem at an inert prime, and $\lambda_{ej} = \lambda$ for all $e, j$. In both cases $\Xi(0) = [z^0]\Xi_1 = 0$, since $0 < i_0$. $\square$

**Example.** Let $p = d = 7$. Then $\pi = \sqrt{-7}$, $q = 7$, $\rho = 1/12$, $i_0 = 2$ and $c_\varpi = \varpi^8/7$. So $v(c_\varpi) = 8/12 - 1 = -1/3$, and $v(c_\varpi\pi) = 1/6 = 1/(p-1)$. The theorem gives
$$\Xi \equiv \lambda\Bigl(\tfrac12 z^2 + 2z^8 + z^{14} + 2z^{50} + 2z^{56} + z^{98} + \cdots\Bigr) \pmod{\sqrt{-7}}.$$
Here $z^8 = z^{7}z$ ($e = 1$, $j = 0$), $z^{50} = z^{49}z$ ($e = 2$, $j = 0$), and $z^{56} = (z^7z)^7$ ($e = 1$, $j = 1$). The theorem does not say that $\lambda$ is a unit at $p = d$.

**Remark (Formalization).** (1) The number $\varpi$ is taken from the existence statement of Volume 3, and only $|\varpi| = p^{-\rho}$ is kept. The numbers $\lambda_{ej}$ in the theorem have a special form (all equal to $\lambda$, or $\frac12\lambda$, $\lambda$, $2\lambda$), but the theorem states only their existence. Later files obtain $\varpi$, $\Xi$, $W$ and $\lambda_{ej}$ with `obtain`. (2) The sum in item 4 is an infinite sum `tsum` in the topology of coefficientwise convergence. The family is summable, since $(z^{p^e}z)^{p^j}$ has order $(p^e + 1)p^j$, which tends to infinity (`New.summable_smul_X_pow_mul_X_pow`). So the junk value of `tsum` for a family that is not summable does not occur. (3) The congruences modulo $\pi$ in the proof are computed in the ring $\mathfrak{o}/\pi\mathfrak{o}$. The source gives this ring two unnamed instances, `Nontrivial` and `CharP p` ([Exponent.lean](lean:New/Derivatives/FormalGroup/Exponent.lean#L504) and [L510](lean:New/Derivatives/FormalGroup/Exponent.lean#L510)). (4) The theorem does not state $W(0) = 1$, but it follows from $\theta(0) = 1$ and $\Xi(0) = 0$. (5) The module docstring names earlier bounds for one curve at inert primes, by Bannai and Kobayashi, by Bannai, Kobayashi and Yasuda, and by Fujiwara. It says that they are not used. The proof above uses only the results of Volume 3 and of Sections 2 and 3.
