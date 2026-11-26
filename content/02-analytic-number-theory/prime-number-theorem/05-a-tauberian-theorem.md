---
title: A Tauberian theorem
lean:
  - Lib/Analytic/PrimeNumberTheorem/Tauberian.lean
decls:
  - New.iteratedDeriv_transform
  - New.integrableOn_and_integral_pow_mul_exp_neg_mul
  - New.integrableOn_and_integral_gamma_mul_quadratic
  - New.norm_taylorCoeff_transform_sub_le
  - New.norm_iteratedDeriv_dslope_le
  - New.norm_taylorCoeff_dslope_le
  - New.abs_sub_le_of_unit_steps
  - New.norm_taylorCoeff_transform_sub_le_of_lipschitz
  - New.eventually_log_pow_le_and_pow_le_exp_sqrt
  - New.one_sub_le_re_and_norm_le_of_mem_closedBall
  - New.norm_taylorCoeff_dslope_le_inv_pow
  - New.eventually_abs_le_inv_pow_of_transform
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A Tauberian theorem

This section proves the Tauberian theorem of the source. It turns a bound for a function $F$ in a thin region to the left of the line $\operatorname{Re} s = 1$ into a bound $|R(u)| \leq u^{-B}$ for a Lipschitz function $R$ whose Laplace transform is the slope of $F$ at $1$. Section 6 applies it with $R(v) = R_q(e^v)$, the weighted prime remainder at $y = e^v$.

### The idea

Let $R$ be a function on $[0, \infty)$, and let
$$\Phi(s) = \int_0^\infty R(v)\, e^{(1 - s)v}\, dv \qquad (\operatorname{Re} s > 2).$$
Put $s = 1 + z$. Then $\Phi(1 + z)$ is the Laplace transform of $R$ at $z$. Differentiate $k$ times at a real point $z = H > 0$:
$$\frac{(-H)^k H}{k!}\, \Phi^{(k)}(1 + H) = \int_0^\infty R(v)\, \frac{H^{k + 1} v^k e^{-Hv}}{k!}\, dv. \tag{5.1}$$
The weight $g_{k, H}(v) = H^{k + 1} v^k e^{-Hv}/k!$ is the Gamma density with mean $(k + 1)/H$ and variance $(k + 1)/H^2$. Choose $H = (k + 1)/u$. Then the mean is $u$ and the standard deviation is $u/\sqrt{k + 1}$. For large $k$ the density is a narrow peak at $u$, and the left side of (5.1) is close to $R(u)$. This is the inversion formula of Post and Widder for the Laplace transform.

The second reading of the left side uses $F$. If $\Phi(s) = (F(s) - F(1))/(s - 1)$ and $F$ is holomorphic on the disc about $1 + H$ of radius $H + \eta$, then the Cauchy estimate bounds $\Phi^{(k)}(1 + H)$ by $k!$ times $(H + \eta)^{-k}$ times a bound for $\Phi$. Multiply by $H^{k + 1}/k!$: the factor $(H/(H + \eta))^k \approx \exp(-k\eta/H) = \exp(-u\eta)$ appears. So the coefficient is small if $u\eta$ is large. The disc reaches to $1 - \eta$, to the left of the line, and this is where the zero-free region enters. With $\eta = (\log T)^{-A}$ and $u$ a power of $\log T$ the gain $e^{-u\eta}$ beats every power of $u$.

So $R(u)$ is close to a number that is small. The two errors are: the width of the peak, which a Lipschitz condition on $R$ controls, and the Cauchy estimate. Both are powers of $u$.

### The textbook route

The classical proof of an error term goes through Perron's formula and a contour integral: $\psi(x, \chi)$ is an integral of $-L'/L(s, \chi)\, x^s/s$ on a vertical line, and the line is moved to the left into the zero-free region (Davenport, Chapters 17 and 19). Montgomery and Vaughan, Section 6.2, use a contour integral in their Tauberian form, and the source cites that section. The method here replaces the vertical contour by one disc. It needs the function only in a bounded region, and it needs no truncated Perron formula. The error term depends on the width of the region. With the width $l^{-A}$ of Section 4 the gain is $e^{-u l^{-A}}$, and the method gives powers of $u = \log y$. With the classical width $c/l$ the same method gives $\exp(-c'\sqrt u)$ (Exercise 4). The source needs only powers, so it uses the weak region.

### The transform and its derivatives

**Lemma (Derivatives of the transform).** Let $R$ be measurable on $\mathbb{R}$, let $|R(v)| \leq C e^v$ for $v \geq 0$, and let $\Phi(s) = \int_0^\infty R(v) e^{(1 - s)v}\, dv$ for $\operatorname{Re} s > 2$. Then for $k \geq 0$ and $\operatorname{Re} s > 2$ the function $(-v)^k R(v) e^{(1 - s)v}$ is integrable on $(0, \infty)$, and
$$\Phi^{(k)}(s) = \int_0^\infty (-v)^k R(v)\, e^{(1 - s)v}\, dv.$$

Lean: `New.iteratedDeriv_transform` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* By induction on $k$. The case $k = 0$ is the definition, with integrability from $|R(v) e^{(1 - s)v}| \leq C e^{(2 - \operatorname{Re} s)v}$. For the step, differentiate under the integral sign (Mathlib: `hasDerivAt_integral_of_dominated_loc_of_deriv_le`). Choose $\varepsilon > 0$ with $2 + 2\varepsilon < \operatorname{Re} s$. For $\operatorname{Re} z > 2 + 2\varepsilon$, the derivative $-v\,G_k(z, v)$ of the integrand $G_k(z, v) = (-v)^k R(v) e^{(1 - z)v}$ satisfies $|v\,G_k(z, v)| \leq |G_k(2 + \varepsilon, v)|/\varepsilon$, because $\varepsilon v \leq e^{\varepsilon v}$. The right side is integrable by the case $k$. $\square$

**Lemma (Gamma integrals).** Let $H > 0$ and $j \geq 0$. Then $v^j e^{-Hv}$ is integrable on $(0, \infty)$, and
$$\int_0^\infty v^j e^{-Hv}\, dv = \frac{j!}{H^{j + 1}}.$$

Lean: `New.integrableOn_and_integral_pow_mul_exp_neg_mul` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* This is the Laplace transform of $v^j$, from Mathlib. Integrability follows since the integral is not $0$. $\square$

**Lemma (The second moment).** Let $H > 0$, $k \geq 0$ and $a, b$ real. Then $v^k e^{-Hv}(a + b(v - (k + 1)/H)^2)$ is integrable on $(0, \infty)$, and
$$\int_0^\infty v^k e^{-Hv}\Big(a + b\Big(v - \frac{k + 1}{H}\Big)^2\Big)\, dv = \frac{k!}{H^{k + 1}}\Big(a + b\,\frac{k + 1}{H^2}\Big).$$

Lean: `New.integrableOn_and_integral_gamma_mul_quadratic` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* Let $m = (k + 1)/H$. Expand: the integrand is $(a + bm^2) v^k e^{-Hv} - 2bm\, v^{k + 1} e^{-Hv} + b\, v^{k + 2} e^{-Hv}$. By the last lemma the integral is
$$(a + bm^2)\frac{k!}{H^{k + 1}} - 2bm\frac{(k + 1)!}{H^{k + 2}} + b\frac{(k + 2)!}{H^{k + 3}} = \frac{k!}{H^{k + 1}}\Big(a + \frac{b}{H^2}\big((k + 1)^2 - 2(k + 1)^2 + (k + 1)(k + 2)\big)\Big),$$
and the bracket is $k + 1$. $\square$

### The first reading: a mean of R

**Lemma (The coefficient as a mean).** Let $R$, $C$ and $\Phi$ be as in the lemma on derivatives, and let $H > 1$, $k \geq 0$ and $a, b, c$ real. Suppose that
$$|R(v) - c| \leq a + b\Big(v - \frac{k + 1}{H}\Big)^2 \qquad \text{for all } v > 0.$$
Then
$$\Big|\frac{(-H)^k H}{k!}\, \Phi^{(k)}(1 + H) - c\Big| \leq a + b\,\frac{k + 1}{H^2}.$$

Lean: `New.norm_taylorCoeff_transform_sub_le` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* The point $1 + H$ has real part $> 2$. By [the derivatives of the transform](/decl/New.iteratedDeriv_transform/), the left side without $c$ is (5.1), that is $\int_0^\infty g_{k, H}(v) R(v)\, dv$. By [the Gamma integrals](/decl/New.integrableOn_and_integral_pow_mul_exp_neg_mul/) with $j = k$, $\int_0^\infty g_{k, H} = 1$. So the left side is $|\int_0^\infty g_{k, H}(v)(R(v) - c)\, dv|$. Bound $|R(v) - c|$ by the hypothesis, and use [the second moment](/decl/New.integrableOn_and_integral_gamma_mul_quadratic/) times $H^{k + 1}/k!$. $\square$

**Lemma (Unit steps).** Let $L$ be real. If $|R(v) - R(u)| \leq L(v - u)$ for all $0 \leq u \leq v \leq u + 1$, then $|R(v) - R(u)| \leq L|v - u|$ for all $u, v \geq 0$.

Lean: `New.abs_sub_le_of_unit_steps` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* Let $u \leq v$. Cut $[u, v]$ into $n$ equal steps of length at most $1$, and add the $n$ bounds. $\square$

**Lemma (Lipschitz functions).** Let $R$ be measurable, with $|R(y) - R(x)| \leq L|y - x|$ for all $x, y \geq 0$, and let $\Phi$ be its transform. Let $u, \delta > 0$, $k \geq 0$, and $H = (k + 1)/u > 1$. Then
$$\Big|\frac{(-H)^k H}{k!}\, \Phi^{(k)}(1 + H) - R(u)\Big| \leq L\Big(\delta + \frac{u^2}{(k + 1)\delta}\Big).$$

Lean: `New.norm_taylorCoeff_transform_sub_le_of_lipschitz` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* First, $L \geq 0$, and $|R(v)| \leq |R(0)| + Lv \leq (|R(0)| + L)e^v$, so the lemma on derivatives applies. Next, $|v - u| \leq \delta + (v - u)^2/\delta$ for every $v$, since $(|v - u| - \delta)^2 \geq 0$ gives $\delta|v - u| \leq \delta^2/2 + (v - u)^2/2$. So
$$|R(v) - R(u)| \leq L\delta + \frac{L}{\delta}(v - u)^2,$$
and $u = (k + 1)/H$. Apply [the coefficient as a mean](/decl/New.norm_taylorCoeff_transform_sub_le/) with $c = R(u)$, $a = L\delta$ and $b = L/\delta$. The bound is $L\delta + (L/\delta)(k + 1)/H^2 = L(\delta + u^2/((k + 1)\delta))$. $\square$

The choice $\delta = u/\sqrt{k + 1}$ would give $2Lu/\sqrt{k + 1}$, the standard deviation of the peak times $2L$. The source chooses $\delta$ in the final proof.

### The second reading: the Cauchy estimate

Let $F$ be a function on $\mathbb{C}$. The source writes `dslope F 1` for the slope
$$g(s) = \frac{F(s) - F(1)}{s - 1} \quad (s \neq 1), \qquad g(1) = F'(1).$$

**Lemma (Derivatives of the slope).** Let $H \geq 0$, $\eta > 0$ and $M$ real. Suppose that $F$ is complex differentiable at each point of the closed disc $D$ about $1 + H$ of radius $H + \eta$, with $|F| \leq M$ on $D$. Then for every $k \geq 0$,
$$|g^{(k)}(1 + H)| \leq k!\,\frac{2M/\eta}{(H + \eta)^k}.$$

Lean: `New.norm_iteratedDeriv_dslope_le` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* The point $1$ is inside $D$, so $g$ is holomorphic on a neighbourhood of $D$. On the boundary circle, $|s - 1| \geq (H + \eta) - H = \eta$, so $|g(s)| \leq (|F(s)| + |F(1)|)/\eta \leq 2M/\eta$. The Cauchy estimate on that circle (Mathlib: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) gives the bound. $\square$

**Lemma (The coefficient is small).** Let $0 < \eta \leq H$, and let $F$ and $M$ be as in the last lemma. Then
$$\Big|\frac{(-H)^k H}{k!}\, g^{(k)}(1 + H)\Big| \leq \frac{4MH}{\eta}\exp\Big(-\frac{(k + 1)\eta}{2H}\Big).$$

Lean: `New.norm_taylorCoeff_dslope_le` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* By the last lemma the left side is at most
$$\frac{2MH}{\eta}\Big(\frac{H}{H + \eta}\Big)^k = \frac{2M(H + \eta)}{\eta}\Big(\frac{H}{H + \eta}\Big)^{k + 1} \leq \frac{4MH}{\eta}\Big(\frac{H}{H + \eta}\Big)^{k + 1}.$$
Let $x = \eta/H \in (0, 1]$. Then $\log(1 + x) \geq x/2$, so $H/(H + \eta) = (1 + x)^{-1} \leq e^{-x/2}$. $\square$

**Lemma (The disc).** Let $H \geq 0$ and $\eta$ real, and let $|s - (1 + H)| \leq H + \eta$. Then $\operatorname{Re} s \geq 1 - \eta$ and $|s| \leq 2H + \eta + 1$.

Lean: `New.one_sub_le_re_and_norm_le_of_mem_closedBall` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* $|\operatorname{Re} s - (1 + H)| \leq |s - (1 + H)| \leq H + \eta$, and $|s| \leq |s - (1 + H)| + 1 + H$. $\square$

**Lemma (Growth comparisons).** Let $c$ be real and $A, j \geq 0$ natural numbers. For all large $u$,
$$(c \log u)^{2A} \leq u \qquad \text{and} \qquad u^j \leq e^{\sqrt u/2}.$$

Lean: `New.eventually_log_pow_le_and_pow_le_exp_sqrt` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* A power of $\log u$ is $o(u)$, and a power of $t$ is $o(e^{t/2})$; take $t = \sqrt u$ and $t^{2j} = u^j$. $\square$

**Lemma (The coefficient at the chosen point).** Let $u > 0$, $l \geq 1$, $A, B, k \geq 0$ natural numbers, and $H = (k + 1)/u > 1$ with $4H \leq u^{2B + 5}$. Suppose that $l^{2A} \leq u$ and $u^{3B + 7} \leq e^{\sqrt u/2}$. If $F$ is complex differentiable with $|F| \leq l^A$ at each point of the closed disc about $1 + H$ of radius $H + l^{-A}$, then
$$\Big|\frac{(-H)^k H}{k!}\, g^{(k)}(1 + H)\Big| \leq u^{-(B + 1)}.$$

Lean: `New.norm_taylorCoeff_dslope_le_inv_pow` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* Let $\eta = l^{-A} \leq 1 < H$ and $M = l^A$. By [the last estimate](/decl/New.norm_taylorCoeff_dslope_le/), the coefficient is at most $4 l^{2A} H \exp(-(k + 1)\eta/(2H))$. Here $(k + 1)/H = u$ and $l^A \leq \sqrt u$, so the exponent is $-u/(2l^A) \leq -\sqrt u/2$. With $l^{2A} \leq u$ and $4H \leq u^{2B + 5}$, the bound is at most $u^{2B + 6} e^{-\sqrt u/2} \leq u^{2B + 6}/u^{3B + 7} = u^{-(B + 1)}$. $\square$

### The theorem

**Theorem (Tauberian theorem).** Let $R : \mathbb{R} \to \mathbb{R}$ be measurable, and let $L$ be real with
$$|R(v) - R(u)| \leq L(v - u) \qquad \text{for all } 0 \leq u \leq v \leq u + 1.$$
Let $F : \mathbb{C} \to \mathbb{C}$ satisfy
$$\frac{F(s) - F(1)}{s - 1} = \int_0^\infty R(v)\, e^{(1 - s)v}\, dv \qquad \text{for } \operatorname{Re} s > 2.$$
Let $A$ be a natural number, and suppose that for all large $l$, $F$ is complex differentiable with $|F(s)| \leq l^A$ at every $s$ with $\operatorname{Re} s \geq 1 - l^{-A}$ and $|s| \leq e^l$. Then for every natural number $B$,
$$|R(u)| \leq u^{-B} \qquad \text{for all large } u.$$

Lean: `New.eventually_abs_le_inv_pow_of_transform` (Lib/Analytic/PrimeNumberTheorem/Tauberian.lean).

*Proof.* First, $L \geq 0$ (take $u = 0$, $v = 1$), and by [unit steps](/decl/New.abs_sub_le_of_unit_steps/) $R$ is $L$-Lipschitz on $[0, \infty)$. For $\operatorname{Re} s > 2$ the slope $g$ equals the transform $\Phi$.

Let $u$ be large; precisely, let $u \geq 2L + 8$, let $l = (2B + 5)\log u$ be at least $1$ and so large that the hypothesis on $F$ holds, and let $u$ satisfy [the growth comparisons](/decl/New.eventually_log_pow_le_and_pow_le_exp_sqrt/) with $c = 2B + 5$ and $j = 3B + 7$. Put
$$k = \lfloor u^{2B + 4} \rfloor, \qquad H = \frac{k + 1}{u}, \qquad \eta = l^{-A}, \qquad \delta = u^{-(B + 1)}.$$
Then $u^{2B + 4} \leq k + 1$, so $H > 1$, and $H \leq k + 1 \leq 2u^{2B + 4}$. Let $c_k$ be the coefficient $(-H)^k H\, g^{(k)}(1 + H)/k!$.

*$c_k$ is close to $R(u)$.* By [the Lipschitz lemma](/decl/New.norm_taylorCoeff_transform_sub_le_of_lipschitz/) with this $\delta$,
$$|c_k - R(u)| \leq L\Big(u^{-(B + 1)} + \frac{u^2\, u^{B + 1}}{u^{2B + 4}}\Big) = \frac{2L}{u^{B + 1}}.$$

*$c_k$ is small.* Each $s$ in the disc about $1 + H$ of radius $H + \eta$ has, by [the disc](/decl/New.one_sub_le_re_and_norm_le_of_mem_closedBall/), $\operatorname{Re} s \geq 1 - \eta$ and
$$|s| \leq 2H + \eta + 1 \leq 4u^{2B + 4} + 2 \leq 8u^{2B + 4} \leq u^{2B + 5} = e^l,$$
since $u \geq 8$. So $F$ is differentiable with $|F| \leq l^A$ on the disc. Also $4H \leq 8u^{2B + 4} \leq u^{2B + 5}$. By [the coefficient at the chosen point](/decl/New.norm_taylorCoeff_dslope_le_inv_pow/), $|c_k| \leq u^{-(B + 1)}$.

So $|R(u)| \leq (1 + 2L)u^{-(B + 1)} \leq u^{-B}$, since $u \geq 2L + 8 > 1 + 2L$. $\square$

The proof spends the parameters as follows. The width of the peak must be at most $u^{-(B + 1)}$, which forces $k \approx u^{2B + 4}$ and makes $H$ a large power of $u$. The disc then has radius about $u^{2B + 4}$, so the region must reach to $|s| \approx u^{2B + 5}$, and $l = (2B + 5)\log u$. The gain $e^{-u/(2l^A)}$ needs $l^A$ much smaller than $u$, which holds because $l$ is a multiple of $\log u$.

**Remark (Formalization).** The classical Tauberian theorems for the prime number theorem use the monotonicity of $\psi$ (Newman's theorem in the form of Zagier) or a truncated Perron formula. The source uses a Lipschitz condition in place of monotonicity. It is stated for steps of length at most $1$, since that is what [slow variation](/decl/New.abs_primeRemainder_exp_sub_le/) of Volume 1 gives for $R_q(e^v)$. The Lipschitz condition is what makes the inversion formula give an error term with no smoothing. The hypothesis on $F$ is local: $F$ need not be entire or bounded on a half-plane. It must be holomorphic and at most $l^A$ only in the region of width $l^{-A}$ and radius $e^l$, for each large $l$. The same exponent $A$ serves for the width and for the bound. Section 6 uses $A = 26$.

**Remark (Formalization).** The integral in the hypothesis is a Bochner integral. If the integrand were not integrable, Lean would give it the value $0$. Here this does not happen: the Lipschitz condition gives $|R(v)| \leq (|R(0)| + L)e^v$, and [the derivatives of the transform](/decl/New.iteratedDeriv_transform/) proves integrability for $\operatorname{Re} s > 2$. The value $F(1)$ is only a constant in the hypothesis, and the source never evaluates the slope at $1$ in a way that uses the value $g(1)$; the Cauchy estimate only uses that $g$ is holomorphic near the disc, which follows from the differentiability of $F$ at $1$. The function $R$ is defined on all of $\mathbb{R}$, but the statement uses only its values for $v \geq 0$. The hypothesis on $\operatorname{Re} s > 2$ instead of $\operatorname{Re} s > 1$ is a convenience: the Lipschitz bound gives growth $e^v$, so the integral converges absolutely for $\operatorname{Re} s > 2$, and the point $1 + H$ with $H > 1$ is in that half-plane.
