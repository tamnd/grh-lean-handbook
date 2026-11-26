---
title: Isolation
lean:
  - New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean
decls:
  - New.Data.eight_mul_pow_mul_two_pow_le
  - New.Data.two_pow_mul_pow_f_le_b_pow_nStar
  - New.Data.integrable_tail_and_integral_le
  - New.Data.norm_holMinorsPi_mul_pow_le
  - New.Data.integral_norm_holMinorsPi_sq_eq_inv_prod
  - New.Data.integral_norm_holMinorsPi_mul_pow_le
  - New.Data.integrable_mul_holMinorsPi
  - New.Data.norm_integral_mul_holMinorsPi_mul_le
  - New.Data.integral_mul_norm_apply_one_mul_le
  - New.Rows.IsPeak
  - New.Data.norm_apply_one_le_of_forall_isPeak
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Isolation

The last step of the proof that products span is an estimate on the archimedean group $G_\infty = \prod_\tau U(\mathrm{diag}\,s)$. A holomorphic form $F$ is orthogonal, at each of its peaks, to a kernel $K$ close to a fixed function $K_0$. Then $K_0(1)$ is small. The holomorphic discrete series, their basic functions and formal degrees are in [discrete series](/chapter/discrete-series/).

### Notation

Let $D$ be admissible data with $b = D.b$, $t = D.t$, $f$ infinite places, and $n_* = 2ft^3$ ([the data and their sizes](/chapter/data-and-sizes/)). Let $1 \leq \#n \leq t$, and let the order $o$ put the signs $+1$ first. For a weight $u$ (one $u_\tau \in \mathbb{Z}^n$ for each $\tau$) let $m_u = \prod_\tau \mathrm{holMinors}(u_\tau)$ be the product of quotients of principal minors. Write $|h|$ for the largest operator norm of $h \in G_\infty$ at a place. In this section $u$ and $u'$ are dominant in each sign block, with a gap of at least $300n_*$ between the blocks (`HasHolGap`), and the entries of $u$ have modulus at most $5b$.

For such a weight, $l_\tau = 2u_\tau + 2\rho$ is a doubled Harish-Chandra parameter with a large gap, and its discrete series coefficient is $\mathrm{holMinors}(u_\tau)$ (`New.Data.hasLargeGap_and_dsCoeff_eq_holMinors`).

### Two numerical facts

**Lemma (The tail constant).** For $n \leq t$ and $L \leq 10b + t$,
$$8\bigl(2000(n+L+1)^6\bigr)^{2n^2}2^{10n^3} \leq 2^{13t^3}b^{14t^2}.$$

Lean: `New.Data.eight_mul_pow_mul_two_pow_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* In admissible data $b$ is very large against $t$. A comparison of logarithms gives $2000(n+L+1)^6 \leq b^7$. So the left side is at most $2^3(b^7)^{2n^2}2^{10n^3}$. As $1 \leq t$ and $n \leq t$, this is at most $2^{3t^3}b^{14t^2}2^{10t^3} = 2^{13t^3}b^{14t^2}$. $\square$

**Lemma (The power of $b$).** $2^{6n_*}\bigl(2^{13t^3}b^{14t^2}\bigr)^f \leq b^{n_*}$.

Lean: `New.Data.two_pow_mul_pow_f_le_b_pow_nStar` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Admissible data satisfy $2^{25} \leq b$ and $14 \leq t$. The left side is $(2^{25})^{ft^3}\,b^{14ft^2}$, since $6n_* = 12ft^3$. Bound $2^{25}$ by $b$ and $14t^2$ by $t \cdot t^2$. The result is $b^{ft^3}b^{ft^3} = b^{n_*}$. $\square$

### Integrals of basic functions

**Lemma (Tail).** Let $l = 2v + 2\rho$ have a large gap and $|v_i| \leq 5b$. The function $\mathrm{tail}(g) = d(l)\,(2/\|g\|)^{10n^3}$, with $d(l)$ the formal degree, is integrable on $U(\mathrm{diag}\,s)$ with integral at most $2^{13t^3}b^{14t^2}$.

Lean: `New.Data.integrable_tail_and_integral_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The entries of $l$ have modulus at most $L = 2\lfloor 5b\rfloor + n$. The general tail bound of [discrete series](/chapter/discrete-series/) (`New.integral_tail_le`) gives integrability and the bound $8(2000(n+L+1)^6)^{2n^2}2^{10n^3}$, since $10n^3 > 8n^2$. Apply the lemma on the tail constant. $\square$

**Lemma (Pointwise decay).** $|m_{u'}(h)|\,|h|^{6n_*} \leq 2^{6n_*}\prod_\tau(2/\|h_\tau\|)^{10n^3}$.

Lean: `New.Data.norm_holMinorsPi_mul_pow_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Choose a place $a$ with $\|h_a\| = |h|$. A discrete series coefficient with gap $8n_*$ satisfies $|\mathrm{holMinors}(u'_\tau)(g)| \leq (2/\|g\|)^{10n^3 + k}$ for $k \leq 6n_*$. Take $k = 6n_*$ at $a$ and $k = 0$ elsewhere. Then $|h|^{6n_*}(2/|h|)^{6n_*} = 2^{6n_*}$. $\square$

**Lemma ($L^2$ norm).** If $\mathrm{holMinors}(u_\tau)$ is the coefficient of $l_\tau$ for each $\tau$, then $\int|m_u|^2 = \bigl(\prod_\tau d(l_\tau)\bigr)^{-1}$.

Lean: `New.Data.integral_norm_holMinorsPi_sq_eq_inv_prod` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The integral over the product group is the product of the integrals, and the integral of $|c|^2$ for a normalised discrete series coefficient $c$ is $d(l)^{-1}$ by the Schur orthogonality relations. $\square$

**Theorem (Weighted integral).** $0 < \int|m_u|^2$, the function $|m_{u'}(h)|\,|h|^{6n_*}$ is integrable, and
$$\int|m_{u'}(h)|\,|h|^{6n_*}\,dh \leq b^{n_*}\int|m_u|^2.$$

Lean: `New.Data.integral_norm_holMinorsPi_mul_pow_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Positivity follows from the $L^2$ norm lemma, as formal degrees are positive. Put $I = \int|m_u|^2 = (\prod_\tau d(l_\tau))^{-1}$. By pointwise decay, $|m_{u'}(h)||h|^{6n_*} \leq 2^{6n_*}\,I\prod_\tau\mathrm{tail}_\tau(h_\tau)$, with the tails formed with the formal degrees of $u$. The right side is a product of integrable functions. Its integral is at most $2^{6n_*}I(2^{13t^3}b^{14t^2})^f \leq b^{n_*}I$ by the tail lemma and the lemma on the power of $b$. $\square$

**Corollary (Integrals against $m_{u'}$).** Let $A$ be continuous with $|A(h)| \leq C|h|^{6n_*}$. Then $Am_{u'}$ is integrable and $|\int Am_{u'}| \leq C\,b^{n_*}\int|m_u|^2$.

Lean: `New.Data.integrable_mul_holMinorsPi` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* $|Am_{u'}| \leq C|m_{u'}||h|^{6n_*}$. Apply the theorem. $\square$

**Lemma (Orthogonality makes it small).** Let $W$, $K$, $K'$ be continuous, $|W| \leq M$, and $|K - K_0|, |K' - K_0| \leq \delta|h|^{6n_*}$. If $\int WK'm_{u'} = 0$ and $Km_{u'}W$ is integrable, then $|\int Km_{u'}W| \leq 2\delta M\,b^{n_*}\int|m_u|^2$.

Lean: `New.Data.norm_integral_mul_holMinorsPi_mul_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* By orthogonality $\int Km_{u'}W = \int W(K - K')m_{u'}$. Here $|W(K - K')| \leq 2\delta M|h|^{6n_*}$. Apply the corollary with $C = 2\delta M$. $\square$

**Lemma (Reproducing a value).** Let $f$ be holomorphic of weight $u$. Let $W_\theta$, for $\theta$ on the circle, have circle mean $\int_\theta W_\theta(h) = \overline{m_u(h)c}$ with $c \neq 0$. If $f(h)W_\theta(h)$ is jointly integrable and $|\int fW_\theta| \leq B$ for every $\theta$, then $\bigl(\int|m_u|^2\bigr)|f(1)|\,|c| \leq B$.

Lean: `New.Data.integral_mul_norm_apply_one_mul_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Exchange the integrals over $\theta$ and $h$ (Fubini). The result is $\bar c\int f\,\overline{m_u}$. The reproducing formula for holomorphic functions of weight $u$ gives $\int f\,\overline{m_u} = (\int|m_u|^2)f(1)$. Take the mean of the bounds $B$. $\square$

### The isolation estimate

**Definition (Peak).** A *peak* of a function $F$ is a point $x$ such that $|F|$ is bounded and $|F(x)| > \frac12\sup|F|$. Then $|F(y)| \leq 2|F(x)|$ for all $y$, and $F(x) \neq 0$.

Lean: `New.Rows.IsPeak` (Lib/DiscreteSeries/Holomorphic/PeaksAwayFromCusp.lean).

**Theorem (Isolation).** Let $F$ on $G = G_\infty \times G_f$ be continuous and holomorphic of weight $u$ in the archimedean variable, with a peak $z$. Let $|K_0| \leq C$. Suppose that at every peak $x$ there is $K$, holomorphic of weight $u - u'$, with $|K(h) - K_0(h)| \leq \delta|h|^{6n_*}$ and
$$\int_{G_\infty}\overline{F(x(h,1))}\,K(h)\,m_{u'}(h)\,dh = 0.$$
Then $|K_0(1)| \leq (4b^{n_*} + 1)\,\delta$.

Lean: `New.Data.norm_apply_one_le_of_forall_isPeak` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Let $\mathrm{rot}(\theta)$ be the torus element $\mathrm{diag}(\theta^{o_i})$ at every place. As $F$ is holomorphic of weight $u$, $F(z\,\mathrm{rot}(\theta)) = \chi_u(\theta)F(z)$ with a character value $\chi_u(\theta) = \prod_{\tau,i}\theta^{o_iu_{\tau i}}$ of modulus $1$. So $|F(z\,\mathrm{rot}(\theta))| = |F(z)|$, and every $z\,\mathrm{rot}(\theta)$ is a peak. The hypothesis gives $K_\theta$ for each $\theta$. Put
$$W_\theta(h) = \overline{F(z\,\mathrm{rot}(\theta)h)\,\chi_u(\theta)^{-1}}.$$
Then $|W_\theta| \leq 2|F(z)|$ by the peak property, and $\int W_\theta K_\theta m_{u'} = 0$. As $h \mapsto F(zh)$ is holomorphic of weight $u$, the circle mean of $W_\theta(h)$ is $\overline{m_u(h)F(z)}$. Now use the single function $K_0' = K_{\theta=0}$. It satisfies $|K_0'| \leq (C + \delta)|h|^{6n_*}$, so $K_0'm_{u'}W_\theta$ is integrable. The lemma on orthogonality, with $K = K_0'$, $K' = K_\theta$ and $M = 2|F(z)|$, gives $|\int K_0'm_{u'}W_\theta| \leq 4\delta|F(z)|\,b^{n_*}\int|m_u|^2$. The function $K_0'm_{u'}$ is holomorphic of weight $u$ with value $K_0'(1)$ at $1$. The lemma on reproducing a value with $c = F(z) \neq 0$ gives $|K_0'(1)| \leq 4\delta b^{n_*}$. Finally $|K_0'(1) - K_0(1)| \leq \delta$, since $|1| = 1$. $\square$

**Remark (Formalization).** The functions $K_\theta$ come from the hypothesis by `choose`. Only $K_{\theta=0}$ enters the bound. The constant $C$ appears only to make the integrals converge; it does not enter the bound. Of the admissible data the theorem uses only $E$, the places, $t$ and $b$.
