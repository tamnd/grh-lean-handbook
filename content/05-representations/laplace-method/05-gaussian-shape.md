---
title: The Gaussian shape near the identity
lean:
  - New/Appendix/DiscreteSeries/GaussianShape.lean
decls:
  - New.DiscreteSeries.one_le_pow_mul_kTypeNormSq
  - New.DiscreteSeries.exp_neg_le_kTypeNormSq
  - New.DiscreteSeries.gapWeightedNormSq
  - New.DiscreteSeries.sum_norm_lie_coordProj_sq
  - New.DiscreteSeries.sum_trace_coordProj_mul
  - New.DiscreteSeries.norm_weightMinors_sq_le_exp
  - New.DiscreteSeries.exists_weightMinors_conj_reducedExp_eq_cexp
  - New.DiscreteSeries.exists_weightMinors_neg_paramAddRho_eq_cexp
  - New.DiscreteSeries.flenstedJensen_div_exp_sub
  - New.DiscreteSeries.mul_norm_exp_sub_one_le
  - New.DiscreteSeries.exists_norm_dsCoeff_div_cexp_sub_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Gaussian shape near the identity

This section proves that near $1$ the coefficient $c_l(g)$ is its phase $\exp\operatorname{tr}(\mu\log g)$ times a number in $[0, 1]$, up to a relative error of $10\%$ and an exponentially small absolute error. The number is a Gaussian in $\log g$. The proof multiplies the estimates of section 4 over the sets $\{i : t \leq w_i\}$ and averages over $K$.

### The integral formula

We recall the formula of the previous chapter. For a weight $w \in \mathbb{Z}^n$ and an invertible matrix $g$ let
$$ m_w(g) = \prod_{t \leq 0} \frac{\det_{\{i \,:\, t \leq w_i\}}(g)}{\det g}\ \prod_{t > 0}\det\nolimits_{\{i \,:\, t \leq w_i\}}(g). $$
Only finitely many factors differ from $1$: for $t \leq \min w$ the set is all of $n$, and for $t > \max w$ it is empty. For a dominant $w$ and $k \in K$, $m_w(k)$ is the matrix coefficient of a unit highest weight vector of the representation of $K$ with highest weight $w$. Write $\|m_w\|^2 = \int_K |m_w|^2\,dk$ for the Haar measure of mass $1$. Write $\lambda^\rho = \lambda + \rho$. Near $1$ the coefficient is
$$ c_l(g) = \frac{1}{\|m_\mu\|^2}\int_K \frac{|m_\mu(k)|^2}{m_{-\lambda^\rho}(k^* g k)}\, dk. $$
This is the integral of Flensted-Jensen with first argument $1$; the previous chapter shows that $c_l$ is given by it when $g$ is accretive, which holds for $\|g - 1\| < 1$.

### The size of the K-type

By Schur orthogonality, $\|m_\mu\|^2$ is the inverse of the dimension of the representation of $K$ with highest weight $\mu$. Weyl's dimension formula (Humphreys, *Introduction to Lie Algebras and Representation Theory*, §24.3) then gives a bound $\|m_\mu\|^2 \geq (\text{polynomial in } L)^{-n^2}$. The source proves a bound of this kind in another way.

**Lemma (Lower bound for the K-type).** Let $l$ have large gap $A$ and $|l_i| \leq L$ for all $i$. Write $N = \#n$. Then
$$ 1 \leq \left(2000(N + L + 1)^6\right)^{2N^2} \cdot 4\|m_\mu\|^2. $$
Lean: `New.DiscreteSeries.one_le_pow_mul_kTypeNormSq` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Apply [the volume bound](/decl/New.measure_ball_le_integral_dsCoeff/) of the previous chapter to the group $K$ with $j$ the inclusion and radius $r = 1$. In the operator norm, all of $K$ lies in the ball of radius $1$, and $K$ has mass $1$. On $K$, $c_l = m_\mu$. So $1 \leq (2000(N+L+1)^6)^{2N^2}\int_K 4|m_\mu|^2$. $\square$

**Lemma (Exponential form).** Let $l$ be as above, and let $T \geq 1$ with $N^2 \leq T$ and $N^2\log(N + L + 1) \leq T$. Then $\|m_\mu\|^2 \geq e^{-5000T}$.
Lean: `New.DiscreteSeries.exp_neg_le_kTypeNormSq` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Take logarithms: $\log\|m_\mu\|^2 \geq -\log 4 - 2N^2(\log 2000 + 6\log(N+L+1))$. Use $\log 4 \leq 4$, $\log 2000 \leq 2000$ and the two hypotheses on $T$. $\square$

**Remark (Formalization).** The lower bound uses the volume bound of the previous chapter, which is a statement about $c_l$ near $1$. It does not use Weyl's formula. The constant $5000$ is far from optimal; it only needs to be a fixed number, since the error in the main lemma below is $e^{-100T}$ and $T$ is free.

### The weighted quadratic form

**Definition (Weighted norm).** For $w \in \mathbb{Z}^n$ and a matrix $A$,
$$ Q_w(A) = \sum_{i,j} |w_i - w_j|\,|A_{ij}|^2. $$
Lean: `New.DiscreteSeries.gapWeightedNormSq` (New/Appendix/DiscreteSeries/GaussianShape.lean).

So $Q_w \geq 0$ and $Q_{-w} = Q_w$. Let $P_t$ be the projection to $\{i : t \leq w_i\}$.

**Lemma (Sum of commutators).** If $a \leq w_i \leq b$ for all $i$, then
$$ \sum_{a < t \leq b}\|[P_t, A]\|^2 = Q_w(A), \qquad \sum_{a < t \leq b}\operatorname{tr}(P_t A) = \operatorname{tr}(\operatorname{diag}(w) A) - a\operatorname{tr}A. $$
Lean: `New.DiscreteSeries.sum_norm_lie_coordProj_sq` (New/Appendix/DiscreteSeries/GaussianShape.lean), `New.DiscreteSeries.sum_trace_coordProj_mul` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* The entry $(i, j)$ of $[P_t, A]$ is $\pm A_{ij}$ if exactly one of $t \leq w_i$, $t \leq w_j$ holds, and $0$ otherwise. Exactly $|w_i - w_j|$ values of $t$ separate $i$ from $j$. For the traces, exactly $w_i - a$ values of $t$ in $(a, b]$ satisfy $t \leq w_i$. $\square$

**Lemma (Gaussian bound on K).** For $k \in K$ and every weight $w$, $|m_w(k)|^2 \leq \exp(-Q_w(k)/2)$.
Lean: `New.DiscreteSeries.norm_weightMinors_sq_le_exp` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Since $|\det k| = 1$, $|m_w(k)|^2$ is the product of $|\det_{\{t \leq w_i\}} k|^2$ over $t$. Apply [the size of one minor](/decl/New.DiscreteSeries.norm_principalMinor_sq_le_exp/) to each factor and sum the exponents by the previous lemma. $\square$

**Example.** Let $n = \{1, 2\}$ with $\varepsilon = (1, 1)$, so $K = U(2)$, and $w = (1, 0)$. Then $m_w(k) = k_{11}$, and $Q_w(k) = |k_{12}|^2 + |k_{21}|^2 = 2(1 - |k_{11}|^2)$. The lemma says $|k_{11}|^2 \leq \exp(|k_{11}|^2 - 1)$, which is $x \leq e^{x - 1}$.

### All minors at once

**Lemma (Weight minors of a conjugate).** Let $l$ be injective, and let $w$ satisfy $l_i < l_j$ whenever $w_j < w_i$. Let $Z$ be in the Lie algebra of $U(\varepsilon)$ with $\|Z\| \leq \delta \leq 1/20$, and let $k \in K$. Let $\hat g$ be the reduced exponential of $Z$ for the order $o = l$. Then
$$ m_w(k^*\hat g k) = \exp\left(\operatorname{tr}(\operatorname{diag}(w)Z) + \tfrac14 Q_w(Z) + r\right), \qquad |r| \leq 10^5\delta\,(Q_w(Z) + Q_w(k)). $$
Lean: `New.DiscreteSeries.exists_weightMinors_conj_reducedExp_eq_cexp` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* The condition on $w$ says that each set $\{i : t \leq w_i\}$ comes first in the order $o = l$. Apply [the minor of a conjugate](/decl/New.DiscreteSeries.exists_principalMinor_conj_reducedExp_eq_cexp/) to each factor. The factors with $t \leq 0$ are divided by $\det(k^*\hat g k) = e^{\operatorname{tr}Z}$. Add the exponents with the lemma on sums of commutators. $\square$

**Lemma (The denominator).** Let $l$ have gap $h$, let $Z$, $\delta$, $k$ be as above, and let $q = Q_{-\lambda^\rho}(Z)/4$. Then
$$ m_{-\lambda^\rho}(k^*\hat g k) = \exp\left(q - \operatorname{tr}(\mu Z) - r\right), \qquad |r| \leq 5\cdot 10^5\,\delta\,(q + Q_\mu(k) + N^2). $$
Lean: `New.DiscreteSeries.exists_weightMinors_neg_paramAddRho_eq_cexp` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Apply the previous lemma to $w = -\lambda^\rho$. The order condition holds since $\lambda^\rho$ is ordered like $l$. The difference $\lambda^\rho - \mu = 2\rho_c$ has entries of absolute value at most $N$. So $\operatorname{tr}(\lambda^\rho Z)$ and $\operatorname{tr}(\mu Z)$ differ by at most $N^2\|Z\|$, and $Q_{-\lambda^\rho}(k) \leq Q_\mu(k) + 2N^2$, since $\|k\|^2 = N$. $\square$

### The main lemma

**Lemma (Mean over K).** Let $y$ be invertible, and suppose that $m_{-\lambda^\rho}(k^* y k) = \exp(q - \vartheta - r(k))$ for all $k \in K$, with $q$ real. Then
$$ \frac{c(y)}{e^{\vartheta}} - e^{-q} = \frac{1}{\|m_\mu\|^2}\int_K |m_\mu(k)|^2 e^{-q}\left(e^{r(k)} - 1\right)dk, $$
where $c(y)$ is the integral of Flensted-Jensen with first argument $1$.
Lean: `New.DiscreteSeries.flenstedJensen_div_exp_sub` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Put the form of the denominator into the integral formula, and subtract $e^{-q} = \|m_\mu\|^{-2}\int_K |m_\mu|^2 e^{-q}$. $\square$

**Lemma (Small or negligible).** Let $T \geq 1$, $\delta \geq 0$, $\delta T \leq 10^{-12}$, and $q, Q \geq 0$, $0 \leq N' \leq T$. Let $0 \leq m \leq e^{-Q/2}$ and $|r| \leq 10^6\delta(q + Q + N')$. Then
$$ m\, e^{-q}\,|e^r - 1| \leq \tfrac{1}{10}e^{-q}m + e^{-5100T}. $$
Lean: `New.DiscreteSeries.mul_norm_exp_sub_one_le` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Let $s = q + Q + N'$. If $s \leq 50000T$, then $|r| \leq 1/20$ and $|e^r - 1| \leq 1/10$. If $s > 50000T$, then $q + Q > 49999T$, so $me^{-q} \leq e^{-(q + Q/2)}$ is tiny, while $|e^r - 1| \leq e^{|r|} + 1$ and $|r| \leq 10^{-6}s/T$ is much smaller than $q + Q/2$. $\square$

**Theorem (Gaussian shape).** Let $l$ have large gap $A$, $|l_i| \leq L$, and let $g \in U(\varepsilon)$ with $\|g - 1\| \leq \delta$. Let $T \geq 1$ with $N^2 \leq T$, $N^2\log(N + L + 1) \leq T$ and $\delta T \leq 10^{-12}$. Then there is $\varrho \in [0, 1]$ with
$$ \left|\frac{c_l(g)}{\exp\operatorname{tr}(\mu\log g)} - \varrho\right| \leq \frac{\varrho}{10} + e^{-100T}. $$
Lean: `New.DiscreteSeries.exists_norm_dsCoeff_div_cexp_sub_le` (New/Appendix/DiscreteSeries/GaussianShape.lean).

*Proof.* Let $Z = \log g$, defined by the power series, which converges since $\|g - 1\| \leq 10^{-12}$. Then $Z$ is in the Lie algebra and $\|Z\| \leq 2\delta$. Put $q = Q_{-\lambda^\rho}(Z)/4$ and $\varrho = e^{-q}$. Then $\varrho \in [0, 1]$.

First, $c_l(g)$ is the integral of Flensted-Jensen at $g = e^Z$, and by [the triangular factors](/decl/New.DiscreteSeries.flenstedJensen_reducedExp/) it is the same at $\hat g$. Second, the lemma on the denominator gives $r(k)$ for each $k$ with $\vartheta = \operatorname{tr}(\mu Z)$. The lemma on the mean over $K$ writes $c_l(g)/e^{\vartheta} - \varrho$ as a mean. Third, by the Gaussian bound on $K$, $|m_\mu(k)|^2 \leq e^{-Q_\mu(k)/2}$, so the lemma on small or negligible terms applies with $m = |m_\mu(k)|^2$, $Q = Q_\mu(k)$ and $N' = N^2$. Integrate over $K$:
$$ \left|\frac{c_l(g)}{e^{\vartheta}} - \varrho\right| \leq \frac{1}{\|m_\mu\|^2}\left(\frac{\varrho}{10}\|m_\mu\|^2 + e^{-5100T}\right) \leq \frac{\varrho}{10} + e^{-100T}, $$
by the exponential form of the lower bound for $\|m_\mu\|^2$. $\square$

**Remark (Formalization).** The theorem states only that some $\varrho$ exists. The explicit value $\varrho = \exp(-Q_{-\lambda^\rho}(\log g)/4)$ appears only in the proof. The error terms $r(k)$ are chosen for each $k$ with `choose`; their values outside the stated bounds do not matter. In section 6 only the existence of $\varrho \in [0, 1]$ is used.

**Remark (Formalization).** In this theorem $\|g - 1\|$ is the Frobenius norm. The two lemmas on the size of the $K$-type use the operator norm, and so does the statement of the theorem of section 6. The operator norm is at most the Frobenius norm, which is at most $\sqrt N$ times the operator norm. The source keeps the analysis near $1$ in section 6 in the Frobenius norm, and uses the operator norm for the balls in the final statement.

### Why this is a Gaussian

The number $\varrho = e^{-Q_{-\lambda^\rho}(Z)/4}$ with $Z = \log g$ is a Gaussian in $Z$. In the entry $(i, j)$ its exponent is $|\lambda^\rho_i - \lambda^\rho_j|\,|Z_{ij}|^2/4$. So its width in this entry is of size $|\lambda_i - \lambda_j|^{-1/2}$, and a large gap makes it narrow in the noncompact directions. The phase $\exp\operatorname{tr}(\mu Z)$ is the character of the lowest $K$-type, extended to $Z$. So the theorem says: near $1$, the coefficient is a character times a Gaussian. This is the input to Laplace's method.
