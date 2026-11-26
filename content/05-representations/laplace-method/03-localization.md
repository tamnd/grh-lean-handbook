---
title: Localization near the identity
lean:
  - New/Appendix/DiscreteSeries/Localization.lean
decls:
  - New.DiscreteSeries.noncompactPart
  - New.DiscreteSeries.two_mul_re_sub_one_apply
  - New.DiscreteSeries.norm_sq_add_re_trace_le
  - New.DiscreteSeries.norm_sub_one_sq
  - New.DiscreteSeries.norm_noncompactPart_inv
  - New.DiscreteSeries.norm_onBlock_gram_sub_one_le
  - New.DiscreteSeries.dsCoeff_mul_eq_of_sub_one_eq_inclMatrix
  - New.DiscreteSeries.one_add_norm_sq_le_norm_det_one_add
  - New.DiscreteSeries.conjTranspose_blockDiagPart_mul_blockDiagPart
  - New.DiscreteSeries.norm_dsCoeff_pow_four_le
  - New.DiscreteSeries.IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le
  - New.DiscreteSeries.IsLaplaceDatum.norm_subOnePair_mul_intDiagonal_sq_le
  - New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_onBlock_eq
  - New.DiscreteSeries.IsLaplaceDatum.norm_snd_sq
  - New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Localization near the identity

The integrand $\theta$ is small far from the compact subgroup, by the decay of $c_l$. This section proves the converse statement that we need for Laplace's method: if $\theta(s)$ is not small, then $s$ can be moved to a point $t$ with $\theta(t) = \theta(s)$ where $g$ and $g'$ are both near $1$. Steepness is used only in this section.

Throughout, $(l, k, j, \tau, B, e, \varphi)$ is a Laplace datum and $\|\cdot\|$ is the Frobenius norm. For $s \in S$ we write $j(s) = (g, g')$, $y$ and $y'$ for the noncompact parts of $g$ and $g'$, and $x = g - 1$.

### Identities for unitary matrices

**Definition (Noncompact part).** For an $n \times n$ matrix $A$, the noncompact part is $A$ minus its block diagonal part. It keeps the entries $A_{ij}$ with $\varepsilon_i \neq \varepsilon_j$.
Lean: `New.DiscreteSeries.noncompactPart` (New/Appendix/DiscreteSeries/Localization.lean).

**Lemma (Row relation).** For $g \in U(\varepsilon)$ and every index $i$,
$$ 2\operatorname{Re} x_{ii} = 2\sum_j |y_{ij}|^2 - \sum_j |x_{ij}|^2. $$
Lean: `New.DiscreteSeries.two_mul_re_sub_one_apply` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* The relation $g J_\varepsilon g^* = J_\varepsilon$ in the entry $(i, i)$ reads $\sum_j \varepsilon_j |g_{ij}|^2 = \varepsilon_i$. Multiply by $\varepsilon_i$. The terms with $\varepsilon_j = \varepsilon_i$ have sign $+$ and the terms with $\varepsilon_j \neq \varepsilon_i$ have sign $-$, so
$$ \sum_j |g_{ij}|^2 - 2\sum_j |y_{ij}|^2 = 1. $$
Now $\sum_j |g_{ij}|^2 = \sum_j |x_{ij}|^2 + 2\operatorname{Re}x_{ii} + 1$. $\square$

The row relation says that the real part of the diagonal of $g - 1$ is negative to second order, unless $g$ has a large noncompact part. The next lemma sums it with weights.

**Lemma (Weighted row relation).** Let $g \in U(\varepsilon)$, let $a, C$ be real, and let $v, w \in \mathbb{Z}^n$. Assume $a v_i^2 \leq w_i$ for all $i$, and $w_i \leq C$ whenever $\varepsilon_i \neq \varepsilon_j$ for some $j$. Then
$$ a\|\operatorname{diag}(v)\, x\|^2 + 2\operatorname{Re}\operatorname{tr}(\operatorname{diag}(w)\, x) \leq 2C\|y\|^2. $$
Lean: `New.DiscreteSeries.norm_sq_add_re_trace_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Multiply the row relation for $i$ by $w_i$ and sum over $i$. On the left, $w_i\sum_j|x_{ij}|^2 \geq a v_i^2 \sum_j |x_{ij}|^2$. On the right, $y_{ij} \neq 0$ only if $\varepsilon_i \neq \varepsilon_j$, and then $w_i \leq C$. $\square$

The sum of the row relations over all $i$ gives an identity for the distance to $1$. The noncompact part also behaves well under inversion, since $g^{-1} = J_\varepsilon g^* J_\varepsilon$.

**Lemma (Distance to one).** For $g \in U(\varepsilon)$,
$$ \|g - 1\|^2 = 2\|y\|^2 - 2\operatorname{Re}\operatorname{tr}(g - 1). $$
Lean: `New.DiscreteSeries.norm_sub_one_sq` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Sum the row relation over $i$. $\square$

**Lemma (Inverse).** For $g \in U(\varepsilon)$ the noncompact parts of $g^{-1}$ and $g$ have the same norm.
Lean: `New.DiscreteSeries.norm_noncompactPart_inv` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* The noncompact part of $g^{-1} = J_\varepsilon g^* J_\varepsilon$ is $J_\varepsilon y^* J_\varepsilon$, and multiplication by $J_\varepsilon$ and the adjoint keep the Frobenius norm. $\square$

### The rows and columns off the compact block

Let $D$ be the diagonal matrix that is $0$ on $e(X)$ and $1$ elsewhere. So $Dx$ keeps the rows of $g - 1$ off $X$ and $xD$ keeps the columns.

**Lemma (Rows).** Let $B \geq 1$. Then $\|D(g - 1)\|^2 \leq 6(\|y\|^2 + \|y'\|^2)$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_intDiagonal_mul_subOnePair_sq_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Apply the weighted row relation to $g$ with $a = B$, the vector $v$ of the diagonal of $D$, $w = -\mu$ and $C = 3B$. The hypotheses hold by steepness: on $X$ both $v$ and $\mu$ are $0$, and off $X$ we have $B \leq -\mu_i \leq 3B$. On $X$ we also have $-\mu_i = 0 \leq 3B$. This gives
$$ B\|Dx\|^2 - 2\operatorname{Re}\operatorname{tr}\mu(g - 1) \leq 6B\|y\|^2. $$
Apply it to $g'$ with $a = 0$, $v = 0$, $w = \mu'$ and $C = 3B$. Condition 6 of a Laplace datum gives the hypotheses, and
$$ 2\operatorname{Re}\operatorname{tr}\mu'(g' - 1) \leq 6B\|y'\|^2. $$
Since $\varphi(s) = \operatorname{tr}\mu(g-1) - \operatorname{tr}\mu'(g'-1)$ is imaginary, the two real parts are equal. Add the two inequalities and divide by $B > 0$. $\square$

This is the key point of the section. Neither inequality alone bounds $Dx$, since the real part of $\operatorname{tr}\mu(g-1)$ has no sign. The imaginary phase passes the information from the second factor to the first.

**Lemma (Columns).** Let $B \geq 1$. Then $\|(g - 1)D\|^2 \leq 6(\|y\|^2 + \|y'\|^2)$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_subOnePair_mul_intDiagonal_sq_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Apply the lemma on rows to $s^{-1}$. Then $g^{-1} - 1 = J_\varepsilon (g - 1)^* J_\varepsilon$, so $D(g^{-1} - 1)$ has the norm of $(g-1)D$. The noncompact parts of $g^{-1}$ and $g'^{-1}$ have the norms of $y$ and $y'$. $\square$

**Lemma (Gram matrix of the block).** Let $a_X$ be the $X \times X$ block of $g$. Then $\|a_X^* a_X - 1\| \leq \|D(g - 1)\|^2$.
Lean: `New.DiscreteSeries.norm_onBlock_gram_sub_one_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* The signs are $+1$ on $X$. The block on $X$ of $g^* J_\varepsilon g = J_\varepsilon$ reads $a_X^* a_X + W^* J W = 1$, where $W$ consists of the rows of $g$ off $X$ restricted to the columns in $X$, and $J$ is the diagonal of signs off $X$. These rows of $g$ equal the rows of $g - 1$ there. So $\|a_X^* a_X - 1\| = \|W^* J W\| \leq \|W\|^2 \leq \|D(g-1)\|^2$. $\square$

### Moving by the diagonal copy of the compact block

**Lemma (Left translation).** Let $g_0 \in U(\varepsilon)$ be such that $g_0 - 1$ vanishes outside the rows and columns of $e(X)$, where the sign is $+1$ and the weight $\mu$ is $0$. Then $c_l(g_0 g) = c_l(g)$ for all $g \in U(\varepsilon)$.
Lean: `New.DiscreteSeries.dsCoeff_mul_eq_of_sub_one_eq_inclMatrix` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* The coefficient is $c_l(g) = F(a, a^{-1} g)$, where $a$ is the block diagonal part of $g$ and $F$ is the integral of Flensted-Jensen of the previous chapter. The element $g_0$ is block diagonal, so the block diagonal part of $g_0 g$ is $g_0 a$, and $(g_0 a)^{-1} g_0 g = a^{-1} g$. In the integral, $a$ enters through the product of principal minors on the sets $\{i : t \leq \mu_i\}$. The set $e(X)$ lies inside such a set if $t \leq 0$ and is disjoint from it if $t > 0$. So each principal minor of $g_0 A$ is $\det g_0$ times that of $A$ for $t \leq 0$, and equal to it for $t > 0$. The factors with $t \leq 0$ are divided by the determinant, so the product does not change. $\square$

**Lemma (Translation keeps the integrand).** For every unitary $u$ on $X$ and every $s$ there is $t \in S$ with $\theta(t) = \theta(s)$, with the block of $j(t)_1$ on $X$ equal to $u a_X$, and with the same norms of both noncompact parts as $s$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_onBlock_eq` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Take $s_0$ given by condition 7 for $u$ and put $t = s_0 s$. The two components of $j(s_0)$ satisfy the hypotheses of the left translation lemma, by steepness and by condition 5. So both coefficients are unchanged. The phase $\varphi(s_0) = \Phi(\operatorname{sub}(s_0))$ is $0$, since $\mu$ and $\mu'$ vanish on $e(X)$ and $\tau(X)$. By additivity $\varphi(t) = \varphi(s)$. Left multiplication by a block diagonal unitary matrix keeps the norm of the noncompact part. $\square$

**Lemma (Second component).** $\|g' - 1\|^2 = \|g - 1\|^2 - 2\|y\|^2 + 2\|y'\|^2$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_snd_sq` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Apply the identity for the distance to one to $g$ and $g'$, and use condition 2 on the traces. $\square$

### The localization theorem

**Theorem (Localization).** Let $B \geq 1$ and $0 < r \leq 1/6$. Let $s \in S$ with $\|y\|^2 + \|y'\|^2 \leq r^2$. Then there is $t \in S$ with $\theta(t) = \theta(s)$ and
$$ \|j(t)_1 - 1\| \leq 4r, \qquad \|j(t)_2 - 1\| \leq 4r. $$
Lean: `New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* By the lemmas on the Gram matrix and on the rows, $\|a_X^* a_X - 1\| \leq 6r^2 \leq r < 1$. So $a_X^* a_X$ is invertible, and so is $a_X$. Write $a_X = k_1 z_1$ by the polar decomposition. Then $z_1^2 = a_X^* a_X$, so $\|z_1 - 1\| \leq \|z_1^2 - 1\| \leq r$. Translate by $u = k_1^{-1}$: we get $t$ with $\theta(t) = \theta(s)$, block $z_1$ on $X$, and the same noncompact norms. For $t$, the entries of $j(t)_1 - 1$ lie in the rows off $X$, in the columns off $X$, or in the block on $X$. These parts contribute at most $6r^2$, $6r^2$ and $r^2$. So $\|j(t)_1 - 1\|^2 \leq 13r^2$. By the lemma on the second component, $\|j(t)_2 - 1\|^2 \leq 13r^2 + 2r^2 = 15r^2$. Since $15 \leq 16$, both norms are at most $4r$. $\square$

### Decay off the compact subgroup

The localization is used together with a decay bound, which shows that $s$ with large noncompact parts contribute little.

**Lemma (Determinant).** For every square matrix $A$, $1 + \|A\|^2 \leq |\det(1 + A^* A)|$.
Lean: `New.DiscreteSeries.one_add_norm_sq_le_norm_det_one_add` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Let $t_i \geq 0$ be the eigenvalues of $A^* A$. Then $\|A\|^2 = \sum t_i$ and $\det(1 + A^*A) = \prod(1 + t_i) \geq 1 + \sum t_i$. $\square$

**Lemma (Block diagonal part).** For $g \in U(\varepsilon)$ with block diagonal part $a$, $a^* a = 1 + y^* y$.
Lean: `New.DiscreteSeries.conjTranspose_blockDiagPart_mul_blockDiagPart` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* Put $\tilde g = J_\varepsilon g J_\varepsilon$. Then $a = (g + \tilde g)/2$ and $y = (g - \tilde g)/2$. From $g^* J_\varepsilon g = J_\varepsilon$ we get $g^* \tilde g = 1$ and $\tilde g^* g = 1$. Expand: $a^* a - y^* y = (g^* \tilde g + \tilde g^* g)/2 = 1$. $\square$

**Theorem (Decay).** Let $l$ have large gap $h$. Then for every $g \in U(\varepsilon)$,
$$ |c_l(g)|^4 \leq (1 + \|y\|^2)^{-h}. $$
Lean: `New.DiscreteSeries.norm_dsCoeff_pow_four_le` (New/Appendix/DiscreteSeries/Localization.lean).

*Proof.* By the two lemmas, $1 + \|y\|^2 \leq \det(a^* a) = |\det a|^2$. The decay bound of the previous chapter, [the decay](/decl/New.norm_dsCoeff_sq_mul_det_pow_le_one/), with $c = h$ (allowed, since the gap is $500(\#n)^3 + h \geq h$), gives $|c_l(g)|^2 \leq |\det a|^{-h}$. Square it. $\square$

So if $\|y\|^2 + \|y'\|^2 \geq \rho^2$, then $(1 + \|y\|^2)(1 + \|y'\|^2) \geq 1 + \rho^2$ and $|\theta(s)|^4 \leq (1 + \rho^2)^{-h}$. If $h$ is large compared with $\rho^{-2}$, this is tiny. Section 6 uses this split between near and far points.
