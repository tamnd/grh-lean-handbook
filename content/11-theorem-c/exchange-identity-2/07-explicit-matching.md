---
title: Explicit matching
lean:
  - New/Determinant/Exchange/ExplicitMatching.lean
decls:
  - New.Rows.matchedPoly
  - New.Rows.realPairWeil_stackedDetProd
  - New.Rows.realPairWeil_matchedPoly
  - New.Rows.exists_mul_eq_circle_mean
  - New.Rows.exists_stackedDetProd_eq_sum_unitary
  - New.Rows.exists_mul_apply_eq_apply_matchedPoly
  - New.Rows.exists_clm_eq_thetaIntegral_modDatum
  - New.Rows.exists_linearMap_eq_integral_modKernel
  - New.Rows.integral_modKernel_stackedDetProd
  - New.Rows.exists_stdClassSum_eq_of_exchange
  - New.Rows.exists_stdClassSum_eq_mul_integral_modKernel
  - New.Rows.exists_mul_stdClassSum_eq_integral_modKernel
  - New.Rows.areMatched_det_one
  - New.Rows.integral_modKernel_matchedPoly_of_isEmpty
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Explicit matching

The exchange identity gives a Schwartz vector $x$ that nobody writes down. The later chapters need explicit real data: products of determinants. This section takes $V = I_a$, the positive definite standard space, and moves the identity to such data. The cost is one more constant $c'$, which may be $0$.

Fix splittings $j \colon m \sqcup l \simeq n$ and $f \colon p \sqcup l \simeq b$. The space $W$ has signs $+1$ on $m$ and $-1$ on $l$, and $V'$ has $+1$ on $p$ and $-1$ on $l$. Fix $e \colon p \sqcup a \simeq m$. For each infinite place $\tau$ let $\eta_{\tau k}$, $k \in \iota_\tau$, be complex $p \times m$ matrices.

1. $\mathrm{SD}(\eta)$ is the product over $\tau$, $k$ of the determinants of $\eta_{\tau k}$ stacked over the $a \times m$ matrix of variables, with columns ordered by $e$. It lives on $(W, I_a)$.
2. $\mathrm{MP}(\eta) = \prod_\tau \det(y^-_\tau)^{|\iota_\tau| + |n| - 2|l|}\prod_{\tau, k}\det(\eta_{\tau k}y_\tau)$. Here $y^-_\tau$ is the $l \times l$ block of variables with both signs $-1$, and $y_\tau$ the $m \times p$ block with both signs $+1$. It lives on $(V', W)$.

Lean: `New.Rows.matchedPoly` (New/Determinant/Exchange/ExplicitMatching.lean).

### The archimedean step

Let $\gamma_\tau = |l| - |\iota_\tau|$ and let the real Weil action be twisted by $\prod_\tau\det(u_\tau)^{\gamma_\tau}$ on the second group.

**Lemma (Laws).** For $k$ in $U(m)$ at each place, placed in the positive block, the action of $k$ carries $\mathrm{SD}(\eta k^{-T})$ to $\prod_\tau\det(k_\tau)^{-|\iota_\tau|}\,\mathrm{SD}(\eta)$, and carries $\mathrm{MP}(\eta)$ to $\prod_\tau\det(k_\tau)^{-|\iota_\tau|}\,\mathrm{MP}(\eta k^T)$.

Lean: `New.Rows.realPairWeil_stackedDetProd`, `New.Rows.realPairWeil_matchedPoly` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* The point is block diagonal, so by the law of [the Weil representation](/chapter/weil-representation/) on polynomial vectors it acts by a linear substitution of the variables times a character. The substitution multiplies each matrix of a determinant by $k^{\pm T}$, and the factor is $\det k^{-|\iota_\tau|}$ after the twist $\gamma$. $\square$

**Lemma (Circle mean).** Let $t(z)$ be the diagonal point of $U(m)$ with entries $z^{-2}$ on $p$ and $z^{-1}$ on $a$. For each vector $y$ there is $\kappa$ such that for every functional $\ell$ invariant under $U(a)$, the mean over $|z| = 1$ of $z^{-|a|\sum|\iota_\tau|}\,\ell(\omega(t(z), z^{-1})y)$ is $\kappa\,\ell(\mathrm{SD}(\eta_0))$, where $\eta_0 = (1\ 0)$ is the standard frame.

Lean: `New.Rows.exists_mul_eq_circle_mean` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* Both sides are continuous in $y$ and polynomial vectors are dense, so take $y$ the vector of $P$. The torus scales every variable outside the columns $e(a)$ by $z$ and fixes these columns, after the scalar factors cancel. So the integrand is a polynomial in $z$, and its mean is its value at $z = 0$: the vector of $P_0$, which is $P$ with the other variables set to $0$. $P_0$ is a polynomial in square $a \times a$ matrices. Averaged over $U(a)$ with the weight $\prod_\tau \det^{-|\iota_\tau|}$, it is a multiple $\kappa$ of $\prod_\tau \det^{|\iota_\tau|}$, by the result on semi-invariant linear forms in the source ([`New.exists_forall_eq_mul_map_det_pow`](/decl/New.exists_forall_eq_mul_map_det_pow/)). As $\ell$ is invariant, it does not see the average. For $\eta_0$, the stacked determinant is the minor in the columns $e(a)$. $\square$

**Lemma (Polarization).** If $a \neq \emptyset$, there are coefficients $w_k$ on finitely many $k \in U(m)$ with $\mathrm{SD}(\xi) = \sum_k w_k\,\mathrm{SD}(\eta_0 k^T)$ and $\mathrm{MP}(\xi) = \sum_k w_k\,\mathrm{MP}(\eta_0 k^T)$.

Lean: `New.Rows.exists_stackedDetProd_eq_sum_unitary` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* As $|p| < |m|$, the products $\prod\det(\xi_{\tau k}Y_\tau)$ lie in a module that is irreducible under the unitary group ([`New.exists_pairedDetProd_eq_sum_unitary`](/decl/New.exists_pairedDetProd_eq_sum_unitary/)), so one combination works for every $Y$ over every ring. At a point $x$, a stacked determinant is $d\det(\xi Y)$ for some $Y$ and $d$, by part (a) of the lemma on products of determinants in Section 6. $\mathrm{MP}$ is a fixed polynomial times the product for $Y = y$. $\square$

**Theorem (Matching of real data).** Let $a \neq \emptyset$. There is a polynomial $Q_0$ such that each vector $v$ has $\kappa$ with this property. Let $\ell_g$ be continuous functionals with $\ell_g(\omega(x_1, x_2)w) = \ell_{gx_1}(w)$, and $\ell'$ linear on polynomials with $\ell_x(v) = \ell'(Q)$ whenever $x$ carries the vector of $Q_0$ to that of $Q$. Then $\kappa\,\ell_1(\mathrm{SD}(\eta)) = \ell'(\mathrm{MP}(\eta))$ for all $\eta$.

Lean: `New.Rows.exists_mul_apply_eq_apply_matchedPoly` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* Take $Q_0 = \mathrm{MP}(\eta_0)$ and $\kappa$ from the circle mean for $y = v$. Fix $k \in U(m)$ and $\xi = \eta_0 k^T$. Since $\eta_0\,(k\,t(z))^T = z^{-2}\xi$, the point $k\,t(z)$ carries $Q_0$ to a multiple of $\mathrm{MP}(z^{-2}\xi)$, by the laws. So $\ell_{k t(z)}(v)$ is $\ell'$ of that polynomial. Apply the circle mean to the invariant functional $\det(k)^{|\iota|}\,\ell_k$. The first law moves $\mathrm{SD}(\eta_0)$ to $\mathrm{SD}(\xi)$. The integrand is constant in $z$, as the powers of $z$ and of $\det k$ cancel. This gives the claim for $\xi$. Polarization and linearity give it for all $\eta$. $\square$

### The explicit identity

**Lemma (The functionals).** (a) The theta integral over $U(I_a)$ with datum $\Phi$ and real part $w$ is a continuous linear functional of $w$. (b) For matched $\Phi$, $\Psi$ and $\mathfrak{m} \neq (1)$, the integral over $[U(V')]$ of the kernel with data $\Psi$, $Q$ is a linear form in $Q$. (c) If $\alpha$ is tame for $(\mathfrak{m}, \gamma, \chi)$ and $\Phi$ is matched for $\chi^{-1}$, the integral over $U(I_a)$ of the kernel with data $\Phi$, $\mathrm{SD}(\eta)$ is its class sum at level $K_0$.

Lean: `New.Rows.exists_clm_eq_thetaIntegral_modDatum`, `New.Rows.exists_linearMap_eq_integral_modKernel`, `New.Rows.integral_modKernel_stackedDetProd` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* (a) The integral is the lift of the constant $1$, which has rapid decay on a definite group, and the datum is linear in $w$. (b) $\Psi$ lives on first columns of invertible matrices, so the kernel has rapid decay by Section 6, and the integral is linear. (c) The real group of $I_a$ fixes the vector of $\mathrm{SD}(\eta)$ under the twisted action, by the first law with $\eta$ fixed. Translation by $k \in K_0$ replaces $\Phi$ by $\alpha(\det k)\Phi(k^{-1}\cdot) = \Phi$, by tameness and matching. So the kernel is a function on the finite class space, and the integral is the class sum. $\square$

**Theorem (Explicit exchange).** Let $|a| = |b| + 2d$ and $|n| = 2|l| + 2s_0$ with $s_0 \geq 1$. There are $C > 0$ and $c'$, possibly $0$, such that every $\alpha$ of weight $-|\iota_\tau|$ that is tame for $(\mathfrak{m}, \chi)$ has $c$ with:

(a) $|c|^2 = C\,L_{\mathfrak{m}}(\nu^{-1}, d) \neq 0$ for $\nu = \alpha/\upsilon^{s_0}$;

(b) for all $\eta$, $g$ and matched $\Phi$, $\Psi$ for $\chi^{-1}$,
$$c'\,\mathrm{cs}_{K_0}\bigl(h \mapsto \alpha(\det h)\,\theta^{W, I_a}_{\upsilon^{|l|}, 1}(\Phi, \mathrm{SD}(\eta))(g, h)\bigr) = c\,\alpha(\det g)\int_{[U(V')]}\alpha(\det x)^{-1}\,\theta^{V', W}_{\upsilon^{|l|}, \upsilon^{|l|}}(\Psi, \mathrm{MP}(\eta))(x, g)\,dx.$$

Lean: `New.Rows.exists_stdClassSum_eq_of_exchange`, `New.Rows.exists_stdClassSum_eq_mul_integral_modKernel` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* Step 1. Take $Q_0$ from the matching of real data. Apply the exchange identity of Section 1 to $(W, I_a, V')$ and the vector of $Q_0$, with $\mu_\tau = |\iota_\tau| + s_0$. Its hypotheses hold: $I_a$ has no minus signs, so $\operatorname{neg}(W) = |l| = \operatorname{neg}(V')$; $2|l| + 2 \leq |n|$ as $s_0 \geq 1$; and $|n| \leq 2\mu_\tau + 2|l|$. This gives $C > 0$ and $v$. Let $c'$ be the $\kappa$ of $v$.

Step 2. Let $\alpha$ be as stated. Then $\nu^{-1}$ is tame for $(\mathfrak{m}, \mu, \chi^{-1})$, and the exchange identity gives $c$ with (a). Put $\gamma = \upsilon^{|l|}\alpha$. It is tame of weight $|l| - |\iota_\tau|$, and $\gamma = \nu\,\upsilon^{|l| + s_0} = \nu\,\upsilon^{|n|/2}$ is the character of $W$ in the exchange identity for the character $\nu^{-1}$. The characters $1$ on $I_a$ and $\gamma$ on $V'$ satisfy the condition on space characters. So the theta integral with $(\gamma, 1)$ and real part $v$ is $c$ times the integral with $(\gamma, \gamma)$ and $Q_0$, at every point.

Step 3. Let $\ell_y$ be the functional (a) at $g(y, 1)$, and $\ell' = c$ times the form (b) at $g$. A real point $y$ that carries $Q_0$ to $Q$ moves the kernel of $Q_0$ at $gy$ to the kernel of $Q$ at $g$. So Step 2 gives the hypothesis of the matching of real data. Its conclusion and part (c) give (b) with the characters $\gamma$. The twist law of the kernels turns $\gamma$ into $\upsilon^{|l|}$ with the factors $\alpha(\det h)$, $\alpha(\det g)$, $\alpha(\det x)^{-1}$. $\square$

**Corollary.** Let $|a| = |b| + 2d$ and $2|l| + 2 \leq |n|$. There is $C \geq 0$, possibly $0$, such that every $\alpha$ of weight $|l| - |\iota_\tau|$ tame for $(\mathfrak{m}, \chi)$ has $c$ with $|c|^2 = C/L_{\mathfrak{m}}(\alpha^{-1}\upsilon^{|b|+d}, d)$ and, for all $\eta$, matched $\Phi$, $\Psi$ for $\chi^{-1}$, all $\beta$ and $g$,
$$c\,\mathrm{cs}_{K_0}\bigl(\theta^{W, I_a}_{\alpha, \beta}(\Phi, \mathrm{SD}(\eta))(g, \cdot)\bigr) = \int_{[U(V')]}\theta^{V', W}_{\alpha/\beta, \alpha}(\Psi, \mathrm{MP}(\eta))(x, g)\,dx.$$

Lean: `New.Rows.exists_mul_stdClassSum_eq_integral_modKernel` (New/Determinant/Exchange/ExplicitMatching.lean).

*Proof.* Write $|b| + d = s_0 + |l|$; then $s_0 \geq 1$. Apply the theorem and write $\alpha = \upsilon^{|l|}\alpha_0$, so $\alpha_0$ has weight $-|\iota_\tau|$ and the same tame part. Then $(\alpha_0/\upsilon^{s_0})^{-1} = \alpha^{-1}\upsilon^{|b|+d}$. The theorem gives $c_0 \neq 0$. Put $c = c'/c_0$ and $C = |c'|^2/C_0$. The twist law gives each kernel of the corollary as the kernel of the theorem times $\beta(\det g)^{-1}$ and values of $\alpha_0$. Divide (b) by $c_0$. $\square$

**Example (Rank zero).** Let $b = \emptyset$, so $a \simeq n$ and $d = |n|/2$. The functions $\chi\circ\det$ and $1$ are matched for $\chi^{-1}$. The space $V'$ has volume $1$, $\mathrm{MP}(\eta) = 1$, and the kernel of $(V', W)$ with data $1$, $1$ is $\alpha(\det g)$. So the right side of (b) is $c\,\alpha(\det g)$.

Lean: `New.Rows.areMatched_det_one`, `New.Rows.integral_modKernel_matchedPoly_of_isEmpty` (New/Determinant/Exchange/ExplicitMatching.lean).

**Remark (Formalization).** Three points. First, the exponent $|\iota_\tau| + |n| - 2|l|$ is a truncated subtraction of natural numbers. It is exact here, as $2|l| + 2 \leq |n|$. Second, the explicit theorem gives no information on $c'$: if $c' = 0$, part (b) says only that the right side vanishes, and the corollary has $C = 0$. The [register of findings](/chapter/register-of-findings/) records this constant. Third, the explicit exchange is the one place in this chapter where the margin $+2$ of the exchange identity is a real hypothesis, through $s_0 \geq 1$.
