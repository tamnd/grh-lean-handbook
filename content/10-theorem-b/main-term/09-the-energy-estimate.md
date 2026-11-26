---
title: The energy estimate
lean:
  - New/Spanning/MainTerm/EnergyEstimate.lean
decls:
  - New.Filling.normalizingConst
  - New.Filling.gramScalar_mul_headDensity
  - New.Filling.prod_bandLimit_eq_gram
  - New.Filling.sieve_constant_le
  - New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le
  - New.Filling.sum_norm_sum_cosetAmplitude_sq_le
  - New.Filling.IsOpenElement.leadingMinor_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The energy estimate

This section puts the parts together and proves [the theorem on the main term](/chapter/main-term/#what-the-chapter-proves). Siegel's step at $T$ is combined with the Bessel systems at the infinite places. The global sieve bounds the result, and a computation of constants gives the right side of the theorem.

### Normalisation

The Gram matrix $R$ of Siegel's step must be the product of the top forms of the sieve systems.

**Lemma (Gram matrix).** Let $\sigma$ be in the floor group with last frame product $t$. Let $R(p, q)$ be the product over the infinite places $v$ of the top forms $\operatorname{bandLimit}_n$ of the Bessel systems, at the scaled heads $x_v(p)_a = \operatorname{unitOrOne}(\kappa_v^{2(\varrho - a)}N^{-1}\Phi_v(p_a))$. Then $R$ is the Gram matrix of the orbital integrals $\int W^\flat(y) \otimes W^\flat((w_p\sigma)^{-1}y)^*\,dy$, each weighted by the product over $v$ of the scalars of the normalised orbital integral of [Bessel functions at a real place](/chapter/bessel-real-place/).

Lean: `New.Filling.prod_bandLimit_eq_gram` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* The cut Bessel function at infinity is a product over $v$, so the orbital integral is a tensor product over $v$. The top form at $v$ is the inner product of two normalised orbital integrals. Multiply over $v$. $\square$

**Lemma (Normalising constant).** The product of the scalars of the normalised orbital integrals at $x_v(p)$ and of the head density of $p$ at $T$ is $r\sqrt{G}$, where $r = \operatorname{normalizingConst}(k - 1)$ does not depend on $p$ and $G = (\prod_v(|t|_v^2 - N^2))^{k-1}$.

Lean: `New.Filling.normalizingConst`, `New.Filling.gramScalar_mul_headDensity` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* The scalar at $v$ contains $\prod_{a<\varrho}|x_a|^{k+1+2(\varrho-a-1)}$. The head density at $T$ contains the same powers of the moduli of $p_a$ at $T$. The entries $p_a$ are $T$-units, so by the product formula the powers of $p_a$ cancel. What remains is $\sqrt{c_G}$, the powers of the frame scales and the numbers of indices, which is $r$, times the factor of $t$. $\square$

### The constant

**Lemma (Sieve constant).** Let $\#S_g \leq f$. The bound of [the global sieve](/chapter/main-term/#the-global-sieve), with the finite mass $m = (1 + b^{-6})(b^{6k})^{-\#S_g}$, times the constant $(1 + b^{-6})\operatorname{scaledSiegelConst}$ of Siegel's step, is at most
$$r^2(1 + b^{-4})(b^{6k})^{-\#S_g}\,\mathcal D_{\mathrm{main}}\,\nu^2.$$

Lean: `New.Filling.sieve_constant_le` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* The product of the constants of Poisson summation is $(\operatorname{vol}\hat{\mathcal O})^{n}$ over the Jacobians of the scalings at infinity. Together with $\operatorname{scaledSiegelConst}$ and the inverse degrees it gives $r^2\mathcal D_{\mathrm{main}}\nu^2$; this is an identity of explicit products (`New.Filling.prod_poissonConst_eq`). The factors $(1 + b^{-10})^f \leq 1 + b^{-9}$, $1 + b^{-6}$ twice, and the error $b^{2403n^9f}$ times the decay constant, which is at most $b^{-10}$ times the main term (`New.Filling.scaledSiegelConst_mul_decayConst_le`), combine to at most $1 + b^{-4}$ (`New.Filling.one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four`). $\square$

### Siegel's step and the sieve

**Theorem (Siegel's step, global form).** Let $1/M$, $1/N$ and the lattice basis be integral off $T$, let $G$ be a filling datum and $Y$ an intermediate group. For finitely many distinct classes $(c_i, \bar n_i, c'_i, \sigma_i)$ with $\sigma_i$ in the floor group, last entry $t_i$ with $|t_i|_v > N$, positions integral off $T$ and $n_i \in Y$ at $T$,
$$r^2\sum_i\Bigl\|\sum_{p}\operatorname{cosetAmplitude}(w_{(p, t_i)}\sigma_i)\Bigr\|^2 \leq (1 + b^{-6})\operatorname{scaledSiegelConst}\cdot\operatorname{Re}\sum_t\sum_{p,q}\prod_v\operatorname{bandLimit}_n\cdot\frac{\rho_\pi(p, q)}{\operatorname{massRatio}(Y)},$$
where $p$ runs over the heads with entries in a finite set $T_0$ of $T$-units.

Lean: `New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* Group the classes by their last entry $t$. For one $t$, apply [Siegel's step](/chapter/main-term/#siegels-bound) with the Gram matrix of the lemma on the Gram matrix and $\rho_p$ the scalar of the normalised orbital integral; the lemma on the normalising constant gives $\rho_p\kappa_p = r\sqrt G$. Add over $t$. $\square$

**Theorem (Bound for coset sums).** Let $S$ be admissible and $S_g$ a set of chosen places above $p_0$. For finitely many distinct classes as above, with the reductions in $\operatorname{fixer}(S_g, D)$,
$$\sum_i\Bigl\|\sum_p\operatorname{cosetAmplitude}(w_{(p, t_i)}\sigma_i)\Bigr\|^2 \leq (1 + b^{-4})(b^{6k})^{-\#S_g}\,\mathcal D_{\mathrm{main}}\,\nu^2.$$

Lean: `New.Filling.sum_norm_sum_cosetAmplitude_sq_le` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* Take filling data $G$ at $T$ ([Section 5](/chapter/main-term/#the-place-at-t-and-filling-data)) and the group $Y$ of [the finite sieve system](/chapter/main-term/#fixed-lines-and-the-finite-system); by (a) it contains the components of the $n_i$. Apply the global form of Siegel's step. The forms at the infinite places and at $T$ are sieve systems, so the global sieve bounds the right side by its constant. The lemma on the sieve constant bounds this by $r^2$ times the right side of the claim. Divide by $r^2 > 0$. $\square$

### Proof of the main theorem

**Lemma (Open elements).** If $s$ is open and $\gamma$ is a term over $(c, s, c')$, the leading minors $D_0, \dots, D_\varrho$ of the frame products of $\gamma$ are nonzero.

Lean: `New.Filling.IsOpenElement.leadingMinor_ne_zero` (New/Spanning/MainTerm/EnergyEstimate.lean).

*Proof.* The reduction of a minor of $\gamma$ modulo the chosen place $w$ is the minor of $(h(f_j, sf_l))$, which is nonzero. So the minor is nonzero. $\square$

*Proof of [the theorem on the main term](/chapter/main-term/#what-the-chapter-proves).* Choose $T$ by [the choice of places](/chapter/main-term/#the-place-at-t-and-filling-data) for the finite set $\mathcal T$ of entries. The left side is a sum in $[0, \infty]$ of squared norms of blocks, so it suffices to bound every finite sum of nonzero blocks. Each nonzero block over an open $s$ is, by the lemma on open elements and [blocks as coset sums](/chapter/main-term/#kloosterman-sums-and-unfolding), a sum over heads $p$ with entries in $\mathcal T$ of coset amplitudes at $w_{(p,t)}\sigma$, for some $(t, \sigma, k)$ that names the link. Distinct blocks give distinct classes $(c, \bar k, c', \sigma)$, because the link $\Lambda$ is the link of $w_1\sigma$. The reductions lie in the fixer. Apply the bound for coset sums. $\square$
