---
title: Moving blocks
lean:
  - New/Spanning/Unfolding/AmplitudeSums.lean
decls:
  - New.Filling.isStable_besselS
  - New.Filling.besselFn_mul_of_mem_classUnipotent
  - New.Filling.besselKernel_besselU_mul
  - New.Filling.mem_termsOver_iff_mul_mul_inv_mem
  - New.Filling.mul_mul_inv_mem_inter_termsOver
  - New.Filling.tsum_classCutoff_ratToInf_mul_eq_one
  - New.Filling.lintegral_mul_eq_of_isCutoff
  - New.Filling.hasSum_amplitudeSum_of_cutoff
  - New.Filling.amplitudeSum_mul_mul_inv
  - New.Filling.amplitudeSum_besselU_mul
  - New.Filling.amplitudeSum_eq_zero_of_not_agrees
  - New.Filling.measurePreserving_pi_orbitMeasure
  - New.Filling.integral_classCutoff_eq_unipotentCovolume
  - New.Filling.amplitudeSum_besselS_one_eq_ite
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Moving blocks

An amplitude sum is defined with the weight $\beta_c(y)\beta_{c'}(\gamma^{-1}y)$. This section shows that any other weight with the same orbit sums gives the same sum. With this freedom a block can be moved by elements of the Bessel group. Three results follow: the scalar law under the unipotent group, the vanishing of the blocks whose reduction does not agree, and the value of the identity block.

The standing assumptions are those of [the previous section](/chapter/poincare-series/#convergence-of-the-amplitude-sums). In addition $T$ is *stable*: for all rational $u, u' \in \mathsf{U}$ and all $\gamma$, $u^{-1}\gamma u' \in T$ if and only if $\gamma \in T$ ([Definition](/decl/New.Filling.IsStable/)).

### The action of the unipotent group

**Lemma (The Bessel group is stable).** The set of rational points of the Bessel subgroup $R_0$ is stable.

Lean: `New.Filling.isStable_besselS` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* $R_0$ is a group that contains $\mathsf{U}$. $\square$

[The anatomy of a term](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data) proves that for a rational $u \in \mathsf{U}$, $W(\iota_\infty(u)y) = \chi(u)^{-1}W(y)$ (`New.Filling.besselFn_ratToInf_mul`), and that $\chi(u) = 1$ when $h_c^{-1}uh_c \in K(M)$.

**Lemma (Invariance under the group of a class).** For $u \in \mathsf{U}_c(M)$, $W(\iota_\infty(u)y) = W(y)$, for both sides.

Lean: `New.Filling.besselFn_mul_of_mem_classUnipotent` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* The factor is $\chi(u)^{-1}$, and $\chi(u) = 1$ since $h_c^{-1}uh_c$ lies in the principal level. $\square$

**Lemma (The kernel under the unipotent group).** Let $u, u' \in \mathsf{U}$ be rational. Then the kernel $K(\gamma, y) = W(y)\otimes\overline{W(\gamma^{-1}y)}$ satisfies

$$K(u\gamma u'^{-1}, uy) = \chi(u)^{-1}\chi(u')\,K(\gamma, y).$$

Lean: `New.Filling.besselKernel_besselU_mul` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* We have $(u\gamma u'^{-1})^{-1}uy = u'\gamma^{-1}y$. So the first factor changes by $\chi(u)^{-1}$ and the second by $\overline{\chi(u')^{-1}} = \chi(u')$, since $|\chi(u')| = 1$. $\square$

**Lemma (Terms under translation).** Let $\sigma$ be a term over $(c, t, c_1)$ and $\sigma'$ a term over $(c', t', c_1')$. Then $\gamma$ is a term over $(c_1, s, c_1')$ if and only if $\sigma\gamma\sigma'^{-1}$ is a term over $(c, tst'^{-1}, c')$. In particular, for $u \in \mathsf{U}_c(M)$ and $u' \in \mathsf{U}_{c'}(M)$ the map $\gamma \mapsto u\gamma u'^{-1}$ preserves $T \cap \mathrm{terms}(c, s, c')$.

Lean: `New.Filling.mem_termsOver_iff_mul_mul_inv_mem`, `New.Filling.mul_mul_inv_mem_inter_termsOver` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Terms compose and invert like a groupoid ([the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block)). An element of $\mathsf{U}_c(M)$ is a term over $(c, 1, c)$. Stability keeps $T$. $\square$

**Lemma (Translated cutoffs).** Let $\sigma \in R_0$ be rational and a term over $(c, t, c_1)$. Then for all $y$,

$$\sum_{u \in \mathsf{U}_{c_1}(M)}\beta_c(\sigma uy) = 1.$$

Lean: `New.Filling.tsum_classCutoff_ratToInf_mul_eq_one` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* $R_0$ normalizes $\mathsf{U}$. By the lemma on terms under translation with $s = 1$, conjugation by $\sigma$ maps $\mathsf{U}_{c_1}(M)$ onto $\mathsf{U}_c(M)$. So the sum is $\sum_{u' \in \mathsf{U}_c(M)}\beta_c(u'\sigma y)$, which is $1$ because $\beta_c$ is a cutoff for $\mathsf{U}_c(M)$. $\square$

### The change of weight

A *cutoff* for a group $H$ acting on a measure space is a measurable $\beta \geq 0$ with $\int_H\beta(u\cdot p)\,du = 1$ for every point $p$ ([reduction theory](/chapter/reduction-theory/), [Definition](/decl/New.IsCutoff/)). For an invariant function $F$, $\int\beta F$ is the integral of $F$ over the quotient for every cutoff $\beta$ ([Lemma](/decl/New.IsCutoff.integral_orbitMeasure/)).

**Lemma (Two cutoffs give one integral).** Let $H$ act measurably on $Z$ and preserve $\mu$, with $H$ carrying an inversion invariant measure. Let $\beta, \beta'$ be cutoffs and $F \geq 0$ measurable and invariant. Then $\int\beta F\,d\mu = \int\beta'F\,d\mu$.

Lean: `New.Filling.lintegral_mul_eq_of_isCutoff` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Both sides are the integral of $F$ over the quotient by $H$. $\square$

**Theorem (Change of weight).** Let $T$ be stable. Let $\varphi(\gamma, y) \in [0, \infty]$ be measurable in $y$, with

$$\sum_{(u, u') \in \mathsf{U}_c(M)\times\mathsf{U}_{c'}(M)}\varphi(u\gamma u'^{-1}, \iota_\infty(u)y) = 1$$

for all $\gamma \in T \cap \mathrm{terms}(c, s, c')$ and all $y$. Then, for both sides:

1. the integrals $\int\varphi(\gamma, y)K(\gamma, y)\,dy$, for $\gamma \in T \cap \mathrm{terms}(c, s, c')$, have the sum $\mathcal{A}(c, s, c')$ (a `HasSum`);
2. each integrand is integrable;
3. $\sum_\gamma\int\varphi(\gamma, y)\,\|K(\gamma, y) - K^\flat(\gamma, y)\|\,dy \leq \nu b^{-k^3f}/2$.

Lean: `New.Filling.hasSum_amplitudeSum_of_cutoff` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Put $X = T \cap \mathrm{terms}(c, s, c')$ and $\Delta = \mathsf{U}_c(M)\times\mathsf{U}_{c'}(M)$. Let $\Delta$ act on $X \times G_\infty$ by $(u, u')\cdot(\gamma, y) = (u\gamma u'^{-1}, \iota_\infty(u)y)$. This is well defined by the lemma on terms under translation. It preserves the measure $\rho$, the counting measure on $X$ times the Haar measure. By the lemmas on the kernel and on the invariance under the group of a class, the kernel is invariant: the factor is $\chi(u)^{-1}\chi(u') = 1$.

The weight $\beta_0(\gamma, y) = \beta_c(y)\beta_{c'}(\gamma^{-1}y)$ is a cutoff for $\Delta$: its orbit sum is $\sum_u\beta_c(uy)\cdot\sum_{u'}\beta_{c'}(u'\gamma^{-1}y) = 1$. The hypothesis says that $\varphi$ is a cutoff too.

For any cutoff $\beta$ and any invariant $F \geq 0$, the lemma on two cutoffs gives $\int\beta F\,d\rho = \int\beta_0F\,d\rho$. For $F = \|K\|$ the right side is at most $\sum_{c'}\sum_\gamma(\text{majorants})$, which is finite by [the theorem on the majorants](/chapter/poincare-series/#convergence-of-the-amplitude-sums). So $\beta K$ is integrable on $X \times G_\infty$, and by Fubini each slice $\beta(\gamma, \cdot)K(\gamma, \cdot)$ is integrable. This gives part 2 for $\varphi$.

By Fubini, $\sum_\gamma\int\beta(\gamma, y)K(\gamma, y)\,dy$ converges to the integral of $K$ over the quotient, for every cutoff $\beta$. For $\beta_0$ the sum is $\mathcal{A}(c, s, c')$. So the integral over the quotient is $\mathcal{A}(c, s, c')$, and the same sum for $\varphi$ converges to it. This is part 1.

For part 3, put $F = \|K - K^\flat\|$, which is invariant. The lemma on two cutoffs and the theorem on the tail of the cut give the bound. $\square$

**Remark (Formalization).** Part 2 is what makes each Bochner integral of the change of weight a true integral. The definition of $\mathcal{A}(c, s, c')$ uses `toReal` of $\beta_c\beta_{c'}$. Where a cutoff is $\infty$, `toReal` gives $0$. The cutoffs are almost everywhere finite, so this does not change any integral.

### Moving a block

**Theorem (Moving a block).** Let $T$ be stable. Let $\sigma, \sigma' \in R_0$ be rational, $\sigma$ a term over $(c, t, c_1)$ and $\sigma'$ a term over $(c', t', c_1')$. Suppose that $\gamma \in T$ if and only if $\sigma\gamma\sigma'^{-1} \in T$. Let $L$ be a continuous linear map with $K(\sigma\gamma\sigma'^{-1}, \sigma y) = L(K(\gamma, y))$ for all $\gamma, y$. Then

$$\mathcal{A}(c, tst'^{-1}, c') = L\bigl(\mathcal{A}(c_1, s, c_1')\bigr).$$

Lean: `New.Filling.amplitudeSum_mul_mul_inv` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Put $\varphi(\gamma, y) = \beta_c(\sigma y)\,\beta_{c'}(\sigma'\gamma^{-1}y)$. Its orbit sums under $\mathsf{U}_{c_1}(M)\times\mathsf{U}_{c_1'}(M)$ are products of two sums of translated cutoffs, so they are $1$. The change of weight writes $\mathcal{A}(c_1, s, c_1')$ as $\sum_\gamma\int\varphi(\gamma, y)K(\gamma, y)\,dy$, with integrable terms. Apply $L$, which commutes with the integral and the sum. Substitute $y \mapsto \sigma^{-1}y$, which preserves the Haar measure, and $\gamma \mapsto \sigma\gamma\sigma'^{-1}$, which is a bijection from $T \cap \mathrm{terms}(c_1, s, c_1')$ onto $T \cap \mathrm{terms}(c, tst'^{-1}, c')$. The term at $\sigma\gamma\sigma'^{-1}$ becomes $\int\beta_c(y)\beta_{c'}((\sigma\gamma\sigma'^{-1})^{-1}y)K(\sigma\gamma\sigma'^{-1}, y)\,dy$, the amplitude of $\sigma\gamma\sigma'^{-1}$. $\square$

**Theorem (The scalar law).** Let $T$ be stable, and let $u, u' \in K \cap \mathsf{U}(\mathbb{A}_f)$ with reductions $\bar u, \bar u'$. Then

$$\mathcal{A}(c, \bar us\bar u'^{-1}, c') = \chi(u)^{-1}\chi(u')\,\mathcal{A}(c, s, c').$$

Lean: `New.Filling.amplitudeSum_besselU_mul` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* By [rational approximation with the same character](/decl/New.Filling.exists_rat_approx_unipotentChar_eq/) there are rational $x, x' \in \mathsf{U}$ with $\chi(x) = \chi(u)$, $\chi(x') = \chi(u')$, $u^{-1}x_{c,c} \in K(M)$ and $u'^{-1}x'_{c',c'} \in K(M)$. So $x$ is a term over $(c, \bar u, c)$ and $x'$ over $(c', \bar u', c')$. Stability gives $\gamma \in T \Leftrightarrow x\gamma x'^{-1} \in T$. The lemma on the kernel gives $L = \chi(x)^{-1}\chi(x')$. Moving the block gives the claim. $\square$

**Corollary (Blocks that do not agree vanish).** Let $T$ be stable. If $s$ does not agree, then $\mathcal{A}(c, s, c') = 0$.

Lean: `New.Filling.amplitudeSum_eq_zero_of_not_agrees` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* That $s$ does not agree means: there are $u, u' \in K \cap \mathsf{U}$ with $\bar us = s\bar u'$ and $\chi(u) \neq \chi(u')$ ([Definition](/decl/New.Filling.Agrees/)). Then $\bar us\bar u'^{-1} = s$. The scalar law gives $\mathcal{A}(c, s, c') = \chi(u)^{-1}\chi(u')\mathcal{A}(c, s, c')$ with a factor $\neq 1$. So $\mathcal{A}(c, s, c') = 0$. $\square$

### The identity block

**Lemma (Unfolding at several places).** Let $\nu_0$ be a unimodular Haar measure on a subgroup $A$ of $G_1$ and $P$ a finite set. The map $(x, u) \mapsto (u_vx_v)_v$ carries the product of the quotient measures on $(A\backslash G_1)^P$ and of the copies of $\nu_0$ to the Haar measure on $G_1^P$.

Lean: `New.Filling.measurePreserving_pi_orbitMeasure` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* At one place this is the definition of the quotient measure in [reduction theory](/chapter/reduction-theory/). A product of measure preserving maps is measure preserving for the product measures. $\square$

**Lemma (The integral of a cutoff).** For every class $c$ and $x \in G_\infty$, $\int_{\prod_v\mathsf{U}(\mathbb{R})}\beta_c(ux)\,du = \nu$, as a complex number.

Lean: `New.Filling.integral_classCutoff_eq_unipotentCovolume` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* The integral of $\beta_c(ux)$ in $[0, \infty]$ is $\nu$ ([Lemma](/decl/New.Filling.lintegral_classCutoff_eq_unipotentCovolume/)). It is finite, so $\beta_c(ux) < \infty$ for almost all $u$, and the Bochner integral of `toReal` is the same number. $\square$

**Theorem (The identity block).** Let $i, j$ be Bessel coordinates. The entry $(i, j)$ of the amplitude sum of the full side over $T = R_0$ and the block $(c, 1, c')$ is

$$\mathcal{A}(c, 1, c')_{i,j} = \begin{cases}\nu & \text{if } c = c' \text{ and } i = j,\\ 0 & \text{otherwise.}\end{cases}$$

Lean: `New.Filling.amplitudeSum_besselS_one_eq_ite` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* A rational $\gamma \in R_0$ that is a term over $(c, 1, c')$ has $c = c'$ and $\gamma \in \mathsf{U}_c(M)$ ([identity terms are unipotent](/decl/New.Filling.eq_and_mem_classUnipotent_of_besselS/)). If $c \neq c'$ the index set is empty and the sum is $0$.

Let $c = c'$. Put $\varphi(\gamma, \cdot) = \beta_c$ if $\gamma = 1$ and $0$ otherwise. For $\gamma \in \mathsf{U}_c(M)$ the orbit sum is $\sum_{u, u'}[u\gamma u'^{-1} = 1]\,\beta_c(uy) = \sum_u\beta_c(uy) = 1$, since for each $u$ exactly one $u'$, namely $u\gamma$, gives $1$. So the change of weight applies with $T = R_0$, which is stable. Only $\gamma = 1$ contributes, and

$$\mathcal{A}(c, 1, c)_{i,j} = \int\beta_c(y)\prod_vF_v(y_v)\,dy,\qquad F_v(y) = W_{v,i_v}(y)\overline{W_{v,j_v}(y)}.$$

The function $F_v$ is invariant under $\mathsf{U}$, since $W_v(uy) = \theta(u)W_v(y)$ with $|\theta(u)| = 1$. Unfold at all places with the lemma on unfolding at several places. The integral of $\beta_c$ over the unipotent part is $\nu$. So

$$\mathcal{A}(c, 1, c)_{i,j} = \nu\prod_v\int_{\mathsf{U}\backslash G_1}W_{v,i_v}\overline{W_{v,j_v}}.$$

The coordinates of $W_v$ are orthonormal in $L^2(\mathsf{U}\backslash G_1)$ ([Corollary](/decl/New.BesselSystem.orthonormal/), in [Bessel functions at a real place](/chapter/bessel-real-place/#schur-bounds-and-orthonormality)). So each factor is $1$ if $i_v = j_v$ and $0$ otherwise. The product is $1$ exactly when $i = j$. $\square$

The theorem says that the diagonal block of the scaled Poincaré map is the identity: after division by $\nu$, the identity terms give the identity matrix. [Moments of the Poincaré map](/chapter/moments/) uses this result.
