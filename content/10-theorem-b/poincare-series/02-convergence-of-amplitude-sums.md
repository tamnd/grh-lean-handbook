---
title: Convergence of the amplitude sums
lean:
  - New/Spanning/Unfolding/AmplitudeSums.lean
decls:
  - New.Filling.tsum_mul_inv_pow_le_of_layers
  - New.Filling.scaledBesselLengthProd
  - New.Filling.tsum_classCutoff_mul_inv_pow_le
  - New.Filling.le_scaledBesselLengthProd_mul
  - New.Filling.enorm_besselKernel_sub_cut_le
  - New.Filling.lintegral_classCutoff_mul_prod
  - New.Filling.tsum_lintegral_classCutoff_mul_majorant_le
  - New.Filling.cut_exponent_le
  - New.Filling.inv_pow_mul_unipotentCovolume_mul_card_le
  - New.Filling.exists_tsum_classCutoff_mul_prod_enorm_le
  - New.Filling.tsum_amplitudeMajorant_lt_top
  - New.Filling.tsum_lintegral_enorm_besselKernel_sub_cut_le
  - New.Filling.summable_amplitude
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Convergence of the amplitude sums

An amplitude sum is a sum `tsum` of Bochner integrals. In Lean both are $0$ when they do not converge ([conventions](/chapter/theorem-b-plan/#conventions-that-change-the-meaning)). This section proves that they converge. It also bounds the change of an amplitude sum when $W$ is replaced by its cut $W^\flat$. Both bounds come from one count: the number of terms $\gamma$ for which $\gamma^{-1}y$ is short grows like a power of the length, and the Bessel functions decay faster.

Throughout, $S$ is admissible, $E$ contains a primitive $5040$-th root of unity, $T$ is a set of rational elements, $c$ is a class and $s \in \bar G$. Write $n = \varrho + 1$, $r$ for the rank of $G_1$, $f$ for the number of infinite places, $b$ for the base of $S$ and $i = r^3f$. Write $\gamma^{-1}y$ for $\iota_\infty(\gamma)^{-1}y$, where $\iota_\infty$ maps $G(E)$ to $G_\infty$.

### Sums by layers

**Lemma (Summation by layers).** Let $u_p \geq 1$ and $w_p \in [0, \infty]$ for $p$ in a set $\alpha$, and let $K \geq 0$. Suppose that for every $R \geq 1$ the points with $u_p \leq R$ have total weight at most $(KR^e)^d$. If $2ed < i$, then

$$\sum_p w_p\, u_p^{-i} \leq 2K^d.$$

Lean: `New.Filling.tsum_mul_inv_pow_le_of_layers` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Let $\mu$ be the measure on $\alpha$ with mass $w_p$ at $p$. The sum is $\int u^{-i}\,d\mu$. By the layer cake formula it is $\int_0^1 \mu\{u^{-i} > t\}\,dt$, since $u^{-i} \leq 1$. For $t \in (0, 1)$ the set $\{u^{-i} > t\}$ lies in $\{u \leq t^{-1/i}\}$, of measure at most $K^dt^{-ed/i}$. So the sum is at most $K^d\int_0^1 t^{-ed/i}\,dt = K^d/(1 - ed/i)$. As $ed/i < 1/2$, this is at most $2K^d$. $\square$

### The scaled length and the count of terms

At a real place the length of $x \in G_1$ is $\ell(x) = \inf_{\sigma}(\|\sigma x\| + 1)$, the infimum over the Bessel subgroup. Its scaled form is $\max(1, \ell(x)/b^{6n})$ ([the group, the Bessel subgroup and the length](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length)).

**Definition (Product of the scaled lengths).** For $y \in G_\infty$,

$$L(y) = \prod_v \max\bigl(1, \ell(y_v)/b^{6n}\bigr).$$

Then $L(y) \geq 1$, and $L(y)$ is at least the scaled length at each place.

Lean: `New.Filling.scaledBesselLengthProd` (New/Spanning/Unfolding/AmplitudeSums.lean).

The count uses a packing lemma of [counts of frames](/chapter/frame-counts/). In one line: if the weights $w_p$ sit on distinct pairs (class $d_p$, term $\gamma_p$ over $(c, s, d_p)$), each $w_p$ is at most $\beta_{d_p}(\gamma_p^{-1}y)$, and every $\gamma_p^{-1}y$ has length at most $b^{6n+2}R$ at each place, then the weights add up to at most $(b^{6n^2}R^2)^{\dim}$, where $\dim = 2nrf$ is the real dimension of the space of frames ([Lemma](/decl/New.Filling.tsum_le_of_le_classCutoff_mul/)).

**Lemma (The count of terms).** For every $y \in G_\infty$,

$$\sum_{d}\ \sum_{\gamma \in T \cap \mathrm{terms}(c, s, d)} \beta_d(\gamma^{-1}y)\, L(\gamma^{-1}y)^{-i} \leq 2b^{12n^3rf}.$$

Lean: `New.Filling.tsum_classCutoff_mul_inv_pow_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Index the terms by the pairs $p = (d, \gamma)$. Put $w_p = \beta_d(\gamma^{-1}y)$ and $u_p = L(\gamma^{-1}y)$. Fix $R \geq 1$. If $u_p \leq R$ and $w_p \neq 0$, then at each place $\ell((\gamma^{-1}y)_v)/b^{6n} \leq L(\gamma^{-1}y) \leq R$, so $\ell \leq b^{6n}R \leq b^{6n+2}R$. The packing lemma, applied to the weights $w_p\mathbf{1}_{u_p \leq R}$ with the whole space of frames, gives the total weight $(b^{6n^2}R^2)^{2nrf}$. So the summation by layers applies with $K = b^{6n^2}$, $e = 2$ and $d = 2nrf$. Its condition is $8nrf < r^3f$, which holds since $r \geq 2\varrho + 1$ and $\varrho \geq 10^5$ give $8n < r^2$. The bound is $2(b^{6n^2})^{2nrf} = 2b^{12n^3rf}$. $\square$

### Decay majorants and the gain of the cut

At each real place $v$ the Bessel system gives a *decay majorant* $A_v$ with a bound $a_v$ ([decay and the cut](/chapter/bessel-real-place/#decay-and-the-cut)). In one line: $A_v$ is measurable and left invariant under the Bessel subgroup, $\max(1, \ell(x)/b^{6n})^{3i}\|W_v(x)\| \leq A_v(x)$ and the same for $W^\flat_v$, $A_v \leq a_v < \infty$, and $a_v\int_{\mathsf{U}\backslash G_1}A_v \leq b^{400r^2}\dim$. The cut changes $W_v$ only where $\ell(x) > b^{6n+2}/2$.

**Lemma (Where the cut acts).** If the kernel of $\gamma$ at $y$ differs from the cut kernel, then $b \leq L(y)\,L(\gamma^{-1}y)$.

Lean: `New.Filling.le_scaledBesselLengthProd_mul` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Suppose $L(y)L(\gamma^{-1}y) < b$. Then $L(z) < b$ for $z = y$ and for $z = \gamma^{-1}y$, since the other factor is at least $1$. If $W^\flat_v(z_v) \neq W_v(z_v)$ at some place, then $\ell(z_v) > b^{6n+2}/2$, and $\max(1, \ell(z_v)/b^{6n}) \geq b^2/2 \geq b$ since $b \geq 2$. That contradicts $L(z) < b$. So $W$ and $W^\flat$ agree at both points, and the two kernels are equal. $\square$

**Lemma (The difference of the kernels).** Let $A_v$, $a_v$ be decay majorants. Then

$$\bigl\|W(y)\otimes\overline{W(\gamma^{-1}y)} - W^\flat(y)\otimes\overline{W^\flat(\gamma^{-1}y)}\bigr\| \leq 2b^{-2i}\prod_v A_v(y_v)\prod_v a_v\, L(\gamma^{-1}y)^{-i}.$$

The same bound holds for the cut side, where the left side is $0$.

Lean: `New.Filling.enorm_besselKernel_sub_cut_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* If the kernels are equal there is nothing to prove. Otherwise the lemma on where the cut acts gives $b^{2i} \leq L(y)^{2i}L(\gamma^{-1}y)^{2i}$. The norm of a tensor is the product of the norms. At $y$, the majorant gives $L(y)^{2i}\prod_v\|W_v(y_v)\| \leq \prod_v A_v(y_v)$, since $L(y)^{3i}$ is the product of the local powers of the scaled lengths. At $\gamma^{-1}y$, it gives $L(\gamma^{-1}y)^{2i}\prod_v\|W_v\| \leq \prod_v a_v\,L(\gamma^{-1}y)^{-i}$. So $b^{2i}$ times the norm of each kernel is at most the product on the right without the factor $2$. The triangle inequality adds the two kernels. $\square$

### Unfolding the cutoff

The quotient measure on $\mathsf{U}\backslash G_1$ and the unfolding $y = ux$ of a Haar measure are the background of [reduction theory](/chapter/reduction-theory/). The integral of a class cutoff over the real unipotent group is the covolume $\nu$, the same for each class ([Lemma](/decl/New.Filling.lintegral_classCutoff_eq_unipotentCovolume/), in [counts of frames](/chapter/frame-counts/)).

**Lemma (Unfolding a cutoff).** Let $w_v : G_1 \to [0, \infty]$ be measurable and left invariant under $\mathsf{U}$ for each $v$. Then

$$\int_{G_\infty}\beta_c(y)\prod_v w_v(y_v)\,dy = \nu\prod_v\int_{\mathsf{U}\backslash G_1}w_v\,d\bar y.$$

Lean: `New.Filling.lintegral_classCutoff_mul_prod` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Write $y = ux$ with $u \in \prod_v\mathsf{U}(\mathbb{R})$ and $x$ in the product of the quotients. This map carries the product of the quotient measures and of the Haar measures to the Haar measure of $G_\infty$. The factors $w_v$ do not see $u$. The inner integral of $\beta_c(ux)$ over $u$ is $\nu$. The integral of a product over a product measure is the product of the integrals. $\square$

**Lemma (The majorant of the sum).** Let $A_v$, $a_v$ be decay majorants. Then

$$\sum_d\sum_{\gamma}\int\beta_c(y)\beta_d(\gamma^{-1}y)\prod_vA_v(y_v)\prod_va_v\,L(\gamma^{-1}y)^{-i}\,dy \leq \nu\cdot 2b^{12n^3rf}\cdot b^{400r^2f}\cdot\#I,$$

where $\gamma$ runs over $T \cap \mathrm{terms}(c, s, d)$ and $\#I$ is the number of Bessel coordinates.

Lean: `New.Filling.tsum_lintegral_classCutoff_mul_majorant_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Exchange the sum and the integral; all terms are nonnegative. For fixed $y$ the sum over $(d, \gamma)$ is at most $\prod_va_v\cdot 2b^{12n^3rf}$ by the count of terms. What is left is $2b^{12n^3rf}\int\beta_c\prod_v a_vA_v$. Unfolding the cutoff gives $\nu\prod_v a_v\int A_v$. Each factor is at most $b^{400r^2}\dim_v$, and the product of the dimensions is $\#I$. $\square$

**Lemma (The exponents).** If $12n^3 + 500 \leq k$, $k + 1 \leq r$ and $f \geq 1$, then

$$12n^3rf + 1 + 400r^2f + 2kf + k^3f \leq 2r^3f.$$

Lean: `New.Filling.cut_exponent_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Divide by $f$. From $12n^3 \leq r$ we get $12n^3r \leq r^2$. From $k < r$ we get $2k + 1 \leq r^2$ and $k^3 \leq r^3$. From $402 \leq r$ we get $402r^2 \leq r^3$. So the left side is at most $r^2 + 400r^2 + r^2 + r^3 \leq 2r^3$. $\square$

**Lemma (The constants of the tail).** For admissible $S$,

$$2b^{-2i}\cdot\nu\cdot 2b^{12n^3rf}\cdot b^{400r^2f}\cdot\#I \leq \nu b^{-k^3f}/2.$$

Lean: `New.Filling.inv_pow_mul_unipotentCovolume_mul_card_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Cancel $\nu > 0$. The claim is $8b^{12n^3rf}b^{400r^2f}\#I\,b^{k^3f} \leq b^{2r^3f}$. The admissibility gives $\#I \leq b^{2kf}$, and $8 \leq b$ since $b \geq 1000$. The field $1000(2\varrho + 2)^9 \leq k$ of the filling data gives $12n^3 + 500 \leq k$, and $k + 1 \leq r$ holds for the shape. So the lemma on the exponents applies. $\square$

### The two theorems

**Theorem (A uniform bound for the sum at a point).** There is a finite constant $C$ such that for all $y \in G_\infty$,

$$\sum_d\sum_{\gamma \in T \cap \mathrm{terms}(c, s, d)}\beta_d(\gamma^{-1}y)\prod_v\|W_v((\gamma^{-1}y)_v)\| \leq C.$$

The same holds for $W^\flat$.

Lean: `New.Filling.exists_tsum_classCutoff_mul_prod_enorm_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* Take decay majorants. At $\gamma^{-1}y$ they give $\prod_v\|W_v\| \leq \prod_va_v\,L(\gamma^{-1}y)^{-3i} \leq \prod_va_v\,L(\gamma^{-1}y)^{-i}$. The count of terms bounds the sum by $C = \prod_va_v\cdot 2b^{12n^3rf}$, which is finite. $\square$

The *majorant* of the amplitude of $\gamma$ over $(c, d)$ is $\int\beta_c(y)\beta_d(\gamma^{-1}y)\,\|W(y)\otimes\overline{W(\gamma^{-1}y)}\|\,dy$. The norm of the amplitude is at most its majorant ([Lemma](/decl/New.Filling.enorm_amplitude_le/), in [counts of frames](/chapter/frame-counts/)).

**Theorem (The majorants have a finite sum).** For both sides, full and cut,

$$\sum_d\sum_{\gamma \in T \cap \mathrm{terms}(c, s, d)}\int\beta_c(y)\beta_d(\gamma^{-1}y)\,\bigl\|W(y)\otimes\overline{W(\gamma^{-1}y)}\bigr\|\,dy < \infty.$$

Lean: `New.Filling.tsum_amplitudeMajorant_lt_top` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* The norm of the kernel is $\prod_v\|W_v(y_v)\|\prod_v\|W_v((\gamma^{-1}y)_v)\|$. The first product is at most $\prod_vA_v(y_v)$, and the second at most $\prod_va_v\,L(\gamma^{-1}y)^{-i}$. The lemma on the majorant of the sum bounds the total by $\nu\cdot 2b^{12n^3rf}b^{400r^2f}\#I < \infty$. $\square$

**Theorem (The tail of the cut).** For both sides,

$$\sum_d\sum_{\gamma \in T \cap \mathrm{terms}(c, s, d)}\int\beta_c(y)\beta_d(\gamma^{-1}y)\,\bigl\|K(\gamma, y) - K^\flat(\gamma, y)\bigr\|\,dy \leq \nu b^{-k^3f}/2,$$

where $K$ is the kernel of the side and $K^\flat$ is the cut kernel.

Lean: `New.Filling.tsum_lintegral_enorm_besselKernel_sub_cut_le` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* By the lemma on the difference of the kernels, the integrand is at most $2b^{-2i}$ times the integrand of the lemma on the majorant of the sum. That lemma and the lemma on the constants of the tail give the bound. $\square$

**Corollary (Summability).** For each class $c'$ the amplitudes of the elements of $T \cap \mathrm{terms}(c, s, c')$ are summable.

Lean: `New.Filling.summable_amplitude` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* The norm of each amplitude is at most its majorant. The majorants over $c'$ are part of the finite sum of the theorem. A family of vectors in a finite-dimensional space whose norms have a finite sum is summable. $\square$

**Remark (Formalization).** The corollary removes the junk value of `tsum` from the amplitude sums: for admissible $S$ each amplitude sum is a true sum. It does not by itself remove the junk value of each Bochner integral. That step is part (b) of the theorem on the change of weight in the next section. The bound $\nu b^{-k^3f}/2$ is the form in which layer 4 uses the cut: a block with $W$ and the same block with $W^\flat$ differ by at most this number.
