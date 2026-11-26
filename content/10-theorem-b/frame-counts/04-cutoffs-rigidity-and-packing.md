---
title: Cutoffs, rigidity and packing
lean:
  - New/Spanning/Unfolding/Packing.lean
decls:
  - New.Filling.frameVector_sub_eq_sum
  - New.Filling.exists_gramSchmidtMatrix_le
  - New.Filling.isBoxPartitionOfUnity_reducedIndicator
  - New.Filling.IsBoxPartitionOfUnity.mem_frameBox
  - New.Filling.mem_frameBox_of_classCutoff_ne_zero
  - New.Filling.mem_boxedPoints_of_classCutoff_ne_zero
  - New.Filling.tsum_classCutoff_eq_one
  - New.Filling.frameImage_inr_eq_of_frameProducts_eq
  - New.Filling.norm_Φ_frameProducts_sub_le
  - New.Filling.termsOver.isIntegral_inl_besselFrame
  - New.Filling.one_le_pow_mul_norm_basisScale_div
  - New.Filling.norm_Φ_sub_mul_norm_basisScale_div_le
  - New.Filling.frameImage_eq_frameImage_one_of_close
  - New.Filling.encard_image_frameImage_le
  - New.Filling.tsum_le_of_le_classCutoff_mul
  - New.Filling.exists_classUnipotent_mul_mem_boxedPoints
  - New.Filling.measurable_classCutoff
  - New.encard_le_of_separated
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cutoffs, rigidity and packing

This section proves that the class cutoffs form a partition of unity, and that the frames $\gamma f$ of the terms near one point are few. The *class cutoff* $\beta_c$ (`S.classCutoff c`) is defined in [the anatomy of a term](/chapter/anatomy-of-a-term/). It is a chosen cutoff for $\mathsf U^0_c$ times the indicator of the reduced points (`S.reducedIndicator`). The radius is $\rho_0 = b^{37n}$ (`S.frameBoxRadius`). A *term over* $(c, s, c')$ (`S.termsOver c s c'`) is a rational $\gamma$ with $h_c^{-1}\gamma h_{c'}$ integral and of reduction $s$. The data $S$ are admissible throughout. Among the size hypotheses used here are $\varrho \geq 10^5$, $N \leq b^{60n}$ and $b \geq 1000$, from [the data and their sizes](/chapter/data-and-sizes/).

### The cutoffs

**Lemma.** For every class $c$ and point $y$, some $u \in \mathsf U_c(M)$ makes every entry of the Gram-Schmidt matrix of every $(uy)_v$ at most $b^{26}$ in modulus.

Lean: `New.Filling.exists_gramSchmidtMatrix_le` (New/Spanning/Unfolding/Packing.lean).

*Proof.* Admissible data have a residue domain $D$. Its points have modulus at most $b^{26}$. By the theorem on one coset of [reduced points](/chapter/frame-counts/#reduced-points), some $u$ makes $uy$ reduced. For a reduced point, every entry of the Gram-Schmidt matrix is at most $b^{26}$ in modulus, by `IsResidueDomain.norm_gramSchmidtMatrix_le` of [the anatomy of a term](/chapter/anatomy-of-a-term/). $\square$

**Lemma.** The indicator of the reduced points for the chosen residue domain is a partition of unity in boxes for every class $c$.

Lean: `New.Filling.isBoxPartitionOfUnity_reducedIndicator` (New/Spanning/Unfolding/Packing.lean).

*Proof.* Apply the theorem on reduced points of [reduced points](/chapter/frame-counts/#reduced-points) to the domain chosen by `Classical.epsilon`. A residue domain exists for admissible data. $\square$

**Remark (Formalization).** The set `reducedIndicator` uses `Classical.epsilon S.IsResidueDomain`. For data without a residue domain this would be an arbitrary set. Admissible data have one, so the choice is a residue domain here.

**Lemma.** Let $\omega$ be a partition of unity in boxes, $\omega(y) \neq 0$, $R \geq 0$, and $\ell(y_v) \leq b^{6n+2}R$. Then $y_v \in \operatorname{Box}(b^{37n}R)$.

Lean: `New.Filling.IsBoxPartitionOfUnity.mem_frameBox` (New/Spanning/Unfolding/Packing.lean).

*Proof.* The field on boxes gives $y_v \in \operatorname{Box}(b^{27}\ell(y_v)) \subseteq \operatorname{Box}(b^{6n+29}R)$, and $6n + 29 \leq 37n$ with $b \geq 1$. $\square$

**Lemma.** Let $\beta_c(y) \neq 0$.

1. If $R \geq 0$ and $\ell(y_v) \leq b^{6n+2}R$, then $y_v \in \operatorname{Box}(b^{37n}R)$.
2. If $\ell(y_v) \leq b^{6n+2}$ at every place, then $y$ is a boxed point.

The translates of $\beta_c$ add up to one: $\sum_{u \in \mathsf U_c(M)}\beta_c(uy) = 1$. The function $\beta_c$ is measurable.

Lean: `New.Filling.mem_frameBox_of_classCutoff_ne_zero`, `New.Filling.mem_boxedPoints_of_classCutoff_ne_zero`, `New.Filling.tsum_classCutoff_eq_one`, `New.Filling.measurable_classCutoff` (New/Spanning/Unfolding/Packing.lean).

*Proof.* Write $\beta_c = \beta\cdot\omega$ with $\omega$ the indicator of the reduced points. If $\beta_c(y) \neq 0$, then $\omega(y) \neq 0$, so the last lemma gives (1), and $y$ is reduced, which gives (2). For the sum, the cutoff $\beta$ for $\mathsf U^0_c$ satisfies $\sum_{u \in \mathsf U^0_c}\beta(u\gamma y) = 1$ for every $\gamma$. So the weight $a(\gamma) = \beta(\gamma y)$ has sum $1$ on each right coset, and the field `tsum_mul_eq_one` of $\omega$ gives the claim. $\square$

**Lemma.** If every $\ell(y_v) \leq b^{6n+2}$, then some $u \in \mathsf U_c(M)$ has $uy$ boxed.

Lean: `New.Filling.exists_classUnipotent_mul_mem_boxedPoints` (New/Spanning/Unfolding/Packing.lean).

*Proof.* The translates of $\beta_c$ add up to $1$, so $\beta_c(uy) \neq 0$ for some $u$. Left multiplication by a unipotent element keeps the length ([length](/chapter/bessel-real-place/)). Apply (2) of the last lemma. $\square$

### Rigidity

**Lemma.** If $\gamma f$ and $\gamma'f$ differ only in the coordinates along the $e_a$, then at every place

$$(\gamma^{-1}y)^{-1}f_b - (\gamma'^{-1}y)^{-1}f_b = \sum_{a < \varrho}\Phi_v\bigl((\gamma - \gamma')_{e_a, f_b}\bigr)\frac{s_v(f_b)}{s_v(e_a)}\,y^{-1}e_a,$$

where $s_v$ is the scale of the normalised basis at $v$ (`S.basisScale v`).

Lean: `New.Filling.frameVector_sub_eq_sum` (New/Spanning/Unfolding/Packing.lean).

*Proof.* $(\gamma^{-1}y)^{-1}f_b = y^{-1}(\gamma f_b)$. Write $\gamma f_b$ in the normalised basis at $v$ and subtract. Only the coordinates along the $e_a$ remain. $\square$

**Lemma.** Let $g$ be rational.

1. If the products of $f$ with $gf_a$ are those of $f$ with $f_a$, then $gf_a$ and $f_a$ have the same coordinates outside the $e_i$.
2. At each place $v$, $|\Phi_v(Z(\gamma)_{ba} - Z(\gamma')_{ba})| \leq N\|y^{-1}f_b\|\,\|(\gamma^{-1}y)^{-1}f_a - (\gamma'^{-1}y)^{-1}f_a\|$.
3. For a term $\gamma$ over $(c, s, c')$, the coordinates of $\gamma f_b$ along the $e_a$ are algebraic integers.
4. $1 \leq b^{23\varrho}|s_v(f_b)/s_v(f_a)|$.
5. If $\gamma f$ and $\gamma'f$ differ only along the $e_x$, and $\gamma f_b$, $\gamma' f_b$ agree along $e_x$ for $x > a$, then for every $w \in \mathsf U$, $|\Phi_v(\gamma_{e_a f_b} - \gamma'_{e_a f_b})|\,|s_v(f_b)/s_v(e_a)| \leq \|wy\|\,\|(\gamma^{-1}y)^{-1}f_b - (\gamma'^{-1}y)^{-1}f_b\|$.

Lean: `New.Filling.frameImage_inr_eq_of_frameProducts_eq`, `New.Filling.norm_Φ_frameProducts_sub_le`, `New.Filling.termsOver.isIntegral_inl_besselFrame`, `New.Filling.one_le_pow_mul_norm_basisScale_div`, `New.Filling.norm_Φ_sub_mul_norm_basisScale_div_le` (New/Spanning/Unfolding/Packing.lean).

*Proof.* (1) The products with $e_i$ and with $z$ give the coordinates along $e^*_i$ and $z$. The element $g$ is unitary, so the middle part of $gf_a - f_a$ is isotropic for the middle form. That form is anisotropic off $z$, so the middle part vanishes. (2) The product $h(f_b, \gamma f_a)$ is, up to a real factor $t/N$ with $|t| \geq 1$, the product of $y^{-1}f_b$ with $(\gamma^{-1}y)^{-1}f_a$; apply the Cauchy-Schwarz inequality. (3) The entry is an entry of the integral matrix $h_c^{-1}\gamma h_{c'}$, since the change to the lattice bases keeps it. (4) The scales are powers of $|M_v|$ divided by $\sqrt N$, where $M_v$ is `S.realM v`, with $1 \leq |M_v| \leq b^{23}$, and the exponents differ by at most $\varrho$. (5) Apply $wy$ to the difference of the last lemma. Row $a$ of $w$ is unitriangular on the $e_x$, so only the term $x = a$ is left; then bound the operator norm. $\square$

**Theorem (Rigidity of frames).** Let $g$ be a term over some $(d, r, d')$, $R \geq 1$ and $\rho = b^{37n}R$. Let $z$ be a point with $\ell(z_v) \leq b^{6n+2}R$ and $z_v \in \operatorname{Box}(\rho)$ at every place. If $\|(g^{-1}z_v)^{-1}f_a - z_v^{-1}f_a\| < (N\rho)^{-1}$ for every $v$ and $a$, then $gf = f$.

Lean: `New.Filling.frameImage_eq_frameImage_one_of_close` (New/Spanning/Unfolding/Packing.lean).

*Proof.* Let $\delta_v$ be the largest distance of the frame vectors at $v$. First a principle: let $\phi$ be a function on terms with integral values, and suppose $|\Phi_v(\phi(g) - \phi(1))| \leq N\rho\,\delta_v$ at every place. Then $\phi(g) - \phi(1)$ is an algebraic integer whose conjugates all have modulus less than $1$. Its norm is a rational integer of modulus less than $1$, so it is $0$. Thus $\phi(g) = \phi(1)$.

Apply the principle to the entries of $Z(g)$, with (2): $|\Phi_v(Z(g)_{ba} - Z(1)_{ba})| \leq N\rho\,\delta_v$. So $Z(g) = Z(1)$, and (1) shows that $gf$ and $f$ differ only along the $e_a$. Then fix the coordinates along $e_a$ by downward induction on $a$. Take $w \in \mathsf U$ with $\|wz_v\| \leq b^{6n+2}R$ ([length](/chapter/bessel-real-place/)). By (5) and (4), $|\Phi_v(g_{e_af_b} - \delta_{e_af_b})| \leq b^{23\varrho + 6n + 2}R\,\delta_v \leq N\rho\,\delta_v$, since $23\varrho + 6n + 2 \leq 37n$. The coordinate is integral by (3), and the principle applies. $\square$

### Packing

**Lemma (Packing).** Let $V$ be a real normed space of finite dimension, $m > 0$ and $R \geq 0$. If the points $f(i)$, $i \in S$, have pairwise distances at least $m$ and norms at most $R$, then $|S| \leq (1 + 2R/m)^{\dim V}$.

Lean: `New.encard_le_of_separated` (Lib/General/Analysis/PackingAndSobolev.lean).

*Proof.* The balls of radius $m/2$ about the points are disjoint, and they lie in the ball of radius $R + m/2 = (1 + 2R/m)(m/2)$ about $0$. Compare the Haar volumes; the volume of a ball scales with the power $\dim V$ of its radius. $\square$

**Theorem (Packing of frames).** Let $R \geq 1$, and let $A$ be a set of terms over $(c, s, c')$ with the class $c$ fixed and any $s, c'$. Let $y$ be a point. Suppose that for $\gamma \in A$ the point $x = \gamma^{-1}y$ has $\ell(x_v) \leq b^{6n+2}R$ and $x_v \in \operatorname{Box}(b^{37n}R)$ at every place, and that the frame vectors of any two such points differ by an element of a real subspace $V$. Then the frames $\gamma f$, $\gamma \in A$, take at most $(b^{6n^2}R^2)^{\dim V}$ values.

Lean: `New.Filling.encard_image_frameImage_le` (New/Spanning/Unfolding/Packing.lean).

*Proof.* Choose one $p \in A$ for each frame, and fix $\gamma_0 \in A$. Map $p$ to $F(\gamma_0) - F(p) \in V$, where $F(\gamma)$ is the tuple of the frame vectors of $\gamma^{-1}y$. Let $p \neq q$ have different frames. The term $p^{-1}q$ sends $p^{-1}y$ to $q^{-1}y$. If all the frame vectors of these two points were closer than $(N\rho)^{-1}$, rigidity would give $p^{-1}qf = f$, so $pf = qf$. Hence the points are $(N\rho)^{-1}$-separated in the sup norm. They have norm at most $2\rho$. The packing lemma gives at most $(1 + 4N\rho^2)^{\dim V}$ points. Finally $1 + 4N\rho^2 \leq 5b^{60n}\rho^2 \leq b^{134n+1}R^2 \leq b^{6n^2}R^2$, since $N \leq b^{60n}$, $b \geq 5$ and $n \geq 23$. $\square$

**Theorem (Packing of weights).** Let $p \mapsto (k_p, \gamma_p)$ be injective, $w_p \geq 0$ weights, $y$ a point and $R \geq 1$. Suppose that for $p$ in the support of $w$, $\gamma_p$ is a term over $(c, s, k_p)$, the point $x_p = \gamma_p^{-1}y$ has $\ell((x_p)_v) \leq b^{6n+2}R$, and $w_p \leq x\,\beta_{k_p}(x_p)$. If the frame vectors of any two $x_p$ differ by an element of $V$, then

$$\sum_p w_p \leq (b^{6n^2}R^2)^{\dim V}\,x.$$

Lean: `New.Filling.tsum_le_of_le_classCutoff_mul` (New/Spanning/Unfolding/Packing.lean).

*Proof.* On the support, $\beta_{k_p}(x_p) \neq 0$, so $x_p$ lies in the box, by the lemma on cutoffs. Colour $p$ by the frame $\gamma_pf$. Two terms over $(c, s, \cdot)$ with the same frame have the same class, and $\gamma_p^{-1}\gamma_q \in \mathsf U^0_{k_p}$ (`termsOver.eq_and_mem_classUnipotent₀`). So in one colour, $q \mapsto \gamma_q^{-1}\gamma_p$ is an injective map into $\mathsf U_{k_p}(M)$, and the weights are at most $x$ times translates of $\beta_{k_p}$ at the point $\gamma_p^{-1}y$. These translates add up to at most $1$. So one colour has weight at most $x$. The number of colours is bounded by the packing of frames. Apply the lemma on colouring of [reduced points](/chapter/frame-counts/#reduced-points). $\square$

**Remark (Formalization).** All sums here are `tsum` in $[0, \infty]$, and the bounds are `ENNReal.ofReal` of real numbers. These real numbers are at least $1$, so `ofReal` changes nothing. The weights may be infinite; then the hypothesis $w_p \leq x\beta$ forces $x = \infty$, and the bound is trivial.
