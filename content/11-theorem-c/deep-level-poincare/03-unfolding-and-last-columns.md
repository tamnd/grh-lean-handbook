---
title: Unfolding, real slices and last columns
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean
decls:
  - New.Space.hasSum_integral_translates
  - New.Exchange.translatedCoeff
  - New.Exchange.sliceConst
  - New.Exchange.norm_dsCoeff_translate_le
  - New.Exchange.integrable_translatedCoeff_and_integral_norm_le
  - New.G.inlLine
  - New.G.inlLine_snd_mem_principalLevel_iff
  - New.Space.IsLastColumn
  - New.Space.exists_isLastColumn
  - New.Space.IsLastColumn.inv_mul_mem_range
  - New.Space.IsLastColumn.le_norm_archCoords_sub
  - New.Space.IsLastColumn.norm_archCoords_one_le
  - New.Space.IsLastColumn.norm_archCoords_le
  - New.Space.tsum_eq_tsum_cosets
  - New.Space.hasSum_integral_of_summable_integral_norm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Unfolding, real slices and last columns

This section collects the tools for the period theorem of Section 4. There are three kinds: unfolding over the rational points, the decay of the real factor of the kernel along a slice, and the last columns that index the cosets.

### Setting

Let $E$ be a CM field with $f$ infinite places $w$. Let $V$ be a hermitian space over $E$ of rank $n$ with signs $s$ ([hermitian spaces](/chapter/adeles-hermitian-spaces/)). Write $G = G(E, s)$ for the adelic unitary group, $G_\infty$ for its real part (one copy of $U(\mathrm{diag}\,s)$ for each $w$), and $G_f$ for its finite part. Write $\Gamma_V \subset G$ for the rational points of $V$ and $\mu_V$ for the measure on a fundamental domain ([finite volume and classes](/chapter/reduction-theory/)). Let $Z = V \oplus \langle 1 \rangle$, where $\langle 1 \rangle$ is the standard line with matrix $(1)$. Its last basis vector is $\tilde e$. This needs a primitive root of unity of order $5040$ in $E$, as all standard spaces of the source do. The operator norm of a matrix is $\|\cdot\|$.

### Unfolding

**Lemma (Unfolding).** Let $f$ be integrable on $G$. Then for every $\delta \in \Gamma_V$ the function $h \mapsto f(\delta h)$ is integrable for $\mu_V$, and

$$\sum_{\delta \in \Gamma_V} \int f(\delta h)\, d\mu_V(h) = \int_G f(g)\, dg,$$

with the sum absolutely convergent.

Lean: `New.Space.hasSum_integral_translates` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The map $(\delta, h) \mapsto \delta h$ carries the product of the counting measure on $\Gamma_V$ and $\mu_V$ to the Haar measure on $G$ (`New.Space.measurePreserving_orbitMeasure`, [finite volume and classes](/chapter/reduction-theory/)). So $(\delta, h) \mapsto f(\delta h)$ is integrable on the product, and Fubini's theorem gives both claims. $\square$

**Lemma (Unfolding of a family).** Let $(P_i)_{i \in I}$ be a countable family of integrable functions on $G$ with $\sum_i \int_G |P_i| < \infty$. Then

$$\sum_{i} \int_G P_i = \int \sum_{(i, \delta) \in I \times \Gamma_V} P_i(\delta h)\, d\mu_V(h).$$

Lean: `New.Space.hasSum_integral_of_summable_integral_norm` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Apply the unfolding lemma to $|P_i|$. It shows that $\sum_\delta \int |P_i(\delta h)|\, d\mu_V = \int_G |P_i|$. So the norms of all terms $(i, \delta)$ have a finite sum. Sum and integral then commute, and the unfolding lemma for each $P_i$ gives the value. $\square$

### Real slices of a translated coefficient

For a doubled parameter $l$ on $U(\mathrm{diag}\,s)$, write $c_l$ for the Flensted-Jensen matrix coefficient ([the parameter and the coefficient](/chapter/discrete-series/), [dsCoeff](/decl/New.HCParam.dsCoeff/)). Its decay bound is $|c_l(g)| \leq (2/\|g\|)^c$ for every $c$ up to the gap ([norm_dsCoeff_le_pow](/decl/New.DiscreteSeries.norm_dsCoeff_le_pow/)). A parameter has a *large gap for $A$* if its gap is at least $500 N^3 + A$, with $N$ the rank (`New.HCParam.HasLargeGap`).

**Definition (Translated coefficient).** Let $l_w$ be a doubled parameter for each infinite place $w$, and let $\alpha, \omega \in G_\infty$. For $g \in G_\infty$,

$$\psi_{l,\alpha,\omega}(g) = \prod_w \overline{c_{l_w}(\alpha_w^{-1} g_w \omega_w)}.$$

Lean: `New.Exchange.translatedCoeff` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

**Definition (Slice constant).** For $A \in \mathbb{N}$ and $\alpha, \omega$ in the real group of $Z$,

$$C_A(\alpha, \omega) = \prod_w \big(2(\|\alpha_w\|\,\|\omega_w\|)^2\big)^A \cdot 16^A \cdot \mathrm{vol}\{r \in U(\mathrm{diag}\,s) : \|r - 1\| \leq 1\}.$$

Lean: `New.Exchange.sliceConst` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

**Lemma (A translated coefficient decays).** Let $l$ have a large gap for $2A$ on $U(\mathrm{diag}\,s)$ with $n \geq 1$. For $\alpha, x, \omega \in U(\mathrm{diag}\,s)$,

$$|c_l(\alpha^{-1} x \omega)| \leq \big(2(\|\alpha\|\,\|\omega\|)^2\big)^A \Big(\frac{2}{\|x\|}\Big)^A \|x\|^{-A}.$$

Lean: `New.Exchange.norm_dsCoeff_translate_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* From $x = \alpha(\alpha^{-1} x \omega)\omega^{-1}$ and $\|\omega^{-1}\| = \|\omega\|$ for a unitary matrix, $\|x\| \leq \|\alpha\|\,\|\alpha^{-1} x \omega\|\,\|\omega\|$. So $2/\|\alpha^{-1} x\omega\| \leq 2\|\alpha\|\|\omega\|/\|x\|$. The decay bound with $c = 2A$ gives $|c_l(\alpha^{-1}x\omega)| \leq (2\|\alpha\|\|\omega\|/\|x\|)^{2A}$. Write $(2ab/t)^2 = 2(ab)^2 \cdot (2/t) \cdot t^{-1}$ and take the $A$-th power. $\square$

Let $\iota : U(\mathrm{diag}\,s) \to U(\mathrm{diag}(s, 1))$ be the block embedding $r \mapsto \mathrm{diag}(r, 1)$.

**Lemma (Integrable slices).** Let $8(n+1)^2 < A$, and let every $l_w$ on $U(\mathrm{diag}(s,1))$ have a large gap for $2A$. Let $\alpha, \omega, g$ be in the real group of $Z$, and let $t > 0$ with $t \leq \prod_w \|g_w\, \iota(r_w)\|$ for every $r \in G_\infty$. Then the slice $r \mapsto \psi_{l,\alpha,\omega}(g \cdot \iota(r))$ is integrable on $G_\infty$, and

$$\int_{G_\infty} |\psi_{l,\alpha,\omega}(g \cdot \iota(r))|\, dr \leq C_A(\alpha,\omega)\, t^{-A}.$$

Lean: `New.Exchange.integrable_translatedCoeff_and_integral_norm_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Put $B_w = (2(\|\alpha_w\|\|\omega_w\|)^2)^A$ and $D_w(r) = (2/\|\iota(r)\, g_w^{-1}\|)^A$. The integral decay lemma of [first properties and decay](/chapter/discrete-series/) ([integral_decay_le](/decl/New.DiscreteSeries.integral_decay_le/)) says that $D_w$ is integrable on $U(\mathrm{diag}\,s)$, with integral at most $16^A \mathrm{vol}\{\|r - 1\| \leq 1\}$. It needs $8(n+1)^2 < A$ and the properness of $\iota$. Since $\|\iota(r)^{-1}g_w^{-1}\| = \|g_w\iota(r)\|$, the decay lemma above gives, at each place,

$$|c_{l_w}(\alpha_w^{-1} g_w \iota(r_w) \omega_w)| \leq B_w\, D_w(r_w^{-1})\, \|g_w \iota(r_w)\|^{-A}.$$

The product over $w$ of the last factors is at most $t^{-A}$. So $|\psi(g\iota(r))| \leq (\prod_w B_w D_w(r_w^{-1}))\, t^{-A}$. The right side is integrable on the product $G_\infty$, as a product of integrable functions of separate variables. The function $\psi$ is continuous, so it is integrable. Integrate the bound. The inversion $r \mapsto r^{-1}$ preserves the Haar measure, and the integral of the product is the product of the integrals. $\square$

### The embedding of V

**Definition (The embedding of $V$).** The map $\iota_V : G(E, s) \to G(E, (s, 1))$ sends $h$ to $h \oplus 1$. Its image fixes $\tilde e$.

Lean: `New.G.inlLine` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

Let $J(a)$ be the principal level of $a \in \mathcal{O}_E$: the finite adelic integral points congruent to $1$ modulo $a$ ([forms of a type](/chapter/automorphic-forms/)).

**Lemma.** For $h \in G(E, s)$, the finite part of $h \oplus 1$ lies in $J(a)$ for $Z$ if and only if the finite part of $h$ lies in $J(a)$ for $V$.

Lean: `New.G.inlLine_snd_mem_principalLevel_iff` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The block matrix $\mathrm{diag}(h, 1)$ is integral and congruent to $1$ modulo $a$ if and only if $h$ is. The extra entries are $0$ and $1$. $\square$

### Last columns

**Definition (Last column).** A rational vector $y$ of $Z$ is the *last column* of $\gamma \in G(E,(s,1))$ if for every $k \in G(E, s)$ and every point $u$, the coordinates of $y$ at $u$ are the last column of the adelic matrix of $u^{-1} \gamma (k \oplus 1)$.

Lean: `New.Space.IsLastColumn` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

**Lemma.** Every rational point $\gamma$ of $Z$ has a last column.

Lean: `New.Space.exists_isLastColumn` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The rational point $\gamma$ is the action of a rational isometry $g$ of $Z$. Take $y = g(0 \oplus 1)$. The coordinates of $0 \oplus 1$ at the base point are $\tilde e$, and $k \oplus 1$ fixes $\tilde e$. So the last column of $u^{-1}\gamma(k \oplus 1)$ is the coordinate vector of $g(0 \oplus 1)$ at $u$. $\square$

**Lemma (Same last column).** If $\gamma$ and $\gamma'$ have the same last column, then $\gamma^{-1}\gamma'$ lies in the image of $\iota_V$.

Lean: `New.Space.IsLastColumn.inv_mul_mem_range` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Take $k = 1$ and $u = \gamma$ in the definition. Then $\gamma^{-1}\gamma'$ maps $\tilde e$ to $\tilde e$. A unitary map of $V \oplus \langle 1 \rangle$ that fixes $\tilde e$ preserves its orthogonal complement $V$. So it is $g \oplus 1$, and its block matrix is $\mathrm{diag}(g, 1)$. $\square$

So the cosets $\gamma\, \iota_V(\Gamma_V)$ are fixed by their last columns.

Let $\lambda(V, x)$ be the first minimum of $V$ at the point $x$: the least length of a nonzero lattice vector, cut off at $1$ ([firstMinimum](/decl/New.Space.firstMinimum/)). Lengths are those of the archimedean coordinates ([archCoords](/decl/New.Space.archCoords/)). We write $\|y\|_x$ for the length of $y$ in the space $Z$ moved to the point $x \oplus 1$. Write $\Phi_w$ for the embedding of $E$ at $w$.

**Lemma (Last columns are separated).** Let $y \neq y'$ be the last columns of $\gamma$ and $\gamma'$. Let $a \neq 0$ in $\mathcal{O}_E$, and let $x, k, k' \in G(E,s)$ be such that the finite parts of $(x \oplus 1)^{-1}\gamma(k \oplus 1)$ and $(x \oplus 1)^{-1}\gamma'(k' \oplus 1)$ lie in $J(a)$. Let $0 \leq R \leq |\Phi_w(a)|$ for every $w$. Then

$$R\, \lambda(V, x) \leq \|y - y'\|_x.$$

Lean: `New.Space.IsLastColumn.le_norm_archCoords_sub` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Write $y - y' = a v$ with $v = a^{-1}(y - y')$, so $v \neq 0$. At each finite place, the last columns of the two matrices of level $a$ are $\tilde e + a t$ and $\tilde e + a t'$ with integral $t, t'$. These are the coordinates of $y$ and $y'$ at $x \oplus 1$. So the coordinates of $a v$ are $a(t - t')$, and those of $v$ are integral. So $v$ lies in the lattice of $Z$ at $x \oplus 1$. The summand $\langle 1 \rangle$ is definite with no vector shorter than $1$. Since $\lambda$ is cut off at $1$, the first minimum of $Z$ at $x \oplus 1$ is at least $\lambda(V, x)$. So $\lambda(V,x) \leq \|v\|_x$. At each place $w$ the coordinate of $a v$ is $\Phi_w(a)$ times that of $v$, and $|\Phi_w(a)| \geq R$. So $R\|v\|_x \leq \|a v\|_x = \|y - y'\|_x$. $\square$

**Lemma.** If $y$ is the last column of $1$, then $\|y\|_x \leq f$ for every $x$.

Lean: `New.Space.IsLastColumn.norm_archCoords_one_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The archimedean coordinates of $y$ at $x \oplus 1$ are the vector $\tilde e$ at each of the $f$ places. Its length is $\sqrt f \leq f$. $\square$

**Lemma.** If $y$ is the last column of $\gamma$, then for all $x, k$,

$$\|y\|_x \leq f \prod_w \|((x \oplus 1)^{-1}\gamma(k \oplus 1))_w\|.$$

Lean: `New.Space.IsLastColumn.norm_archCoords_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Let $g = (x \oplus 1)^{-1}\gamma(k\oplus 1)$ and let $y_0$ be the last column of $1$. By the definition, the coordinates of $y$ at $x \oplus 1$ are $g$ applied to those of $y_0$. At each place the length grows by at most $\|g_w\|$, and each $\|g_w\| \geq 1$, since $1 \leq \|g_w\|\,\|g_w^{-1}\|$ and $\|g_w^{-1}\| = \|g_w\|$ in a unitary group. So $\|y\|_x \leq (\prod_w\|g_w\|)\|y_0\|_x$. The previous lemma gives $\|y_0\|_x \leq f$. $\square$

### Sums over cosets

**Lemma (Sum over cosets).** Let $C$ be a set of representatives of the left cosets of $\iota_V(\Gamma_V)$ in $\Gamma_Z$. Let $p$ be a function on $G(E,(s,1))$ and $W \subseteq C$ such that $p(\sigma\, \iota_V(h)) \neq 0$ for some $h$ implies $\sigma \in W$. Then

$$\sum_{\gamma \in \Gamma_Z} p(\gamma) = \sum_{(\sigma, \delta) \in W \times \Gamma_V} p(\sigma\, \iota_V(\delta)).$$

Lean: `New.Space.tsum_eq_tsum_cosets` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The map $(\sigma, \delta) \mapsto \sigma\,\iota_V(\delta)$ from $C \times \Gamma_V$ to $\Gamma_Z$ is a bijection, since $C$ is a set of representatives and $\iota_V$ is injective. Each $h \oplus 1$ in $\Gamma_Z$ has $h \in \Gamma_V$. Off $W \times \Gamma_V$ the terms vanish. So both sums have the same nonzero terms. $\square$

**Remark (Formalization).** The sums are `tsum`. A `tsum` of a family that is not summable is $0$ in Mathlib. The coset lemma is an equality of `tsum` for any $p$, as it comes from a bijection of index sets. The convergence that the period theorem needs is proved apart, by the bounds of Section 4.
