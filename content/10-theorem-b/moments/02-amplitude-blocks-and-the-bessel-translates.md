---
title: Amplitude blocks and the Bessel translates
lean:
  - New/Spanning/Unfolding/Moments.lean
  - New/Spanning/Unfolding/SquareExpansion.lean
decls:
  - New.Filling.HasAmplitudeBlocks
  - New.Filling.hasAmplitudeBlocks_smul_of_inner_eq
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sq_eq_secondMoment
  - New.Filling.exists_unitary_besselFn_mul
  - New.Filling.amplitudeSum_besselS_apply
  - New.Filling.amplitudeSum_besselS_inv
  - New.Filling.amplitudeSum_mul_inv_apply
  - New.Filling.besselTranslate
  - New.Filling.besselTranslate_eq_zero
  - New.Filling.besselTranslate_apply
  - New.Filling.besselTranslate_one
  - New.Filling.besselTranslate_mul
  - New.Filling.besselTranslate_mul_left
  - New.Filling.adjoint_besselTranslate
  - New.Filling.hilbertSchmidtNorm_besselTranslate_comp
  - New.Filling.trace_besselTranslate
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Amplitude blocks and the Bessel translates

This section fixes the hypothesis on $P$ that all later results use. Then it builds the operator $r_\psi(s)$ of the terms in the Bessel group. In the Petersson formula the diagonal term comes from the identity element alone. Here the diagonal term comes from the whole group $R_0$, and it is not a scalar: it is a representation of $\bar R_0$ on the source. The section shows that it is a unitary representation.

### Amplitude blocks

Recall the setting of [the first section](/chapter/moments/#what-the-chapter-proves). The source is $\mathbb{C}^{X}$ with $X = \mathrm{Classes}\times\mathrm{BesselCoord}$, with the standard basis $e_x$. For $x = (c, i)$ we write $x_1 = c$ and $x_2 = i$. A term over the block $(c, s, c')$ is a rational $\gamma$ such that $h_c^{-1}\gamma h_{c'}$ lies in $K$ and has reduction $s$ ([Definition](/decl/New.Filling.termsOver/)). For a set $T$ of rational points, the block $\mathcal{A}_T(c, s, c')$ is the sum over the terms in $T$ of the amplitudes, a matrix indexed by pairs of Bessel coordinates ([Definition](/decl/New.Filling.amplitudeSum/)). The amplitude of $\gamma$ is the integral of the weights $\beta_c(y)\beta_{c'}(\gamma^{-1}y)$ against the kernel

$$K(\gamma, y)_{(i, j)} = W(y)_i\,\overline{W(\iota_\infty(\gamma)^{-1}y)_j}.$$

In this chapter all blocks are blocks of the full function $W$, unless the cut function is named.

**Definition (Amplitude blocks).** Let $\rho$ be a representation of $\bar G$ on an inner product space $V$, and let $P$ be a linear map from the source to $V$. Then $P$ *has amplitude blocks* if for all $s \in \bar G$ and all $x, y \in X$

$$\langle\rho(s)Pe_y, Pe_x\rangle = \frac{\mathcal{A}(x_1, s, y_1)_{x_2, y_2}}{\nu}.$$

Lean: `New.Filling.HasAmplitudeBlocks` (New/Spanning/Unfolding/Moments.lean).

The inner product is linear in the second argument. So the entry $\langle e_x, P_se_y\rangle = \langle Pe_x, \rho(s)Pe_y\rangle$ of $P_s = P^*\rho(s)P$ is the complex conjugate of $\mathcal{A}(x_1, s, y_1)_{x_2, y_2}/\nu$. The unfolding of [the chapter on Poincaré series](/chapter/poincare-series/) gives the identity of the definition up to a positive factor. The next lemma removes the factor.

**Lemma (Scaling).** Let $c > 0$. Suppose that $\langle\rho(s)Pe_y, Pe_x\rangle = c\,\mathcal{A}(x_1, s, y_1)_{x_2, y_2}$ for all $s, x, y$. Then $(c\nu)^{-1/2}P$ has amplitude blocks.

Lean: `New.Filling.hasAmplitudeBlocks_smul_of_inner_eq` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Put $a = \sqrt{(c\nu)^{-1}}$, a real number, and $\nu > 0$ ([Lemma](/decl/New.Filling.unipotentCovolume_pos/)). Then $\langle\rho(s)aPe_y, aPe_x\rangle = a^2c\,\mathcal{A}(x_1, s, y_1)_{x_2, y_2}$, since $\bar a = a$. And $a^2c = 1/\nu$. $\square$

The lemma does not need admissibility. The scaled Poincaré map has amplitude blocks by this lemma ([Theorem](/decl/New.Data.hasAmplitudeBlocks_scaledPoincare/), stated in [the section on unfolding and bounds](/chapter/theorem-b-plan/#unfolding-and-bounds)).

**Lemma (The norm of $P_s$).** If $P$ has amplitude blocks, then for each $s \in \bar G$

$$\|P_s\|^2 = \mathsf{E}(\mathcal{A}, \{s\}) = \sum_{c, c'}\frac{\|\mathcal{A}(c, s, c')\|^2}{\nu^2}.$$

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sq_eq_secondMoment` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The squared Hilbert-Schmidt norm of an operator is the sum of the squared moduli of its entries in orthonormal bases ([Lemma](/decl/New.hilbertSchmidtNorm_sq_eq_sum_entries/)). The entry $(x, y)$ of $P_s$ has modulus $|\mathcal{A}(x_1, s, y_1)_{x_2, y_2}|/\nu$. Group the pairs $(x, y)$ by the pair of classes $(x_1, y_1)$. The sum over the coordinates $(x_2, y_2)$ is the squared Euclidean norm of the block. $\square$

**Remark (Formalization).** The hypothesis is an identity for every $s$, every $x$ and every $y$, with no limit. The block $\mathcal{A}$ is a sum `tsum` over the terms. If the family of amplitudes were not summable, the block would be $0$ and the hypothesis would ask for $\langle\rho(s)Pe_y, Pe_x\rangle = 0$. No result of this chapter uses summability. [The section on conventions](/chapter/theorem-b-plan/#conventions-that-change-the-meaning) proves it for admissible data. A $P$ that satisfies the hypothesis with the junk values satisfies the conclusions of this chapter, because the proofs use only the identities of blocks below.

### The action of the Bessel group on $W$

An element $\gamma$ of $R_0$ is $\gamma = u\eta$ with $u \in \mathsf{U}$ and $\eta$ in the definite group $U(X_0)$. At each infinite place $v$, $\eta$ is the image of an element $k_v$ of the compact group $U(1)$ that acts on the Bessel system at $v$ by $\mathrm{rep}_v(k_v)$.

**Lemma (The Bessel group acts by unitary matrices).** Let $\gamma \in R_0$ be rational, and let $W$ be the full or the cut Bessel function. Then there is a unitary matrix $M$ indexed by the Bessel coordinates such that $W(\iota_\infty(\gamma)y) = MW(y)$ for all $y$.

Lean: `New.Filling.exists_unitary_besselFn_mul` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Write $\gamma = u\eta$ as above. [The chapter on the anatomy of a term](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data) gives $W(\iota_\infty(u)y) = \chi(u)^{-1}W(y)$, where $\chi = \psi_U$ is the character of $\mathsf{U}$. Each local Bessel function satisfies $W_v(\mathrm{embedH}(k)z) = \mathrm{rep}_v(k)W_v(z)$, and $W$ is the tensor product of the $W_v$ (Lemma `New.Filling.besselFn_mul_of_eq_embedH` of the same file). So

$$M = \chi(u)^{-1}\bigotimes_v\mathrm{rep}_v(k_v).$$

The scalar has modulus $1$, as $\chi$ takes values on the unit circle. A tensor product of unitary matrices is unitary, since $(\bigotimes_vA_v)^*(\bigotimes_vA_v) = \bigotimes_vA_v^*A_v = 1$. So $M^*M = |\chi(u)|^{-2}\cdot 1 = 1$. $\square$

The next three lemmas compute blocks with the theorem on [moving a block](/chapter/poincare-series/#moving-blocks): for a stable $T$, terms $\sigma$ over $(c, t, c_1)$ and $\sigma'$ over $(c', t', c_1')$ in $R_0$ with $\gamma \in T \Leftrightarrow \sigma\gamma\sigma'^{-1} \in T$, and a continuous linear map $L$ with $K(\sigma\gamma\sigma'^{-1}, \sigma y) = L(K(\gamma, y))$, one has $\mathcal{A}_T(c, tst'^{-1}, c') = L(\mathcal{A}_T(c_1, s, c_1'))$ ([Theorem](/decl/New.Filling.amplitudeSum_mul_mul_inv/)).

From here on, $E$ contains a primitive root of unity of order $5040$ and $S$ is admissible.

**Lemma (Blocks of the Bessel group).** Let $\gamma \in R_0$ be a term over $(c, s, c')$ with $W(\iota_\infty(\gamma)y) = MW(y)$ for all $y$. Then for every class $d$ and all coordinates $i, j$

$$\mathcal{A}_{R_0}(c, s, d)_{i, j} = \begin{cases}\nu M_{i, j} & \text{if } c' = d,\\ 0 & \text{otherwise.}\end{cases}$$

Lean: `New.Filling.amplitudeSum_besselS_apply` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Apply the theorem on moving a block with $T = R_0$, which is stable ([Lemma](/decl/New.Filling.isStable_besselS/)), $\sigma = \gamma$ over $(c, s, c')$ and $\sigma' = 1$ over $(d, 1, d)$. The element $1$ is a term over $(d, 1, d)$, because it lies in the unipotent group of the class $d$. As $\gamma \in R_0$, $\delta \in R_0$ if and only if $\gamma\delta \in R_0$. Let $L = M\otimes 1$. Then

$$K(\gamma\delta, \iota_\infty(\gamma)y)_{(a, b)} = (MW(y))_a\,\overline{W(\iota_\infty(\delta)^{-1}y)_b} = \bigl(L\,K(\delta, y)\bigr)_{(a, b)}.$$

So $\mathcal{A}_{R_0}(c, s, d) = L(\mathcal{A}_{R_0}(c', 1, d))$, that is, $\mathcal{A}_{R_0}(c, s, d)_{i, j} = \sum_kM_{i, k}\mathcal{A}_{R_0}(c', 1, d)_{k, j}$. [The identity block](/decl/New.Filling.amplitudeSum_besselS_one_eq_ite/) is $\nu$ at $k = j$ when $c' = d$, and $0$ otherwise. $\square$

**Lemma (The inverse block).** For all classes $c, d$, all $s$ and all $i, j$

$$\mathcal{A}_{R_0}(d, s^{-1}, c)_{j, i} = \overline{\mathcal{A}_{R_0}(c, s, d)_{i, j}}.$$

Lean: `New.Filling.amplitudeSum_besselS_inv` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* First let $\gamma \in R_0$ be a term over $(c, s, d)$, and let $M$ be unitary with $W(\iota_\infty(\gamma)y) = MW(y)$. Then $\gamma^{-1}$ is a term over $(d, s^{-1}, c)$ ([Lemma](/decl/New.Filling.termsOver.inv/)), and $W(\iota_\infty(\gamma)^{-1}y) = M^{-1}W(y) = M^*W(y)$. The previous lemma, applied twice, gives $\nu M_{i, j}$ on the right side and $\nu(M^*)_{j, i} = \nu\overline{M_{i, j}}$ on the left side. If $R_0$ has no term over $(c, s, d)$, then it has no term over $(d, s^{-1}, c)$, since the inverse of such a term would be one. Both sums are over the empty set, and both sides are $0$. $\square$

**Lemma (Right translation).** Let $T$ be stable, and let $\delta \in R_0$ be a term over $(d, t, d')$ with $W(\iota_\infty(\delta)y) = NW(y)$ for all $y$. Suppose that $\gamma \in T$ if and only if $\gamma\delta^{-1} \in T$. Then for every class $c$, every $s$ and all $i, j$

$$\mathcal{A}_T(c, st^{-1}, d)_{i, j} = \sum_k\overline{N_{j, k}}\,\mathcal{A}_T(c, s, d')_{i, k}.$$

Lean: `New.Filling.amplitudeSum_mul_inv_apply` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Move the block with $\sigma = 1$ over $(c, 1, c)$ and $\sigma' = \delta$. Let $L = 1\otimes\bar N$, with $\bar N$ the entrywise conjugate. As $\iota_\infty(\gamma\delta^{-1})^{-1}y = \iota_\infty(\delta)\iota_\infty(\gamma)^{-1}y$,

$$K(\gamma\delta^{-1}, y)_{(a, b)} = W(y)_a\,\overline{(NW(\iota_\infty(\gamma)^{-1}y))_b} = \bigl(L\,K(\gamma, y)\bigr)_{(a, b)}.$$

So $\mathcal{A}_T(c, st^{-1}, d) = L(\mathcal{A}_T(c, s, d'))$. This is the claim. $\square$

### The operators $r_\psi(s)$

**Definition (Bessel translate).** For $s \in \bar G$, $r_\psi(s)$ is the operator on the source with the entries

$$\langle e_x, r_\psi(s)e_y\rangle = \overline{\mathcal{A}_{R_0}(x_1, s, y_1)_{x_2, y_2}/\nu}.$$

Lean: `New.Filling.besselTranslate` (New/Spanning/Unfolding/Moments.lean).

So $r_\psi(s)$ is built from the blocks of the terms in $R_0$ as $P_s$ is built from the blocks of all terms.

**Lemma (Vanishing off $\bar R_0$).** If $s \notin \bar R_0$, then $r_\psi(s) = 0$.

Lean: `New.Filling.besselTranslate_eq_zero` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Let $\gamma \in R_0$ be a term over $(c, s, c')$, with $k = h_c^{-1}\gamma h_{c'} \in K$ of reduction $s$. The class representatives conjugate $R_0$ into $R_0$ (Lemma `New.Filling.translateByClassReps_mem_besselS`), so $k$ is an integral point of $R_0$ and $s \in \bar R_0$. So for $s \notin \bar R_0$ every block of $R_0$ is a sum over the empty set, which is $0$. $\square$

**Remark (Formalization).** The source defines $r_\psi(s)$ for every $s \in \bar G$, with the value $0$ off $\bar R_0$. This is a convention, not a junk value. It lets the results below state sums over all of $\bar G$ and over sets that contain elements outside $\bar R_0$.

**Lemma (The value of $r_\psi(s)$).** Let $\gamma \in R_0$ be a term over $(c, s, c')$ with $W(\iota_\infty(\gamma)y) = MW(y)$ for all $y$. Then for every vector $\varphi$ and every coordinate $i$

$$(r_\psi(s)\varphi)(c, i) = \sum_j\overline{M_{i, j}}\,\varphi(c', j).$$

Lean: `New.Filling.besselTranslate_apply` (New/Spanning/Unfolding/Moments.lean).

*Proof.* By definition $(r_\psi(s)\varphi)(c, i) = \sum_{(d, j)}\overline{\mathcal{A}_{R_0}(c, s, d)_{i, j}}\,\varphi(d, j)/\nu$. By the lemma on blocks of the Bessel group only $d = c'$ contributes, with $\overline{\nu M_{i, j}}/\nu = \overline{M_{i, j}}$. $\square$

So $r_\psi(s)$ moves the class $c'$ to the class $c$ and acts on the coordinates by the conjugate of $M$. [The level structure](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data) gives, for each class $c$ and each $s \in \bar R_0$, a class $c'$ and a term $\gamma \in R_0$ over $(c, s, c')$ ([Lemma](/decl/New.Filling.exists_besselS_mem_termsOver/)). So every row block of $r_\psi(s)$ is computed by the lemma.

**Lemma (The identity).** $r_\psi(1) = 1$.

Lean: `New.Filling.besselTranslate_one` (New/Spanning/Unfolding/Moments.lean).

*Proof.* For each class $c$, the element $1$ is a term over $(c, 1, c)$ and acts on $W$ by $M = 1$. The value lemma gives $(r_\psi(1)\varphi)(c, i) = \varphi(c, i)$. $\square$

**Lemma (Multiplicativity).** If $s, t \in \bar R_0$, then $r_\psi(st) = r_\psi(s)r_\psi(t)$.

Lean: `New.Filling.besselTranslate_mul` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Fix a class $c$. Choose a term $\gamma \in R_0$ over $(c, s, c')$ and a term $\delta \in R_0$ over $(c', t, c'')$. Let $M$ and $N$ be the matrices of $\gamma$ and $\delta$ on $W$. Then $\gamma\delta$ is a term over $(c, st, c'')$ ([Lemma](/decl/New.Filling.termsOver.mul/)) and acts on $W$ by $MN$. The value lemma, applied three times, gives

$$(r_\psi(st)\varphi)(c, i) = \sum_k\overline{(MN)_{i, k}}\,\varphi(c'', k) = \sum_j\overline{M_{i, j}}\sum_k\overline{N_{j, k}}\,\varphi(c'', k) = (r_\psi(s)r_\psi(t)\varphi)(c, i).$$

$\square$

**Lemma (Multiplicativity on the left).** If $t \in \bar R_0$ and $s \in \bar G$, then $r_\psi(ts) = r_\psi(t)r_\psi(s)$.

Lean: `New.Filling.besselTranslate_mul_left` (New/Spanning/Unfolding/Moments.lean).

*Proof.* If $s \in \bar R_0$, this is the previous lemma. If not, then $ts \notin \bar R_0$, since $\bar R_0$ is a group. Both sides are $0$ by the vanishing lemma. $\square$

**Lemma (The adjoint).** For every $s \in \bar G$, $r_\psi(s)^* = r_\psi(s^{-1})$.

Lean: `New.Filling.adjoint_besselTranslate` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The matrix of the adjoint is the conjugate transpose. Its entry $(x, y)$ is $\mathcal{A}_{R_0}(y_1, s, x_1)_{y_2, x_2}/\nu$. By the lemma on the inverse block this is $\overline{\mathcal{A}_{R_0}(x_1, s^{-1}, y_1)_{x_2, y_2}}/\nu$, the entry $(x, y)$ of $r_\psi(s^{-1})$. $\square$

With the identity and multiplicativity, the lemma shows that $r_\psi$ restricted to $\bar R_0$ is a unitary representation.

**Lemma (Unitary invariance).** If $t \in \bar R_0$, then $\|r_\psi(t)A\| = \|A\|$ for every operator $A$ on the source.

Lean: `New.Filling.hilbertSchmidtNorm_besselTranslate_comp` (New/Spanning/Unfolding/Moments.lean).

*Proof.* We have $r_\psi(t)^*r_\psi(t) = r_\psi(t^{-1})r_\psi(t) = r_\psi(1) = 1$. So $\|r_\psi(t)v\|^2 = \langle v, r_\psi(t)^*r_\psi(t)v\rangle = \|v\|^2$ for every vector $v$. An operator $B$ with $\|Bv\| \leq \|Av\|$ for all $v$ has $\|B\| \leq \|A\|$ in Hilbert-Schmidt norm ([Lemma](/decl/New.hilbertSchmidtNorm_le_of_norm_le/)). Apply this in both directions. $\square$

**Lemma (The trace).** For every $s \in \bar G$

$$\operatorname{tr}r_\psi(s) = \sum_{(c, i)}\frac{\mathcal{A}_{R_0}(c, s^{-1}, c)_{i, i}}{\nu}.$$

Lean: `New.Filling.trace_besselTranslate` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The trace is $\sum_x\langle e_x, r_\psi(s)e_x\rangle = \sum_x\overline{\mathcal{A}_{R_0}(x_1, s, x_1)_{x_2, x_2}}/\nu$. The lemma on the inverse block with $c = d$ and $i = j$ turns each summand into $\mathcal{A}_{R_0}(x_1, s^{-1}, x_1)_{x_2, x_2}/\nu$. $\square$

[The section on the induced character](/chapter/moments/#the-induced-character) computes this trace as $D_X$ times a character of $\bar R_0$.
