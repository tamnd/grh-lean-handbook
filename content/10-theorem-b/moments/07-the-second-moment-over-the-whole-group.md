---
title: The second moment over the whole group
lean:
  - New/Spanning/Unfolding/MomentBounds.lean
  - New/Spanning/Unfolding/SquareExpansion.lean
  - New/Spanning/Unfolding/Moments.lean
decls:
  - New.le_apply_one_of_inner_eq
  - New.leadingMinor_frameGram_eq_zero
  - New.Filling.InScalarCoset.not_isOpenElement
  - New.Filling.inScalarCoset_one
  - New.Filling.amplitudeSum_besselS_eq_zero
  - New.Filling.secondMoment_singleton
  - New.Filling.secondMoment_eq_sum_secondMoment_singleton
  - New.Filling.secondMoment_univ_eq_secondMoment_compl_besselS
  - New.Filling.card_inScalarCoset_le
  - New.Filling.pow_mul_identitySecondMoment_le_mul_mainSecondMoment
  - New.Filling.levelPrime_pow_le_meetNorm_of_mem_fixer
  - New.Filling.sum_secondMoment_inScalarCoset_le
  - New.Filling.eight_mul_M_pow_mul_identitySecondMoment_le
  - New.Filling.div_levelPrime_pow_mul_mainSecondMoment_le
  - New.Filling.secondMoment_fixer_univ_le
  - New.Filling.secondMoment_fixer_isOpenElement_le
  - New.Filling.levelPrime_pow_mul_sqrt_le
  - New.Filling.sum_leadingMinor_eq_zero_le
  - New.Filling.sum_not_isOpenElement_le
  - New.Filling.le_one_add_nine_mul_of_le_add
  - New.Filling.sum_secondMoment_le
  - New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The second moment over the whole group

This section proves the second moment (SM) of [the plan](/chapter/theorem-b-plan/#the-four-layers-of-the-proof): $\sum_{s \in \bar G}\|P_s\|^2 \leq (1 + 9b^{-4})\mathcal{D}_{\mathrm{main}}$. The proof bounds the function $\beta(s) = \mathsf{E}(\mathcal{A}, \{s\})$, which is $\|P_s\|^2$. It uses only two properties of $\beta$: positive type, and $\beta(1) \leq 2D_X$.

The idea is a maximal family of fixed vectors. A *frame vector* at a chosen place $w$ above $p_0$ is a nonzero vector of the span of the frame $e_1, \dots, e_\varrho, z$, modulo $w$ or modulo its conjugate. The fixer of a set of places with one frame vector at each is a subgroup ([Definition](/decl/New.Filling.fixer/), in [the section on climbing the flags](/chapter/poincare-series/#climbing-the-flags)). An element $s$ is *open* if at some chosen place $w$ above $p_0$ all leading minors of size less than $n$ of the frame products $(h(f_j, s f_l))$ are nonzero ([Definition](/decl/New.Filling.IsOpenElement/)). [The chapter on the main term](/chapter/main-term/) bounds the links over the open elements of a fixer.

### Second moments by points

**Lemma (A function of positive type).** Let $G$ be a group, and let $\beta : G \to \mathbb{R}$ with $\beta(a^{-1}b) = \langle u(a), u(b)\rangle$ for vectors $u(a)$ of a complex inner product space. Then $\beta(s) \leq \beta(1)$ for all $s$.

Lean: `New.le_apply_one_of_inner_eq` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* $\|u(a)\|^2 = \beta(1)$ for every $a$. So $\beta(s) = \operatorname{Re}\langle u(1), u(s)\rangle \leq \|u(1)\|\|u(s)\| \leq (\|u(1)\|^2 + \|u(s)\|^2)/2 = \beta(1)$. $\square$

**Lemma (Second moments by points).** $\mathsf{E}(A, \{\sigma\}) = \nu^{-2}\sum_{c, c'}\|A(c, \sigma, c')\|^2$, and $\mathsf{E}(A, \Omega) = \sum_{s \in \Omega}\mathsf{E}(A, \{s\})$.

Lean: `New.Filling.secondMoment_singleton`, `New.Filling.secondMoment_eq_sum_secondMoment_singleton` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* Both follow from the definition, a finite sum over $c$, $c'$ and $s \in \Omega$, by a change of the order of summation. $\square$

**Lemma (No identity term off $\bar R_0$).** If $s \notin \bar R_0$, then $\mathcal{A}_{R_0}(c, s, c') = 0$ for every side and all $c$, $c'$. So if $\Omega$ is disjoint from $\bar R_0$, then $\mathsf{E}(\mathcal{A}, \Omega) = \mathsf{E}(\mathcal{A}_{R_0^c}, \Omega)$.

Lean: `New.Filling.amplitudeSum_besselS_eq_zero` (New/Spanning/Unfolding/SquareExpansion.lean), `New.Filling.secondMoment_univ_eq_secondMoment_compl_besselS` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* A term $\gamma \in R_0$ over $(c, s, c')$ gives $k = h_c^{-1}\gamma h_{c'}$ in $K_S$ and in the adelic Bessel group, with reduction $s$. Then $s \in \bar R_0$. So the sum is over the empty set. For the second part, split the terms into $R_0$ and its complement ([the split lemma](/chapter/remaining-terms/)); the first part is $0$ on $\Omega$. $\square$

### Scalar cosets are not open

**Lemma (A column of zeros).** Let $\varrho > 0$, and let the column of $g$ at the first frame vector $e_1$ be zero off $e_1$. Then every leading minor of size $l > 0$ of the frame products of $g$ is $0$.

Lean: `New.leadingMinor_frameGram_eq_zero` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* The vector $e_1$ is isotropic and orthogonal to the frame. So $h(f_b, ge_1) = g_{e_1e_1}h(f_b, e_1) = 0$ for each frame vector $f_b$. The column $0$ of the frame products is zero, and so is each leading minor that contains it. $\square$

**Lemma (Scalar cosets).** If $s$ lies in a scalar coset $\zeta\bar R_0$, then $s$ is not open. Each $s \in \bar R_0$ lies in the scalar coset of $\zeta = 1$.

Lean: `New.Filling.InScalarCoset.not_isOpenElement`, `New.Filling.inScalarCoset_one` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Write $s = \zeta t$ with $t \in \bar R_0$. The column of $t$ at $e_1$ is the unit vector $e_1$ ([Lemma](/decl/New.Filling.apply_besselFrame_zero_of_mem_reducedImage/)), so the column of $s$ at $e_1$ is zero off $e_1$ at every place. As $\varrho \geq 10^5 > 0$, the minor of size $1$ vanishes at each chosen place by the previous lemma. The second part takes $t = s$. $\square$

**Lemma (The number of scalar cosets).** At most $M^f\#\bar R_0$ elements of $\bar G$ lie in a scalar coset of $\bar R_0$.

Lean: `New.Filling.card_inScalarCoset_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* For each such $s$ choose $\zeta$ and $t$ with $s = \zeta t$. The map $s \mapsto ((\zeta \bmod w)_w, t)$ is injective, since $s$ is determined by it. Its target has $\prod_wp_{i(w)}\cdot\#\bar R_0 = p_0^fp_1^f\#\bar R_0 = M^f\#\bar R_0$ elements, as there are $f$ chosen places above each $p_i$ and the residue field at $w$ has $p_i$ elements. $\square$

**Lemma (The scalar cosets carry little).** Let $E$ contain a primitive root of unity of order $5040$. If $\beta(s) \leq 2D_X$ for all $s$, then $\sum_{s \in \zeta\bar R_0\text{ for some }\zeta}\beta(s) \leq 2M^f\mathcal{D}_{\mathrm{id}}$.

Lean: `New.Filling.sum_secondMoment_inScalarCoset_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* The sum has at most $M^f\#\bar R_0$ terms, each at most $2D_X$, and $\mathcal{D}_{\mathrm{id}} = \#\bar R_0D_X$. $\square$

### The arithmetic of the bounds

We write $\tau_a = b^{-6ka}\mathcal{D}_{\mathrm{main}}$ for $a$ chosen places.

**Lemma (Four inequalities).** For a set of $a$ chosen places above $p_0$, and for $l < n$:

1. $b^{5kf}\mathcal{D}_{\mathrm{id}} \leq \tau_a$;
2. $8M^f\mathcal{D}_{\mathrm{id}} \leq \tau_f$;
3. $(b^{2f}/p_0^f)^k\mathcal{D}_{\mathrm{main}} \leq \tau_f/8$;
4. $p_0^l\sqrt{p_0^r} \leq b^{6k}$, with $r = 2\varrho + k + 1$.

Lean: `New.Filling.pow_mul_identitySecondMoment_le_mul_mainSecondMoment`, `New.Filling.eight_mul_M_pow_mul_identitySecondMoment_le`, `New.Filling.div_levelPrime_pow_mul_mainSecondMoment_le`, `New.Filling.levelPrime_pow_mul_sqrt_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* (1) As $a \leq f$, $b^{6ka}b^{5kf} \leq b^{11kf}$, and $b^{11kf}\mathcal{D}_{\mathrm{id}} \leq \mathcal{D}_{\mathrm{main}}$ by (1.1). (2) $8 \leq b$ and $M \leq b^{23}$ give $8M^f \leq b^{23f+1} \leq b^{5kf}$, since $23f + 1 \leq 5kf$ for $k \geq 1000$; then use (1) with $a = f$. (3) $p_0 \geq b^{10}$ gives $(b^{2f}/p_0^f)^k \leq b^{-8kf} = b^{-2kf}b^{-6kf}$, and $b^{2kf} \geq 8$ as $kf \geq 40$ ([Lemma](/decl/New.Filling.forty_le_k_mul_numInfPlaces/)) and $b \geq 2$. (4) Square both sides. As $p_0 \leq b^{11}$, the left side is at most $b^{11(2l + r)}$. As $l \leq \varrho$ and $2000(\varrho + 1) \leq k$, $11(2l + r) \leq 11(4\varrho + k + 1) \leq 12k$. $\square$

**Lemma (A meet at every place of a fixer).** If $s$ lies in the fixer of all $f$ chosen places above $p_0$, then $p_0^f \leq \mathrm{meetNorm}(s)$.

Lean: `New.Filling.levelPrime_pow_le_meetNorm_of_mem_fixer` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* An element that fixes a frame vector at $w$ meets at $w$, or at its conjugate (the Boolean of the vector). The $f$ places obtained in this way are distinct, as they lie over distinct $w$. The product of their norms is $p_0^f$, and it is at most the meet norm ([Lemma](/decl/New.Filling.prod_le_meetNorm/)). $\square$

### The two fixers

**Lemma (The fixer of all places).** Let $E$ contain a primitive root of unity of order $5040$, and let $\beta(s) \leq 2D_X$ for all $s$. For frame vectors at all $f$ chosen places above $p_0$, the sum of $\beta$ over their fixer is at most $\tau_f$.

Lean: `New.Filling.secondMoment_fixer_univ_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* Split the fixer into the elements in scalar cosets and the rest $\Omega$. The first part is at most $2M^f\mathcal{D}_{\mathrm{id}} \leq \tau_f/4 \leq \tau_f/2$ by (2). The set $\Omega$ avoids the scalar cosets and is disjoint from $\bar R_0$. So $\sum_\Omega\beta = \mathsf{E}(\mathcal{A}_{R_0^c}, \Omega)$, and [the expansion of the squares](/decl/New.Filling.sqrt_secondMoment_compl_besselS_le/) gives

$$\sqrt{\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega)} \leq \sqrt{L} + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}},$$

with $L$ a bound on the links over $\Omega$. Every $s \in \Omega$ has meet norm at least $p_0^f$ by the previous lemma. So [the crude bound on links](/decl/New.Filling.linkSecondMoment_le_of_le_meetNorm/) gives $L = (b^{2f}/p_0^f)^k\mathcal{D}_{\mathrm{main}} \leq \tau_f/8$ by (3). Also $b^{-30}\mathcal{D}_{\mathrm{id}} \leq \tau_f/8$ by (2). With $(x + y)^2 \leq 2(x^2 + y^2)$, $\sum_\Omega\beta \leq 2(\tau_f/8 + \tau_f/8) = \tau_f/2$. Add the two parts. $\square$

**Lemma (The open elements of a fixer).** Assume Weil data on $E$. For a set of $a$ chosen places above $p_0$ with frame vectors, the sum of $\beta$ over the open elements of their fixer is at most $(1 + 4b^{-4})\tau_a$.

Lean: `New.Filling.secondMoment_fixer_isOpenElement_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* Let $\Omega$ be this set. No open element lies in a scalar coset, so $\Omega$ avoids the scalar cosets and $\bar R_0$. The main term ([Theorem](/decl/New.Filling.linkSecondMoment_isOpenElement_le/)) bounds the links over $\Omega$ by $(1 + b^{-4})\tau_a\nu^2$. With $x = b^{-4}$, the expansion of the squares gives

$$\sqrt{\textstyle\sum_\Omega\beta} \leq \sqrt{(1 + x)\tau_a} + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}} \leq (1 + x/2)\sqrt{\tau_a} + (x/2)\sqrt{\tau_a} = (1 + x)\sqrt{\tau_a}.$$

Here $\sqrt{1 + x} \leq 1 + x/2$, $b^{-15} \leq x/2$ and $\mathcal{D}_{\mathrm{id}} \leq \tau_a$ by (1). So $\sum_\Omega\beta \leq (1 + x)^2\tau_a \leq (1 + 4x)\tau_a$, as $x \leq 1$. $\square$

### The elements that are not open

**Lemma (Singular minors).** Let $\beta \geq 0$ have positive type on $\bar G$, let $\Gamma \leq \bar G$ be a subgroup, and let $w$ be a chosen place above $p_0$. Suppose that for every frame vector $d$ at $w$, the elements of $\Gamma$ that fix $d$ carry at most $b^{-6k}\sum_\Gamma\beta$. Let $l < n$. Then the $s \in \Gamma$ whose leading minor $\delta_l$ of size $l$ of the frame products of $s_{0, w}$ vanishes carry at most $3b^{-10}\sum_\Gamma\beta$.

Lean: `New.Filling.sum_leadingMinor_eq_zero_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* Let $\pi : \Gamma \to \mathrm{GL}_r(\mathbb{F}_w)$ be the component at $w$, and $q = p_0$ the size of the residue field. Let $A_0$ be the $r\times l$ matrix of the first $l$ frame vectors, and $A_1 = JA_0$ with $J$ the Gram matrix. Then $\delta_l(s) = \det(A_1^{\mathsf{T}}\pi(s)A_0)$. For $v \neq 0$, the vector $A_0v$ is a frame vector modulo $w$, and the elements with $\pi(s)A_0v = A_0v$ fix it. The vector $A_1v$, under the inverse transpose of $\pi(s)$, is a frame vector modulo the conjugate of $w$. So both hypotheses of [the lemma on singular minors](/decl/New.card_mul_sum_det_eq_zero_le/) hold with $Y = b^{-6k}\sum_\Gamma\beta$, and

$$q\sum_{\delta_l(s) = 0}\beta(s) \leq 2\sum_\Gamma\beta + q^l\sqrt{q^r}\,Y \leq 2\sum_\Gamma\beta + b^{6k}Y = 3\sum_\Gamma\beta,$$

by (4). Divide by $q \geq b^{10}$. $\square$

**Lemma (Not open).** Under the hypotheses of the previous lemma, the elements of $\Gamma$ that are not open carry at most $b^{-4}\sum_\Gamma\beta$.

Lean: `New.Filling.sum_not_isOpenElement_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* An element that is not open has $\delta_l(s) = 0$ at $w$ for some $l < n$. Sum the previous lemma over the $n$ values of $l$: the bound is $3nb^{-10}\sum_\Gamma\beta$. As $n \leq b$ and $3 \leq b^5$, $3nb^{-10} \leq b^{-4}$. $\square$

### The bound over the whole group

**Lemma (A linear inequality).** If $0 \leq x \leq 1/10$, $C \geq 0$ and $m \leq (1 + 4x)C + xm$, then $m \leq (1 + 9x)C$.

Lean: `New.Filling.le_one_add_nine_mul_of_le_add` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* $(1 - x)m \leq (1 + 4x)C \leq (1 - x)(1 + 9x)C$, since $(1 - x)(1 + 9x) - (1 + 4x) = x(4 - 9x) \geq 0$. Divide by $1 - x > 0$. $\square$

**Theorem (The second moment of the blocks).** Assume Weil data on $E$. Let $\beta(s) = \mathsf{E}(\mathcal{A}, \{s\})$ satisfy $\beta(a^{-1}b) = \langle u(a), u(b)\rangle$ for some map $u$ into a complex inner product space, and $\beta(1) \leq 2D_X$. Then $\sum_{s \in \bar G}\beta(s) \leq (1 + 9b^{-4})\mathcal{D}_{\mathrm{main}}$.

Lean: `New.Filling.sum_secondMoment_le` (New/Spanning/Unfolding/MomentBounds.lean).

*Proof.* Let $\mathrm{mass}(A, d)$ be the sum of $\beta$ over the fixer of a set $A$ of places with frame vectors $d$. There are finitely many pairs $(A, d)$. Choose one that makes $b^{6k\#A}\mathrm{mass}(A, d)$ largest. The empty set gives the fixer $\bar G$, so

$$\sum_{\bar G}\beta \leq b^{6k\#A}\mathrm{mass}(A, d).$$

It suffices to show $\mathrm{mass}(A, d) \leq (1 + 9b^{-4})\tau_{\#A}$.

If $A$ is the set of all $f$ places, then $\beta(s) \leq \beta(1) \leq 2D_X$ by positive type, and the lemma on the fixer of all places gives $\mathrm{mass} \leq \tau_f$.

Otherwise take $w \notin A$. For a frame vector $d'$ at $w$, the fixer of $A\cup\{w\}$ with $d$ updated at $w$ is the set of elements of the fixer $\Gamma$ of $(A, d)$ that fix $d'$ (`New.Filling.mem_fixer_insert`). Maximality gives $b^{6k(\#A + 1)}\sum_{\Gamma\cap\mathrm{Fix}(d')}\beta \leq b^{6k\#A}\mathrm{mass}(A, d)$. This is the hypothesis of the lemma on elements that are not open. So

$$\mathrm{mass}(A, d) = \sum_{\Gamma,\text{ open}}\beta + \sum_{\Gamma,\text{ not open}}\beta \leq (1 + 4b^{-4})\tau_{\#A} + b^{-4}\mathrm{mass}(A, d).$$

The linear inequality with $x = b^{-4} \leq 1/10$ ends the proof. $\square$

**Remark (Formalization).** The maximizing pair comes from `Finite.exists_max`. It need not be unique, and the result does not depend on the choice. Positive type is needed only for the elements that are not open and for $\beta(s) \leq \beta(1)$.

**Theorem (Second moment).** Assume Weil data on $E$. Let $\rho$ be a unitary representation of $\bar G$ on a finite-dimensional space $V$, and let $P$ have amplitude blocks. Then

$$\sum_{s \in \bar G}\|P^*\rho(s)P\|^2 \leq (1 + 9b^{-4})\mathcal{D}_{\mathrm{main}}.$$

Lean: `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* By [the norm of the blocks](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sq_eq_secondMoment/), $\|P_s\|^2 = \beta(s)$. Let $u(s)$ be the Hilbert-Schmidt vector of $\rho(s)PP^*\rho(s)^*$. Then $\langle u(a), u(b)\rangle = \|P_{a^{-1}b}\|^2$ ([Lemma](/decl/New.inner_hilbertSchmidtVector_translate/)), so $\beta$ has positive type. Also $\beta(1) = \|P^*P\|^2 \leq 2D_X$ ([Lemma](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_adjoint_comp_sq_le/)). Apply the previous theorem. $\square$
