---
title: The expansion of the squares
lean:
  - New/Spanning/Unfolding/SquareExpansion.lean
  - New/Spanning/Unfolding/Climbing.lean
  - New/Spanning/Unfolding/BesselLevelStructure.lean
decls:
  - New.Filling.InScalarCoset
  - New.Filling.exists_scalar_mul_besselS
  - New.Filling.eq_one_of_reduceAt_eq_one
  - New.Filling.eq_one_of_reduceAt_scalar_eq_one
  - New.Filling.AvoidsScalarCosets
  - New.Filling.AvoidsScalarCosets.not_normOnePairOccursFrom_zero
  - New.Filling.normOnePairOccursFrom_zero_of_mem_besselS
  - New.Filling.isStable_compl_besselS
  - New.Filling.AvoidsScalarCosets.amplitudeSum_compl_besselS_eq
  - New.Filling.forty_le_k_mul_numInfPlaces
  - New.Filling.sqrt_secondMoment_compl_besselS_le
  - New.Filling.apply_besselFrame_zero_of_mem_reducedImage
  - New.Filling.meetsAt_of_eq_of_mem_reducedImage
  - New.Filling.prod_levelPrime_le_meetNorm_of_eq
  - New.Filling.avoidsScalarCosets_setOf_exists_apply_eq
  - New.Filling.M_div_b_le_levelPrime_sq
  - New.Filling.secondMoment_compl_besselS_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The expansion of the squares

The square of a Poincaré series is a sum over pairs of terms. In rank one the terms that are not the identity give Kloosterman sums, and these are small in mean. Here the role of the identity is played by the terms in $R_0$. This section shows that, over the elements $s$ that are near $\bar R_0$, the other terms carry little second moment. The bound is the input of [the section on the identity terms](/chapter/moments/#the-identity-terms).

The proof has three parts. First, a term off $R_0$ whose characters agree and that is not a remaining term is a scalar times an element of $R_0$; near $\bar R_0$ the scalar is $1$. Second, the terms whose characters do not agree cancel. So near $\bar R_0$ the blocks of the terms off $R_0$ are the blocks of the remaining terms $\Gamma^*$. Third, an $s$ near $\bar R_0$ meets the frame at many places, so its meet norm is large, and the crude bound of [the chapter on the remaining terms](/chapter/remaining-terms/) applies.

Throughout, $E$ contains a primitive root of unity of order $5040$ and $S$ is admissible, unless a result says less. The frame is $f = (e_1, \dots, e_\varrho, z)$, indexed by $a = 0, \dots, \varrho$, so that $f_0 = e_1$.

### Scalar cosets

For an integral idele $\zeta$, the residue of $\zeta$ at a chosen place $w$ is written $\bar\zeta_w$.

**Definition (Scalar coset).** An element $s \in \bar G$ lies in the *scalar coset* of $\zeta$ if there is $t \in \bar R_0$ with $s_{i, w} = \bar\zeta_w t_{i, w}$ for every $i$ and every chosen place $w$ above $p_i$.

Lean: `New.Filling.InScalarCoset` (New/Spanning/Unfolding/Climbing.lean).

A norm one pair occurs for $\gamma$ from the index $0$ on if there is $\zeta$ with $\zeta\bar\zeta = 1$ such that for every index $a$ there are coefficient vectors $x, y$, zero above $a$, with $x_a = \zeta$, $y_a = 1$ and $fx = \gamma fy$ ([Definition](/decl/New.NormOnePairOccursFrom/)). At $a = 0$ this says $\gamma e_1 = \zeta e_1$.

**Lemma (Terms with a norm one pair).** Let $\gamma$ be a term over $(c, s, c')$ for which a norm one pair occurs from the index $0$ on. Then there is $\zeta \in E$ with $\zeta\bar\zeta = 1$, integral at every finite place, such that $\gamma = \zeta\gamma_0$ with $\gamma_0 \in R_0$, and $s$ lies in the scalar coset of $\zeta$.

Lean: `New.Filling.exists_scalar_mul_besselS` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Let $k = h_c^{-1}\gamma h_{c'} \in K$, with reduction $s$. The pair at index $0$ gives $\gamma e_1 = \zeta e_1$. The class representatives act only on $X_0$ in the lattice coordinates, so the entry of $\gamma$ at $(e_1, e_1)$, which is $\zeta$, is the same entry of the integral matrix $k$. So $\zeta$ is integral. The pairs at all indices say that the flags of $f$ and of $\zeta^{-1}\gamma f$ agree with the leading coefficients $1$. So $\gamma_0 = \zeta^{-1}\gamma$ lies in $R_0$ (Lemma `New.scalarIsometry_inv_mul_mem_besselS`). Let $z = \zeta\cdot 1$, an element of $K$ because $\zeta$ and $\bar\zeta$ are integral. Then $k_0 = z^{-1}k$ equals $h_c^{-1}\gamma_0h_{c'}$, an integral point of $R_0$, so its reduction $t$ lies in $\bar R_0$. The reduction of $z$ at $w$ is $\bar\zeta_w\cdot 1$. So $s_{i, w} = \bar\zeta_wt_{i, w}$. $\square$

The scalar $\zeta$ is a unit of norm one, so it is a root of unity. The next lemma uses the freeness of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/#the-level-structure-of-the-bessel-data).

**Lemma (Freeness).** Let $n$ be a finite set with $\#n \leq k$ and $i \in \{0, 1\}$. Let $\gamma$ be a rational point of the unitary group of the standard definite form in $n$ variables and $g$ a finite adelic point. If $g^{-1}\gamma g$ is integral and reduces to $1$ at every chosen place above $p_i$, then $\gamma = 1$.

Lean: `New.Filling.eq_one_of_reduceAt_eq_one` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* The $f$ chosen places above $p_i$ have the norm $p_i \geq b^{10} \geq k^{10} > (2\#n)^2$. Their product is $p_i^f > (2\#n)^{2f} = (2\#n)^{[E:\mathbb{Q}]}$. The number $\tau = \operatorname{tr}(\gamma - 1)$ is an algebraic integer that lies in each of these places, so $|N(\tau)| \geq p_i^f$ if $\tau \neq 0$. Every conjugate of $\tau$ has modulus at most $2\#n$, since the form is definite and the conjugates of $\gamma$ are unitary. So $\tau = 0$. Then $\operatorname{tr}(\gamma - 1)^*(\gamma - 1) = -2\operatorname{Re}\tau = 0$ at each infinite place, so $\gamma = 1$. This is the general freeness lemma `New.Variety.eq_one_of_reduceAt_eq_one` of the source, applied to the places above $p_i$. $\square$

**Lemma (Scalars near $1$).** Let $\zeta \in E$ be integral with $\zeta\bar\zeta = 1$, and let $\bar\zeta_w = 1$ at every chosen place $w$ above $p_i$. Then $\zeta = 1$.

Lean: `New.Filling.eq_one_of_reduceAt_scalar_eq_one` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* View $\zeta$ as an isometry of the standard form in one variable. Apply freeness with $\#n = 1 \leq k$ and $g = 1$. $\square$

**Definition (Avoiding scalar cosets).** A set $\Omega \subset \bar G$ *avoids scalar cosets* if no $s \in \Omega$ lies in the scalar coset of an integral $\zeta \neq 1$ with $\zeta\bar\zeta = 1$.

Lean: `New.Filling.AvoidsScalarCosets` (New/Spanning/Unfolding/SquareExpansion.lean).

**Lemma (No norm one pairs off $R_0$).** Let $\Omega$ avoid scalar cosets. Let $\gamma \notin R_0$ be a term over $(c, s, c')$ with $s \in \Omega$. Then no norm one pair occurs for $\gamma$ from the index $0$ on.

Lean: `New.Filling.AvoidsScalarCosets.not_normOnePairOccursFrom_zero` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* If one occurs, then $\gamma = \zeta\gamma_0$ with $\gamma_0 \in R_0$ and $s$ in the scalar coset of $\zeta$. As $s \in \Omega$, $\zeta = 1$. Then $\gamma = \gamma_0 \in R_0$, a contradiction. $\square$

The lemma needs neither the root of unity nor admissibility.

### The blocks off $R_0$ near $\bar R_0$

**Lemma (The Bessel group has norm one pairs).** For $\gamma \in R_0$, a norm one pair occurs from the index $0$ on, with $\zeta = 1$.

Lean: `New.Filling.normOnePairOccursFrom_zero_of_mem_besselS` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* An element of $R_0$ maps each $f_a$ to $f_a$ plus a combination of the $f_b$ with $b < a$ ([the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block)). Take $y = e_a$ and let $x$ be the coefficient vector of $\gamma f_a$. Then $x_a = 1$, $y_a = 1$, both vanish above $a$, and $fx = \gamma fy$. $\square$

**Lemma (The complement is stable).** The complement of $R_0$ is stable.

Lean: `New.Filling.isStable_compl_besselS` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* $u^{-1}\gamma u' \in R_0$ if and only if $\gamma \in R_0$, as $R_0$ is stable. Take negations. $\square$

**Theorem (Blocks off $R_0$ are blocks of $\Gamma^*$).** Let $\Omega$ avoid scalar cosets and $s \in \Omega$. Then for all classes $c, c'$, for the full and for the cut function,

$$\mathcal{A}_{R_0^c}(c, s, c') = \mathcal{A}_{\Gamma^*}(c, s, c').$$

Lean: `New.Filling.AvoidsScalarCosets.amplitudeSum_compl_besselS_eq` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* We use three facts from [the section on reduced groups](/chapter/poincare-series/#reduced-groups-and-the-structure-of-a-term): $\Gamma^*$ is stable; if a norm one pair occurs for $\gamma$ from the index $0$ on, then $\gamma \notin \Gamma^*$; if the characters of $\gamma$ agree and $\gamma \notin \Gamma^*$, then such a pair occurs.

By the previous lemma and the second fact, $\Gamma^* \subset R_0^c$. Let $A$ be the set of $\gamma$ whose characters agree. Split twice ([Lemma](/decl/New.Filling.amplitudeSum_eq_inter_compl_add_inter/)):

$$\mathcal{A}_{R_0^c} = \mathcal{A}_{\Gamma^*} + \mathcal{A}_{R_0^c \cap \Gamma^{*c} \cap A^c} + \mathcal{A}_{R_0^c \cap \Gamma^{*c} \cap A}.$$

The set $R_0^c \cap \Gamma^{*c} \cap A^c$ is stable: each of the three sets is stable, and for rational $u, u' \in \mathsf{U}$ the characters of $u\gamma u'$ agree if and only if those of $\gamma$ agree ([Lemma](/decl/New.Filling.charsAgree_mul_mul_iff_of_mem_besselU/)). No element of it has agreeing characters. So its blocks are $0$ ([Theorem](/decl/New.Filling.amplitudeSum_eq_zero_of_not_charsAgree/)). An element $\gamma$ of the last set has agreeing characters and is not in $\Gamma^*$, so a norm one pair occurs for $\gamma$ from the index $0$ on. If $\gamma$ were a term over $(c, s, c')$, this would contradict the lemma on norm one pairs off $R_0$. So the last block is a sum over the empty set. $\square$

**Lemma (A small exponent).** $kf \geq 40$.

Lean: `New.Filling.forty_le_k_mul_numInfPlaces` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* $k \geq 1000(2\varrho + 2) \geq 40$ and $f \geq 1$. $\square$

**Theorem (The terms off $R_0$, with a bound on links).** Let $\Omega$ avoid scalar cosets. Let $C \geq 0$ with $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq C\nu^2$. Then

$$\sqrt{\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega)} \leq \sqrt{C} + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}}.$$

Lean: `New.Filling.sqrt_secondMoment_compl_besselS_le` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* By the theorem above, $\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega) = \mathsf{E}(\mathcal{A}_{\Gamma^*}, \Omega)$. By Minkowski's inequality ([Lemma](/decl/New.Filling.sqrt_secondMoment_add_le/))

$$\sqrt{\mathsf{E}(\mathcal{A}_{\Gamma^*}, \Omega)} \leq \sqrt{\mathsf{E}(\mathcal{A}_{\Gamma^*} - \mathcal{A}^\flat_{\Gamma^*}, \Omega)} + \sqrt{\mathsf{E}(\mathcal{A}^\flat_{\Gamma^*}, \Omega)}.$$

The cut costs $\mathsf{E}(\mathcal{A}_{\Gamma^*} - \mathcal{A}^\flat_{\Gamma^*}, \Omega) \leq b^{-40}\mathcal{D}_{\mathrm{id}}$ ([Theorem](/decl/New.Filling.secondMoment_sub_cut_le/)). The sum over the remaining terms ([Theorem](/decl/New.Filling.secondMoment_remainingTerms_le/)) gives $\mathsf{E}(\mathcal{A}^\flat_{\Gamma^*}, \Omega) \leq C + b^{-kf}\mathcal{D}_{\mathrm{id}} \leq C + b^{-40}\mathcal{D}_{\mathrm{id}}$, as $kf \geq 40$. With $\sqrt{x + y} \leq \sqrt x + \sqrt y$,

$$\sqrt{\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega)} \leq \sqrt C + 2b^{-20}\sqrt{\mathcal{D}_{\mathrm{id}}} \leq \sqrt C + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}},$$

because $2b^{-5} \leq 1$. $\square$

**Remark (Formalization).** In Lean the hypothesis reads $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq \operatorname{ofReal}(C\nu^2)$ in $[0, \infty]$. The number $\mathsf{L}$ may be $\infty$; then no $C$ satisfies the hypothesis, and the theorem says nothing. The condition $C \geq 0$ is needed for $\sqrt C$, since Lean sets $\sqrt C = 0$ for $C < 0$.

### Elements near $\bar R_0$

We now take $\Omega_i = \{s : s_i = t_i \text{ for some } t \in \bar R_0\}$, the set of $s$ that agree with an element of $\bar R_0$ at all chosen places above $p_i$. The meet norm and meeting are those of [the section on climbing the flags](/chapter/poincare-series/#climbing-the-flags).

**Lemma (The reduced Bessel group fixes $e_1$).** If $t \in \bar R_0$, then at each chosen place $w$ the column of $t_{i, w}$ at $e_1$ is the column of the identity matrix.

Lean: `New.Filling.apply_besselFrame_zero_of_mem_reducedImage` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* $t$ is the reduction of an integral point $k$ of $R_0$, and $ke_1 = e_1$. Reduce the column. $\square$

**Lemma (Meeting near $\bar R_0$).** Let $t \in \bar R_0$ and $s_i = t_i$. Then $s$ meets at each chosen place $w$ above $p_i$, with either value of the flag of conjugation.

Lean: `New.Filling.meetsAt_of_eq_of_mem_reducedImage` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* At $(w, \epsilon)$ the action of $s$ depends only on $s_i$, so it is the action of $t$. Write $t$ as the reduction of an integral point $k$ of $R_0$. The action of $t$ at $(w, \epsilon)$ is the integral matrix of $k$ reduced entrywise modulo the place (Lemma `New.Filling.actionAt_reduction`). As $ke_1 = e_1$, this matrix maps $e_1$ to $e_1$. So $e_1$ is a nonzero common vector of the span of $f$ and its image. $\square$

**Lemma (The meet norm near $\bar R_0$).** If $t \in \bar R_0$ and $s_i = t_i$, then $p_i^{2f} \leq \operatorname{meetNorm}(s)$.

Lean: `New.Filling.prod_levelPrime_le_meetNorm_of_eq` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* The pairs $(w, \epsilon)$ of a chosen place above $p_i$ and a flag of conjugation are $2f$ places above $M$, each of norm $p_i$. The previous lemma says that $s$ meets at all of them. The product of their norms is at most the meet norm ([Lemma](/decl/New.Filling.prod_le_meetNorm/)). $\square$

**Lemma (No scalar cosets near $\bar R_0$).** The set $\Omega_i$ avoids scalar cosets.

Lean: `New.Filling.avoidsScalarCosets_setOf_exists_apply_eq` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Let $s \in \Omega_i$ with $s_i = t_i$, $t \in \bar R_0$, and let $s$ lie in the scalar coset of $\zeta$ by $t' \in \bar R_0$. Compare the entries at $(e_1, e_1)$ at a place $w$ above $p_i$: $1 = (t_{i, w})_{e_1e_1} = (s_{i, w})_{e_1e_1} = \bar\zeta_w(t'_{i, w})_{e_1e_1} = \bar\zeta_w$. So $\bar\zeta_w = 1$ at every $w$ above $p_i$, and $\zeta = 1$ by the lemma on scalars near $1$. $\square$

**Lemma (The level primes are close).** For $i = 0, 1$, $M/b \leq p_i^2$.

Lean: `New.Filling.M_div_b_le_levelPrime_sq` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* $p_j \leq b^{11} = b\cdot b^{10} \leq bp_i$ for both $j$. So $M = p_ip_{1-i} \leq bp_i^2$. $\square$

**Theorem (The second moment near $\bar R_0$).** For $i = 0, 1$,

$$\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega_i) \leq b^{-12}\mathcal{D}_{\mathrm{id}}.$$

Lean: `New.Filling.secondMoment_compl_besselS_le` (New/Spanning/Unfolding/SquareExpansion.lean).

*Proof.* Put $z = p_i^{2f} \neq 0$. Every $s \in \Omega_i$ has $z \leq \operatorname{meetNorm}(s)$. The crude bound on links ([Theorem](/decl/New.Filling.linkSecondMoment_le_of_le_meetNorm/)) gives $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega_i) \leq C\nu^2$ with $C = (b^{2f}/z)^k\mathcal{D}_{\mathrm{main}}$. By the previous lemma, $z = (p_i^2)^f \geq (M/b)^f$. By (1.1), $\mathcal{D}_{\mathrm{main}} \leq (M/b^6)^{kf}\mathcal{D}_{\mathrm{id}}$. So

$$C \leq \Big(\frac{b^{3f}}{M^f}\Big)^k\Big(\frac{M}{b^6}\Big)^{kf}\mathcal{D}_{\mathrm{id}} = b^{-3kf}\mathcal{D}_{\mathrm{id}} \leq b^{-30}\mathcal{D}_{\mathrm{id}},$$

since $3kf \geq 30$. The set $\Omega_i$ avoids scalar cosets. The previous theorem gives

$$\sqrt{\mathsf{E}(\mathcal{A}_{R_0^c}, \Omega_i)} \leq b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}} + b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}} = 2b^{-15}\sqrt{\mathcal{D}_{\mathrm{id}}}.$$

Square: $\mathsf{E} \leq 4b^{-30}\mathcal{D}_{\mathrm{id}} \leq b^{-12}\mathcal{D}_{\mathrm{id}}$, as $4 \leq b^{18}$. $\square$

The exponent $12$ has a large margin. The exponent $3kf$ of the gain comes from the $2f$ places at which $s$ meets the frame: each place gives a factor $p_i^k$ against the factor $(M/b^6)^{k/2}$ of (1.1).
