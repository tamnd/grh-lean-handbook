---
title: Letters and windows for the data
lean:
  - New/Congruences/LocalLoss/CrystallineDefect.lean
decls:
  - New.Selmer.farWindowStart
  - New.Selmer.fitsWindows_and_image_neg_sub_one
  - New.Selmer.smul_eq_pow_of_coefficientEmbedding_eq_pow
  - New.Selmer.complexEmbeddingOf_eq_of_coefficientEmbedding_eq
  - New.Selmer.pow_ordProj_pow_sub_one_eq_one
  - New.Selmer.notMem_bPlaces_of_coefficientEmbedding_eq_pow
  - New.Selmer.eventually_exists_lettersReadThick
  - New.Selmer.crystallineSizes_data
  - New.Selmer.IsMainSummandWeights.le_two_mul_natAbs
  - New.Selmer.hasFewLowJumps_tateDual_of_isMainSummandWeights
  - New.Selmer.subset_Icc_of_jump_eq_single
  - New.Selmer.sum_count_neg_sub_one_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Letters and windows for the data

The bound of [Section 4](/chapter/local-loss/#three-regimes-of-the-prime) has three kinds of hypotheses: size conditions, windows for the jumps, and a chart whose letters read thickness. This section checks all three for the data $D$ and the weights of a main summand. The next section uses them to prove the main theorem.

Throughout, $e : E \to \bar{\mathbb{Q}}_\ell$ is an embedding and $j : \Gamma \to G_\ell$ is a completion group for $e$, as in [Section 2](/chapter/local-loss/#crystalline-cocycles-and-the-defect). For $g \in G_\ell$ write $\sigma_g = \sigma_{e,g}$ and $c_g : O \to \mathbb{C}_\ell$. An element $g$ is *at a b-place* if the infinite place of $\sigma_g$ lies in the sparse set $\mathrm{bPlaces}$ of the data.

### The windows

**Definition (Far window start).** For $i \in \mathbb{N}$ and a complex embedding $\sigma$, put
$$S_i(\sigma) = b_\sigma + (i\Delta + h_2 - 2t), \qquad b_\sigma = \begin{cases} b & \text{the place of } \sigma \text{ is a b-place,} \\ G & \text{otherwise,}\end{cases}$$
with $b = \mathrm{natB}$, $G = \mathrm{offWeight}$, and truncated subtraction.

Lean: `New.Selmer.farWindowStart` (New/Congruences/LocalLoss/CrystallineDefect.lean).

By the definition of the lift weights in [the data and its sizes](/chapter/data-and-sizes/), $w_i(\sigma) = b_\sigma + (i + \frac12)\Delta = b_\sigma + i\Delta + h_2$. So $S_i(\sigma) = w_i(\sigma) - 2t$.

**Lemma (Windows of a main summand).** Let $t' \leq t$, $i \in \mathbb{N}$ and $\sigma$ a complex embedding. Let $J$ be a multiset of integers such that each $u \in J$ has $\Delta \leq 4|u| \leq 8m\Delta$ or $|\varepsilon_\sigma u + w_i(\sigma)| \leq t$. Let $U$ be a finite set each of whose members is in $J$ or is a natural number $c < t'$. Then $U$ fits the windows $(h_2^2 + 1, -\varepsilon_\sigma, S_i(\sigma), 4t)$, and the image $\{-u - 1 : u \in U\}$ fits $(h_2^2 + 1, \varepsilon_\sigma, S_i(\sigma), 4t)$.

Lean: `New.Selmer.fitsWindows_and_image_neg_sub_one` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* The scale conditions of the data give $3t \leq h_2$ and $2m\Delta \leq h_2^2$. A low jump has $|u| \leq 2m\Delta \leq h_2^2$, and $c < t \leq h_2^2$. So both lie in the low window, and $-u - 1$ lies in $[-h_2^2 - 1, h_2^2 + 1]$. A high jump has $-\varepsilon_\sigma u \in [w_i - t, w_i + t]$, which lies in $[S_i, S_i + 4t]$, as $S_i = w_i - 2t$. Then $\varepsilon_\sigma(-u - 1) = -\varepsilon_\sigma u - \varepsilon_\sigma$ lies in $[w_i - t - 1, w_i + t + 1] \subset [S_i, S_i + 4t]$. $\square$

The sign of the window of $U$ is $-\varepsilon_\sigma$, and that of the dual jumps is $\varepsilon_\sigma$. This is the opposite pair of windows that the bounds on cup products need.

### Letters and b-places

The letters of a chart are read from $c_g(\zeta)$ for a root of unity $\zeta \in O$. The next lemmas compare letters with complex embeddings.

**Lemma (Equal powers on roots of unity).** Let $\zeta \in O$ be a primitive $N$-th root of unity, $g, g' \in G_\ell$ and $n \in \mathbb{N}$. If $c_{g'}(\zeta) = c_g(\zeta)^n$, then $(g'g^{-1})(z) = z^n$ for every $z \in \bar{\mathbb{Q}}_\ell$ with $z^N = 1$.

Lean: `New.Selmer.smul_eq_pow_of_coefficientEmbedding_eq_pow` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* The roots $z$ with $z^N = 1$ are the powers $\zeta^a$. The hypothesis says $g'(\zeta) = g(\zeta)^n = g(\zeta^n)$, so $g'g^{-1}$ maps $g(\zeta)$ to $g(\zeta)^n$. Since $g(\zeta)$ is again primitive, every $z$ is a power of it, and $g'g^{-1}$ acts on $z$ by the $n$-th power. $\square$

**Lemma (An unramified letter knows its embedding).** Let $\kappa$ be an unramified Kummer chart of $\Gamma$ and $\zeta \in O$ a primitive $(\ell^f - 1)$-th root of unity. If $c_g(\zeta) = c_{g'}(\zeta)$, then $\sigma_g = \sigma_{g'}$.

Lean: `New.Selmer.complexEmbeddingOf_eq_of_coefficientEmbedding_eq` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* By the previous lemma with $n = 1$, $g g'^{-1}$ fixes all $(\ell^f - 1)$-th roots of unity, hence the constants $W(\mathbb{F}_{\ell^f})$ of the chart. For an unramified chart $E = z + \ell$, and $\theta(E) = 0$ gives $\theta(z) = -\ell$, which $gg'^{-1}$ fixes too. So $gg'^{-1}$ fixes the chart, and the chart property puts it in $j(\Gamma)$. By the [criterion for equal embeddings](/decl/New.Selmer.IsCompletionGroup.complexEmbeddingOf_eq_iff/), $\sigma_g = \sigma_{g'}$. $\square$

**Lemma (A Frobenius on the prime-to-$\ell$ part).** Let $F \in G_\ell$ act on the residue field as $x \mapsto x^{\ell^f}$, and let $z$ be a primitive $N$-th root of unity with $F(z) = z$. Then $(z^{\ell^{v_\ell(N)}})^{\ell^f - 1} = 1$.

Lean: `New.Selmer.pow_ordProj_pow_sub_one_eq_one` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Put $\xi = z^{\ell^{v_\ell(N)}}$, a root of unity of order prime to $\ell$. A Frobenius acts on such roots by $\xi \mapsto \xi^{\ell^f}$. Since $F$ fixes $z$, it fixes $\xi$. So $\xi^{\ell^f} = \xi$, and $\xi^{\ell^f - 1} = 1$. $\square$

**Lemma (Thick letters are sparse).** Let $\ell \leq kt$. Let $F \in j(\Gamma)$ be a Frobenius for $\ell^f$, and $\zeta \in O$ a primitive $(\ell^f - 1)$-th root of unity. Let $a, a' \in [1, \lfloor \log_\ell h_2^3 \rfloor]$ and $g_0, g_1, g_2 \in G_\ell$ with
$$c_{g_1}(\zeta) = c_{g_0}(\zeta)^{\ell^a}, \qquad c_{g_2}(\zeta) = c_{g_0}(\zeta)^{\ell^{a + a'}}.$$
If $g_0$ and $g_2$ are at b-places, then $g_1$ is not.

Lean: `New.Selmer.notMem_bPlaces_of_coefficientEmbedding_eq_pow` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* We apply [b-places are spaced](/decl/New.Selmer.notMem_bPlaces_of_short_arc/), whose input is the sparseness from [progression-free sets](/chapter/progression-free-sets/). Let $\xi$ be the prime-to-$\ell$ part of $e(\zeta_{q_1})$, where $\zeta_{q_1} \in E$ is the primitive $q_1$-th root of unity of the data. Since $F \in j(\Gamma)$ fixes $e(E)$, it fixes $e(\zeta_{q_1})$, and the Frobenius lemma gives $\xi^{\ell^f - 1} = 1$. From the two hypotheses, $c_{g_2}(\zeta) = c_{g_1}(\zeta)^{\ell^{a'}}$. The lemma on equal powers with $N = \ell^f - 1$ now says that $g_2 g_0^{-1}$ and $g_2 g_1^{-1}$ raise $\xi$ to the powers $\ell^{a + a'}$ and $\ell^{a'}$. It remains to check $0 < a' < a + a' < l_0$. From $h_2^3 \leq (2^{\mathrm{towerExp}})^{12}$ one gets $\lfloor \log_\ell h_2^3 \rfloor \leq 12\,\mathrm{towerExp}$, so $a + a' \leq 27\,\mathrm{towerExp} < l_0$. $\square$

**Theorem (A chart that reads b-places).** For all large $O$ there exist a Kummer chart $\kappa$ of $\Gamma$, a root $\zeta \in O$ with $\zeta^{\ell^f - 1} = 1$, a property $T$ and a sign $s$ on $\mathbb{C}_\ell$ such that the letters $g \mapsto c_g(\zeta)$, $g \in G_\ell$, read thickness for
$$\big(\kappa,\ \mathrm{th}(g) = [g \text{ at a b-place}],\ \varepsilon_g = \varepsilon_{\sigma_g},\ Q = kt,\ h = h_2,\ T,\ s\big).$$

Lean: `New.Selmer.eventually_exists_lettersReadThick` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* The existence of Kummer charts in [Kisin frames](/chapter/kisin-frames/#charts-and-kummer-charts) gives $\kappa$ with $ef = [G_\ell : j(\Gamma)]$, unramified if inertia lies in $j(\Gamma)$, and a Frobenius $F \in j(\Gamma)$. Two cases organise the proof. If $\ell$ divides the conductor $q_1 d$, then $\ell \leq kt$ by the sizes of the data. If $\ell \nmid q_1 d$, then inertia fixes $E$, so it lies in $j(\Gamma)$ and $\kappa$ is unramified. For large $O$ there is a primitive $(\ell^f - 1)$-th root $\zeta$ in $O$.

Let $T(z)$ say that some $g$ at a b-place has $c_g(\zeta) = z$. Say that $g$ *reads* $z$ if $g$ is at a b-place, in the case $\ell \mid q_1 d$, and if $c_g(\zeta) = z$, in the case $\ell \nmid q_1 d$. Let $s(z) = \varepsilon_{\sigma_g}$ for a chosen $g$ that reads $z$. We check the six conditions.

1. $ef = [G_\ell : j(\Gamma)]$, from the chart.
2. $e \leq ef = [G_\ell : j(\Gamma)]$, which is the number of embeddings $\sigma_g$. This is at most the number of complex embeddings of $E$, which is at most $h_2$ by the sizes of the data.
3. If $g$ is at a b-place, $T(c_g(\zeta))$ holds by definition. Conversely, let $Q < \ell$ and $T(c_g(\zeta))$, so some $g'$ at a b-place has the same letter. Then $\ell \nmid q_1 d$, the chart is unramified, and $\sigma_g = \sigma_{g'}$ by the lemma above. So $g$ is at a b-place.
4. Let $g$ be at a b-place or let $Q < \ell$. If $\ell \mid q_1 d$, then $\ell \leq Q$, so $g$ is at a b-place. Some $g$ reads every letter, so the chosen element is at a b-place, and [b-places have one sign](/decl/New.Selmer.cmSign_eq_of_mem_bPlaces/) when $\ell \mid q_1 d$. If $\ell \nmid q_1 d$, the chosen element has the letter of $g$, so it has the embedding of $g$ and its sign.
5. If $\ell \mid q_1 d$, then $\ell \leq Q$, and "reads $z$" does not depend on $z$, so $s$ is constant. If $\ell \nmid q_1 d$, the chart is unramified, and $\ell \geq 7$, since the primes up to $7$ divide $q_0$, which divides $q_1$.
6. Let $\ell \leq Q$ and let $z = c_{g_0}(\zeta)$, $z^{\ell^a} = c_{g_1}(\zeta)$ and $z^{\ell^{a + a'}} = c_{g_2}(\zeta)$ with $g_0, g_1, g_2$ at b-places. This contradicts the lemma on sparse letters. $\square$

**Remark (Formalization).** The sign $s$ is defined with a choice (Hilbert's $\varepsilon$ operator) of an element that reads the letter. Conditions 4 and 5 hold for every choice. This is finding F-152 of the notes: the sparseness of the b-places is used here, in condition 6, and nowhere else in this chapter.

### Sizes and low jumps

**Lemma (Sizes of the data).** For $i \leq m$, the numbers
$$Q = kt,\ m,\ h = h_2,\ G,\ b,\ \delta = i\Delta + h_2 - 2t,\ \eta = h_2^2 + 1,\ W = 4t$$
are crystalline sizes.

Lean: `New.Selmer.crystallineSizes_data` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Each condition except 6 is a comparison of the logarithmic scales of [the data and its sizes](/chapter/data-and-sizes/). For 6: $\delta \leq m\Delta + h_2 = 2mh_2 + h_2 < h_2^2 + 1$. $\square$

**Lemma (Jumps of a main summand are large).** If $J$ satisfies the main summand weights, every $u \in J(\sigma)$ has $h_2 \leq 2|u|$.

Lean: `New.Selmer.IsMainSummandWeights.le_two_mul_natAbs` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* A low jump has $|u| \geq \Delta/4 = h_2/2$. A high jump has $|\varepsilon u + w_i| \leq t$ with $w_i \geq h_2 \geq 3t$, so [high jumps are large](/decl/New.Selmer.lt_natAbs_of_abs_add_liftWeight_le/) gives $|u| > h_2/2$. $\square$

**Lemma (Few low jumps of the dual).** Let $J$ satisfy the main summand weights for $(r, t')$. Let $L$ be potentially crystalline over $O$ with $\mathrm{jump}(L, \gamma, u)$ equal to the multiplicity of $u$ in $J(\sigma(\gamma))$, for a map $\sigma$ from embeddings of $O$ to complex embeddings. Let each member of $U(\gamma)$ be in $J(\sigma(\gamma))$ or be a natural number $c < t'$, and each member of $U'(\gamma)$ be a jump of $L^\vee(1)$ at $\gamma$. Then $L^\vee(1)$ has few low jumps for $(h_2, \lfloor rm/k \rfloor, h_2^2 + 1, U, U')$.

Lean: `New.Selmer.hasFewLowJumps_tateDual_of_isMainSummandWeights` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* A jump $u$ of $L^\vee(1)$ means that $-u - 1$ is a jump of $L$, with the same multiplicity. Condition 1: a negative member of $U(\gamma)$ is in $J$, so $2|u| \geq h_2$ by the previous lemma. A negative member $u$ of $U'(\gamma)$ has $-u - 1 \geq 0$ a jump of $L$, so $2(-u-1) \geq h_2$ and $2u \leq -h_2$. Condition 2: the sum of the jumps of $L^\vee(1)$ over $[-h_2^2 - 1, h_2^2 + 1]$ is the left side of the next lemma, with $h = h_2$ and $J = J(\sigma(\gamma))$. The main summand weights bound its right side by $rm/k$. $\square$

**Lemma (Reindexing low jumps).** Let $2 \leq h^2$ and let $J$ be a multiset of integers. Then
$$\sum_{u \in [-h^2 - 1,\, h^2 + 1]} \#_J(-u - 1) \leq \#\{u \in J : |u| \leq 2h^2\},$$
with multiplicities.

Lean: `New.Selmer.sum_count_neg_sub_one_le` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Induction on $J$. Adding a member $a$ adds $1$ to the left side exactly when $u = -a - 1$ lies in $[-h^2 - 1, h^2 + 1]$. Then $|a| \leq h^2 + 2 \leq 2h^2$, so it adds $1$ to the right side too. $\square$

**Lemma (The dual of a character).** If $L$ is potentially crystalline with the single jump $c < t$ at every embedding, then every jump of $L^\vee(1)$ lies in $[-h_2^2 - 1, 0]$.

Lean: `New.Selmer.subset_Icc_of_jump_eq_single` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* The only jump of the dual is $-c - 1$, and $0 \leq c < t \leq h_2^2$. $\square$
