---
title: The defect at a place above ℓ
lean:
  - New/Congruences/LocalLoss/CrystallineDefect.lean
decls:
  - New.Selmer.mem_range_of_modEq_one
  - New.Selmer.two_mul_tame_exponent_le_defectBound
  - New.Selmer.crystalline_bound_le_defectBound
  - New.Selmer.normLength_dualDefect_le_defectBound_of_isTameType
  - New.Selmer.IsSummandClass
  - New.Selmer.normLength_dualDefect_le_of_isSummandClass
  - New.Selmer.summand_defect_le_at_place
  - New.Selmer.sum_count_neg_sub_one_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The defect at a place above ℓ

This section proves the main theorem of the chapter. The class of lattices is tame at a level prime, or crystalline. The tame case uses one result of [cup products](/chapter/cup-products/) and the congruence $\ell \equiv 1$ modulo the conductor. The crystalline case uses the crystalline bound of [Section 4](/chapter/local-loss/#three-regimes-of-the-prime) with the inputs of [Section 5](/chapter/local-loss/#letters-and-windows-for-the-data). Then two comparisons of sizes turn each exponent into $\mathrm{defectBound}(\ell)$.

The setting is that of Section 5: $j : \Gamma \to G_\ell$ is a completion group for $e : E \to \bar{\mathbb{Q}}_\ell$, $\sigma_g = \sigma_{e,g}$, $\varepsilon_\sigma$ is the sign of $\sigma$ for the CM type, and $S_i(\sigma)$ is the far window start.

### The tame case

A level prime $p_n$ of the data has $p_n \equiv 1$ modulo $q_1 d$, by [the level primes](/chapter/data-and-sizes/). The first lemma turns this congruence into a statement on groups.

**Lemma (Surjectivity at a split prime).** If $\ell \equiv 1$ modulo the cyclotomic conductor $q_1 d$ of the data, then every $g \in G_\ell$ lies in $j(\Gamma)$.

Lean: `New.Selmer.mem_range_of_modEq_one` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* By the definition of a completion group it suffices that $g$ fixes $e(E)$. By [fixing roots of unity](/decl/New.Selmer.fixes_emb_of_fixes_rootsOfUnity/) it suffices that $g$ fixes every root of unity $z \in e(E)$, whose order divides $q_1 d$. Since $\ell \nmid q_1 d$, there is $a$ with $g(z) = z^{\ell^a}$. As $\ell^a \equiv 1$ modulo $q_1 d$, $z^{\ell^a} = z$. $\square$

So at a level prime all elements $g$ give one complex embedding $\sigma$, and all embeddings of $O$ have one window. The next result of [cup products](/chapter/cup-products/) then applies. A condition $K$ on polynomials is of *tame type* $(\ell, r, N)$ if it holds for $X^{e'} - 1$, with $e' = \mathrm{lcm}\{\ell^a - 1 : 1 \leq a \leq r\}$, and for $q$ mapped to $O[X]$, for some monic $q \in \mathbb{Z}_\ell[X]$ of degree at most $N$.

**Theorem (Exponent for tame classes).** Let $j$ be a surjective open embedding. For each $s \in \Gamma$ in inertia, let $K_s$ be of tame type $(\ell, r, N)$. Let $L \in \mathrm{InClass}(F, s \mapsto K_{s^{-1}}, U')$. Suppose that for every $\gamma$ the set $U(\gamma)$ fits $(\eta, -\varepsilon, b, W)$ and $U'(\gamma)$ fits $(\eta, \varepsilon, b, W)$, for one sign $\varepsilon$. If
$$b + 6(W + \eta) + r^2(N + 1)^2 + 2 < \ell,$$
then $L$ has cup exponent $3r^2(N + 1)^2 + 150(\eta + W + 1)$ for $\mathrm{InClass}(F, K, U)$.

Lean: `New.Lift.hasCupExponent_of_isTameType` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

This is proved in [cup products](/chapter/cup-products/) with a tame chart of ramification $e'$, over which all lattices of the class become crystalline. We use it as stated.

**Lemma (The tame exponent is small).** Let $0 < x \leq t$ and $n \in \{0, 1\}$. Then
$$2\Big(3r^2\big((r + t)r + 1\big)^2 + 150\big(h_2^2 + 1 + 4t + 1\big)\Big) \leq \frac{\mathrm{defectBound}(p_n)}{x}.$$

Lean: `New.Selmer.two_mul_tame_exponent_le_defectBound` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Since $p_n \mid M$, $v_{p_n}(M) \geq 1$. The left side is at most $10^6 (m/k)\, b / t$ by a comparison of the logarithmic scales of the data: the left side is polynomial in $r$, and $b$ is far larger. Then
$$10^6 \frac{m}{k} \cdot \frac{b \cdot 1}{t} \leq 10^6 \frac{m}{k} \cdot \frac{b\,v_{p_n}(M) + \lambda}{x} = \frac{\mathrm{defectBound}(p_n)}{x},$$
since $x \leq t$ and $\lambda \geq 0$. $\square$

**Theorem (Defect for a tame class).** Let $\ell = p_n$ be a level prime and $j$ a completion group for $e$. Let $L \in \mathrm{InClass}(F, s \mapsto K_{s^{-1}}, U')$, and let $K_s$ be of tame type $(\ell, r, (r + t)r)$ for each $s$ in inertia. Let $i \leq m$ and let $\sigma$ be a complex embedding. Suppose every $U(\gamma)$ fits $(h_2^2 + 1, -\varepsilon_\sigma, S_i(\sigma), 4t)$ and every $U'(\gamma)$ fits $(h_2^2 + 1, \varepsilon_\sigma, S_i(\sigma), 4t)$. Then for $0 < x \leq t$,
$$\lambda_O\big(\delta_{\mathrm{InClass}(F, K, U)}(L)\big) \leq [G_\ell : j(\Gamma)] \cdot \mathrm{rank}_O L \cdot \frac{\mathrm{defectBound}(\ell)}{x}.$$

Lean: `New.Selmer.normLength_dualDefect_le_defectBound_of_isTameType` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* By the lemma on surjectivity and $p_n \equiv 1$ modulo $q_1 d$, $j$ is surjective. The level primes are larger than every weight of the data: since $S_i(\sigma) \leq b_\sigma + m\Delta + h_2$, the scales of the data give
$$S_i(\sigma) + 6\big(4t + h_2^2 + 1\big) + r^2\big((r + t)r + 1\big)^2 + 2 < p_n,$$
in both cases $b_\sigma = b$ and $b_\sigma = G$. So the theorem on tame classes, with $N = (r + t)r$, $\eta = h_2^2 + 1$, $W = 4t$ and start $S_i(\sigma)$, gives the cup exponent
$$\kappa = 3r^2\big((r + t)r + 1\big)^2 + 150\big(h_2^2 + 1 + 4t + 1\big).$$
The lemma on the tame exponent gives $\mathrm{rank}_O L \cdot 2\kappa \leq \mathrm{rank}_O L \cdot \mathrm{defectBound}(\ell)/x$. [Exponent to defect](/chapter/local-loss/#crystalline-cocycles-and-the-defect) now gives the bound. $\square$

In the tame case the defect bound is used only through its term $b\,v_\ell(M)$. The loss $\lambda$ plays no part.

### The crystalline case: two comparisons

**Lemma (The crystalline exponent is small).** Let $\ell$ be prime, $\rho \in \mathbb{N}$ and $0 < x \leq t$. Put $\lambda = \mathrm{crysLoss}(h_2, b, \ell)$. Then
$$10^5\Big(\rho \Big\lfloor \frac{2\lambda}{kt} \Big\rfloor m + \Big\lfloor \frac{\rho m}{kx} \Big\rfloor \lambda\Big) \leq \rho \cdot \frac{\mathrm{defectBound}(\ell)}{x}.$$

Lean: `New.Selmer.crystalline_bound_le_defectBound` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Drop the floors: $\lfloor 2\lambda/(kt) \rfloor \leq 2\lambda/(kx)$, as $x \leq t$, and $\lfloor \rho m/(kx) \rfloor \leq \rho m/(kx)$. So the left side is at most
$$10^5\Big(\frac{2\rho m \lambda}{kx} + \frac{\rho m \lambda}{kx}\Big) = \frac{3 \cdot 10^5 \rho m \lambda}{kx} \leq \frac{10^6 \rho m (b\,v_\ell(M) + \lambda)}{kx} = \rho \cdot \frac{\mathrm{defectBound}(\ell)}{x}. \qquad \square$$

### The main theorem

The hypotheses of the main theorem are collected in one structure.

**Definition (Summand class).** Let $r \in \mathbb{N}$, $J$ assign a multiset of integers to each $g \in G_\ell$, and let $L_c$, $c \in \{\mathrm{none}\} \cup \{0, \dots, t - 1\}$, be lattices over $O$ with an action of $\Gamma$. The class $\mathrm{InClass}(F, K, U)$ is a *summand class* for $(r, J, L)$ if:

1. it is tame or crystalline: either $\ell = p_n$ for a level prime and $K_s$ is of tame type $(\ell, r_D, (r_D + t_D)r_D)$ for every $s$ in inertia, or $F = \top$ and $K = \bot$;
2. every $u \in U(\gamma)$ is a jump of some $L_c$ at $\gamma$;
3. $L_{\mathrm{none}}$ has the jumps $J(g)$ at $c_g$, for every $g \in G_\ell$;
4. $L_c$, for $c \neq \mathrm{none}$, has the single jump $c$ at every $c_g$;
5. $\mathrm{rank}_O L_{\mathrm{none}} = r$.

Lean: `New.Selmer.IsSummandClass` (New/Congruences/LocalLoss/CrystallineDefect.lean).

Here $r_D$ and $t_D$ are the rank parameter and $t$ of the data, and the $r$ of the summand is separate. In the class $\mathrm{InClass}(\top, \bot, U)$ there is no condition on inertia, so every lattice in it is crystalline over a finite extension.

**Theorem (Defect of a summand class).** Let $J(\sigma)$ satisfy the main summand weights for $(r, t)$, and let $j$ be a completion group for $e$. Then for all large $O$ the following holds. Let $\mathrm{InClass}(F, K, U)$ be a summand class for $(r, g \mapsto J(\sigma_g), L)$. Then for each $c$ with $L_c \in \mathrm{InClass}(F, K, U)$,
$$\lambda_O\big(\delta_{\mathrm{InClass}(F, K, U)}(L_c^\vee(1))\big) \leq [G_\ell : j(\Gamma)] \cdot \mathrm{rank}_O L_c \cdot \frac{\mathrm{defectBound}(\ell)}{x_c},$$
with $x_{\mathrm{none}} = 1$ and $x_c = t_D$ otherwise.

Lean: `New.Selmer.normLength_dualDefect_le_of_isSummandClass` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* Take $O$ so large that the theorem on a chart that reads b-places gives $(\kappa, \zeta, T, s)$. Let $c$ be given and $x = x_c$. Then $0 < x \leq t_D$, since $t_D$ is odd. Let $i \leq m$ be the index of the lift weight in the main summand weights.

Step 1: an element for each embedding. Every $\gamma : O \to \mathbb{C}_\ell$ is $c_g$ for some $g \in G_\ell$, by [coefficient embeddings are onto](/decl/New.Selmer.coefficientEmbedding_surjective/). Choose such a $g = g_\gamma$ and put $\sigma(\gamma) = \sigma_{g_\gamma}$. Then the multiplicity of $u$ as a jump of $L_{\mathrm{none}}$ at $\gamma$ is its multiplicity in $J(\sigma(\gamma))$, and $L_c$ has the single jump $c$.

Step 2: windows. By condition 2, every $u \in U(\gamma)$ lies in $J(\sigma(\gamma))$ or equals some $c < t$. The lemma on windows of a main summand in Section 5 gives: $U(\gamma)$ fits $(h_2^2 + 1, -\varepsilon_{\sigma(\gamma)}, S_i(\sigma(\gamma)), 4t_D)$, and the set $U^*(\gamma) = \{-u - 1 : u \in U(\gamma)\}$ fits the opposite window.

Step 3: the dual class. By [duality of classes](/chapter/local-duality/#duality-for-crystalline-cocycles), $L_c \in \mathrm{InClass}(F, K, U)$ gives $L_c^\vee(1) \in \mathrm{InClass}(F, s \mapsto K_{s^{-1}}, U^*)$. Also $\mathrm{rank}\, L_c^\vee(1) = \mathrm{rank}\, L_c$.

Step 4: the tame case, $\ell = p_n$. By the lemma on surjectivity every $g$ is in $j(\Gamma)$, so all $\sigma_g$ are equal to $\sigma_1$, by the criterion for equal embeddings. So all windows have the one sign $\varepsilon_{\sigma_1}$ and the one start $S_i(\sigma_1)$. The theorem on a tame class, applied to $L_c^\vee(1)$, gives the bound.

Step 5: the crystalline case, $F = \top$, $K = \bot$. Let $U'(\gamma)$ be the set of $u \in U^*(\gamma)$ that are jumps of $L_c^\vee(1)$ at $\gamma$. Then $L_c^\vee(1) \in \mathrm{InClass}(\top, \bot, U')$, since a jump of the dual lies in $U^*$ and is a jump. The set $U'(\gamma)$ fits the window of $U^*(\gamma)$. The letters $\gamma \mapsto \gamma(\zeta) = c_{g_\gamma}(\zeta)$ read thickness for $(\kappa, \mathrm{th}, \varepsilon, kt_D, h_2, T, s)$ with $\mathrm{th}(\gamma) = [\sigma(\gamma)$ at a b-place$]$ and $\varepsilon_\gamma = \varepsilon_{\sigma(\gamma)}$, by the choice of $(\kappa, \zeta, T, s)$. We apply the crystalline bound of Section 4 with
$$Q = kt_D,\quad h = h_2,\quad G = \mathrm{offWeight},\quad b = \mathrm{natB},\quad \mu = \Big\lfloor \frac{\mathrm{rank}_O L_c \cdot m}{kx} \Big\rfloor,$$
the crystalline sizes of the data from Section 5, and
$$y = \mathrm{rank}_O L_c \cdot \frac{\mathrm{defectBound}(\ell)}{x}.$$
Two inputs remain.

(a) Few low jumps, or low dual jumps. If $c = \mathrm{none}$, then $x = 1$ and $\mu = \lfloor rm/k \rfloor$, and the lemma on few low jumps of the dual in Section 5 applies. If $c \neq \mathrm{none}$, then $L_c$ has the single jump $c < t \leq t_D$, and the lemma on the dual of a character gives $U'(\gamma) \subset [-h_2^2 - 1, 0]$.

(b) The size of $y$. This is the lemma on the crystalline exponent with $\rho = \mathrm{rank}_O L_c$. $\square$

**Remark (Formalization).** In Step 1 the element $g_\gamma$ is chosen. The bound does not depend on the choice, since condition 3 holds for every $g$. In Step 5 the defect is that of $\mathrm{InClass}(\top, \bot, U)$, while the dual lattice is placed in the smaller class with jump sets $U'$. Only the class of $L_c^\vee(1)$ changes, so the defect is the same. Division in $\mathrm{defectBound}(\ell)/x$ is in the nonnegative reals, so it is exact.

**Theorem (The defect at a place).** Let $J(\sigma)$ satisfy the main summand weights for $(r, t)$, and let $j$ be a completion group for $e$. Then for all large $O$ the following holds. Let $F$, $K$, $U$ and lattices $L_c$, $c \in \{\mathrm{none}\} \cup \{0, \dots, t - 1\}$, satisfy:

1. $\ell = p_n$ and $K_s$ is of tame type $(\ell, r_D, (r_D + t_D)r_D)$ for every $s$ in inertia, or $F = \top$ and $K = \bot$;
2. every $u \in U(\gamma)$ is a jump of some $L_c$ at $\gamma$;
3. for every $c$ and $g$, $L_c$ has at $c_g$ the jumps $J(\sigma_g)$ if $c = \mathrm{none}$ and $\{c\}$ otherwise;
4. $\mathrm{rank}_O L_{\mathrm{none}} = r$.

Then for each $c$ with $L_c \in \mathrm{InClass}(F, K, U)$,
$$\lambda_O\big(\delta_{\mathrm{InClass}(F, K, U)}(L_c^\vee(1))\big) \leq [G_\ell : j(\Gamma)] \cdot \mathrm{rank}_O L_c \cdot \frac{\mathrm{defectBound}(\ell)}{x_c},$$
with $x_{\mathrm{none}} = 1$ and $x_c = t_D$ otherwise.

Lean: `New.Selmer.summand_defect_le_at_place` (New/Congruences/LocalLoss/CrystallineDefect.lean).

*Proof.* The four hypotheses are the five conditions of a summand class, with condition 3 split into its cases. Apply the theorem on the defect of a summand class. $\square$

This is the result that [main summands](/chapter/main-summands/) cites: the defect bound is an upper bound for the defect at each place above $\ell$, and for $\ell$ prime to $M$ and large compared with the weights, $\lambda = 0$ and the bound is $0$.

### Where the defect bound comes from

The two comparisons show which term of $\mathrm{defectBound}(\ell)$ pays for which case.

| Case | Exponent | Paid by |
|---|---|---|
| tame, $\ell = p_n$ | polynomial in $r$ | $b\,v_\ell(M)$ |
| crystalline, small $\ell \leq kt$ | about $\lambda m/(kt)$ per rank | $\lambda$ |
| crystalline, large $\ell$ | $\mu \lambda$ and $\lambda$ per rank | $\lambda$ |

For the generic prime, $\ell \nmid M$ and $\ell > 2b + 30h_2^3$, all terms are $0$. The sum of $\mathrm{defectBound}(\ell)$ over all primes is then a finite sum, which the [denominator budget](/chapter/regular-families-plan/#the-denominator-budget) controls.
