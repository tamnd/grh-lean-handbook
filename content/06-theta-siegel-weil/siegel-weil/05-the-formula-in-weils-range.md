---
title: The formula in Weil's range
lean:
  - Lib/SiegelWeil/Formula/WeilRange.lean
  - Lib/SiegelWeil/Formula/StrongApproximation.lean
decls:
  - New.SiegelWeil.lCoord_mul_levi_dyadicDiag
  - New.SiegelWeil.tendsto_integral_theta_zeroTerm_sub
  - New.SiegelWeil.tendsto_zeroTerm_of_notMem
  - New.SiegelWeil.bddAbove_norm_sub_tsum_norm_zeroTerm
  - New.SiegelWeil.exists_lagrangian_equiv_col_mem
  - New.SiegelWeil.tendsto_tsum_zeroTerm_sub_integral_theta
  - New.SiegelWeil.siegel_weil
  - New.Exchange.exists_torus_mul_quasiReflection_fixes
  - New.Exchange.exists_torus_mul_rational_fixes
  - New.Exchange.IsAutFunction.apply_eq_apply_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The formula in Weil's range

This section proves the Siegel-Weil formula. After Sections 3 and 4 the bound in the cusp remains. It comes from an induction on the rank of $S$: along the torus in the direction of one isotropic line, the formula for $S$ reduces to the formula for the complement of a hyperbolic plane. 

Let $P$ be a complete splitting of $S$ into $p$ hyperbolic planes, with isotropic frame $k$, and let $\mathrm{rank}\, T = m$ with $2p < m$. For $x \in \mathbb{N}^p$, $a_x$ is the Levi element of $\mathrm{diag}(2^{x_i})$ at the infinite places, and $\tau_x$ is the normalised torus action `normalisedTorus T P x` of Section 3. For a column $\iota$ of $k$, the source chooses with `New.Space.exists_splitting` a splitting $D_1$ of $S$ that splits off the line of $k_\iota$, with complement $S_1$ of rank $2p - 2$.

A limit "as $x_\iota \to \infty$, uniformly for $f$ in $C$" is along the inverse image of $\mathrm{atTop}$ under $(x, f) \mapsto x_\iota$ on $\mathbb{N}^p \times C$.

**Lemma (The torus on the coordinate of the line).** The Levi element $a_x$ scales the row $D_1.\mathrm{lCoord}$, the $l$-coordinate in $D_1$, by the conjugate of $2^{-x_\iota}$ at the infinite places:
$$D_1.\mathrm{lCoord} \cdot a_x = \overline{(2^{x_\iota})^{-1}}\, D_1.\mathrm{lCoord}.$$

Lean: `New.SiegelWeil.lCoord_mul_levi_dyadicDiag` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Take the entry $\iota$ of the Levi law $P.\mathrm{lCoord} \cdot a_x = (\mathrm{diag}(2^{x})^{-1})^* P.\mathrm{lCoord}$. $\square$

So after the torus element the Heisenberg translates whose mean is the zero term along the line shrink by $2^{-x_\iota}$ at the infinite places.

**Lemma (The line term approaches theta).** Let $C$ be a compact set of vectors. As $x_\iota \to \infty$, uniformly for $f \in C$,
$$\int_{[U(T)]} \Big(\theta\big(\omega_1(1, h)\, \mathrm{ev}_{D_1}(\tau_x f)\big) - \theta\big(\omega(1, h)\, \tau_x f\big)\Big)\, dh \to 0,$$
where $\omega_1$ is the Weil representation of $(S_1, T)$ and $\mathrm{ev}_{D_1}$ is the zero term along the line.

Lean: `New.SiegelWeil.tendsto_integral_theta_zeroTerm_sub` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Let $B$ be the integrable majorant of `theta_normalisedTorus_le` of Section 3, so $\|\theta(\omega(1, h)\tau_x f)\| \le B(h)\|f\|$ for all $x$. The zero term along the line is a mean over a periodic variable $q$, and a mean lies in a closed ball if every value does. Write $q = Mb$ with an integer $M \neq 0$ and move $b$ into a compact fundamental set $\Omega$ by a rational vector, which periodicity removes. By the lemma above, the distance of the value at $q$ from $\theta(\omega(1, h)\tau_x f)$ is the theta value of $\tau_x$ applied to the difference of $f$ and a translate of $f$ by $ay$, $y \in \Omega$, where $a$ is $M$ at the finite places and $M/2^{x_\iota}$ at the infinite places. The majorant bounds it by $B(h)\mu(a, h)$, where $\mu(a, h)$ is the largest such distance for $f \in C$, and $\mu(a, h) \to 0$ as $a \to 0$. Dominated convergence in $h$ ends the proof. $\square$

**Lemma (Terms off the line decay).** Let $m \neq 0$, let $L$ be a Lagrangian of $S$ that does not contain $k_\iota$, and let $C$ be a set of vectors of norm at most $R$. Then $\mathrm{ev}_L(\tau_x f) \to 0$ as $x_\iota \to \infty$, uniformly for $f \in C$.

Lean: `New.SiegelWeil.tendsto_zeroTerm_of_notMem` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Write $L = L_{P'}$ with frame $k'$. Since $k_\iota \notin L$, there is a rational matrix $Y$ with $Y k' = 1$ and $Y k_\iota = 0$. The bound `exists_zeroTerm_normalisedTorus_le` of Section 3, applied with $Z = Y$ times the frame of $P$, gives a constant $c$ with
$$\|\mathrm{ev}_L(\tau_x f)\| \le c\, \|f\|\, \big((2^{d})^{x_\iota}\big)^{-m}$$
where $d$ is the number of infinite places, because column $\iota$ of $Yk$ is zero. The right side tends to $0$ since $m \neq 0$. $\square$

### The induction step

**Lemma (The induction step).** Let $2p < m$. Suppose that the zero terms of $S$ are summable for every $f$ and that the theta function of $S$ is integrable for every $f$. Suppose that the Siegel-Weil formula holds for $S_1$: for every $f_1$, the theta function of $\omega_1(1, h) f_1$ is integrable and
$$\int_{[U(T)]} \theta\big(\omega_1(1, h) f_1\big)\, dh = \mathrm{vol}([U(T)]) \sum_{L_1} \mathrm{ev}_{L_1}(f_1).$$
Then for every compact set $C$, as $x_\iota \to \infty$ uniformly for $f \in C$,
$$\mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(\tau_x f) - \int_{[U(T)]} \theta\big(\omega(1, h)\tau_x f\big)\, dh \to 0.$$

Lean: `New.SiegelWeil.tendsto_tsum_zeroTerm_sub_integral_theta`, `New.SiegelWeil.exists_lagrangian_equiv_col_mem` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Let $A$ be the set of Lagrangians of $S$ that contain $k_\iota$. By `exists_lagrangian_equiv_containing` of Section 2 for $D_1$, the Lagrangians of $S_1$ are in bijection with $A$, and the zero term along the image of $L_1$ is $\mathrm{ev}_{L_1} \circ \mathrm{ev}_{D_1}$. Split the sum over $L$ into the sums over $A$ and its complement. By the bijection and the formula for $S_1$, applied to $f_1 = \mathrm{ev}_{D_1}(g)$, the volume times the sum over $A$ is the integral of the theta function of $\omega_1(1,h)\mathrm{ev}_{D_1}(g)$. So for each $g$ the difference is
$$\int \Big(\theta\big(\omega_1(1, h)\mathrm{ev}_{D_1} g\big) - \theta\big(\omega(1, h) g\big)\Big)\, dh + \mathrm{vol}([U(T)]) \sum_{L \notin A} \mathrm{ev}_L(g).$$
At $g = \tau_x f$ the first term tends to $0$ by the lemma on the line term. The terms of the second sum tend to $0$ by the lemma on the terms off the line, and they are dominated by $b(L) R$, with $b$ the summable bound of `exists_summable_zeroTerm_bound` and $R$ a bound of the norms on $C$. Dominated convergence for sums ends the proof. $\square$

### The proof of the formula

**Theorem (Siegel-Weil formula in Weil's range).** Let $P$ be a complete splitting of $S$ into $p$ hyperbolic planes, and let $2p < m$. Then:

1. the operator norms $\|\mathrm{ev}_L\|$ are summable over the Lagrangians $L$ of $S$;
2. for every $f \in \mathcal{S}(\mathrm{Hom}(S, T))$, the function $h \mapsto \theta(\omega(1, h) f)$ is integrable for the quotient measure on $[U(T)]$, and
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(f).$$

Lean: `New.SiegelWeil.siegel_weil`, `New.Exchange.thetaIntegral_pairWeil`, `New.ThetaKernel.theta_rat_mul`, `New.pairThetaKer` (Lib/SiegelWeil/Formula/WeilRange.lean; Lib/Weil/DualPair/ThetaIntegrals.lean; Lib/Weil/DualPair/ThetaLiftConvergence.lean; Lib/Weil/DualPair/WeilAction.lean).

*Proof.* Use strong induction on the rank of $S$, for all complete splittings at once.

*Summability and integrability.* Part 1 is `exists_summable_zeroTerm_bound` at $x = 0$, and integrability is `integrable_theta_splitWeil` of Section 3.

*The difference.* Let
$$\ell(f) = \mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(f) - \int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh.$$
The source defines $\ell$ as a continuous functional. It remains to show $\ell = 0$.

*The case $S = 0$.* There is one Lagrangian, its zero term is the theta function, and $U(T)$ acts trivially on $\mathrm{Hom}(S, T) = 0$.

*The limit along the torus.* Let $S \neq 0$, $C$ compact and $\iota$ a column of $k$. Take $D_1$ and $S_1$ as in the notation. The Lagrangian of $P$ contains $k_\iota$, so it is the image of a Lagrangian $L_1$ of $S_1$, and $S_1$ has the complete splitting chosen for $L_1$, with $p - 1$ planes and $2(p-1) < m$. The induction hypothesis gives the formula for $S_1$, and the induction step gives $\ell(\tau_x f) \to 0$ as $x_\iota \to \infty$, uniformly for $f \in C$.

*Invariance.* The functional $\ell$ is invariant under $U(T)(\mathbb{A})$: for the integral by `thetaIntegral_pairWeil`, for the zero terms by `mixedValue_splitWeil` of Section 2. It is invariant under the rational points $\gamma$ of $U(S)$: the theta function by `theta_rat_mul`, and the sum of the zero terms because `exists_lagrangian_equiv_containing` for `isometrySplitting γ` permutes the Lagrangians.

*The bound in the cusp.* The next lemma gives hypothesis 3 of the vanishing criterion of Section 4, which then gives $\ell = 0$. $\square$

**Lemma (The bound in the cusp).** Let $\ell$ be a continuous functional invariant under the rational points of $U(S)$. Suppose that for every compact $C$ and every $\iota$, $\ell(\tau_x f) \to 0$ as $x_\iota \to \infty$ uniformly for $f \in C$. Suppose that $\sum_L \|\mathrm{ev}_L(f)\|$ converges for every $f$. Then for every $f$ the function
$$g \mapsto \big\|\ell(\omega(g, 1) f)\big\| - \sum_L \big\|\mathrm{ev}_L(\omega(g, 1) v)\big\|$$
is bounded above on $U(S)(\mathbb{A})$, where $v$ is the vacuum.

Lean: `New.SiegelWeil.bddAbove_norm_sub_tsum_norm_zeroTerm` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* By the Siegel set theorem of Section 3, every $g$ is $\gamma a_x \kappa$ with $\gamma$ rational, $x \in \mathbb{N}^p$ and $\kappa$ in a compact set $\Omega$. Put $s(\kappa) = \|\mathrm{ev}_{L_P}(\omega(\kappa, 1)v)\|$. It is positive by `norm_zeroTerm_vacElem_pos` and continuous, so the vectors $s(\kappa)^{-1}\omega(\kappa, 1) f$, $\kappa \in \Omega$, form a compact set $K$. By the uniform limit, only finitely many $x$ have $\|\ell(\tau_x u)\| > 1$ for some $u \in K$, and on these $\ell(\omega(a_x\kappa, 1) f)$ is bounded by some $B$. For the other $x$, invariance and `norm_zeroTerm_parabolic_mul` give
$$\|\ell(\omega(g, 1) f)\| \le \|\mathrm{ev}_{L_P}(\omega(a_x\kappa, 1) v)\| = \|\mathrm{ev}_{\sigma(L_P)}(\omega(g, 1) v)\|,$$
with $\sigma$ the bijection of the Lagrangians given by $\gamma$, and one term is at most the sum. $\square$

**Remark (Formalization).** The source states the formula at $g = 1$ only. The formula for $\omega(g, 1) f$ is the formula at $g$. The complete splitting of $S_1$ is chosen with `Lagrangian.chosenSplitting`, and the choice does not change the right side by `zeroTerm_homSource_congr` of Section 2. In the case $S = 0$ the source still asks for a complete splitting $P$ with $p = 0$.

### Constancy in equal rank

The folder also contains a constancy theorem, used where a period of a theta lift between spaces of equal rank must be constant. The proof above does not use it. Let $H$ split one hyperbolic plane off a hermitian space $W$, with complement $W_0$. An automorphic function on $U(W)(\mathbb{A})$ is a continuous function that is left invariant under the rational points, as defined in [the Rallis inner product formula](/chapter/rallis-inner-product/).

**Theorem (Constancy of automorphic functions).** Let $D$ be an automorphic function on $U(W)(\mathbb{A})$, and let $S$ be a nonempty set of finite places. Suppose that:

1. $D$ is right invariant under the finite adelic points supported on $S \cup \bar S$;
2. $D$ is right invariant under the integral finite adelic points that are trivial on $S$;
3. (`h_torus`) if $D$ is left invariant under the unipotent radical elements of $H$, then there is a function $F$ on $U(W_0)(\mathbb{A})$ with $D(H.\mathrm{levi}(t, g)) = F(g)$ for all $t \in \mathrm{GL}_1(\mathbb{A}_E)$ and all $g$.

Then $D(g) = D(1)$ for every $g$.

Lean: `New.Exchange.IsAutFunction.apply_eq_apply_one`, `New.Exchange.exists_torus_mul_rational_fixes`, `New.Exchange.exists_torus_mul_quasiReflection_fixes`, `New.Exchange.IsAutFunction` (Lib/SiegelWeil/Formula/StrongApproximation.lean; Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

*Proof.* By hypothesis 1, continuity and additive strong approximation, $D$ is left invariant under the radicals of all splittings of a plane with complement $W_0$, and hypothesis 3 gives $F$. Witt's theorem and the quasi-reflections give the invariance under the components on $R \cup \bar R$ of a Levi element with a rational block of $W_0$ (`exists_torus_mul_rational_fixes`, `exists_torus_mul_quasiReflection_fixes`). Weak approximation in $W_0$, the Iwasawa decomposition and hypothesis 2 reduce every point to such elements. $\square$

**Remark (Formalization).** The theorem replaces strong approximation for special unitary groups, which the source cites from Kneser, *Starke Approximation in algebraischen Gruppen I*, J. reine angew. Math. 218 (1965). Hypothesis 3 is a condition on $D$ along the torus of the plane. [The register of findings](/chapter/register-of-findings/) lists it as F-084, with the question whether every call site discharges it. In the pinned source, the only call of `apply_eq_apply_one` is in `New/Determinant/Exchange/LargeTriple.lean`, and there the argument for hypothesis 3 is a proof term, not a further hypothesis.
