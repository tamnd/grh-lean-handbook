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

This section proves the Siegel-Weil formula. Sections 2 and 3 gave the convergence of both sides, and Section 4 gave a criterion for the vanishing of their difference. The remaining input is the bound in the cusp that the criterion asks for. It comes from an induction on the rank of $S$: along the torus in the direction of one isotropic line, the formula for $S$ reduces to the formula for the complement of a hyperbolic plane. The last part of the section treats a constancy theorem that the source keeps in the same folder.

### Notation

Let $P$ be a complete splitting of $S$ into $p$ hyperbolic planes, with isotropic frame $k$, and let $\mathrm{rank}\, T = m$ with $2p < m$. For $x \in \mathbb{N}^p$, $a_x$ is the Levi element of $\mathrm{diag}(2^{x_i})$ at the infinite places, and $\tau_x$ is the normalised torus action `normalisedTorus T P x` of Section 3. For a column $\iota$ of $k$, the source chooses with `New.Space.exists_splitting` a splitting $D_1$ of $S$ that splits off the line of $k_\iota$, with complement $S_1$ of rank $2p - 2$.

The limit "as $x_\iota \to \infty$, uniformly for $f$ in $C$" is the limit along the filter on $\mathbb{N}^p \times C$ that is the inverse image of $\mathrm{atTop}$ under $(x, f) \mapsto x_\iota$. All the limits of this section are of this form.

### The torus and the line

**Lemma (The torus on the coordinate of the line).** Let $D_1$ split off the line of the column $\iota$ of $k$. The Levi element $a_x$ scales the row $D_1.\mathrm{lCoord}$, which gives the $l$-coordinate of a vector in $D_1$, by the conjugate of $2^{-x_\iota}$ at the infinite places:
$$D_1.\mathrm{lCoord} \cdot a_x = \overline{(2^{x_\iota})^{-1}}\, D_1.\mathrm{lCoord}.$$

Lean: `New.SiegelWeil.lCoord_mul_levi_dyadicDiag` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* For $P$ itself the Levi law gives $P.\mathrm{lCoord} \cdot a_x = (\mathrm{diag}(2^{x})^{-1})^* P.\mathrm{lCoord}$. Take the entry $\iota$ of this identity. $\square$

The zero term along the line is a mean of Heisenberg translates in the direction of $D_1.\mathrm{lCoord}$. After the torus element, these translations shrink by $2^{-x_\iota}$ at the infinite places. This is the content of the next lemma.

**Lemma (The line term approaches theta).** Let $C$ be a compact set of vectors. As $x_\iota \to \infty$, uniformly for $f \in C$,
$$\int_{[U(T)]} \Big(\theta\big(\omega_1(1, h)\, \mathrm{ev}_{D_1}(\tau_x f)\big) - \theta\big(\omega(1, h)\, \tau_x f\big)\Big)\, dh \to 0,$$
where $\omega_1$ is the Weil representation of $(S_1, T)$ and $\mathrm{ev}_{D_1}$ is the zero term along the line.

Lean: `New.SiegelWeil.tendsto_integral_theta_zeroTerm_sub` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Let $B$ be the integrable majorant of `theta_normalisedTorus_le` of Section 3, so that $\|\theta(\omega(1, h)\tau_x f)\| \le B(h)\|f\|$ for all $x$. Let $\Omega$ be a compact set of adelic vectors whose translates by rational vectors cover all vectors. For a scalar $a$ and $h \in U(T)(\mathbb{A})$, let $\mu(a, h)$ be the largest distance of a translate of $f$ by $a y$ from $f$, for $y \in \Omega$ and $f \in C$. The function $\mu$ is continuous and bounded, and $\mu(0, h) = 0$.

By dominated convergence, $\int B(h)\mu(a, h)\, dh \to 0$ as $a \to 0$. Choose an integer $M \neq 0$ and a size at infinity for which this integral is at most $\varepsilon$, at the scalar that is $M$ at the finite places and $M/2^j$ at the infinite places, for $j$ large.

The zero term along the line is the mean over the periodic variable $q$ of the vector at $q$ in the direction of the line. The mean lies in a closed ball if every value lies in it. Write $q = M b$, and move $b$ into $\Omega$ by a rational vector $c$. Periodicity under rational vectors removes $Mc$. Since $h$ commutes with the zero term and the torus scales $D_1.\mathrm{lCoord}$ by the lemma above, the distance of the value at $q$ from $\theta(\omega(1, h)\tau_x f)$ is the theta value of $\tau_x$ applied to the difference of a translate of $f$ and $f$. The majorant bounds it by $B(h)\mu(a, h)$ with $a$ the scalar above at $j = x_\iota$. Integrate over $h$. $\square$

**Lemma (Terms off the line decay).** Let $m \neq 0$, let $L$ be a Lagrangian of $S$ that does not contain $k_\iota$, and let $C$ be a set of vectors of norm at most $R$. Then $\mathrm{ev}_L(\tau_x f) \to 0$ as $x_\iota \to \infty$, uniformly for $f \in C$.

Lean: `New.SiegelWeil.tendsto_zeroTerm_of_notMem` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Write $L$ as the Lagrangian of a complete splitting $P'$ with frame $k'$ and dual frame $l'$. Since $k_\iota \notin L$, the linear form $v \mapsto l'^* J v$ on $L$ extends to a rational matrix $Y$ with $Y k_\iota = 0$. Then $Y k' = 1$, so $Y$ gives a left inverse of the adelic frame of $P'$. The bound `exists_zeroTerm_normalisedTorus_le` of Section 3, applied with $Z = Y$ times the frame of $P$, gives a constant $c$ with
$$\|\mathrm{ev}_L(\tau_x f)\| \le c\, \|f\|\, \big((2^{d})^{x_\iota}\big)^{-m}$$
where $d$ is the number of infinite places. The reason is that column $\iota$ of $Yk$ is zero, so the exponent $x_\iota$ can be replaced by $0$ in the product $Z\, \mathrm{diag}(2^x)$, and the bound only sees the change of the sum of the exponents. The right side tends to $0$ since $m \neq 0$. $\square$

### The induction step

**Lemma (Lagrangians through the line).** The Lagrangians of $S_1$ are in bijection $\sigma$ with the Lagrangians of $S$ that contain $k_\iota$. The zero term along $\sigma(L)$ is the zero term along $L$ taken after the zero term along the line.

Lean: `New.SiegelWeil.exists_lagrangian_equiv_col_mem`, `New.SiegelWeil.exists_lagrangian_equiv_containing` (Lib/SiegelWeil/Formula/WeilRange.lean; Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is `exists_lagrangian_equiv_containing` of Section 2 for $D_1$. The span of one column lies in $L$ exactly when the column does. $\square$

**Lemma (The induction step).** Let $2p < m$. Suppose that the zero terms of $S$ are summable for every $f$ and that the theta function of $S$ is integrable for every $f$. Suppose that the Siegel-Weil formula holds for $S_1$: for every $f_1$, the theta function of $\omega_1(1, h) f_1$ is integrable and
$$\int_{[U(T)]} \theta\big(\omega_1(1, h) f_1\big)\, dh = \mathrm{vol}([U(T)]) \sum_{L_1} \mathrm{ev}_{L_1}(f_1).$$
Then for every compact set $C$, as $x_\iota \to \infty$ uniformly for $f \in C$,
$$\mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(\tau_x f) - \int_{[U(T)]} \theta\big(\omega(1, h)\tau_x f\big)\, dh \to 0.$$

Lean: `New.SiegelWeil.tendsto_tsum_zeroTerm_sub_integral_theta` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Let $A$ be the set of Lagrangians of $S$ that contain $k_\iota$. Split the sum over $L$ into the sum over $A$ and the sum over the complement. By the bijection and the formula for $S_1$, applied to $f_1 = \mathrm{ev}_{D_1}(g)$, the volume times the sum over $A$ is the integral of the theta function of $\omega_1(1,h)\mathrm{ev}_{D_1}(g)$. So for each $g$ the difference is
$$\int \Big(\theta\big(\omega_1(1, h)\mathrm{ev}_{D_1} g\big) - \theta\big(\omega(1, h) g\big)\Big)\, dh + \mathrm{vol}([U(T)]) \sum_{L \notin A} \mathrm{ev}_L(g).$$
At $g = \tau_x f$, the first term tends to $0$ by the lemma on the line term. The terms of the second sum tend to $0$ one by one, by the lemma on the terms off the line. They are dominated by $b(L) R$, where $b$ is the summable bound of `exists_summable_zeroTerm_bound` and $R$ bounds the norms on $C$. Dominated convergence for sums gives that the second sum tends to $0$. $\square$

### The proof of the formula

**Theorem (Siegel-Weil formula in Weil's range).** Let $P$ be a complete splitting of $S$ into $p$ hyperbolic planes, and let $2p < m$. Then:

1. the operator norms $\|\mathrm{ev}_L\|$ are summable over the Lagrangians $L$ of $S$;
2. for every $f \in \mathcal{S}(\mathrm{Hom}(S, T))$, the function $h \mapsto \theta(\omega(1, h) f)$ is integrable for the quotient measure on $[U(T)]$, and
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(f).$$

Lean: `New.SiegelWeil.siegel_weil`, `New.Exchange.thetaIntegral_pairWeil`, `New.ThetaKernel.theta_rat_mul`, `New.pairThetaKer` (Lib/SiegelWeil/Formula/WeilRange.lean; Lib/Weil/DualPair/ThetaIntegrals.lean; Lib/Weil/DualPair/ThetaLiftConvergence.lean; Lib/Weil/DualPair/WeilAction.lean).

*Proof.* The proof is by strong induction on the rank of $S$, for all $p$ and all complete splittings at once.

*Summability and integrability.* The bound $b$ of `exists_summable_zeroTerm_bound` at $x = 0$, where $\tau_0 = 1$, gives part 1. Integrability is `integrable_theta_splitWeil` of Section 3. By part 1 the sum $\sum_L \mathrm{ev}_L$ converges in operator norm, so its value at $f$ is $\sum_L \mathrm{ev}_L(f)$.

*The difference.* Let
$$\ell(f) = \mathrm{vol}([U(T)]) \sum_L \mathrm{ev}_L(f) - \int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh.$$
The source defines $\ell$ as a continuous functional, with the integral taken as a strong integral of operators. It remains to show $\ell = 0$.

*The case $S = 0$.* Then $p = 0$, there is one Lagrangian, and the theta function is its zero term. The space $\mathrm{Hom}(S, T)$ is zero, so the group of $T$ acts trivially, and the integral of the constant theta value is the volume times that value.

*The limit along the torus.* Let $S \neq 0$, let $C$ be compact and $\iota$ a column of $k$. The column $k_\iota$ is not zero and is isotropic. So `New.Space.exists_splitting` gives $D_1$ and $S_1$ as in the notation. The Lagrangian of $P$ contains $k_\iota$, so it is the image of a Lagrangian $L_1$ of $S_1$, and $S_1$ has the complete splitting chosen for $L_1$. The rank of $S_1$ is smaller, and the number of planes of $S_1$ is $p - 1$, so $2(p-1) < m$. The induction hypothesis gives the formula for $S_1$. The induction step gives $\ell(\tau_x f) \to 0$ as $x_\iota \to \infty$, uniformly for $f \in C$.

*Invariance.* The functional $\ell$ is invariant under $U(T)(\mathbb{A})$. For the integral this is `thetaIntegral_pairWeil`: acting by an element of the group that is integrated over does not change the theta integral. For the zero terms it is `mixedValue_splitWeil` of Section 2. It is invariant under the rational points $\gamma$ of $U(S)$. The theta function is invariant by `theta_rat_mul` of the theta kernel `pairThetaKer`. The sum of the zero terms is invariant because `exists_lagrangian_equiv_containing`, for the splitting `isometrySplitting γ` with no hyperbolic plane, is a bijection of all Lagrangians that turns the zero term along $L$ of $\omega(\gamma) f$ into the zero term along $\sigma(L)$ of $f$.

*The bound in the cusp.* The next lemma turns the limit along the torus and the invariance under the rational points into hypothesis 3 of the vanishing criterion of Section 4. The criterion applies with $\mathrm{rank}\, S = 2p$ and $2p < m$, and gives $\ell = 0$. $\square$

**Lemma (The bound in the cusp).** Let $\ell$ be a continuous functional invariant under the rational points of $U(S)$. Suppose that for every compact $C$ and every $\iota$, $\ell(\tau_x f) \to 0$ as $x_\iota \to \infty$ uniformly for $f \in C$. Suppose that $\sum_L \|\mathrm{ev}_L(f)\|$ converges for every $f$. Then for every $f$ the function
$$g \mapsto \big\|\ell(\omega(g, 1) f)\big\| - \sum_L \big\|\mathrm{ev}_L(\omega(g, 1) v)\big\|$$
is bounded above on $U(S)(\mathbb{A})$, where $v$ is the vacuum.

Lean: `New.SiegelWeil.bddAbove_norm_sub_tsum_norm_zeroTerm` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Let $\Omega$ be the compact set of the Siegel set theorem of Section 3, so every $g$ is $\gamma a_x \kappa$ with $\gamma$ rational, $x \in \mathbb{N}^p$ and $\kappa \in \Omega$. Put $s(\kappa) = \|\mathrm{ev}_{L_P}(\omega(\kappa, 1)v)\|$, where $L_P$ is the Lagrangian of $P$. It is positive by `norm_zeroTerm_vacElem_pos` and continuous. So the set $K$ of the vectors $s(\kappa)^{-1}\omega(\kappa, 1) f$ for $\kappa \in \Omega$ is compact.

Let the bad set be the set of $x$ with $\|\ell(\tau_x u)\| > 1$ for some $u \in K$. By the uniform limit, for each $\iota$ only finitely many values of $x_\iota$ occur in it. So the bad set is finite, and $\ell(\omega(g, 1) f)$ is bounded by some $B > 0$ on the compact set $\{a_x \kappa\}$ of its points.

Let $g = \gamma a_x \kappa$. By invariance, $\ell(\omega(g, 1)f) = \ell(\omega(a_x\kappa, 1) f)$. If $x$ is bad, the bound $B$ applies. If $x$ is good, $\|\ell(\tau_x(s(\kappa)^{-1}\omega(\kappa,1)f))\| \le 1$. The factor of the normalised torus is the factor by which $a_x$ scales the zero term along $L_P$, by `norm_zeroTerm_parabolic_mul`. So
$$\|\ell(\omega(a_x\kappa, 1) f)\| \le \|\mathrm{ev}_{L_P}(\omega(a_x\kappa, 1) v)\| = \|\mathrm{ev}_{\sigma(L_P)}(\omega(g, 1) v)\|,$$
where $\sigma$ is the bijection of the Lagrangians given by $\gamma$. One term is at most the sum of all terms. In both cases the difference is at most $B$. $\square$

**Remark (Formalization).** The source proves the formula at the point $1$ of $U(S)(\mathbb{A})$ and for every $f$, and it does not state the formula at other points. Since $\omega(g, 1) f$ is again a vector, the formula at $\omega(g, 1) f$ is the formula at $g$. The induction runs over all complete splittings of all spaces of smaller rank, so the source chooses the complete splitting of $S_1$ with `Lagrangian.chosenSplitting`. The choice does not change the right side, since the zero terms do not depend on the splitting by `zeroTerm_homSource_congr` of Section 2. In the case $S = 0$ the source still asks for a complete splitting $P$ with $p = 0$.

### Constancy in equal rank

The folder of the formula also contains a constancy theorem for automorphic functions. The source uses it where the period of a theta lift between spaces of equal rank must be a constant. It is not used in the proof above.

Let $W$ be a hermitian space and $H$ a splitting of one hyperbolic plane off $W$, with complement $W_0$. A function $D$ on $U(W)(\mathbb{A})$ is an automorphic function, `New.Exchange.IsAutFunction W D`, if it is continuous and left invariant under the rational points. The singular forms of [the Rallis inner product formula](/chapter/rallis-inner-product/) use the same predicate.

**Theorem (Constancy of automorphic functions).** Let $D$ be an automorphic function on $U(W)(\mathbb{A})$, and let $S$ be a nonempty set of finite places. Suppose that:

1. $D$ is right invariant under the finite adelic points supported on $S \cup \bar S$;
2. $D$ is right invariant under the integral finite adelic points that are trivial on $S$;
3. (`h_torus`) if $D$ is left invariant under the unipotent radical elements of $H$, then there is a function $F$ on $U(W_0)(\mathbb{A})$ with $D(H.\mathrm{levi}(t, g)) = F(g)$ for all $t \in \mathrm{GL}_1(\mathbb{A}_E)$ and all $g$.

Then $D(g) = D(1)$ for every $g$.

Lean: `New.Exchange.IsAutFunction.apply_eq_apply_one`, `New.Exchange.exists_torus_mul_rational_fixes`, `New.Exchange.exists_torus_mul_quasiReflection_fixes`, `New.Exchange.IsAutFunction` (Lib/SiegelWeil/Formula/StrongApproximation.lean; Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

*Proof.* Hypothesis 1 means that $D$ takes the same value at points that agree off $S \cup \bar S$. In the radical of any splitting of a hyperbolic plane with complement $W_0$, the parameters that are rational plus a part supported on $S \cup \bar S$ are dense, and off $S \cup \bar S$ such a point is rational. With continuity and the left invariance, $D$ is left invariant under the radicals of all these splittings. This is additive strong approximation. Hypothesis 3 then gives $F$. Witt's theorem and the quasi-reflections give, for a finite set $R$ of places, the invariance under the components on $R \cup \bar R$ of a Levi element with a rational block of $W_0$ (`exists_torus_mul_rational_fixes`, `exists_torus_mul_quasiReflection_fixes`). Weak approximation in $W_0$ makes the rational points dense up to points that are trivial on $R$. With the Iwasawa decomposition and hypothesis 2, every point reduces to such Levi elements. $\square$

**Remark (Formalization).** The theorem is a weak substitute for strong approximation for special unitary groups, which the source cites from Kneser, *Starke Approximation in algebraischen Gruppen I*, J. reine angew. Math. 218 (1965). The source concludes only the constancy of $D$, and only with hypothesis 3. That hypothesis is a condition on $D$ along the torus of the plane. The register of findings lists it as F-084 in [the register of findings](/chapter/register-of-findings/), with the question whether every call site discharges it. In the pinned source, the only call of `apply_eq_apply_one` is in `New/Determinant/Exchange/LargeTriple.lean`, and there the argument for hypothesis 3 is a proof term, not a further hypothesis. The Siegel-Weil formula `siegel_weil` does not have this hypothesis.
