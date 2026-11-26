---
title: The unfolding in stages
lean:
  - New/UpperBound/Seesaw/UnfoldingStages.lean
decls:
  - New.Data.isEquivariant_unfoldStageOn
  - New.Data.fixesLeft_ratBessel_unfoldStage
  - New.Data.integral_unfoldStageOn
  - New.Seesaw.DoubleLiftData.constTerm_mul_constTerm_eq_inv_mul_zeroTerm
  - New.Seesaw.formAdjoint_stackedStringMap_mul_stackedStringMap
  - New.Seesaw.DoubleLiftData.zeroTerm_stackedStringMap_planes
  - New.Seesaw.DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq
  - New.Seesaw.integral_theta_tripleWeil_eq_lift_comp
  - New.Data.exists_zeroTerm_eq_integrated
  - New.Data.exists_unfoldStage_eq_algFormCoeff_of_sourceFn
  - New.Data.exists_unfoldStageOn_even_eq_sourceFn
  - New.Data.exists_unfoldStage_eq_algFormCoeff
  - New.Data.map_evaluatedDatum_of_conj_mem
  - New.Data.evaluatedDatum_out
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The unfolding in stages

Section 1 defined the functions $\mathcal{W}_k$ of the unfolding. This section proves the identity of one stage, and then evaluates $\mathcal{W}_{2i+2}$ after each pair of lifts: on the image of the definite group it is a coefficient of the composite of the first $i + 1$ pairs of theta lifts between the definite spaces $X_j$. The step from one pair to the next uses the double lift data and the equivariant evaluation of Section 4.

### The identity of one stage

**Proposition (The stage functions are equivariant).** The function $\mathcal{W}_k$ on the Bessel group $R_k$ of $\mathsf{Y}_k$ is invariant under the rational points and equivariant for the unipotent character. The function $\mathcal{W}_{k+1}$ on $U(Y_{k+1})$ is continuous and left invariant under the rational points of the Bessel group of $\mathsf{Y}'$.

Lean: `New.Data.isEquivariant_unfoldStageOn`, `New.Data.continuous_unfoldStage`, `New.Data.fixesLeft_ratBessel_unfoldStage`.

*Proof.* For $k = 0$, $\mathcal{W}_0$ is the source function of $\varphi$, which is equivariant by construction (Lean: `New.Grading.sourceFn`). For $k + 1$, $\mathcal{W}_{k+1}$ is the unfolded function of $\mathcal{W}_k$, which is continuous and invariant under the rational Bessel points by [one step of unfolding](/chapter/bessel-periods/). The equivariance of its translate on $R_{k+1}$ follows from the same file. $\square$

**Theorem (The stage identity).** Let $k \leq 2\varrho + 1$, let $\mathsf{Y}'$ grade $Y_{k+1}$ with a string of length $2\varrho - k$, and let $z$ be automorphic and rapidly decreasing on $U(Y_{k+1})$. Then $\mathcal{W}_{k+1} z$ is integrable on $[R']$, the quotient by the rational points of the Bessel group of $\mathsf{Y}'$, and

$$\int_{[R_k]} \mathcal{W}_k(r) \int_{[U(Y_{k+1})]} \theta\big(\omega(r g_k, h)\,\varphi_{k+1}\big)\, z(h)\, dh\, dr = \int_{[R']} \mathcal{W}_{k+1}(h)\, z(h)\, dh,$$

where $g_k = (\xi_k, y_k)$, $\varphi_{k+1}$ is the datum of lift $k + 1$ of the lower chain, and $\omega$ is the Weil action normalised by the chain character of lift $k + 1$.

Lean: `New.Data.integral_unfoldStageOn`.

*Proof.* Move $g_k$ into the datum (Lean: `New.Data.twistedPairWeil_movedDatum`): the left side is the integral of $\mathcal{W}_k$ against the lift of $z$ with the moved datum $\omega(g_k, 1)\varphi_{k+1}$. The one-step unfolding theorem of [Bessel periods](/chapter/bessel-periods/) (Lean: `New.Grading.integral_besselGroup_unfold`), applied with the equivariant function $\mathcal{W}_k$, turns it into the integral over $[R']$ of the unfolded function times $z$. By definition this unfolded function is $\mathcal{W}_{k+1}$. $\square$

### Two steps at once

For a pair $\mathsf{Y} \to \mathsf{Y}' \to \mathsf{Y}''$ with double lift data $D$, the two constant terms at the two shifts combine into one zero term on $\mathrm{Hom}(V', V^- \oplus V'')$. Write $\mathrm{CT}(f, w)$ for the constant term of $f$ at a map $w$, and $f \boxtimes f'$ for the joined datum. Suppose that $\theta(f \boxtimes f') = \zeta\, \theta(f)\theta(f')$ for a constant $\zeta \neq 0$ and all $f$, $f'$.

**Lemma (Products of constant terms).**

1. $\mathrm{CT}(f, w)\,\mathrm{CT}(f', w') = \zeta^{-1}\, Z_D\big(\varrho(w) f \boxtimes \varrho(w') f'\big)(0)$, where $Z_D$ is the zero term along the splitting to the part of degree $0$.
2. The stacked map $S = (\mathrm{sh}^*, \mathrm{sh}')$ is isotropic: $S^* S = -\mathrm{sh}\,\mathrm{sh}^* + \mathrm{sh}'^*\mathrm{sh}' = 0$.
3. For a unipotent $n$ of $U(V')$, $\zeta^{-1} Z_D(\varrho(S)(f \boxtimes f'))$ at the map $c\,(n - 1)_{\mathrm{gr}\,1, X'}$ into the planes equals $\mathrm{CT}(f, n^{-1}\mathrm{sh})\,\mathrm{CT}(f', \mathrm{sh}'\,n)$.

Lean: `New.Seesaw.DoubleLiftData.constTerm_mul_constTerm_eq_inv_mul_zeroTerm`, `New.Seesaw.formAdjoint_stackedStringMap_mul_stackedStringMap`, `New.Seesaw.DoubleLiftData.zeroTerm_stackedStringMap_planes`.

*Proof.* (1) Both constant terms are means over maps of positive degree, and the maps of positive degree of $\mathrm{Hom}(V', V^- \oplus V'')$ are the pairs of such maps. The theta value of the joined datum is $\zeta$ times the product. (2) Both products depend only on $\mathsf{Y}'$ and on the common constant $c$ of $\mathsf{Y}$ and $\mathsf{Y}'$, and the sign of $V^-$ makes them cancel. (3) The map $S(n - 1)$ is the sum of a map of positive degree and of the map $c\,(n-1)$ from $X'$ into an isotropic half of the planes (Lean: `New.Seesaw.DoubleLiftData.exists_add_eq_homAtPoint_stackedStringMap`). The first part is absorbed by the mean, and (1) applies with $w = n^{-1}\mathrm{sh}$, $w' = \mathrm{sh}'\,n$. $\square$

**Theorem (The double unfolding).** Let $D$ be double lift data. There is a constant $\zeta_D$ with the following property. Let $a$, $b$ be characters of $[U(1)]$, $f$, $f'$ data on $\mathrm{Hom}(V, V')$ and $\mathrm{Hom}(V', V'')$, $k \in U(X_0)$, and $W$ an equivariant function on the Bessel group of $\mathsf{Y}$. Then

$$\int_{[R']}\int_{[R]} W(g)\,\mathrm{CT}_{\mathrm{sh}}(f)(g, r)\,\mathrm{CT}_{\mathrm{sh}'}(f')(r, \iota'' k)\, dg\, dr = \int_{[U(X)]} W(\iota g)\, \zeta_D \int_{[U(X')]} \theta\Big(\mathrm{tw}_{a,b}(g, r, \epsilon(k))\, D.\mathrm{zeroTerm}\big(\varrho(S)(f \boxtimes f')\big)\Big)\, dr\, dg.$$

Lean: `New.Seesaw.DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq`.

*Proof.* Each Bessel group is the product of the unitary group of the definite part and the unipotent group. Integrate first over the unipotent groups. Over the unipotent group of $\mathsf{Y}$, the character of $W$ cancels that of the kernel, since $s$ is odd (Lean: `New.Seesaw.mul_constTermAtStringMap_unipotent_mul`). Over the unipotent group of $\mathsf{Y}'$, a unipotent $n$ moves into the points of the two constant terms (Lean: `New.Seesaw.constTermAtStringMap_unipotent_mul_left`, `New.Seesaw.constTermAtStringMap_unipotent_mul_right`), so by part 3 of the lemma the integrand is a zero term evaluated along the row $(n-1)_{\mathrm{gr}\,1, X'}$. The mean over these rows is the zero term off the planes, which composes with $Z_D$ to the zero term along the splitting of $D$. The two means give constants $\kappa$, $\kappa'$, and $\zeta_D = \zeta^{-1}\kappa\kappa'$, up to the normalisations of the measures. $\square$

**Remark (Formalization).** The theorem gives $\zeta_D$ by an existence statement and does not show $\zeta_D \neq 0$. The users do not need it: the constant goes into the linear form $l$ of the next theorems and then into the constant $c$ of the theorem of Section 1, which is allowed to be $0$.

On the definite spaces the integral of the theta kernel is a composite of two lifts.

**Proposition (Two definite lifts).** Let $k$, $k'$ compute the theta lifts of algebraic forms from $X$ to $X'$ and from $X'$ to $X''$, with characters twisted by the rank, and let $L$ be the composite $\Phi \otimes \Phi' \mapsto k'_{\Phi'} \circ k_{\Phi}$. For each Fock vector $u$ and linear form $t$ there is a linear form $t''$ such that, for all finite data $y$, forms $\varphi$ and $g \in U(X'')$,

$$\int_{[U(X)]} c_t(\varphi)(x) \int_{[U(X')]} \theta\big(\mathrm{tw}(x, r, g)\,(u \otimes y)\big)\, dr\, dx = c_{t''}\big(L(y)\varphi\big)(g),$$

where $c_t(\varphi)$ is the coefficient of $\varphi$ at $t$.

Lean: `New.Seesaw.integral_theta_tripleWeil_eq_lift_comp`.

*Proof.* By linearity in $u$ it suffices to take $u = P Q \otimes (\Phi \boxtimes \Phi')$ for polynomials $P$, $Q$ in the two blocks (Lean: `New.Seesaw.arrowProduct_integrated_polyVector`). Then the theta kernel of the triple is the product of the two theta kernels, and the integrand is integrable on the compact quotients (Lean: `New.Seesaw.integrable_algFormCoeff_mul_theta_tripleWeil`). Fubini gives the lift from $X$ to $X'$ inside and then the lift from $X'$ to $X''$. $\square$

### The evaluation after each pair

Now apply this to the tower. Let $R$ be double lift data for $Y_{2i} \to Y_{2i+1} \to Y_{2i+2}$, with a grading $\mathsf{Y}$ of $Y_{2i+2}$, and suppose that the evaluation of pair $i$ of Section 4 is the finite evaluation of $R$. Let $\Theta_i$ be the composite of the first $i$ pairs of theta lifts between the definite spaces, with the kernels of the tame character $\vartheta$ and the evaluated data (Lean: `New.doubleLiftChain`).

**Theorem (Evaluation after each pair).** Fix $t$, the archimedean points $\xi_k$ and a point $x$ of $U(Y_{2i+2})_\infty$.

1. The zero term along the splitting of $R$ of the joined, moved data of lifts $2i + 1$ and $2i + 2$, translated by $S$, is $v \otimes \mathrm{ev}_i(\vartheta, y)$ for a Fock vector $v$ that does not depend on $\vartheta$ or $y$.
2. For each $i$ with $2i \leq 2\varrho + 1$ there is a linear form $l$, independent of $\vartheta$, $\varphi$ and $y$, such that $\mathcal{W}_{2i}$ on $R_{2i}$ is the source function of $\Theta_i\varphi$ at $l$.
3. There is a linear form $l$, independent of $\vartheta$, $\varphi$ and $y$, such that for $g \in U(X)$,

$$\mathcal{W}_{2i+2}\big(\iota g\cdot(x, y_{2i+2})\big) = c_l\big(\Theta_{i+1}\varphi\big)(\epsilon_R(g)).$$

Lean: `New.Data.exists_zeroTerm_eq_integrated`, `New.Data.exists_unfoldStageOn_even_eq_sourceFn`, `New.Data.exists_unfoldStage_eq_algFormCoeff`, `New.Data.exists_unfoldStage_eq_algFormCoeff_of_sourceFn`.

*Proof.* (1) The real parts of the data are tensored with the finite parts, and the zero term and the translation act on each factor separately (Section 4, the [finite zero term](/decl/New.Seesaw.zeroTermFin/)). The real factor depends only on $\xi$ and $x$. The finite factor is the finite evaluation of the moved finite data, which is $\mathrm{ev}_i(\vartheta, y)$.

(2) and (3) by induction on $i$. For $i = 0$, $\mathcal{W}_0$ is the source function of $\varphi$ and $\Theta_0 = \mathrm{id}$. Suppose (2) for $i$, so $\mathcal{W}_{2i}$ is the source function of $\psi = \Theta_i\varphi$ at $l$. The value $\mathcal{W}_{2i+2}(\iota g\cdot(x, y_{2i+2}))$ is, by two applications of the definition of $\mathcal{W}$, the double integral of the double unfolding theorem with $W = \mathcal{W}_{2i}$. By that theorem and part (1) it is an integral of the theta kernel of the definite spaces against the coefficient of $\psi$, and by the proposition on two definite lifts it is $c_{l''}(L(\mathrm{ev}_i)\psi)(\epsilon_R(g))$, which is (3) since $L(\mathrm{ev}_i)\Theta_i = \Theta_{i+1}$. For (2) at $i + 1$: $\mathcal{W}_{2i+2}$ on $R_{2i+2}$ is equivariant, so it is determined by its values on the image of $U(X_{2i+2})$, and these are the coefficients just computed. $\square$

The evaluated data depend on $y$ only through classes modulo the levels.

**Proposition (Invariance of the evaluated data).**

1. Let $u \in U(X_{2i+2})_{\mathrm f}$ with $y_{2i+2}^{-1}\,\iota(u)\, y_{2i+2}$ in the level $J_{2i+2}(\vartheta)$. Then $(1, u)$ fixes $\mathrm{ev}_i(\vartheta, y)$ in the second factor.
2. $\mathrm{ev}_i(\vartheta, y)$ does not change if each $y_k$ is replaced by the chosen representative of its class modulo $J_k(\vartheta)$.

Lean: `New.Data.map_evaluatedDatum_of_conj_mem`, `New.Data.evaluatedDatum_out`.

*Proof.* (1) The evaluation commutes with $\iota$ (Lean: `New.Data.doubleLiftEvalY_inclXFin`), and the datum of lift $2i + 2$ moved by $y_{2i+2}$ is fixed by $(1, z)$ whenever $y_{2i+2}^{-1} z\, y_{2i+2}$ lies in the level (Lean: `New.Data.liftWeilFin_translatedPointDatumY`). (2) The elements of the levels fix the data of the lifts (Lean: `New.Data.liftWeilFin_pointDatumY`), so the moved data depend only on the classes. $\square$

**Remark (Formalization).** Part 2 uses `Quotient.out`, a choice of representatives. The proposition says that the choice does not matter, which is what allows Section 7 to sum over classes.
