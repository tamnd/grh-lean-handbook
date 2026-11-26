---
title: Schur bounds and orthonormality
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/SchurBound.lean
  - New/Spanning/Bessel/Orthonormality.lean
decls:
  - New.SchurLe
  - New.RealPlace.HasSchurBound
  - New.isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame
  - New.norm_frame_conj_single
  - New.exists_mem_filtration_smear_word
  - New.convolve_formalDegree_mul_dsCoeffInFrame_self
  - New.convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv
  - New.HCParam.HasLargeGap.norm_sq_eq_formalDegree_mul_integral
  - New.exists_derivative_kernels
  - New.IsBesselFunction.lintegral_enorm_sq_integral_inner_translate
  - New.IsBesselFunction.convolve_of_integrable
  - New.IsBesselFunction.hasSchurBound_of_convolve_eq
  - New.IsBesselFunction.integral_mul_conj_embedH_mul
  - New.IsBesselFunction.integral_mul_conj_eq
  - New.BesselSystem.orthonormal
  - New.IsCutPair.integrable_cut
  - New.IsCutPair.exists_integral_cut_mul_conj_eq
  - New.IsCutPair.lintegral_sq_inner_cut_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Schur bounds and orthonormality

This section proves two kinds of $L^2$ bounds for a Bessel function $F$ that is fixed by the idempotent $e_\lambda = d_\lambda c_\lambda$ of the discrete series. The first kind is the *Schur bound*: $F$ has right derivatives of all orders, and the convolution of each derivative of low order with an integrable function $\varphi$ has an $L^2(\mathsf U\backslash G_1)$ norm controlled by $\|\varphi\|_2$. The second kind is *orthonormality*: if the type $\rho$ of $F$ is irreducible, the matrix $\int F \otimes \overline F$ over $\mathsf U\backslash G_1$ is a scalar. The [open cell bound](/chapter/bessel-real-place/#the-open-cell-bound) uses the Schur bound, and the users of a Bessel system use orthonormality.

Both are forms of Schur's orthogonality relations for the discrete series. The source names Harish-Chandra for the smoothness of the vectors of a discrete series and for these relations. The general versions on a group with a measure are in [the chapter on Bessel subgroups and the big cell](/chapter/bessel-bruhat/#bessel-functions-and-the-schur-bound): [Proposition](/decl/New.IsBoundedMeasurable.integral_inner_translate/) computes $\int\langle F(ya), F(yb)\rangle$, and [Theorem](/decl/New.IsBoundedMeasurable.lintegral_sq_convolve_convolve_le/) bounds $\int|(F * x) * \check z|^2$. This section supplies the kernels $x$ and checks the hypotheses.

Throughout, $l = 2\lambda$ is a doubled Harish-Chandra parameter for the signs $\varepsilon$ with the gap $500r^3 + A$ ([`New.HCParam.HasLargeGap`](/chapter/discrete-series/)) and with $|l_a| \leq L$ for all $a$. The function $c_\lambda$ on $G_1$ is the pullback of the coefficient on $U(\operatorname{diag}\varepsilon)$ by the unitary frame $P$, and $d_\lambda > 0$ is the formal degree. Convolution is $(F * k)(y) = \int_{G_1} k(a^{-1})F(ya)\,da$ ([`New.convolve`](/decl/New.convolve/)).

### The two definitions

**Definition (Schur inequality).** Let $W : G_1 \to \mathbb{C}^I$ and $D \in [0, \infty]$. Then $W$ satisfies the *Schur inequality with constant $D$* if for every integrable $\varphi : G_1 \to \mathbb{C}$
$$\int_{\mathsf U\backslash G_1}\Bigl\|\int_{G_1}\varphi(y)\,W(\gamma y)\,dy\Bigr\|^2 d\gamma \leq D\int_{G_1}|\varphi|^2.$$

Lean: `New.SchurLe` (New/Spanning/Bessel/Basic.lean).

**Definition (Schur bound).** Let $W : G_1 \to \mathbb{C}^I$, let $\rho$ be a unitary representation of $H = U(k)$ on $\mathbb{C}^I$, let $B \in \mathbb{R}$ and $D \in [0, \infty]$. Then $W$ has the *Schur bound* $(B, D)$ if there is a family $V_w$ of continuous functions, indexed by the words $w$ in pairs $(a, b)$ of indices of $G_1$, with $V_{[\,]} = W$, such that for every word $w$:

1. $V_w$ is a Bessel function of type $\rho$;
2. for every curve $\gamma$ in $G_1$ with $\gamma'(t) = \gamma(t)X$ at a point $t$,
$$(V_w \circ \gamma)'(t) = \sum_{a, b} X_{ab}\,V_{(a, b) :: w}(\gamma(t));$$
3. if $|w| \leq 2n^2$, then $V_w$ satisfies the Schur inequality with the constant $B^{2|w|}D$.

Lean: `New.RealPlace.HasSchurBound` (New/Spanning/Bessel/Basic.lean).

Item 2 says that $V_{(a, b) :: w}$ is the right derivative of $V_w$ along the matrix unit $E_{ab}$. So $V_w$ is the iterated right derivative of $W$ along the letters of $w$, the first letter of the word applied last. Each letter costs the factor $B^2$ in the constant.

**Remark (Formalization).** In `SchurLe` the inner integral is a Bochner integral, which has the junk value $0$ when its integrand is not integrable. For a bounded $W$ and an integrable $\varphi$ the integrand is integrable, so the junk value does not occur for Bessel functions. The integral of $|\varphi|^2$ is over $G_1$ for its Haar measure and may be $\infty$; then the inequality holds and says nothing. The family $V$ is part of an existence statement, so the derivatives of high order are not unique objects of the source. Item 2 differentiates the matrix entries of $\gamma(s)$, not a curve in an abstract Lie group, and item 3 has no content for $|w| > 2n^2$.

### The kernel and the frame

**Lemma.** Let $l$ have the gap $500r^3 + A$. Then:

1. $e_\lambda = d_\lambda c_\lambda$ is bounded and measurable on $G_1$;
2. $e_\lambda * e_\lambda = e_\lambda$ on $G_1$;
3. for every matrix unit $E_{ij}$, the matrix $P^{-1}E_{ij}P$ has operator norm $1$.

Lean: `New.isBoundedMeasurable_formalDegree_mul_dsCoeffInFrame`, `New.convolve_formalDegree_mul_dsCoeffInFrame_self`, `New.norm_frame_conj_single` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* (1) The coefficient is continuous and $|c_\lambda| \leq 1$ ([`New.DiscreteSeries.norm_dsCoeff_le_one`](/decl/New.DiscreteSeries.norm_dsCoeff_le_one/)). (2) The function $e_\lambda$ is an [idempotent kernel](/decl/New.IsIdempotentKernel/) on $G_1$ (`New.isIdempotentKernel_dsCoeffInFrame`, Lib/Weil/Periods/Grading.lean). An idempotent kernel satisfies $\int e(a^{-1})e(ya) = e(y)e(1)/e(1)$, and this is $e * e = e$. (3) $P$ is unitary, and multiplication by a unitary matrix on either side does not change the operator norm. The norm of $E_{ij}$ is $1$. $\square$

**Lemma (Change of group).** Let $\beta$ be a bump function on $U(\operatorname{diag}\varepsilon)$: a smooth function of compact support. Let $\pi : G_1 \to U(\operatorname{diag}\varepsilon)$ be conjugation by the frame. Then
$$e_\lambda * (\beta \circ \pi) = d_\lambda\,(c_\lambda \star \beta) \circ \pi,$$
where $c_\lambda \star \beta$ is the smearing of $c_\lambda$ by $\beta$ on $U(\operatorname{diag}\varepsilon)$ (`New.DiscreteSeries.smear`, Lib/DiscreteSeries/FlenstedJensen/RightDerivatives.lean).

Lean: `New.convolve_formalDegree_mul_dsCoeffInFrame_comp_frameEquiv` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* $\pi$ is a group isomorphism that carries the Haar measure of $G_1$ to that of $U(\operatorname{diag}\varepsilon)$ (`New.DiscreteSeries.integral_comp_frameEquiv`). Pull $d_\lambda$ out of the integral and substitute. $\square$

**Lemma (Norm in the module).** For $x$ in the module $M_\lambda = U(\mathfrak g)c_\lambda$ of [the chapter on the discrete series](/chapter/discrete-series/),
$$\|x\|^2 = d_\lambda\int_{U(\operatorname{diag}\varepsilon)}|x(g)|^2\,dg.$$

Lean: `New.HCParam.HasLargeGap.norm_sq_eq_formalDegree_mul_integral` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* The norm of $M_\lambda$ is by definition the norm of the image $\sqrt{d_\lambda}\,x$ in $L^2$ (`New.HCParam.HasLargeGap.toL2`). Take the real part of the inner product formula for this image at the translate $1$. $\square$

### Derivatives of a function fixed by the idempotent

**Lemma (A word in the filtration).** Let $\beta$ be a bump with $c_\lambda \star \beta = c_\lambda$. Let $w$ be a word of length $s$, and let $\beta_w$ be the derivative of $\beta$ along the letters of $w$, each letter $(a, b)$ acting by $P^{-1}E_{ab}P$. Then $c_\lambda \star \beta_w = x$ for a vector $x$ in step $s$ of the filtration of $M_\lambda$ with
$$\|x\| \leq \bigl((r + 1)^4(L + r + 1 + s)\bigr)^s.$$

Lean: `New.exists_mem_filtration_smear_word` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* Induction on $w$. For the empty word $x = c_\lambda$, the generator, of norm $1$. For the step from $w$ to $q :: w$, let $x$ be the vector of $w$ and $M = P^{-1}E_qP$. Smearing commutes with right derivatives (`New.DiscreteSeries.rightDeriv_smear`), so the new vector is $Mx$, in step $s + 1$. The generator is $K$-highest ([`New.isKHighest_dsGenerator`](/decl/New.isKHighest_dsGenerator/)) of weight $\Lambda$, and $|\Lambda_a| \leq L + r$ (`New.abs_lowestKType_le`, Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The filtration bound `New.HCParam.IsKHighest.norm_apply_le_of_mem_filtration` (Lib/DiscreteSeries/Rigidity/HighestVectorsAndFiltration.lean) gives
$$\|Mx\| \leq (r + 1)^4(L + r + 1 + s)\,\|M\|\,\|x\|,$$
and $\|M\| = 1$ by the lemma on the frame. The factor for step $s$ is at most the factor for step $s + 1$, so the product of the $s + 1$ factors is at most $((r + 1)^4(L + r + 1 + s + 1))^{s+1}$. $\square$

The filtration bound is the place where the gap enters. It uses the Casimir lower bound of the unitary module $M_\lambda$, which [the chapter on the discrete series](/chapter/discrete-series/) proves under the gap condition.

**Theorem (Derivative kernels).** There are functions $X_w$ on $G_1$, one for each word $w$, with:

1. $X_{[\,]} = e_\lambda$;
2. each $X_w$ is integrable, and $e_\lambda * X_w = X_w$;
3. $d_\lambda^{-1}\int_{G_1}|X_w|^2 \leq \bigl((r + 1)^4(L + r + 1 + |w|)\bigr)^{2|w|}$;
4. if $F : G_1 \to \mathbb{C}^I$ is bounded and measurable with $F * e_\lambda = F$, then along a curve $\gamma$ with $\gamma'(t) = \gamma(t)Z$,
$$\bigl((F * X_w) \circ \gamma\bigr)'(t) = \sum_{a, b} Z_{ab}\,(F * X_{(a, b) :: w})(\gamma(t)).$$

Lean: `New.exists_derivative_kernels` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* Choose a bump $\beta$ with $c_\lambda \star \beta = c_\lambda$ (`New.exists_smear_dsCoeffSmooth_eq`, Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean). Put $X_w = d_\lambda(c_\lambda \star \beta_w) \circ \pi$. By the change of group, $X_w = e_\lambda * (\beta_w \circ \pi)$.

(1) $c_\lambda \star \beta = c_\lambda$. (2) $X_w$ is the convolution of two integrable functions. Associativity for the bounded function $e_\lambda$ and the idempotence of $e_\lambda$ give $e_\lambda * X_w = (e_\lambda * e_\lambda) * (\beta_w \circ \pi) = X_w$. (3) Let $x$ be the vector of the lemma on words. By the norm in the module and the change of variables by $\pi$,
$$\|x\|^2 = d_\lambda\int|x|^2 = d_\lambda^{-1}\int_{G_1}|X_w|^2.$$
Square the bound of the lemma. (4) $F * X_w = (F * e_\lambda) * (\beta_w \circ \pi) = F * (\beta_w \circ \pi)$. So $F$ is continuous, and $F * X_w$ is the smearing of $F \circ \pi^{-1}$ by $\beta_w$, read through $\pi$. A smearing is differentiable along right translations, and its derivative along $Y$ is the smearing by the derivative of the bump along $Y$ (`New.DiscreteSeries.hasDerivAt_smear`). The curve $\pi\gamma$ has $(\pi\gamma)' = \pi\gamma \cdot P^{-1}ZP$. Expand $Z = \sum Z_{ab}E_{ab}$; the term of $E_{ab}$ is the smearing by $\beta_{(a, b) :: w}$. $\square$

**Lemma.** Let $F$ be a Bessel function of type $\rho$ and $k$ an integrable function on $G_1$. Then $F * k$ is a Bessel function of type $\rho$.

Lean: `New.IsBesselFunction.convolve_of_integrable` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* Convolution on the right commutes with left translations, with scalars and with the linear maps $\rho(h)$. The convolution of a bounded measurable function with an integrable one is bounded and measurable. $\square$

### The Schur bound

**Theorem (Schur bound for a Bessel function).** Let $F$ be a Bessel function of type $\rho$, integrable on $\mathsf U\backslash G_1$, with $F * e_\lambda = F$. Let
$$B \geq (r + 1)^4(L + r + 1 + 2n^2).$$
Then $F$ has the Schur bound $\bigl(B,\ d_\lambda^{-1}\int_{\mathsf U\backslash G_1}\|F\|^2\bigr)$.

Lean: `New.IsBesselFunction.hasSchurBound_of_convolve_eq` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* Take $X_w$ from the theorem on derivative kernels and put $V_w = F * X_w$. Then $V_{[\,]} = F * e_\lambda = F$. Each $V_w$ is continuous and, by the last lemma, a Bessel function. Item 2 of the definition is item 4 of the theorem. For item 3, let $|w| \leq 2n^2$ and let $\varphi$ be integrable. With $\check\varphi(a) = \varphi(a^{-1})$,
$$\int_{G_1}\varphi(y)\,V_w(\gamma y)\,dy = (V_w * \check\varphi)(\gamma) = \bigl((F * X_w) * \check\varphi\bigr)(\gamma).$$
Apply [Theorem](/decl/New.IsBoundedMeasurable.lintegral_sq_convolve_convolve_le/) with $\psi = e_\lambda$, $d = e_\lambda(1) = d_\lambda$, $x = X_w$ and $z = \varphi$. The hypotheses are $e_\lambda * X_w = X_w$ and $F * e_\lambda = F$. The result is
$$\int_{\mathsf U\backslash G_1}|V_w * \check\varphi|^2 \leq \frac{\int|X_w|^2}{d_\lambda}\cdot\frac{1}{d_\lambda}\int_{\mathsf U\backslash G_1}\|F\|^2\cdot\int_{G_1}|\varphi|^2.$$
By item 3 of the theorem on kernels and $|w| \leq 2n^2$, the first factor is at most $((r + 1)^4(L + r + 1 + 2n^2))^{2|w|} \leq B^{2|w|}$. $\square$

**Theorem (Square norm of the matrix coefficient).** Under the hypotheses of the Schur bound, except the one on $B$,
$$\int_{G_1}\Bigl|\int_{\mathsf U\backslash G_1}\langle F(y), F(yg)\rangle\,dy\Bigr|^2 dg = d_\lambda^{-1}\Bigl(\int_{\mathsf U\backslash G_1}\|F\|^2\Bigr)^2.$$

Lean: `New.IsBesselFunction.lintegral_enorm_sq_integral_inner_translate` (New/Spanning/Bessel/SchurBound.lean).

*Proof.* [Proposition](/decl/New.IsBoundedMeasurable.integral_inner_translate/) with $\psi = e_\lambda$, $a = 1$ and $b = g$ gives $\int\langle F(y), F(yg)\rangle = c_\lambda(g)\int\|F\|^2$. So the left side is $\int_{G_1}|c_\lambda|^2 \cdot (\int\|F\|^2)^2$. By definition of the formal degree, $\int_{G_1}|c_\lambda|^2 = d_\lambda^{-1}$. $\square$

This is the input $h_{\text{coeff}}$ to the local bounds in [the last section](/chapter/bessel-real-place/#the-bessel-system-of-the-data). There the integral $\int\langle F(y), F(yg)\rangle$ appears as `New.Floors.quotientPairing`.

**Remark (Formalization).** The constant of the Schur bound is $d_\lambda^{-1}\int\|F\|^2$, written with `ENNReal.ofReal` of $d_\lambda^{-1}$. For $d_\lambda \leq 0$ this would be $0$, but the gap condition gives $d_\lambda > 0$ ([`New.formalDegree_pos`](/decl/New.formalDegree_pos/)). In a Bessel system the full function has $\int\|W\|^2 = |I|$, so the constant there is $|I|/\deg$. The bound on $B$ is linear in $L$, and in [the last section](/chapter/bessel-real-place/#the-bessel-system-of-the-data) every $P \geq b^5$ satisfies it.

### Orthonormality

**Lemma.** Let $W$ be a Bessel function of type $\rho$ and $s \in H$. Then for all $i, j$
$$\int_{\mathsf U\backslash G_1}W_i(sy)\overline{W_j(sy)}\,dy = \int_{\mathsf U\backslash G_1}W_i(y)\overline{W_j(y)}\,dy.$$

Lean: `New.IsBesselFunction.integral_mul_conj_embedH_mul` (New/Spanning/Bessel/Orthonormality.lean).

*Proof.* The integrand is invariant under $\mathsf U$ on the left, because the character factors cancel. The element $s$ lies in the Bessel subgroup and normalizes $\mathsf U$, and conjugation by $s$ keeps the Haar measure of $\mathsf U$ (`New.RealPlace.measurePreserving_conj_bessel`). Left multiplication by $s$ preserves the Haar measure of $G_1$. So it preserves the quotient measure on invariant functions. $\square$

**Theorem (Schur's lemma for the pairing).** Let $W$ be a Bessel function of type $\rho$, integrable on $\mathsf U\backslash G_1$, and let only scalar matrices commute with all $\rho(h)$. Then
$$\int_{\mathsf U\backslash G_1}W_i(y)\overline{W_j(y)}\,dy = \delta_{ij}\,\frac{1}{|I|}\int_{\mathsf U\backslash G_1}\|W\|^2.$$

Lean: `New.IsBesselFunction.integral_mul_conj_eq` (New/Spanning/Bessel/Orthonormality.lean).

*Proof.* Let $M_{kl} = \int W_k\overline{W_l}$. Each product is integrable, since $W$ is integrable and bounded. For $s \in H$, $W(sy) = R\,W(y)$ with $R = \rho(s)$. Expand and use the last lemma: $RMR^* = M$. Since $R$ is unitary, $M$ commutes with $R$. By the hypothesis, $M = c\cdot 1$. The trace of $M$ is $\int\|W\|^2$, so $c = |I|^{-1}\int\|W\|^2$. $\square$

**Corollary.** For a Bessel system $\mathcal B$ with full function $W$, the coordinates $W_i$ are orthonormal in $L^2(\mathsf U\backslash G_1)$:
$$\int_{\mathsf U\backslash G_1}W_i\overline{W_j} = \delta_{ij}.$$

Lean: `New.BesselSystem.orthonormal` (New/Spanning/Bessel/Orthonormality.lean).

*Proof.* The cut pair gives $\int\|W\|^2 = |I|$, and the system gives irreducibility. Apply the theorem. $\square$

[The chapter on Poincaré series](/chapter/poincare-series/) uses the corollary for the term $\gamma = 1$ of an amplitude sum.

**Theorem (The cut function).** Let $(W, W^\flat)$ be a cut pair of type $\rho$ for $b$ and $f$, and let $\rho$ be irreducible as above. Then:

1. $W^\flat$ is integrable on $\mathsf U\backslash G_1$;
2. there is $c \in [0, 1]$ with $\int W^\flat_i\overline{W^\flat_j} = c\,\delta_{ij}$;
3. for every $v \in \mathbb{C}^I$, $\int_{\mathsf U\backslash G_1}|\langle v, W^\flat(y)\rangle|^2\,dy \leq \|v\|^2$.

Lean: `New.IsCutPair.integrable_cut`, `New.IsCutPair.exists_integral_cut_mul_conj_eq`, `New.IsCutPair.lintegral_sq_inner_cut_le` (New/Spanning/Bessel/Orthonormality.lean).

*Proof.* (1) Let $(A, a)$ be the decay majorant of the cut pair. Since $\ell_b \geq 1$, $\|W^\flat\| \leq \ell_b^{3r^3f}\|W^\flat\| \leq A$. If $a = 0$, then $A = 0$. Otherwise $a\int A \leq b^{400r^2}|I| < \infty$ gives $\int A < \infty$. $W^\flat$ is continuous, so it is measurable. (2) The theorem applies to $W^\flat$, with $c = |I|^{-1}\int\|W^\flat\|^2$. The cut pair gives $\int\|W^\flat\|^2 \leq |I|$, so $c \leq 1$. (3) Expand $|\langle v, W^\flat\rangle|^2 = \sum_{i, j}v_i\overline{v_j}\,\overline{W^\flat_i}W^\flat_j$ and integrate term by term. By (2) the result is $c\|v\|^2 \leq \|v\|^2$. $\square$

Item 3 is used in [the chapter on local densities at the real places](/chapter/real-densities/), in RealShells.lean, to bound a pairing norm of $W^\flat$.

**Remark (Formalization).** The inner product of the source is conjugate linear in its first argument, so $\langle v, W^\flat(y)\rangle = \sum_i\overline{v_i}W^\flat_i(y)$. Irreducibility is a hypothesis in the form of Schur's lemma: every matrix that commutes with all $\rho(h)$ is in the range of `Matrix.scalar`. The source does not derive it from a statement about invariant subspaces. In the theorem the integrals are Bochner integrals, and the proof shows each integrand integrable, so no junk value occurs. The bound of item 3 is a lower Lebesgue integral and holds in $[0, \infty]$.
