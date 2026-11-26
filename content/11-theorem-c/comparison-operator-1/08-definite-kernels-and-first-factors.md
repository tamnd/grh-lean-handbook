---
title: Definite kernels and first factors
lean:
  - New/UpperBound/Kernels/DefiniteKernelSize.lean
  - New/OneLift/ComparisonOperator/FirstFactors.lean
decls:
  - New.Rows.modKernelStdSpace_embFin_mul
  - New.Rows.modKernelScale
  - New.Rows.modKernelScale_ne_zero
  - New.Rows.norm_modKernelScale_mul_modKernelStdSpace_le_one
  - New.Rows.norm_modKernelScale_mul_modKernelStdSpace_le
  - New.Rows.IsModKernelScale
  - New.Rows.exists_ne_zero_isModKernelScale
  - New.Data.renameRowsCols_stackedDetProd_eq_sum
  - New.Data.firstFactorSize_sq_le_exp
  - New.Data.IsIntegralAndSmall
  - New.Data.exists_star_leftSideSeries_eq_classSum
  - New.Data.exists_isIntegralAndSmall_leftSideSeries
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Definite kernels and first factors

The series $\Upsilon$ of the [previous section](/chapter/comparison-operator-1/#line-coordinates) is built from theta kernels of standard definite spaces. This section makes such kernels integral by one constant and bounds their conjugates. Then it shows that the first factors $\overline{c\Upsilon}$ are integral off the tame places and small when there is no twist. The theta kernels `modKernelStdSpace` of definite spaces are in [theta lifts and seesaws](/chapter/theta-lifts-seesaw/), and the two-sided substitution `twoSidedSubst` is in [the exchange identity, part 2](/chapter/exchange-identity-2/).

### Rational equivariance

Let $I_L$, $I_N$ be standard definite spaces over $E$. Let $a$, $b$ be automorphic characters of $U(1)$ with exponents $e$, $e'$ at the infinite places. Let $\Psi$ be a function on matrices modulo $\mathfrak{m}$, and $Q$ a polynomial in the entries of $N \times L$ matrices $x_\tau$.

**Lemma (Rational points).** For rational points $\gamma \in U(I_L)(E)$ and $\gamma' \in U(I_N)(E)$,
$$K_Q\bigl((1, \gamma g), \gamma' h\bigr) = \prod_\tau \tau(\det\gamma')^{-e_\tau}\tau(\det\gamma)^{e'_\tau}\cdot K_{Q'}\bigl((1, g), h\bigr),$$
where $Q'$ is $Q$ after the substitution $x_\tau \mapsto \tau(\gamma'^{-1})^{\mathsf{T}}x_\tau\tau(\gamma)^{\mathsf{T}}$.

Lean: `New.Rows.modKernelStdSpace_embFin_mul` (New/UpperBound/Kernels/DefiniteKernelSize.lean).

*Proof.* The kernel is invariant under the rational points $\gamma^{-1}$ and $\gamma'^{-1}$. They cancel the finite translations and leave a real point. This real point lies in the maximal compact subgroups, as the spaces are definite. It acts on the Fock vector of $Q$ by the substitution and by the scalar of the characters at the determinants. At $\tau$ the real components are the images of $\gamma^{-1}$, $\gamma'^{-1}$. All signs are $1$, so the principal minors are $\det$ or $1$. $\square$

### One constant for integrality and size

**Definition.** For a degree $d$ put
$$c_{L,N}(d) = (M^2)^{2e\,\#(N \times L)}\,s_{\mathrm{vac}}^{\#(N \times L)}\,(M^2\,d_K\,s_{\mathrm{jet}})^d,$$
where $e$ is the number of infinite places of $E$, $s_{\mathrm{vac}}$ makes the values of the rank-one vacuum integral, $s_{\mathrm{jet}}$ is the scale of the Taylor series, and $d_K$ is the discriminant parameter. It is not $0$.

Lean: `New.Rows.modKernelScale`, `New.Rows.modKernelScale_ne_zero` (New/UpperBound/Kernels/DefiniteKernelSize.lean).

**Lemma (Integrality).** Let $\mathfrak{m}$ contain $qM^2$, let the values of $\Psi$ be integral at the primes coprime to $q$, and let $Q$ be homogeneous of degree $d$. Let $p$ be a prime coprime to $q$, with an embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$. If $g$, $h$ are integral above $p$ and $Q$ has coefficients in the valuation ring of $\iota_p$, then $|\iota_p(c_{L,N}(d)K)| \leq 1$.

Lean: `New.Rows.norm_modKernelScale_mul_modKernelStdSpace_le_one` (New/UpperBound/Kernels/DefiniteKernelSize.lean).

*Proof.* The kernel is the pairing $Q(\partial)F(0)$ of $Q$ with the Taylor series $F$ of a theta function. The datum is $\Psi$ at the places dividing $\mathfrak{m}$ and the vacuum elsewhere, translated by $(1, g)$ and $(1, h)$. The factor $(M^2)^{2e\#(N\times L)}s_{\mathrm{vac}}^{\#(N\times L)}$ makes the translated datum integral at $p$, since $g$ and $h$ are integral above $p$. The factor $(M^2d_Ks_{\mathrm{jet}})^d$ makes the Taylor coefficients of degree $d$ integral. Apply the integral coefficients of $Q$. $\square$

**Lemma (Size).** Let $\#L, \#N \leq \Delta$, $d \leq M$, and $M^2 \in \mathfrak{m}$. Let $A \in \mathbb{N}$ bound all conjugates of the values of $\Psi$. Let $\sigma \in \mathrm{Aut}(\mathbb{C})$, and let $B$ bound $|\sigma(Q(z))|$ whenever all $|\sigma(z_i)| \leq M^4$. Then $|\sigma(c_{L,N}(d)K)| \leq e^{x_1}AB$.

Lean: `New.Rows.norm_modKernelScale_mul_modKernelStdSpace_le` (New/UpperBound/Kernels/DefiniteKernelSize.lean).

*Proof.* The normalised kernel is a power of $M^2$ times the jet along $Q$ of the Taylor series of $\omega f_0$. Here $f_0$ is a combination of translates of the vacuum, with coefficients of total size at most $\#(\text{matrices modulo }\mathfrak{m})\cdot A$. The conjugates of this jet are bounded by the jet bound for vacuum combinations, with $B$ entering through the polydisc of radius $M^4$. The remaining constants depend on $\Delta$, $M$ and $d \leq M$, and $e^{x_1}$ absorbs them, since $x_1$ is large in admissible data. $\square$

**Definition and theorem.** A number $c$ is a *scale* for degree $d$ (`IsModKernelScale`) if $c$ times every kernel has the integrality property and the size property above. For all $L$, $N$, $D$ and $d$ there is a scale $c \neq 0$, namely $c_{L,N}(d)$.

Lean: `New.Rows.IsModKernelScale`, `New.Rows.exists_ne_zero_isModKernelScale` (New/UpperBound/Kernels/DefiniteKernelSize.lean).

*Proof.* Combine the three previous results. $\square$

### The determinant product as a sum

**Lemma.** For the short basis $Y = $ `D.shortRows i` of the class in $i$, and renamings $f$ of the positive indices of $W_j$ and $g$ of the indices of $W^{\mathrm{add}}$,
$$P_V = \sum_l \mathrm{letterPoly}(e_l)\circ f\cdot \zeta_l\circ g,$$
where $l$ runs over the basis of the Weyl module of weight $\mu^+$ and $\mathrm{letterPoly}(e_l)$ is the letter polynomial of the $l$-th unit vector in the letters of sign $+1$.

Lean: `New.Data.renameRowsCols_stackedDetProd_eq_sum` (New/OneLift/ComparisonOperator/FirstFactors.lean).

*Proof.* The renaming factors through the reading of $P_V$ in the first $r_+$ columns: the first columns go to the letters of sign $+1$, the coefficients to the variables of $W^{\mathrm{add}}$. By $\mathrm{toPoly}(\zeta) = P_V$ the read polynomial is $\sum_l\zeta_l b_l$ for the basis $b_l$. Both sides are the same double sum up to the order of summation. $\square$

### First factors

**Definition.** A vector $y$ of weight $\mu^+$ is *integral and small* at $h$ for $\vartheta$ if:
1. for every prime $p$ coprime to the norm $N(Q)$ of the tame places of $\vartheta$, the gauge satisfies $\mathrm{weylGauge}(\mu^+, 0, h, y) \leq 1$;
2. if $Q = \emptyset$, every conjugate $\varphi\circ y$, $\varphi \in \mathrm{Aut}(\mathbb{C})$, has $\mathrm{weylNormSq}(\varphi\circ y) \leq \exp(fmb\log^2 b)$.

Lean: `New.Data.IsIntegralAndSmall` (New/OneLift/ComparisonOperator/FirstFactors.lean).

**Lemma (Expansion).** There is $c$ with $|c| = 1$, depending only on $j$, with this property. For all scalars $c_0, c_1, c_2$, every integer $H$, every $u$, $i$, $\vartheta$ and $h$, the conjugate of $g^2c_2Hc_0\bar c_1c\,\Upsilon(h)$ equals $g^2$ times a double class sum over $w \in U(E^{3m})$ and $v \in U(E^m)$ of the conjugates of
$$k_0(v, w)\,\overline{k_1}\,c_2\,K_{W^{\mathrm{add}},V''}\bigl[\Psi^{\mathrm{add}}\bigr]\bigl((1, (1, h^\flat, w)), (1, h)\bigr)\circ(H\zeta).$$
Here $g = $ `D.chosenGroupOrder`, $k_0 = c_0$ times a kernel of $(E^m, E^{3m})$, and $k_1 = c_1$ times a kernel of $(E^j, V'')$.

Lean: `New.Data.exists_star_leftSideSeries_eq_classSum` (New/OneLift/ComparisonOperator/FirstFactors.lean).

*Proof.* The first factor of $\Upsilon$ is a kernel of $((E^j)^-, V'')$. The conjugate of a kernel of a definite space equals a unit $c$ times the kernel of the negative space ([theta lifts and seesaws](/chapter/theta-lifts-seesaw/)), with the characters adjusted, so this factor is a multiple of $\bar k_1$. The other factor is a double class sum after `carrierCoeff` is expanded. Conjugate term by term and collect the scalars. $\square$

**Lemma (Size of the constants).** Let $q = f(b_{\mathbb{N}} + w_{\mathrm{off}} + \Delta + m\Delta)$, $n \leq (10m+1)q$, $n \leq M$ and $0 < H \leq (n^n)^3$. For every $\varphi \in \mathrm{Aut}(\mathbb{C})$, the square of
$$|\varphi(g^2)|^2\,h_{3m}h_m\,e^{3x_1}\,\#GL_{3m}(\mathcal{O}/\varpi^2)\,\sqrt{H^2(M^9)^{(12m+1)q}}$$
is at most $\exp(fmb\log^2b)$, where $h_{3m}$, $h_m$ are the class numbers of the standard levels.

Lean: `New.Data.firstFactorSize_sq_le_exp` (New/OneLift/ComparisonOperator/FirstFactors.lean).

*Proof.* Both class numbers are at most $\exp(x^{30})$. Also $H \leq n^{3n} \leq M^{3n}$, $\#GL(R) \leq \#R^{(3m)^2}$ and $\#R \leq (M^2)^{2e}$. Take logarithms. With $n \leq (10m+1)q$, the scale inequalities of admissible data put the logarithm below $fmb\log^2b$. $\square$

**Theorem (First factors).** For $1 \leq j \leq m$ there is $c \neq 0$, independent of $i$, $\vartheta$ and $h$, such that $\overline{c\,\Upsilon(h)}$ is integral and small at $h$ for $\vartheta$, for every choice $i$.

Lean: `New.Data.exists_isIntegralAndSmall_leftSideSeries` (New/OneLift/ComparisonOperator/FirstFactors.lean).

*Proof.* Let $q$ be the bound on the number of determinants from [line coordinates](/chapter/comparison-operator-1/#line-coordinates). Take $n$ and $H$ from the theorem on the degree and denominator of $\zeta$: each $H\zeta_l$ is homogeneous of degree $n \leq (10m+1)q$ with coefficients in every ring that contains the conjugates of the entries of $Y$. Take scales $c_0$, $c_1$, $c_2$ for the three kernels, and put $c = g^2c_2Hc_0\bar c_1c'$ with $c'$ from the expansion. This $c$ is not $0$. By the expansion, $\overline{c\Upsilon}$ is $g^2$ times a double class sum of conjugates of products of three normalised kernels.

*Integrality.* The vector is a conjugate, so read its factors at $\iota_p\circ\mathrm{conj}$. Move the classes into points integral above $p$, using the rational equivariance. The data are integral away from $N(Q)$, and the entries of $Y\gamma^{\mathsf{T}}$ for the short basis $Y$ are integral above $p$. Each normalised kernel then has $p$-adic size at most $1$, and so has the product. Hence the gauge is at most $1$.

*Size.* Let $Q = \emptyset$. The datum $\Psi^{\mathrm{add}}$ is bounded by $\#GL_{3m}(\mathcal{O}/\varpi^2)$. At small points, $H\zeta$ has squared norm at most $H^2(M^9)^{(12m+1)q}$ by the theorem on the norm of $\zeta$, since the conjugates of the entries of a short basis are at most $M^4$ ([reduction theory](/chapter/reduction-theory/)). By duality it is enough to bound the kernel at every polynomial that is small at the small points. Each normalised kernel then has conjugates at most $e^{x_1}$ times its bounds. Counting the classes and applying the lemma on the size of the constants gives $\mathrm{weylNormSq} \leq \exp(fmb\log^2b)$. $\square$

**Remark (Formalization).** The scales $c_0$, $c_1$, $c_2$ come from `∃` statements, but each is the explicit `modKernelScale`. The unit $c'$ of the expansion is chosen. The representative $h^\flat$ of a class is `Quotient.out`. The size property is asked only when $\vartheta$ has no tame places, and the bound $\exp(fmb\log^2b)$ does not depend on $h$.
