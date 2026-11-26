---
title: Theta functions along a frame
lean:
  - New/Derivatives/Vacuum/TightFrames.lean
  - Lib/Weil/Construction/FourierInversion.lean
  - Lib/CM/Integrality/TorsionValues.lean
decls:
  - New.Space.taylor_line_eq_subst_jetSeries
  - New.Space.eq_zero_of_jetSeries_eq_zero
  - New.taylorAtZero_prod_comp_mul
  - New.mvPowerSeries_eq_of_forall_line
  - New.Space.entireTheta_zero
  - New.Space.theta_eq_prod_of_entireTheta_smul
  - New.Space.jetSeries_eq_prod_of_entireTheta_smul
  - New.Space.jetSeries_eq_prod
  - New.Space.exists_entireTheta_eq_of_isThetaFunction
  - New.Parameters.cmPeriod_mem_cmCurve_lattice
  - New.Parameters.resolutionShift
  - New.Parameters.resolutionLinearForm
  - New.Parameters.resolutionLinearForm_realImage
  - New.Parameters.mul_sum_mul_conj_mem_lattice
  - New.Parameters.IsResolutionProduct
  - New.Parameters.IsResolutionProduct.theta_translate
  - New.Parameters.IsResolutionProduct.jetSeries_translate
  - New.Parameters.IsResolutionProduct.norm_iota_apply_le_one
  - New.Parameters.sum_pullForm_resolutionLinearForm_apply
  - New.Parameters.normalizedShift_prod_comp_of_mem_lattice
  - New.Parameters.exists_isResolutionProduct_of_isTightFrame
  - New.CMLattice.hasIntegralValues_monomialSection
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta functions along a frame

This section proves the main construction of the chapter. Take a tight frame $(w_j)$ of length $M$, a CM lattice $C$ of the right area, and a monomial section of $C$ of degree $m_j$ for each $j$. Compose each section with the linear form of $w_j$ and multiply. The product is the theta function of a vector $F$ of the Weil representation, and the values of $F$ at the finite points are integral at every prime. The proof has three parts: the product has the transformation law of a theta function, Fourier inversion gives $F$, and the values of $F$ are torsion values of monomials.

The section first records how Taylor series of such products behave, since Section 6 and later chapters use them.

### Theta functions and jet series

Let $V$ be a hermitian space of rank $n$ over $E$ with all signs $1$. For a vector $f$ of $\mathcal{S}(V)$, the function $\mathrm{entireTheta}\, f$ on $\mathbb{C}^{\Phi \times n}$ is $y \mapsto \theta(\varrho(y)f)\, e^{|y|^2/2}$ on real vectors in Fock coordinates, and for $f$ in the *finite part* $V^{\mathrm{fin}}$ it extends to an entire function ([theta lifts and the seesaw](/chapter/theta-lifts-seesaw/)). The finite part is the span of the translates of $\mathrm{vac}$ under the finite Heisenberg operators. The *jet series* $J_a f$ is the power series in variables $X_{\tau,k}$ whose coefficient of $X^k$ is $a^{|k|}/k!$ times $\theta$ of $f$ tensored with the Fock vector of $z^k$. So $J_a f$ is the Taylor series of $z \mapsto \mathrm{entireTheta}\, f(a z)$ at $0$, as the next lemma says on each line.

**Lemma.** Let $f \in V^{\mathrm{fin}}$, $a \in \mathbb{C}$ and $v \in \mathbb{C}^{\Phi \times n}$. The Taylor series at $0$ of $t \mapsto \mathrm{entireTheta}\, f(a t v)$ is $J_a f$ with $v_\pi X$ put in place of $X_\pi$.

Lean: `New.Space.taylor_line_eq_subst_jetSeries` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* On the line, $\mathrm{entireTheta}\, f(atv)$ is an integral $\int e^{t L(w)} g(w)\,dw$, with $g$ the Gaussian times the values of $f$ and $L$ a conjugate-linear form. Dominated convergence lets one expand the exponential under the integral, so the $k$-th derivative at $0$ is $\int L(w)^k g(w)\,dw$. Expand $L^k$ by the multinomial theorem. The integral of a monomial against $g$ is the theta functional of $f$ tensored with the Fock vector of that monomial, which is the coefficient of $J_af$. $\square$

**Lemma.** If $f \in V^{\mathrm{fin}}$, $a \ne 0$ and $J_a f = 0$, then $f = 0$.

Lean: `New.Space.eq_zero_of_jetSeries_eq_zero` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* By the last lemma, the restriction of $\mathrm{entireTheta}\, f$ to every line through $0$ has Taylor series $0$, so it vanishes on the line. A vector of $\mathcal{S}(V)$ is determined by its values at the real vectors. $\square$

**Lemma.** Two power series over $\mathbb{C}$ in finitely many variables are equal if their restrictions to every line through $0$ are equal. The Taylor series at $0$ of $x \mapsto \prod_i G_i(c_i x)$, for entire $G_i$, is $\prod_i \widehat{G_i}(c_i X)$, where $\widehat G$ is the Taylor series of $G$.

Lean: `New.mvPowerSeries_eq_of_forall_line`, `New.taylorAtZero_prod_comp_mul` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The restriction to the line of $v$ has as coefficient of $X^r$ the value at $v$ of the homogeneous part of degree $r$. A polynomial over $\mathbb{C}$ is determined by its values. The second claim holds because the Taylor series of a product is the product of the Taylor series. $\square$

**Proposition (Products).** Let $f \in V^{\mathrm{fin}}$, let $G_i$ be entire functions for $i$ in a finite set, and let $\mu_i(c) \in \mathbb{C}^{\Phi \times n}$ be such that
$$\mathrm{entireTheta}\, f(c z) = \prod_i G_i(\mu_i(c) \cdot z) \qquad \text{for all } c \text{ and } z .$$
Then $\theta(f) = \prod_i G_i(0)$, and for every $c$,
$$J_c f = \prod_i \widehat{G_i}\Bigl(\sum_\pi \mu_i(c)_\pi X_\pi\Bigr) .$$

Lean: `New.Space.entireTheta_zero`, `New.Space.theta_eq_prod_of_entireTheta_smul`, `New.Space.jetSeries_eq_prod_of_entireTheta_smul`, `New.Space.jetSeries_eq_prod` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* At $z = 0$, $\mathrm{entireTheta}\, f(0) = \theta(f)$. For the series, compare both sides on the line of $v$. The left side gives the Taylor series of $x \mapsto \mathrm{entireTheta}\, f(c x v)$, and the right side the series of $x \mapsto \prod_i G_i((\mu_i(c) \cdot v) x)$. These are the same function. $\square$

### Fourier inversion

The next theorem is the converse of the transformation law of theta functions. It comes from Fourier analysis on a finite group. A function $S$ on $\mathbb{C}^{\Phi\times n}$ is a *theta function* for a lattice $Y$ of $E^n$ if it is entire and fixed by the signed translations along $Y$, the translations by the real images of the points of $Y$ with their semicharacter.

**Theorem (Fourier inversion).** Let $V$ be a standard space. Let $\delta \in \mathcal{O}_K$ with $\delta\bar\delta = N \ne 0$. Every theta function $S$ for $\bar\delta\, \mathfrak{a}_0^n$ is $\mathrm{entireTheta}\, \varphi$ for some $\varphi \in V^{\mathrm{fin}}$.

Lean: `New.Space.exists_entireTheta_eq_of_isThetaFunction` (Lib/Weil/Construction/FourierInversion.lean).

The proof, in the source, sums the translates of $S$ over representatives of $\mathfrak{a}_0^n/\bar\delta\mathfrak{a}_0^n$ to get theta functions for $\mathfrak{a}_0^n$. These are multiples of the theta function of $\mathrm{vac}$. Orthogonality of the characters of $\delta^{-1}\mathfrak{a}_0^n/\mathfrak{a}_0^n$ then gives $N^{r} S$ as a sum of translates of the theta function of $\mathrm{vac}$, with $r = f \cdot n$. Section 5 uses the explicit form.

### The product along a frame

Fix a CM lattice $C$ with lattice $\Lambda$ and area $A$. For $m \in \mathbb{N}$, $l \in \mathbb{C}$ and a function $g$, the twisted translate is
$$(T^m_l g)(z) = \exp\Bigl(-\frac{m\pi}{A}\Bigl(z \bar l + \frac{|l|^2}{2}\Bigr)\Bigr)\, g(z + l) .$$
A section of degree $m$ of $C$ is a function $g$ with $T^m_l g = \chi(l)^m g$ for $l \in \Lambda$, for a multiplier $\chi$ of absolute value $1$. The monomial section $g_x = \theta^a (\sigma^2)^b G^c$ of $x = (a, b, c)$ has degree $a + 2b + 3c$. Its torsion values are $g_x[u] = (T^{\deg x}_u g_x)(0)$ for torsion points $u$ ([CM elliptic curves](/chapter/cm-elliptic-curves/)).

**Theorem (Monomials).** Let $d \equiv 7 \pmod 8$ be prime and $\iota_p$ a $p$-adic place. For every triple $x$ and every torsion point $u$ of $C$, $|\iota_p(g_x[u])| \le 1$.

Lean: `New.CMLattice.hasIntegralValues_monomialSection` (Lib/CM/Integrality/TorsionValues.lean).

Let $(w_j)_{j\in I}$ be a family in $E$, $b \in \mathbb{C}$, and $\gamma \in E^n$. For $i = (j, k) \in I \times n$ put
$$\ell_i(z) = \frac{b}{\mathrm{areaScale}} \sum_\tau \overline{\tau(w_j)}\, z_{\tau,k}, \qquad s_i(\gamma) = -b \sum_\tau \tau(\gamma_k)\, \overline{\tau(w_j)} = -b\, \langle \gamma_k, w_j\rangle .$$

Lean: `New.Parameters.resolutionLinearForm`, `New.Parameters.resolutionShift` (New/Derivatives/Vacuum/TightFrames.lean).

The real image of $\gamma$ in Fock coordinates has entry $\mathrm{areaScale}\cdot\tau(\gamma_k)$ at $(\tau, k)$. So $\ell_i$ takes the real image of $\gamma$ to $-s_i(\gamma) = b \langle \gamma_k, w_j \rangle$.

Lean: `New.Parameters.resolutionLinearForm_realImage` (New/Derivatives/Vacuum/TightFrames.lean).

**Lemma.** If $a \in \Lambda$ and $x, y \in \mathfrak{a}_0$, then $a \langle y, x\rangle \in \Lambda$. In particular $\Omega_0 \in \Lambda$ for the CM curve.

Lean: `New.Parameters.mul_sum_mul_conj_mem_lattice`, `New.Parameters.cmPeriod_mem_cmCurve_lattice` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The pairing lies in $\mathcal{O}_K$ (Section 2), and $\Lambda$ is an $\mathcal{O}_K$-module. The lattice of the CM curve is $\Omega_0\mathcal{O}_K$. $\square$

**Definition (Resolution product).** Let $m_j \in \mathbb{N}$ and let $g_i$ be functions on $\mathbb{C}$ for $i \in I \times n$. A vector $F$ of $\mathcal{S}(V)$ is the *resolution product* of the $g_i$ along $(w_j)$ at scale $b$ if $F \in V^{\mathrm{fin}}$, every $g_i$ is entire, and for every $\gamma \in E^n$ and every $z$,
$$\mathrm{entireTheta}\bigl(\varrho(\mathrm{fin}(\alpha^{-1}\gamma)) F\bigr)(z) = \prod_{i = (j,k)} \bigl(T^{m_j}_{s_i(\gamma)} g_i\bigr)\bigl(\ell_i(z)\bigr) .$$

Lean: `New.Parameters.IsResolutionProduct` (New/Derivatives/Vacuum/TightFrames.lean).

Here $\mathrm{fin}(\alpha^{-1}\gamma)$ is the adelic vector with finite part $\alpha \cdot \alpha^{-1}\gamma = \gamma$ and real part $0$, so $\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F$ is the translate of $F$ by the rational vector $\gamma$.

**Corollary.** Let $F$ be a resolution product. For every $\gamma \in E^n$,
$$\theta\bigl(\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F\bigr) = \prod_{i = (j,k)} \bigl(T^{m_j}_{s_i(\gamma)} g_i\bigr)(0) .$$
If $V$ is standard, then for every $c \in \mathbb{C}$ the jet series $J_c(\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F)$ is the product over $i = (j,k)$ of the Taylor series of $T^{m_j}_{s_i(\gamma)} g_i$ at the linear form $(bc/\mathrm{areaScale})\sum_\tau \overline{\tau(w_j)}\, X_{\tau,k}$.

Lean: `New.Parameters.IsResolutionProduct.theta_translate`, `New.Parameters.IsResolutionProduct.jetSeries_translate` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The defining identity at $cz$ has the form of the proposition on products, with $\mu_i(c)$ the coefficients of $c\,\ell_i$. $\square$

**Proposition (Integral values).** Let $F$ be the resolution product of the monomial sections $g_{x_i}$ along $(w_j)$ at scale $b$, with $\deg x_i = m_j$ for $i = (j,k)$. Assume that every $w_j$ lies in $\mathfrak{a}_0$, that $\delta \in \mathcal{O}_K$ has $\delta\bar\delta = N \ne 0$, and that $b\bar\delta \in \Lambda$. Then for every $p$-adic place $\iota_p$ and every finite adelic vector $y$,
$$|\iota_p(F(\mathrm{fin}(y)))| \le 1 .$$

Lean: `New.Parameters.IsResolutionProduct.norm_iota_apply_le_one` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The value $F(\mathrm{fin}(y))$ is $\theta(\varrho(\mathrm{fin}(y))F)$. Since $F$ lies in the finite part, it is fixed by the translations by an open subgroup of the finite adeles, up to a character of finite order. As $E$ is dense, there is $\gamma \in E^n$ with $\varrho(\mathrm{fin}(y))F = \varrho(\mathrm{fin}(\alpha^{-1}\gamma))F$. By the corollary,
$$F(\mathrm{fin}(y)) = \prod_{i = (j,k)} \bigl(T^{m_j}_{s_i(\gamma)} g_{x_i}\bigr)(0) = \prod_i g_{x_i}[s_i(\gamma)] .$$
Each $s_i(\gamma)$ is a torsion point of $C$. There is $L \ne 0$ in $\mathbb{N}$ with $L\gamma \in \mathfrak{a}_0^n$. Then
$$N L\, s_i(\gamma) = -\delta \cdot (b\bar\delta)\, \langle L\gamma_k, w_j\rangle \in \Lambda,$$
by the last lemma and because $\Lambda$ is an $\mathcal{O}_K$-module. By the theorem on monomials, every factor has $|\iota_p(\cdot)| \le 1$, and so has the product. $\square$

### The isometry and the main theorem

**Lemma (Isometry).** Let $(w_j)$ with multiplicities $(m_j)$ be a tight frame of length $M$, and let $A = |b|^2 M \sqrt d/2$. Let $H(l, z) = (\pi/A)\,\bar l z$ be the hermitian form of $C$. Then for all $u, v$,
$$\sum_{i = (j,k)} m_j\, H\bigl(\ell_i(u), \ell_i(v)\bigr) = \sum_{\pi} \overline{u_\pi}\, v_\pi .$$

Lean: `New.Parameters.sum_pullForm_resolutionLinearForm_apply` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* As $|b/\mathrm{areaScale}|^2 = |b|^2\sqrt d/(2\pi)$, the factor $\pi/A$ times this is $1/M$. So the left side is
$$\sum_k \sum_{\sigma,\tau} \overline{u_{\tau,k}}\, v_{\sigma,k}\, \frac1M \sum_j m_j\, \tau(w_j)\,\overline{\sigma(w_j)} .$$
The inner sum is $M\delta_{\sigma\tau}$ by the frame identity. $\square$

**Lemma.** Let $g_i$ be sections of degree $m_j$ of $C$, and let $A_i$ be linear forms that take a vector $u$ into $\Lambda$. Let $B = \sum_i m_j H(A_i\,\cdot, A_i\,\cdot)$. Then the translation by $u$ normalized by $B$, with the semicharacter of $\Lambda$, fixes $\prod_i g_i \circ A_i$.

Lean: `New.Parameters.normalizedShift_prod_comp_of_mem_lattice` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Each factor is multiplied by $\chi(A_i u)^{m_j}$ under the translation, and the Gaussian factors multiply to the Gaussian factor of $B$. The product of the multipliers is the canonical multiplier of $B$ at $u$. $\square$

**Theorem (Theta functions along a frame).** Let $V$ be a standard space of rank $n$. Let $\delta \in \mathcal{O}_K$ with $\delta\bar\delta = N \ne 0$, and let $(w_j)$ with multiplicities $(m_j)$ be a tight frame of length $M$. Let $x_i$ be triples with $\deg x_i = m_j$ for $i = (j,k)$. Let $C$ be a CM lattice and $a \in \Lambda$ with
$$\mathrm{area}(C) = \frac{|a|^2}{N}\cdot M \cdot \frac{\sqrt d}{2} .$$
Then there is $F \in \mathcal{S}(V)$ such that:

1. $F$ is the resolution product of the $g_{x_i}$ along $(w_j)$ at scale $a/\bar\delta$;
2. for every $p$-adic place $\iota_p$ and every finite adelic vector $y$, $|\iota_p(F(\mathrm{fin}(y)))| \le 1$;
3. $\mathrm{entireTheta}\, F$ is a theta function for $\bar\delta\,\mathfrak{a}_0^n$.

Lean: `New.Parameters.exists_isResolutionProduct_of_isTightFrame` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Put $b = a/\bar\delta$ and $A_i = \ell_i$, and let $S = \prod_i g_{x_i}\circ A_i$. As $|\bar\delta|^2 = N$, the area is $|b|^2 M\sqrt d/2$. So the forms $m_j H(A_i\,\cdot, A_i\,\cdot)$ add up to the standard form, by the isometry lemma. Let $\gamma = \bar\delta\gamma'$ with $\gamma' \in \mathfrak{a}_0^n$. Then
$$A_i(\text{real image of } \gamma) = b \langle \bar\delta\gamma'_k, w_j\rangle = a \langle \gamma'_k, w_j \rangle \in \Lambda .$$
By the last lemma, $S$ is fixed by the signed translations along $\bar\delta\mathfrak{a}_0^n$, so it is a theta function for this lattice. By Fourier inversion, $S = \mathrm{entireTheta}\, F$ for some $F \in V^{\mathrm{fin}}$. This is item 3. For item 1, the theta function of $\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F$ is the translate of $S$ by $-(\text{real image of }\gamma)$, times a Gaussian factor ([the Weil representation](/chapter/weil-representation/)). The isometry splits this factor over the $i$, and the factor $i$ becomes $T^{m_j}_{s_i(\gamma)} g_{x_i}$ at $A_i(z)$. Item 2 is the proposition on integral values, since $b\bar\delta = a \in \Lambda$. $\square$

**Example.** Take the frame of powers $\zeta^k$, $0 \le k < q_1$, each with multiplicity $1$, of length $q_1$, and $x_i = (1, 0, 0)$, so $g_{x_i} = \theta_C$. For $n = 1$ the theorem gives a vector $F$ with
$$\mathrm{entireTheta}\, F(z) = \prod_{k < q_1} \theta_C\Bigl(\frac{b}{\mathrm{areaScale}} \sum_\tau \overline{\tau(\zeta)}^{\,k}\, z_\tau\Bigr) .$$
The $q_1$ linear forms are the characters of the cyclic group $\langle\zeta\rangle$ read on the places. Section 5 makes this choice with $b = \Omega/q_1$ and $\delta = q_1 e$.

**Remark (Formalization).** The theorem holds with $M = 0$: then $\mathrm{area}(C) = 0$ is impossible for a lattice, so the hypothesis fails and the statement is empty. The source does not require that $F \ne 0$. Nonvanishing comes later, from $\theta(F) = 1$ in Section 5. The source states the integral values for every ring homomorphism $\iota_p \colon \mathbb{C} \to \mathbb{C}_p$, at every finite adelic vector, and not only at the rational ones.
