---
title: One vector and Siegel's formula
lean:
  - Lib/SiegelWeil/OneVector/SiegelClassSum.lean
decls:
  - New.SiegelWeil.shearSplitting
  - New.SiegelWeil.eq_lagrangian_of_notMem_range_shear
  - New.SiegelWeil.zeroTerm_shearSplitting
  - New.SiegelWeil.siegel_weil_one_vector
  - New.exists_fundamentalDomain_real
  - New.realAdele
  - New.exists_isAddFundamentalDomain_realAdele
  - New.star_adeleMatrix_mulVec_dotProduct
  - New.integrable_and_integral_eq_tsum_of_fundamentalDomain
  - New.SiegelWeil.siegel_weil_fourierCoeff
  - New.normDensity
  - New.SiegelWeil.exists_mixedValue_eq_gaussian_mul
  - New.integral_fourierChar_mul_inv_pow
  - New.integral_fourierChar_mul_gaussian_pow
  - New.integral_gaussian_mul_stdAddChar
  - New.classSum_eq_mul_integral
  - New.classSum_eq_mul_normDensity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One vector and Siegel's formula

This section applies the Siegel-Weil formula to one hyperbolic plane $S$, so $p = 1$, and the definite space $T = E^\kappa$ with the form $x^* x$ of rank at least $3$. One Fourier coefficient of the formula counts the vectors of one norm $\alpha$. The result is Siegel's formula for the mean number of representations of $\alpha$ over a genus.

### Siegel's classical formula

For a positive definite lattice $L$ and $\alpha > 0$, Siegel's formula says that the weighted mean of the numbers $r(L_i, \alpha)$ of vectors of norm $\alpha$ over the classes $L_i$ of the genus of $L$ is a product of local densities:
$$\frac{\sum_i r(L_i, \alpha)/\#\mathrm{Aut}(L_i)}{\sum_i 1/\#\mathrm{Aut}(L_i)} = \prod_v \beta_v(\alpha),$$
where $\beta_\infty$ is the volume of the sphere of norm $\alpha$ for a suitable measure. Weil obtained it from the Siegel-Weil formula for one vector in *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5. The source file also names Siegel, Ann. of Math. 36 (1935), and Braun, *Zur Theorie der hermitischen Formen*, Abh. Math. Sem. Hamburg 14 (1941).

The source does not evaluate the local densities. It keeps the finite part as one adelic Fourier integral, the density `New.normDensity`, and Section 7 bounds it.

### The lines of the hyperbolic plane

By the example of Section 2, the Lagrangians of the plane are the line of $k$ and the lines of $l + \jmath^{-1}\beta k$, $\beta \in E^+$.

**Definition (Shear splitting).** For $\beta \in E^+$, the splitting `shearSplitting β` of the hyperbolic plane has the isotropic frame $l + \jmath^{-1}\beta k$, the dual frame $k$, and a complement of rank $0$.

Lean: `New.SiegelWeil.shearSplitting` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

**Lemma (The other line).** A Lagrangian of the hyperbolic plane that is not the line of a shear splitting is the line of $k$, the Lagrangian of `hyperbolicSplitting`.

Lean: `New.SiegelWeil.eq_lagrangian_of_notMem_range_shear` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* If some $y \in L$ has $y_l \neq 0$, isotropy makes $\beta = \jmath y_k / y_l$ real and $L = L_\beta$, which is excluded. So $L$ lies in the line of $k$, and both are Lagrangians. $\square$

Let $\Psi$ be the Schrödinger function of a vector $f$: $\Psi(x)$ is the value `mixedValue` of $f$ at the column $x \in \mathbb{A}_E^\kappa$ for `hyperbolicSplitting`. Let $\psi$ be the standard character `stdAddChar E` of $\mathbb{A}_E$.

**Lemma (Zero terms of the sheared lines).** For $\beta \in E^+$,
$$\mathrm{ev}_{L_\beta}(f) = \int_{\mathbb{A}_E^\kappa} \Psi(x)\, \psi\big(\tfrac12 \beta\, x^* x\big)\, dx,$$
where $L_\beta$ is the line of $l + \jmath^{-1}\beta k$.

Lean: `New.SiegelWeil.zeroTerm_shearSplitting` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* By the symmetry of Chapter 1, the zero term along $L_\beta$ is the integral of the source terms of the opposite splitting. That splitting has the frame $k$ of `hyperbolicSplitting`, and its $k$-coordinate differs by $\overline{\jmath^{-1}\beta}$ times the $l$-coordinate. So the source terms differ by the character $\psi(\frac12\beta x^*x)$. $\square$

**Theorem (The Siegel-Weil formula for one vector).** Let $\mathrm{card}\,\kappa \ge 3$. The operator norms of the zero terms $\mathrm{ev}_{L_\beta}$ are summable over $\beta \in E^+$. For every $f$,
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \Big(\Psi(0) + \sum_{\beta \in E^+} \mathrm{ev}_{L_\beta}(f)\Big).$$

Lean: `New.SiegelWeil.siegel_weil_one_vector` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Apply `siegel_weil` with $P$ = `hyperbolicSplitting` and $p = 1$. The map $\beta \mapsto L_\beta$ is injective and misses the line of $k$, whose zero term is $\Psi(0)$. The lemma on the other line ends the proof. $\square$

### One Fourier coefficient

To count vectors of norm $\alpha$, integrate the formula against $\psi(-\frac12 z\alpha)$ over $z$ in the adeles of $E^+$ modulo $E^+$. A self-adjoint adele is a pair $z = (z_\infty, z_f)$ of real components and a self-adjoint finite adele, and `New.realAdele z` is the adele of $E$.

**Lemma (A fundamental domain for $E^+$).** There are an injective additive map $\iota$ from $E^+$ to these pairs, with `realAdele (ι a + z) = a + realAdele z`, and a bounded set $\Omega$ of real components, such that $\Omega \times \mathfrak{d}^{-1}_{\mathrm{sa}}$ is a fundamental domain for $\iota(E^+)$. Here $\mathfrak{d}^{-1}_{\mathrm{sa}}$ is the group `selfAdjointCodifferent E 1` of self-adjoint finite adeles in the inverse different. For self-adjoint $\beta \in E$,
$$|D_E|^{1/4} \int_{\Omega \times \mathfrak{d}^{-1}_{\mathrm{sa}}} \psi\big(\tfrac12\, z\, \beta\big)\, dz = \begin{cases} 1 & \beta = 0, \\ 0 & \beta \ne 0. \end{cases}$$

Lean: `New.exists_isAddFundamentalDomain_realAdele`, `New.exists_fundamentalDomain_real`, `New.realAdele` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The set $\Omega$ is a fundamental domain for the real components of the inverse different of $E^+$, of volume $|D_{E^+}|^{-1/2} = |D_E|^{-1/4}$, since $E/E^+$ is unramified at the finite places. The character is trivial on $E^+$, and for $\beta \ne 0$ it is a nontrivial character of the compact quotient. $\square$

**Theorem (The Fourier coefficient at $\alpha$).** Let $\mathrm{card}\,\kappa \ge 3$, let $f$ have Schrödinger function $\Psi$, and let $\alpha \in E^+$ be nonzero. Put
$$P(z) = \int_{\mathbb{A}_E^\kappa} \Psi(x)\, \psi\big(\tfrac12\, z\, (x^*x - \alpha)\big)\, dx.$$
Let $\sigma_h(\xi) = \Psi(h^{-1}\xi)$ if $\xi \in E^\kappa$ has $\xi^*\xi = \alpha$, and $0$ otherwise. Then $P$ is integrable, $\sigma_h$ is summable for every $h$, the function $h \mapsto \sum_\xi \sigma_h(\xi)$ is left invariant under the rational points of $U(T)$, and
$$\int_{[U(T)]} \sum_\xi \sigma_h(\xi)\, dh = \mathrm{vol}([U(T)])\, |D_E|^{1/4} \int P(z)\, dz.$$

Lean: `New.SiegelWeil.siegel_weil_fourierCoeff`, `New.star_adeleMatrix_mulVec_dotProduct`, `New.integrable_and_integral_eq_tsum_of_fundamentalDomain` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Let $n(z)$ be the unipotent element of $U(S)$ for $z$, and put $f_z = \psi(\frac12 z\alpha)^{-1}\omega(n(z), 1) f$. Its Schrödinger function is $\Psi(x)\psi(\frac12 z(x^*x - \alpha))$. By the lemma on the sheared lines, and since $\psi(\frac12\beta\alpha) = 1$ for $\beta \in E^+$, the zero term along $L_\beta$ of $f_z$ is $P(\iota\beta + z)$. Unfolding the integral over the fundamental domain into the sum over $\beta$, which is legitimate since the zero terms have summable norms, gives that $P$ is integrable and
$$\int P = \sum_\beta \mathrm{ev}_{L_\beta}\Big(\int_{\Omega\times\mathfrak{d}^{-1}_{\mathrm{sa}}} f_z\, dz\Big).$$
Let $g = |D_E|^{1/4}\int_{\Omega\times\mathfrak{d}^{-1}_{\mathrm{sa}}} f_z\,dz$. By the lemma on the fundamental domain at $\beta = \xi^*\xi - \alpha$, the Schrödinger function of $\omega(1, h) g$ at a rational $\xi$ is $\sigma_h(\xi)$, and at $0$ it is $0$ since $\alpha \ne 0$. Apply the one vector formula to $g$. $\square$

### The Gaussian at infinity

**Lemma (A Gaussian datum).** For every Schwartz-Bruhat function $\Phi_0$ on $(\mathbb{A}_{E,f})^\kappa$ there is a vector $f$ with Schrödinger function
$$\Psi(x) = \exp\Big(-\sum_{v \mid \infty} (x^*x)_v\Big)\, \Phi_0(x_f).$$

Lean: `New.SiegelWeil.exists_mixedValue_eq_gaussian_mul` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* It is enough to treat the indicator of one coset $z + u\widehat{\mathcal{O}}^\kappa$. A Heisenberg translate of $\omega(g)$ applied to the vacuum, for an adapted element $g$ of a scalar that is $u^{-1}$ at the finite places up to a constant, has the required Schrödinger function up to a constant. $\square$

**Lemma (Laplace's integral for $1/\Gamma$).** For an integer $k \ge 1$ and real $x \ge 0$,
$$\int_{\mathbb{R}} e^{2\pi i x z}\, (1 + 2\pi i z)^{-(k+1)}\, dz = \frac{x^k e^{-x}}{k!}.$$
For $n \ge 2$ and $a \ge 0$,
$$\int_{\mathbb{R}} e^{2\pi i a t} \Big(\int_{\mathbb{C}} e^{-(1 + 2\pi i t)|w|^2}\, dw\Big)^n dt = \frac{\pi^n}{(n-1)!}\, a^{n-1} e^{-a}.$$

Lean: `New.integral_fourierChar_mul_inv_pow`, `New.integral_fourierChar_mul_gaussian_pow` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The function $(1 + 2\pi i z)^{-(k+1)}$ is the Fourier transform of $t^k e^{-t}/k!$ on $t > 0$, and it is integrable since $k + 1 \ge 2$. Fourier inversion gives the first formula. The Gaussian integral is $\pi(1 + 2\pi i t)^{-1}$, so the first formula with $k = n - 1$ gives the second. $\square$

**Definition (Norm density).** For a function $\Phi_0 \ge 0$ on $(\mathbb{A}_{E,f})^\kappa$ and a finite adele $\alpha$,
$$\delta(\Phi_0, \alpha) = \int_{z} \int_{x} \psi_f\big(\tfrac12\, z\, (x^*x - \alpha)\big)\, \Phi_0(x)\, dx\, dz,$$
where $z$ runs over the self-adjoint finite adeles, with the measure that gives $\mathfrak{d}^{-1}_{\mathrm{sa}}$ the volume $1$, and each coordinate of $x$ has the measure that gives $\widehat{\mathcal{O}}$ the volume `volÔ E`.

Lean: `New.normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

**Remark (Formalization).** The norm density is a Bochner integral in $z$. If the inner integral is not integrable in $z$, the Lean value is $0$. The class sum theorem below holds with this Lean value in all cases.

**Lemma (Fubini at the infinite places).** For $\Phi_0$ locally constant and $z = (z_\infty, z_f)$, the integral over $x \in \mathbb{A}_E^\kappa$ of the Gaussian times $\Phi_0(x_f)$ times $\psi(\frac12 z(x^*x - \alpha))$ is
$$\prod_{v \mid \infty} e^{2\pi i\, \alpha_v z_v}\Big(\int_{\mathbb{C}} e^{-(1 + 2\pi i z_v)|w|^2}\, dw\Big)^{\mathrm{card}\,\kappa} \cdot \int_x \psi_f\big(\tfrac12 z_f(x^*x - \alpha)\big)\Phi_0(x)\, dx,$$
where $\alpha_v$ is the real part of the embedding of $\alpha$ at $v$ given by the CM type.

Lean: `New.integral_gaussian_mul_stdAddChar` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

### Class sums

For a level $K$, an open subgroup of the stabilizer $K_0$ of $\widehat{\mathcal{O}}^\kappa$, the class sum `New.classSum` of a function $c$ is the sum over the double cosets $U(T)(E)\backslash U(T)(\mathbb{A}_f)/K$ of $c(g)/\#(\Gamma \cap gKg^{-1})$. Section 8 defines the mass from it.

**Lemma (Class sums are integrals).** Let $c$ on $U(T)(\mathbb{A}_f)$ be right invariant under $K$ and, read on the adelic group, left invariant under the rational points. Then
$$\mathrm{classSum}_K(c) = [K_0 : K] \int_{[U(T)]} c\, dh.$$

Lean: `New.classSum_eq_mul_integral`, `New.classSum`, `New.stdLevelIndex` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean; Lib/Adelic/Hecke/Basic.lean; Lib/Adelic/Unitary/Defs.lean).

**Theorem (Siegel's formula for vectors of one norm).** Let $n = \mathrm{card}\,\kappa \ge 3$, let $K$ be a level, and let $\Phi_0 \ge 0$ be locally constant, $K$-invariant and of compact support. Let $\alpha \in E^+$ be totally positive. For $h \in U(T)(\mathbb{A}_f)$, let $\sigma_h(x) = \Phi_0(h^{-1}x)$ if $x \in E^\kappa$ has $x^*x = \alpha$, and $0$ otherwise. Then $\sigma_h$ is summable, and
$$\mathrm{classSum}_K\Big(\sum_x \sigma_h(x)\Big) = \mathrm{classSum}_K(1)\, |D_E|^{1/4} \prod_{v\mid\infty} \frac{\pi^n\, \alpha_v^{\,n-1}}{(n-1)!} \cdot \delta(\Phi_0, \alpha).$$

Lean: `New.classSum_eq_mul_normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Apply the Fourier coefficient theorem to the Gaussian datum for $\Phi_0$, with $P$ given by the Fubini lemma. On the vectors of norm $\alpha$ the Gaussian is $c = \exp(-\sum_v \alpha_v) \ne 0$. The integral of $P$ is the product of the Laplace integrals at $a = \alpha_v > 0$, which is $c$ times the archimedean factor, times $\delta(\Phi_0, \alpha)$. Cancel $c$. The lemma on class sums turns both integrals into class sums with the same index $[K_0 : K]$. $\square$

The classical form is the quotient.

**Remark (Formalization).** The source proves the formula only for the form $x^*x$, the level $K \le K_0$ and weights $\Phi_0 \ge 0$. The finite factor is left as the integral $\delta(\Phi_0, \alpha)$, without a product over places. The factor $|D_E|^{1/4}$ comes from the measure on the adeles of $E^+$. The hypothesis $\mathrm{card}\,\kappa \ge 3$ enters twice: as Weil's range $2p < m$ with $p = 1$, and in the Laplace lemma through $n \ge 2$. The users of the formula are [the main term](/chapter/main-term/) and Section 8.
