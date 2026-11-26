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

This section applies the Siegel-Weil formula to the smallest case: $S$ is one hyperbolic plane, so $p = 1$, and $T$ is the definite space $E^\kappa$ with the form $x^* x$. The rank of $T$ is at least $3$, which is Weil's range $2 < m$. The theta function then counts vectors, and one Fourier coefficient of the formula counts the vectors of one norm $\alpha$. The result is Siegel's formula for the mean number of representations of $\alpha$ by $x^*x$ over a genus.

### The classical statement

Let $L$ be a positive definite lattice of rank $m$ and $\alpha$ a positive number. Siegel's formula says that the weighted mean of the numbers $r(L_i, \alpha)$ of vectors of norm $\alpha$ over the classes $L_1, \dots, L_h$ of the genus of $L$ is a product of local densities:
$$\frac{\sum_i r(L_i, \alpha)/\#\mathrm{Aut}(L_i)}{\sum_i 1/\#\mathrm{Aut}(L_i)} = \prod_v \beta_v(\alpha),$$
where $\beta_\infty$ is the volume of the sphere of norm $\alpha$ for a suitable measure. Weil obtained it from the Siegel-Weil formula for one vector in *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5. The docstring of the source file names Siegel, Ann. of Math. 36 (1935), and Braun, *Zur Theorie der hermitischen Formen*, Abh. Math. Sem. Hamburg 14 (1941), for the classical form and its hermitian version.

The source states the formula for a CM field, the form $x^*x$ of rank at least $3$, any level and any nonnegative invariant weight $\Phi_0$. It does not evaluate the local densities. It keeps the finite part as one adelic Fourier integral, the density `New.normDensity`. Section 7 bounds that integral.

### The lines of the hyperbolic plane

Let $l, k$ be the standard basis of the hyperbolic plane, and let $\jmath$ be the purely imaginary element of the Weil data. Section 2 showed that the Lagrangians of the plane are the line of $k$ and the lines of $l + \jmath^{-1}\beta k$ for $\beta$ in the totally real subfield $E^+$.

**Definition (Shear splitting).** For $\beta \in E^+$, the splitting `shearSplitting β` of the hyperbolic plane has the isotropic frame $l + \jmath^{-1}\beta k$, the dual frame $k$, and a complement of rank $0$.

Lean: `New.SiegelWeil.shearSplitting` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

The frame is isotropic because $\beta = \bar\beta$ and $\bar\jmath = -\jmath$.

**Lemma (The other line).** A Lagrangian of the hyperbolic plane that is not the line of a shear splitting is the line of $k$, the Lagrangian of `hyperbolicSplitting`.

Lean: `New.SiegelWeil.eq_lagrangian_of_notMem_range_shear` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Let $y \in L$. If the $l$-coordinate $y_l$ of $y$ is not zero, $L$ is the line of $y$, and the isotropy of $y$ says that $\jmath y_k / y_l$ is real. So $L$ is the line of the shear splitting of $\beta = \jmath y_k/y_l$, which is excluded. So every $y \in L$ has $y_l = 0$, and $L$ lies in the line of $k$. Both are Lagrangians, so they are equal. $\square$

Let $\Psi$ be the Schrödinger function of a vector $f$: $\Psi(x)$ is the value `mixedValue` of $f$ at the column $x \in \mathbb{A}_E^\kappa$ for `hyperbolicSplitting`. Let $\psi$ be the standard character `stdAddChar E` of $\mathbb{A}_E$.

**Lemma (Zero terms of the sheared lines).** For $\beta \in E^+$,
$$\mathrm{ev}_{L_\beta}(f) = \int_{\mathbb{A}_E^\kappa} \Psi(x)\, \psi\big(\tfrac12 \beta\, x^* x\big)\, dx,$$
where $L_\beta$ is the line of $l + \jmath^{-1}\beta k$.

Lean: `New.SiegelWeil.zeroTerm_shearSplitting` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The zero term along $L_\beta$ is the theta value of the source term at $0$ of the shear splitting. By the symmetry of Chapter 1, it is the integral over $x$ of the source terms of the opposite splitting. The opposite splitting has first frame $k$, the same as `hyperbolicSplitting`, so the two have the same zero term by `zeroTerm_homSource_congr`. Its $k$-coordinate is the $k$-coordinate of `hyperbolicSplitting` plus $\overline{\jmath^{-1}\beta}$ times the $l$-coordinate. So the source terms differ by the character $\psi(\frac12\beta x^*x)$. $\square$

**Theorem (The Siegel-Weil formula for one vector).** Let $\mathrm{card}\,\kappa \ge 3$. The operator norms of the zero terms $\mathrm{ev}_{L_\beta}$ are summable over $\beta \in E^+$. For every $f$,
$$\int_{[U(T)]} \theta\big(\omega(1, h) f\big)\, dh = \mathrm{vol}([U(T)]) \Big(\Psi(0) + \sum_{\beta \in E^+} \mathrm{ev}_{L_\beta}(f)\Big).$$

Lean: `New.SiegelWeil.siegel_weil_one_vector` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Apply `siegel_weil` with $P$ = `hyperbolicSplitting` and $p = 1$, so $2 < \mathrm{card}\,\kappa$. The map $\beta \mapsto L_\beta$ is injective, since the line determines the slope $\beta$. No $L_\beta$ is the line of $k$. So the sum over all Lagrangians is the zero term of the line of $k$, which is $\Psi(0)$, plus the sum over $\beta$, by the lemma on the other line. $\square$

### One Fourier coefficient

To count vectors of one norm $\alpha$, the source integrates the formula against the character $z \mapsto \psi(-\frac12 z\alpha)$ over the adeles $z$ of $E^+$ modulo $E^+$. This needs a fundamental domain and its volume.

Write a self-adjoint adele of $E$ as a pair $z = (z_\infty, z_f)$ of real components at the infinite places and a self-adjoint finite adele. `New.realAdele z` is the corresponding adele of $E$.

**Lemma (A fundamental domain for $E^+$).** There are an injective additive map $\iota$ from $E^+$ to these pairs, with `realAdele (ι a + z) = a + realAdele z`, and a bounded set $\Omega$ of real components, such that $\Omega \times \mathfrak{d}^{-1}_{\mathrm{sa}}$ is a fundamental domain for $\iota(E^+)$. Here $\mathfrak{d}^{-1}_{\mathrm{sa}}$ is the group `selfAdjointCodifferent E 1` of self-adjoint finite adeles in the inverse different. For self-adjoint $\beta \in E$,
$$|D_E|^{1/4} \int_{\Omega \times \mathfrak{d}^{-1}_{\mathrm{sa}}} \psi\big(\tfrac12\, z\, \beta\big)\, dz = \begin{cases} 1 & \beta = 0, \\ 0 & \beta \ne 0. \end{cases}$$

Lean: `New.exists_isAddFundamentalDomain_realAdele`, `New.exists_fundamentalDomain_real`, `New.realAdele` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The group $\mathfrak{d}^{-1}_{\mathrm{sa}}$ meets $E^+$ in the inverse different of $E^+$, because $E/E^+$ is unramified at the finite places. The set $\Omega$ is a bounded fundamental domain for the real components of that ideal in $\mathbb{R}^{f}$, where $f$ is the number of infinite places. Its volume is $N(\mathfrak{d}^{-1}_{E^+})\sqrt{|D_{E^+}|} = |D_{E^+}|^{-1/2}$, and $|D_E| = D_{E^+}^2$. So the volume is $|D_E|^{-1/4}$, and the set $\mathfrak{d}^{-1}_{\mathrm{sa}}$ has volume $1$ for the chosen measure. For $\beta \in E$ the character $z \mapsto \psi(\frac12 z\beta)$ is trivial on $E^+$, so its integral over the fundamental domain is its integral over the compact quotient of the adeles of $E^+$ by $E^+$. For $\beta \ne 0$ the character is not trivial, and the integral is $0$. $\square$

The constant $|D_E|^{1/4}$ makes the covolume of $E^+$ equal to $1$. The source keeps it explicit.

**Lemma (Unfolding over a fundamental domain).** Let $D$ be a fundamental domain of a countable group $\Gamma$ of translations, enumerated by $e : I \simeq \Gamma$. Let $T_i$ be continuous linear functionals with summable norms, $F$ integrable on $D$, and $P$ measurable with $P(e_i + z) = T_i(F(z))$. Then $P$ is integrable and $\int P = \sum_i T_i\big(\int_D F\big)$.

Lean: `New.integrable_and_integral_eq_tsum_of_fundamentalDomain` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The integral of $\|P\|$ is the sum over $i$ of the integrals over $D$ of $\|T_i(F)\|$, which is at most $\sum_i \|T_i\|\int_D\|F\| < \infty$. The same unfolding for $P$ and the continuity of $T_i$ give the value. $\square$

**Theorem (The Fourier coefficient at $\alpha$).** Let $\mathrm{card}\,\kappa \ge 3$, let $f$ have Schrödinger function $\Psi$, and let $\alpha \in E^+$ be nonzero. Put
$$P(z) = \int_{\mathbb{A}_E^\kappa} \Psi(x)\, \psi\big(\tfrac12\, z\, (x^*x - \alpha)\big)\, dx.$$
Let $\sigma_h(\xi) = \Psi(h^{-1}\xi)$ if $\xi \in E^\kappa$ has $\xi^*\xi = \alpha$, and $0$ otherwise. Then $P$ is integrable, $\sigma_h$ is summable for every $h$, the function $h \mapsto \sum_\xi \sigma_h(\xi)$ is left invariant under the rational points of $U(T)$, and
$$\int_{[U(T)]} \sum_\xi \sigma_h(\xi)\, dh = \mathrm{vol}([U(T)])\, |D_E|^{1/4} \int P(z)\, dz.$$

Lean: `New.SiegelWeil.siegel_weil_fourierCoeff`, `New.star_adeleMatrix_mulVec_dotProduct` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Let $n(z)$ be the unipotent element of $U(S)$ for $z$, and put $f_z = \psi(\frac12 z\alpha)^{-1}\omega(n(z), 1) f$. Its Schrödinger function is $\Psi(x)\psi(\frac12 z(x^*x - \alpha))$. By the lemma on the sheared lines, and since $\psi(\frac12\beta\alpha) = 1$ for $\beta \in E^+$, the zero term along $L_\beta$ of $f_z$ is $P(\iota\beta + z)$. The unfolding lemma, with the summable zero terms of the one vector formula, gives that $P$ is integrable and
$$\int P = \sum_\beta \mathrm{ev}_{L_\beta}\Big(\int_{\Omega\times\mathfrak{d}^{-1}_{\mathrm{sa}}} f_z\, dz\Big).$$
Let $g = |D_E|^{1/4}\int_{\Omega\times\mathfrak{d}^{-1}_{\mathrm{sa}}} f_z\,dz$. An adelic isometry keeps the norm of a rational vector, so the Schrödinger function of $\omega(1, h) g$ at a rational $\xi$ is $\Psi(h^{-1}\xi)$ times the integral of the lemma on the fundamental domain at $\beta = \xi^*\xi - \alpha$. This is $\sigma_h(\xi)$. So the theta value of $\omega(1, h) g$ is $\sum_\xi \sigma_h(\xi)$, and the invariance under rational points is that of the theta function. The value $\Psi_g(0)$ is $0$ because $\alpha \ne 0$. Apply the one vector formula to $g$. $\square$

### The Gaussian at infinity

To obtain numbers, the source takes $\Psi$ to be a Gaussian at the infinite places times a weight $\Phi_0$ at the finite places.

**Lemma (A Gaussian datum).** For every Schwartz-Bruhat function $\Phi_0$ on $(\mathbb{A}_{E,f})^\kappa$ there is a vector $f$ with Schrödinger function
$$\Psi(x) = \exp\Big(-\sum_{v \mid \infty} (x^*x)_v\Big)\, \Phi_0(x_f).$$

Lean: `New.SiegelWeil.exists_mixedValue_eq_gaussian_mul` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The functions $\varphi$ for which the Gaussian times $\varphi$ is a Schrödinger function form a subspace. A Schwartz-Bruhat function is a combination of indicators of cosets of open compact subgroups, so it is enough to treat one coset $z + u\widehat{\mathcal{O}}^\kappa$. Choose an adapted element $g$ for a scalar $t$ that is $u^{-1}$ up to the constant of the Weil data at the finite places and scales the vacuum to the Gaussian at the infinite places. A Heisenberg translate of $\omega(g)$ applied to the vacuum, times a constant, then has the required Schrödinger function, since the vacuum is the indicator of $\widehat{\mathcal{O}}$ at the finite places and a Gaussian at infinity. $\square$

**Lemma (Laplace's integral for $1/\Gamma$).** For an integer $k \ge 1$ and real $x \ge 0$,
$$\int_{\mathbb{R}} e^{2\pi i x z}\, (1 + 2\pi i z)^{-(k+1)}\, dz = \frac{x^k e^{-x}}{k!}.$$
For $n \ge 2$ and $a \ge 0$,
$$\int_{\mathbb{R}} e^{2\pi i a t} \Big(\int_{\mathbb{C}} e^{-(1 + 2\pi i t)|w|^2}\, dw\Big)^n dt = \frac{\pi^n}{(n-1)!}\, a^{n-1} e^{-a}.$$

Lean: `New.integral_fourierChar_mul_inv_pow`, `New.integral_fourierChar_mul_gaussian_pow` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* The function $(1 + 2\pi i z)^{-(k+1)}$ is the Fourier transform of the density $p(t) = t^k e^{-t}/k!$ on $t > 0$, by Laplace's integral $\int_0^\infty t^k e^{-st}\, dt = k!/s^{k+1}$. Since $k + 1 \ge 2$, it is bounded by $(1 + (2\pi z)^2)^{-1}$, so it is integrable, and Fourier inversion at $x$ gives the first formula. For the second, the Gaussian integral is $\pi(1 + 2\pi i t)^{-1}$, and the first formula with $k = n - 1$ applies. $\square$

The second formula says that the sphere $x^*x = a$ in $\mathbb{C}^n$ has mass $\pi^n a^{n-1}/(n-1)!$ for the measure $dx/d(x^*x)$. The hypothesis $n \ge 2$ makes the integral absolutely convergent.

**Definition (Norm density).** For a function $\Phi_0 \ge 0$ on $(\mathbb{A}_{E,f})^\kappa$ and a finite adele $\alpha$,
$$\delta(\Phi_0, \alpha) = \int_{z} \int_{x} \psi_f\big(\tfrac12\, z\, (x^*x - \alpha)\big)\, \Phi_0(x)\, dx\, dz,$$
where $z$ runs over the self-adjoint finite adeles, with the measure that gives $\mathfrak{d}^{-1}_{\mathrm{sa}}$ the volume $1$, and each coordinate of $x$ has the measure that gives $\widehat{\mathcal{O}}$ the volume `volÔ E`.

Lean: `New.normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

**Remark (Formalization).** The norm density is a Bochner integral in $z$. If the inner integral is not integrable in $z$, the Lean value is $0$. The definition does not ask for integrability. The class sum theorem below holds with this Lean value in all cases. Section 8 bounds the integral of the norm of the inner integral for the standard lattice in large rank.

**Lemma (Fubini at the infinite places).** For $\Phi_0$ locally constant and $z = (z_\infty, z_f)$, the integral over $x \in \mathbb{A}_E^\kappa$ of the Gaussian times $\Phi_0(x_f)$ times $\psi(\frac12 z(x^*x - \alpha))$ is
$$\prod_{v \mid \infty} e^{2\pi i\, \alpha_v z_v}\Big(\int_{\mathbb{C}} e^{-(1 + 2\pi i z_v)|w|^2}\, dw\Big)^{\mathrm{card}\,\kappa} \cdot \int_x \psi_f\big(\tfrac12 z_f(x^*x - \alpha)\big)\Phi_0(x)\, dx,$$
where $\alpha_v$ is the real part of the embedding of $\alpha$ at $v$ given by the CM type.

Lean: `New.integral_gaussian_mul_stdAddChar` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

### Class sums

For a level $K$, an open subgroup of the stabilizer $K_0$ of $\widehat{\mathcal{O}}^\kappa$, the class sum `New.classSum` of a function $c$ is the sum over the double cosets $U(T)(E)\backslash U(T)(\mathbb{A}_f)/K$ of $c(g)/\#(\Gamma \cap gKg^{-1})$. The mass `New.mass E l` is the class sum of $1$ for the standard space of rank $l$ and $K = K_0$.

**Lemma (Class sums are integrals).** Let $c$ on $U(T)(\mathbb{A}_f)$ be right invariant under $K$ and, read on the adelic group, left invariant under the rational points. Then
$$\mathrm{classSum}_K(c) = [K_0 : K] \int_{[U(T)]} c\, dh.$$

Lean: `New.classSum_eq_mul_integral`, `New.classSum`, `New.stdLevelIndex` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean; Lib/Adelic/Hecke/Basic.lean; Lib/Adelic/Unitary/Defs.lean).

**Theorem (Siegel's formula for vectors of one norm).** Let $n = \mathrm{card}\,\kappa \ge 3$, let $K$ be a level, and let $\Phi_0 \ge 0$ be locally constant, $K$-invariant and of compact support. Let $\alpha \in E^+$ be totally positive. For $h \in U(T)(\mathbb{A}_f)$, let $\sigma_h(x) = \Phi_0(h^{-1}x)$ if $x \in E^\kappa$ has $x^*x = \alpha$, and $0$ otherwise. Then $\sigma_h$ is summable, and
$$\mathrm{classSum}_K\Big(\sum_x \sigma_h(x)\Big) = \mathrm{classSum}_K(1)\, |D_E|^{1/4} \prod_{v\mid\infty} \frac{\pi^n\, \alpha_v^{\,n-1}}{(n-1)!} \cdot \delta(\Phi_0, \alpha).$$

Lean: `New.classSum_eq_mul_normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean).

*Proof.* Take the vector $f$ of the Gaussian datum for $\Phi_0$ and apply the theorem on the Fourier coefficient at $\alpha$, with $P$ given by the Fubini lemma. On the vectors of norm $\alpha$ the Gaussian is the constant $c = \exp(-\sum_v \alpha_v) \ne 0$. So the left side of the coefficient formula is $c$ times the integral of $\sum_x\sigma_h(x)$. On the right side, the integral of $P$ is the product over $v$ of the integrals of the Laplace lemma with $n \ge 2$ and $a = \alpha_v > 0$, times $\delta(\Phi_0, \alpha)$. Each factor contains $e^{-\alpha_v}$, and their product is $c$. Cancel $c$. The left invariance of the sum follows from the coefficient theorem, and the right invariance under $K$ from the invariance of $\Phi_0$. The lemma on class sums turns both integrals into class sums with the same index $[K_0 : K]$. $\square$

The classical form above is the quotient of the two class sums. The source keeps the product form, which also holds when one does not divide by $\mathrm{classSum}_K(1)$.

**Remark (Formalization).** The source proves the formula only for the form $x^*x$, the level $K \le K_0$ and weights $\Phi_0 \ge 0$. The archimedean factor is computed and the finite factor is left as the integral $\delta(\Phi_0, \alpha)$, without a product over places. The factor $|D_E|^{1/4}$ comes from the normalisation of the measure on the adeles of $E^+$. The hypothesis $\mathrm{card}\,\kappa \ge 3$ enters twice: as Weil's range $2p < m$ with $p = 1$, and in the Laplace lemma through $n \ge 2$. The users of the formula are [the main term](/chapter/main-term/) and Section 8.
