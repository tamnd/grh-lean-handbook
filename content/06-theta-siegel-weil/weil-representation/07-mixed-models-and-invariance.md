---
title: Mixed models and Weil's invariance
lean:
  - Lib/Weil/MixedModel/ZeroTerm.lean
  - Lib/Weil/MixedModel/ThetaInvariance.lean
  - Lib/Weil/MixedModel/IsotropicSplitting.lean
  - Lib/Weil/MixedModel/NamedData.lean
decls:
  - New.Space.Splitting.zeroTerm
  - New.Space.Splitting.slice
  - New.Space.Splitting.isMixedLaw_slice
  - New.Space.Splitting.hasSum_theta_slice
  - New.Space.Splitting.integral_dataInner_slice
  - New.Space.Splitting.zeroTerm_omega_levi
  - New.Space.Splitting.zeroTerm_omega
  - New.Space.Splitting.slice_omega_radicalElement_zero
  - New.Space.Splitting.siegelParabolic
  - New.Space.theta_omega_ratEmbed_of_splitting
  - New.Space.diagonalSplitting
  - New.Space.theta_omega_ratEmbed
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Mixed models and Weil's invariance

This section proves the main theorem of the chapter: the theta functional $\theta_V$ is invariant under the rational points of the unitary group. A splitting of $V$ over a smaller space $V_0$ gives a map from $\mathcal{S}(V)$ to $\mathcal{S}(V_0)$, the zero term, and a family of such maps, the slices. The theta functional of $V$ is a sum over the rational slices, and the Levi subgroup acts on the zero term by a character. On a split space this gives the invariance under two Siegel parabolic subgroups, which generate the rational group. Doubling gives the general case. [Chapter 5](/chapter/siegel-weil/) uses the slices for the Siegel-Weil formula.

Throughout, $V$ is a hermitian space with a point over the CM field $E$ with Weil data, of dimension $n$ and signs $s$, as in [Volume 4](/decl/New.Space/). The group $G = G(E, s)$ acts on $\mathcal{S}(V)$ by the [Weil representation](/decl/New.Space.ω/) $\omega$, and $\varrho(y)$ for $y \in \mathbb{A}^n$ is the Heisenberg operator. We read a vector $f$ as the function $f(y) = \theta_V(\varrho(y) f)$ on $\mathbb{A}^n$.

### Splittings, the zero term and the slices

A [splitting](/decl/New.Space.Splitting/) of $V$ over a space $V_0$ with $p$ columns is a decomposition $V = (l E^p \oplus k E^p) \perp \iota V_0$ over $E$. Here $l$ and $k$ are isotropic frames with $l^* J k = 1$, and $\iota$ is an isometry from $V_0$ that is orthogonal to both frames. The rank satisfies $n = n_0 + 2p$. In adelic coordinates, every $y \in \mathbb{A}^n$ is $y = l a + \iota w + k b$ with $a, b \in \mathbb{A}^p$ and $w \in \mathbb{A}^{n_0}$. Volume 4 gives the [Levi elements](/decl/New.Space.Splitting.levi/) $\mathrm{levi}(a, g_0)$ for $a \in \mathrm{GL}_p(\mathbb{A})$ and $g_0$ in the group of $V_0$, and the [radical elements](/decl/New.Space.Splitting.radicalElement/).

**Definition (Zero term).** Let $D$ be a splitting of $V$ over $V_0$. The zero term is the bounded linear map $\mathrm{ev} \colon \mathcal{S}(V) \to \mathcal{S}(V_0)$ with
$$\mathrm{ev}(f)(y) = \int_{\mathbb{A}^p / E^p} f(\iota y + k b) \, db,$$
where the integral is the mean over the compact quotient. For each $y$ the function $b \mapsto f(\iota y + k b)$ is continuous and periodic under $E^p$, and the mean is a vector of $\mathcal{S}(V_0)$ with norm at most a constant times $\|f\|$.

Lean: `New.Space.Splitting.zeroTerm`, `New.Space.Splitting.exists_zeroTerm`, `New.Space.Splitting.zeroTerm_apply`, `New.Space.Splitting.isContPeriodic_along_k` (Lib/Weil/MixedModel/ZeroTerm.lean).

The function is periodic because $k$ is isotropic and orthogonal to $\iota V_0$. The mean is invariant under translation, so $\mathrm{ev}(\varrho(k x) f) = \mathrm{ev}(f)$ for all $x \in \mathbb{A}^p$. Translation along $\iota$ gives $\mathrm{ev}(\varrho(\iota x) f) = \varrho_0(x)\, \mathrm{ev}(f)$.

**Remark (Formalization).** The zero term is defined by `choose` from the existence theorem. The formula above fixes the chosen map, so the choice has no effect.

**Definition (Slices).** For $x \in \mathbb{A}^p$ the slice at $x$ is the bounded map $f \mapsto f[x] = \mathrm{ev}(\varrho(l x) f)$ from $\mathcal{S}(V)$ to $\mathcal{S}(V_0)$.

Lean: `New.Space.Splitting.slice`, `New.Space.Splitting.slice_zero` (Lib/Weil/MixedModel/ZeroTerm.lean).

**Proposition (Mixed law).** For $x, a, b \in \mathbb{A}^p$, $w \in \mathbb{A}^{n_0}$ and $f \in \mathcal{S}(V)$,
$$\big(\varrho(l a + \iota w + k b) f\big)[x] = \beta(2x + a, b)\, \varrho_0(w)\, f[x + a],$$
where $\beta$ is the bicharacter of the [adelic Heisenberg datum](/decl/New.adelicHeisenberg/) of $E^1$, so that $\beta(2x + a, b) = \psi(\tfrac12 \jmath\, b^*(2x + a))$.

Lean: `New.Space.Splitting.isMixedLaw_slice`, `New.Space.Splitting.IsMixedLaw` (Lib/Weil/MixedModel/ZeroTerm.lean; Lib/Weil/MixedModel/IsotropicSplitting.lean).

*Proof.* Write $\varrho(l x)\varrho(l a + \iota w + k b)$ as a scalar times $\varrho(k b)\varrho(\iota w)\varrho(l(x + a))$ by the commutation rule of the Heisenberg operators. The scalar is $\beta(2x + a, b)$, since $l$ and $\iota$ are orthogonal and $l^* J k = 1$. Then apply the two translation rules of the zero term. $\square$

This is the law of the mixed Schrödinger model, with $V_0$ in the middle. When $V_0 = 0$ it is the law of the Schrödinger model on functions of $x \in \mathbb{A}^p$.

### Theta as a sum of slices

**Theorem (Theta of the slices).** Let $D$ be a splitting of $V$ over $V_0$ with $p$ columns, and let $f \in \mathcal{S}(V)$. The family $\xi \mapsto \theta_{V_0}(f[\xi])$, $\xi \in E^p$, is summable, and
$$\theta_V(f) = \sum_{\xi \in E^p} \theta_{V_0}(f[\xi]).$$
The sum of the norms $\sum_\xi \|f[\xi]\|$ is finite, and is at most a constant times $\|f\|$. In particular the zero term is not the zero map.

Lean: `New.Space.Splitting.hasSum_theta_slice`, `New.Space.Splitting.summable_norm_slice`, `New.Space.Splitting.tsum_enorm_slice_le`, `New.Space.Splitting.zeroTerm_ne_zero` (Lib/Weil/MixedModel/ZeroTerm.lean).

*Proof.* The function $b \mapsto f(k b)$ is continuous and periodic under $E^p$. Its Fourier coefficient for the character $b \mapsto \beta(b, \xi)^2$ is $\theta_{V_0}(f[\xi])$: commute $\varrho(l \xi)$ past $\varrho(k b)$, and note that $\theta_V$ absorbs $\varrho(l\xi)$ because $l \xi$ is rational. These characters for $\xi \in E^p$ are the dual family of $\mathbb{A}^p / E^p$. With the bound on the norms, Fourier inversion at $b = 0$ gives $f(0) = \theta_V(f)$ as the sum of the coefficients. If the zero term were $0$, then $\theta_V$ and so the vacuum vector would vanish, against $\langle \mathrm{vac}, \mathrm{vac} \rangle \neq 0$. $\square$

**Theorem (Slices and the inner product).** Let $D$ be a splitting of $V$ over $V_0$ with $p$ columns. For $f, f' \in \mathcal{S}(V)$ the function $x \mapsto \langle f[x], f'[x] \rangle_{V_0}$ is integrable on $\mathbb{A}^p$, and there is a constant $C \in \mathbb{C}$ with
$$\int_{\mathbb{A}^p} \langle f[x], f'[x] \rangle_{V_0}\, dx = C \langle f, f' \rangle_V \quad \text{for all } f, f'.$$

Lean: `New.Space.Splitting.integral_dataInner_slice`, `New.Space.Splitting.integrable_dataInner_slice`, `New.Space.Splitting.integrable_slice`, `New.Space.Splitting.continuous_slice` (Lib/Weil/MixedModel/ThetaInvariance.lean).

*Proof.* The integrand is bounded by a constant times $\|f\|\,\|f'[x]\|$, and $x \mapsto f'[x]$ is integrable. By the mixed law, $\varrho(y)$ translates $x$ by the $l$ coordinate of $y$, up to a character of modulus $1$ and a unitary operator on $\mathcal{S}(V_0)$. The Haar measure is invariant under translation, so the form is invariant under the Heisenberg operators. By the [integral form of Schur's lemma](/decl/New.Heisenberg.IsVacuum.form_eq_mul_modelInner/) it is a multiple of the inner product. $\square$

### The Levi subgroup and the zero term

For the rest of the section, $\chi_{\mathbb{A}} = \upsilon |\cdot|^{-1/2}$ is the character of the ideles of $E$ given by the splitting character $\upsilon$ of the Weil data and the idele norm.

**Theorem (Levi law).** Let $D$ be a splitting of $V$ over $V_0$, let $a \in \mathrm{GL}_p(\mathbb{A})$ and let $g_0$ be in the group of $V_0$. For every $f \in \mathcal{S}(V)$,
$$\mathrm{ev}\big(\omega(\mathrm{levi}(a, g_0)) f\big) = \chi_{\mathbb{A}}(\det a)^{-1}\, \omega_0(g_0)\, \mathrm{ev}(f).$$
For the slices, $\omega(\mathrm{levi}(a, g_0)) f$ has slice $\chi_{\mathbb{A}}(\det a)^{-1}\, \omega_0(g_0)\, f[a^* x]$ at $x$.

Lean: `New.Space.Splitting.zeroTerm_omega_levi`, `New.Space.Splitting.exists_zeroTerm_omega_eq_smul`, `New.Space.Splitting.slice_omega_levi`, `New.Space.Splitting.eq_inv_chiAdelic_of_norm_sq_of_phase`, `New.Space.Splitting.exists_hyperbolic_levi_multiplier_nonneg`, `New.chiAdelic` (Lib/Weil/MixedModel/ThetaInvariance.lean; Lib/Weil/Construction/FiniteMultiplier.lean).

*Proof.* Put $g = \mathrm{levi}(a, g_0)$ and $L = \omega_0(g_0)^{-1} \circ \mathrm{ev} \circ \omega(g)$. The family $x \mapsto L \varrho(l x)$ obeys the mixed law, because $\omega(g)\varrho(y)\omega(g)^{-1} = \varrho(g y)$. Take an element $k_1$ adapted to the splitting. At the vector $\omega(k_1)\mathrm{vac}$ both families are multiples of $\|e(x)\|^2$ times the vacuum of $V_0$, where $e$ is the [vacuum function](/decl/New.vacuumFn/). Since the translates of this vector determine a bounded map, $\mathrm{ev}(\omega(g) f) = c\, \omega_0(g_0)\,\mathrm{ev}(f)$ for all $f$. To find $c$, apply the previous theorem to $u = \omega(k_1)\mathrm{vac}$ and $v = \omega(g) u$. The pair $(v, v)$ gives $|c|^2 = |\det a|$, because $g$ changes the variable $x$ by $a^*$ in the integral. The pair $(u, v)$ gives the phase of $c$: in the [space of $p$ hyperbolic planes](/decl/New.hyperbolicSpace/), the multiplier of the Levi element times $\upsilon(\det a)$ is a nonnegative real number. So $c = \chi_{\mathbb{A}}(\det a)^{-1}$. The formula for the slices follows, since $g$ sends $l a^* x$ to $l x$. $\square$

**Theorem (Elements that keep the frame).** Let $D$ be a splitting of $V$ over $V_0$. Let $g \in G$ satisfy $g k = k a$ in adelic coordinates for a $p \times p$ adelic matrix $a$ with $\det a = d$, an idele. Suppose that the $V_0$ block of $g$ is $g_0$. Then for all $f$,
$$\mathrm{ev}(\omega(g) f) = \chi_{\mathbb{A}}(d)^{-1}\, \omega_0(g_0)\, \mathrm{ev}(f).$$

Lean: `New.Space.Splitting.zeroTerm_omega`, `New.Space.Splitting.ActsOnFrame`, `New.Space.Splitting.exists_eq_radicalElement_mul_levi`, `New.Space.Splitting.exists_levi_mul_radicalElement_eq` (Lib/Weil/MixedModel/ThetaInvariance.lean; Lib/Weil/MixedModel/IsotropicSplitting.lean).

*Proof.* An element that keeps the span of $k$ is a radical element times $\mathrm{levi}(a, g_0)$. This is the form for such elements of the [decomposition of Volume 4](/decl/New.Space.Splitting.exists_eq_radicalElement_mul_levi_mul_isAdapted/). The Levi factor acts by the Levi law. A radical element is a commutator of a Levi element and a radical element, so the scalar by which it acts on the zero term is $1$. $\square$

**Proposition (The centre of the radical).** Let $z$ be a hermitian adelic $p \times p$ matrix. The radical element $\mathrm{radicalElement}(0, z)$ fixes $k$ and $\iota$ and sends $l$ to $l - k \jmath^{-1} z$. For all $x \in \mathbb{A}^p$ and $f$,
$$\big(\omega(\mathrm{radicalElement}(0, z)) f\big)[x] = \psi\big(-\tfrac12 x^* z x\big)\, f[x].$$

Lean: `New.Space.Splitting.slice_omega_radicalElement_zero` (Lib/Weil/MixedModel/ThetaInvariance.lean).

*Proof.* The element keeps the frame $k$ with $a = 1$ and acts as $1$ on $V_0$, so by the previous theorem it fixes the zero term. It sends $l x + k \jmath^{-1} z x$ to $l x$. Write $\varrho(l x)$ as a character times $\varrho(k \jmath^{-1} z x)$ times the image of $\varrho(l x)$, and use $\mathrm{ev}\circ\varrho(k b) = \mathrm{ev}$. The character is $\psi(-\tfrac12 x^* z x)$. $\square$

When $V_0 = 0$ these are the classical formulas for the Siegel parabolic subgroup in the Schrödinger model.

**Remark (Formalization).** The vectors of $\mathcal{S}(V)$ are integrable coefficients against the vacuum, not Schwartz-Bruhat functions. When $V_0 = 0$ the map $x \mapsto f[x]$ plays the part of a vector of the Schrödinger model on $\mathbb{A}^p$. The source does not state this identification, and it does not use the space $L^2(\mathbb{A}^p)$. The formulas for the parabolic subgroup are proved from the vacuum normalization, not taken as a definition. The operators $\mathrm{schrodingerOp}(S)$ of finite Schwartz-Bruhat functions use `choose` for a generalized inverse (finding F-050). They do not enter this section. The hypothesis structure `ScalesTranslations` of finding F-083 belongs to [Chapter 3](/chapter/theta-lifts-seesaw/).

Lean: `New.Space.schrodingerOp` (Lib/Weil/MixedModel/NamedData.lean).

### Weil's invariance

**Definition (Siegel parabolic subgroup).** Let $D$ be a splitting of $V$ with no middle part, that is $V_0 = 0$. Its Siegel parabolic subgroup is the subgroup of the rational unitary group $U(J)$ of the elements $\gamma$ with $\gamma k = k a$ for some $a \in \mathrm{GL}_p(E)$. The opposite parabolic subgroup is that of the splitting with $k$ and $l$ exchanged. The two subgroups generate $U(J)$.

Lean: `New.Space.Splitting.siegelParabolic`, `New.Space.Splitting.siegelParabolic_sup_symm_eq_top` (Lib/Weil/MixedModel/IsotropicSplitting.lean).

**Theorem (Invariance on a split space).** Suppose that $V$ has a splitting $D$ with no middle part. Then $\theta_V(\omega(\gamma) f) = \theta_V(f)$ for every $\gamma \in U(J)$ and every $f \in \mathcal{S}(V)$, where $\gamma$ acts through its [embedding in $G$](/decl/New.Space.ratEmbed/).

Lean: `New.Space.theta_omega_ratEmbed_of_splitting`, `New.Space.theta_omega_ratEmbed_of_mul_k`, `New.Space.thetaStabilizer` (Lib/Weil/MixedModel/ThetaInvariance.lean).

*Proof.* The elements $\gamma$ with $\theta_V \circ \omega(\gamma) = \theta_V$ form a subgroup. Since the two opposite parabolic subgroups of $D$ generate $U(J)$, it is enough that this subgroup contains the Siegel parabolic subgroup of every splitting without middle part. So let $\gamma k = k a$ with $a \in \mathrm{GL}_p(E)$. Let $D'$ be the splitting $\gamma D$, with frames $\gamma l$ and $\gamma k$. Since $\gamma$ keeps the span of $k$, $D'$ and $D$ have the same zero term. By the theorem on elements that keep the frame, $\omega(\gamma)$ changes the zero term by $\chi_{\mathbb{A}}(\det a)^{-1}$. This is $1$: $\det a$ is in $E^\times$, the splitting character is trivial on $E^\times$, and the idele norm is $1$ on $E^\times$ by the product formula. With $\omega(\gamma)\varrho(y)\omega(\gamma)^{-1} = \varrho(\gamma y)$ this gives $(\omega(\gamma) f)[x]_{D'} = f[x]_D$ for all $x$. Now expand $\theta_V(\omega(\gamma) f)$ along $D'$ and $\theta_V(f)$ along $D$ by the theorem on the theta of the slices. The terms agree, so the sums agree. $\square$

**Definition (Diagonal splitting).** Let $V^-$ be the space of the negative form $-J$. The space $V \oplus V^-$ has the splitting without middle part with frames
$$k = \begin{pmatrix} 1 \\ 1 \end{pmatrix}, \qquad l = \begin{pmatrix} \tfrac12 J^{-1} \\ -\tfrac12 J^{-1} \end{pmatrix},$$
so $k$ spans the diagonal $\{(v, v)\}$ and $l$ spans the antidiagonal $\{(v, -v)\}$.

Lean: `New.Space.diagonalSplitting` (Lib/Weil/MixedModel/ThetaInvariance.lean).

**Theorem (Weil's invariance).** For every $\gamma$ in the rational unitary group $U(J)$ of $V$ and every $f \in \mathcal{S}(V)$,
$$\theta_V\big(\omega(\gamma) f\big) = \theta_V(f).$$
Consequently a rational point acts on a vector, read as a function, by substitution: $(\omega(\gamma) f)(y) = f(\gamma^{-1} y)$ for $y \in \mathbb{A}^n$.

Lean: `New.Space.theta_omega_ratEmbed`, `New.Space.exists_theta_boxProd_eq_mul`, `New.Space.exists_theta_boxProd_ne_zero`, `New.Space.omega_ratEmbed_apply` (Lib/Weil/MixedModel/ThetaInvariance.lean).

*Proof.* Put $W = V \oplus V^-$. For a vector $y$ of $V^-$, the functional $f \mapsto \theta_W(f \boxtimes y)$ on $\mathcal{S}(V)$ is invariant under the rational Heisenberg operators of $V$, which act as $\varrho(x, 0)$ on $W$. By the [uniqueness of the theta functional](/decl/New.Space.IsThetaFunctional.eq_smul/) it is $c\,\theta_V$ for a constant $c$. The functional $\theta_W$ does not vanish on all products: otherwise every theta function of $\mathrm{vac} \boxtimes \mathrm{vac}$, the vacuum of $W$, would vanish. Choose $f_0$ and $y$ with $\theta_W(f_0 \boxtimes y) \ne 0$. Then $c \ne 0$. The element $(\gamma, 1)$ is a rational point of the group of $W$, and $\omega_W(\gamma, 1)(f \boxtimes y) = \omega(\gamma) f \boxtimes y$. The space $W$ has the diagonal splitting, so the theorem for split spaces gives
$$c\,\theta_V(\omega(\gamma) f) = \theta_W\big(\omega_W(\gamma, 1)(f \boxtimes y)\big) = \theta_W(f \boxtimes y) = c\,\theta_V(f).$$
Cancel $c$. For the consequence, apply the invariance to $\varrho(y) f$ and use $\omega(\gamma)\varrho(y) = \varrho(\gamma y)\omega(\gamma)$. $\square$

Section 6 uses the theorem for the [normalization](/decl/New.Space.theta_eq_theta_omega/) of $\theta_V$.

**Remark (Formalization).** The doubling uses only that $V \oplus V^-$ is split, so the theorem holds for anisotropic $V$ too. It is one case of Weil's theorem, for the unitary group of a hermitian space with a point and the representation $\omega$ built from the vacuum. The source states no metaplectic group: by Sections 4 and 5 the cocycle of $\omega$ is $1$, so $\omega$ is a representation of $G$ itself.
