---
title: Haar measures on the unipotent groups
lean:
  - Lib/DiscreteSeries/Bessel/Basic.lean
  - Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean
  - Lib/Adelic/QuotientMeasure/Basic.lean
decls:
  - New.Shape.G₁
  - New.RealPlace.unipotentOf
  - New.RealPlace.mem_besselU0_iff_unipotentOf
  - New.Shape.besselHaar₀
  - New.Shape.besselHaar
  - New.RealPlace.measurePreserving_freeEntries_besselHaar₀
  - New.RealPlace.measurePreserving_freeEntries_besselHaar
  - New.RealPlace.IsUnimodularHaar
  - New.RealPlace.IsUnimodularHaar.of_freeEntries
  - New.RealPlace.exists_dilation
  - New.RealPlace.eichlerMatrix_mul
  - New.RealPlace.homogeneousBall
  - New.RealPlace.besselHaar₀_homogeneousBall
  - New.RealPlace.IsTube
  - New.RealPlace.exists_tube
  - New.besselQuotMeasure
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Haar measures on the unipotent groups

From this section on the group is real. The integrals in the unfolding of Poincaré series are over $\mathsf U$, over its subgroup $\mathsf U^0$ that fixes the frame, and over the quotient $\mathsf U \backslash G_1$. This section gives explicit coordinates on $\mathsf U^0$ and $\mathsf U$, defines the two measures as images of Lebesgue measure, and proves that they are two-sided Haar measures. Then it defines balls in $\mathsf U^0$ with a homogeneous volume, and tubes: compact sets that meet each orbit of $\mathsf U^0$ in a controlled measure. The last part defines the measure on $G_1$ that computes integrals over $\mathsf U \backslash G_1$.

### The real group

**Definition.** Let $G_1$ be the unitary group of the complex hermitian form $J_1$ with basis $e_a, x_i, z, e^*_a$, where $h(e_a, e^*_b) = \delta_{ab}$, $h(x_i, x_j) = \delta_{ij}$, $h(z, z) = -1$, and all other products of basis vectors are $0$. This is the form $J_T$ for $A = \mathbb C$ and $T = \operatorname{diag}(1_\kappa, -1)$.

Lean: `New.Shape.G₁` (Lib/DiscreteSeries/Bessel/Basic.lean).

So $G_1 \cong U(\varrho + k, \varrho + 1)$. Write $X$, $W$, $D$ for the matrices whose columns are the $e_a$, the $x_i$ and the $e^*_a$. Then $J_1 = X D^* + D X^* + W W^* - z z^*$, and the columns are orthonormal for the standard inner product of $\mathbb C^r$, with $r = 2\varrho + k + 1$. Norms of matrices are operator norms for this inner product.

### Coordinates on $\mathsf U^0$

An element of $\mathsf U^0$ fixes $e_0, \dots, e_{\varrho - 1}$ and $z$, and it is unitriangular for the levels. So it sends $x_i$ to $x_i$ plus a combination of the $e_a$, and $e^*_b$ to $e^*_b$ plus a combination of the $x_i$ and the $e_a$. It is an Eichler transformation with matrix entries.

**Proposition.** For a complex $k \times \varrho$ matrix $\omega$ and a complex $\varrho \times \varrho$ matrix $\mu$, let $E(\omega, \mu) = 1 + X\omega^* W^* - W\omega D^* - X\mu D^*$. Then
$$E(\omega, \mu)\, E(\omega', \mu') = E(\omega + \omega', \ \mu + \mu' + \omega^*\omega').$$

Lean: `New.RealPlace.eichlerMatrix_mul` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* Multiply out. Since $X^* X = 1$, $W^* W = 1$, $D^* D = 1$ and the other products of two different column matrices are $0$, the only product of two non-identity terms that survives is $X\omega^* W^* \cdot (-W\omega' D^*) = -X\omega^*\omega' D^*$. The other products contain one of $W^* X$, $D^* X$, $D^* W$, which are $0$. $\square$

The matrix $E(\omega, \mu)$ is an isometry if and only if $\mu + \mu^* = \omega^* \omega$. So the hermitian part of $\mu$ is fixed by $\omega$, and only the skew-hermitian part is free. The source parametrises this part by a real matrix.

**Definition.** For $y \in M_\varrho(\mathbb R)$ let $\operatorname{sk}(y)$ be the skew-hermitian matrix with entries $\operatorname{sk}(y)_{aa} = i\, y_{aa}$ and $\operatorname{sk}(y)_{ab} = ((1+i) y_{ab} - (1-i) y_{ba})/\sqrt2$ for $a \ne b$ (Lean: `New.skewOfReal`). For $q = (\alpha, b)$ with $\alpha \in M_{\varrho \times k}(\mathbb C)$ and $b \in M_\varrho(\mathbb R)$, put
$$u(q) = 1 + X\alpha W^* - W\alpha^* D^* + X\big(\operatorname{sk}(b) - \tfrac12 \alpha\alpha^*\big) D^*.$$
This is $E(\omega, \mu)$ with $\omega = \alpha^*$ and $\mu = \frac12\alpha\alpha^* - \operatorname{sk}(b)$.

Lean: `New.RealPlace.unipotentOf` (Lib/DiscreteSeries/Bessel/Basic.lean).

The factor $\sqrt2$ makes $(y_{ab}, y_{ba}) \mapsto (\operatorname{Re}, \operatorname{Im})$ of $\operatorname{sk}(y)_{ab}$ an orthogonal map, so Lebesgue measure in $b$ is Lebesgue measure in the free entries of $\operatorname{sk}(b)$.

**Theorem.** An element $u \in G_1$ lies in $\mathsf U^0$ if and only if $u = u(q)$ for some $q$.

Lean: `New.RealPlace.mem_besselU0_iff_unipotentOf` (Lib/DiscreteSeries/Bessel/Basic.lean).

*Proof.* The element $u(q)$ fixes $X$ and $z$, and its nonzero entries off the diagonal are at $(e_a, x_i)$, $(x_i, e^*_b)$ and $(e_a, e^*_b)$, which are above the level diagonal. So $u(q) \in \mathsf U^0$. Conversely let $u \in \mathsf U^0$. The columns $B = u D$ are dual to the frame and span an isotropic space. Read $\alpha$ from the rows of $B$ at the $x_i$, and $b$ from the skew-hermitian part of the rows at the $e_a$. Isotropy says that the hermitian part of these rows is $-\frac12 \alpha\alpha^*$. So $u(q)^{-1} u$ fixes the frame and the $e^*_a$, and it lies in $\mathsf U^0$. An element of $H$ acts only on the span of the $x_i$, and in $\mathsf U$ the block on the $x_i$ is the identity, since the $x_i$ have the same level. So $u(q)^{-1} u = 1$. $\square$

**Definition.** The measure $\nu^0$ on $\mathsf U^0$ is the image of Lebesgue measure on $M_{\varrho \times k}(\mathbb C) \times M_\varrho(\mathbb R)$ under $q \mapsto u(q)$. The measure $\nu$ on $\mathsf U$ is the image of the product of Lebesgue measure on $\mathbb C^{n(n-1)/2}$ and $\nu^0$ under $(x, u) \mapsto u \cdot \ell(x)$. Here $\ell(x)$ is an explicit element of $\mathsf U$ that fixes the $x_i$ and acts on the frame by the unitriangular $n \times n$ matrix with entries $x$ above the diagonal (Lean: `New.RealPlace.liftUnitriangular`).

Lean: `New.Shape.besselHaar₀` (Lib/DiscreteSeries/Bessel/Basic.lean).

Lean: `New.Shape.besselHaar` (Lib/DiscreteSeries/Bessel/Basic.lean).

### Free entries

The measures are defined as images. Their invariance is proved in coordinates that are entries of the matrix. For a set $p$ of positions $(a, i)$ with $a < \varrho$, the *free entries* of a matrix $M$ are the complex entries $M_{e_a, i}$ for $(a, i) \in p$, together with the real numbers $\operatorname{Im} M_{e_a, e^*_a}$ for $a < \varrho$ (Lean: `New.RealPlace.freeEntries`). Two sets of positions matter. For $\mathsf U^0$, the set $p_0$ has the columns $x_i$ and the columns $e^*_b$ with $b > a$. For $\mathsf U$, the set $p_1$ has the columns $e_b$ and $e^*_b$ with $b > a$, and every column of the middle block.

**Theorem.** The free entries at $p_0$ carry $\nu^0$ to Lebesgue measure, and the free entries at $p_1$ carry $\nu$ to Lebesgue measure. Both maps are injective on the group.

Lean: `New.RealPlace.measurePreserving_freeEntries_besselHaar₀` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

Lean: `New.RealPlace.measurePreserving_freeEntries_besselHaar` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* For $\mathsf U^0$: the entries of $u(q)$ at $(e_a, x_i)$ are $\alpha_{ai}$. The entries at $(e_a, e^*_b)$ for $b > a$ and the imaginary parts on the diagonal are the entries of $\operatorname{sk}(b)$ plus a continuous function of $\alpha$. So the map $q \mapsto$ (free entries) is a linear isometry composed with a shear $(\alpha, b) \mapsto (\alpha, b + c(\alpha))$, and a shear preserves Lebesgue measure by Fubini. For $\mathsf U$ the same argument works after a measurable regrouping of the coordinates into the entries of $\ell(x)$ on the frame and the free entries of $u$. Injectivity on $\mathsf U^0$ holds because $q \mapsto u(q)$ is a bijection onto $\mathsf U^0$ and the shear is injective. For $\mathsf U$, let $u$ and $v$ have the same free entries. Right multiplication by $v^{-1}$ acts on the free entries by a bijection, so $w = uv^{-1}$ has the free entries of $1$. The entries of the frame columns above the level diagonal are free entries, so $w$ fixes the frame and lies in $\mathsf U^0$. The free positions of $\mathsf U^0$ are among those of $\mathsf U$, so $w = 1$ (Lean: `New.RealPlace.injective_freeEntries_besselU`). $\square$

The real dimension of $\mathsf U^0$ is $2\varrho k + \varrho^2$: $2\varrho k$ for $\alpha$, $\varrho(\varrho - 1)$ for the entries above the diagonal of $\operatorname{sk}(b)$, and $\varrho$ for its diagonal.

### Two-sided Haar measures

**Definition.** A measure on a subgroup $S$ of $G_1$ is *unimodular Haar* if it is a left Haar measure, it is right invariant and inversion invariant, it is $\sigma$-finite, and the action of $S$ on $G_1$ by left multiplication has a cutoff: a measurable function $\beta \ge 0$ on $G_1$ with $\int_S \beta(sy)\, d\nu(s) = 1$ for all $y$.

Lean: `New.RealPlace.IsUnimodularHaar` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

The cutoff is the device of [quotients and reduction theory](/chapter/reduction-theory/) for integrals over $S \backslash G_1$ (see [IsCutoff](/decl/New.IsCutoff/)).

**Proposition (Dilations).** For every $T \ge 1$ there is $d \in G_1$ with $(d^{-1} u d)_{ij} = T^{\operatorname{level} i - \operatorname{level} j} u_{ij}$ for all $u \in G_1$ and all $i, j$, and with $\|d^{-1} u d\| \le 1 + r^2 \|u\| / T$ for all $u \in \mathsf U$.

Lean: `New.RealPlace.exists_dilation` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* Let $d$ be diagonal with entry $T^{\varrho - \operatorname{level} i}$ at $i$. The exponents at $e_a$ and $e^*_a$ are $\varrho - a$ and $a - \varrho$, so $d^* J_1 d = J_1$. For $u \in \mathsf U$ the entries of $d^{-1}ud - 1$ vanish when $\operatorname{level} j \le \operatorname{level} i$, and otherwise they are $u_{ij}$ times a power $T^{-m}$ with $m \ge 1$. So each entry of $d^{-1}ud - 1$ has absolute value at most $\|u\|/T$, and a matrix with entries bounded by $c$ has operator norm at most $r^2 c$. $\square$

**Theorem.** Let $S \le \mathsf U$ be a subgroup of $G_1$ defined by the condition that the entries at a set $P$ of positions agree with those of $1$, and let the Bessel subgroup normalise $S$. Let $p$ be the set of positions $(a, i)$ with $(e_a, i) \notin P$ and $\operatorname{level} i < 2\varrho - a$. If the free entries at $p$ are injective on $S$ and carry a measure $\nu_S$ to Lebesgue measure, then $\nu_S$ is unimodular Haar.

Lean: `New.RealPlace.IsUnimodularHaar.of_freeEntries` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* The group $S$ is closed, so it is locally compact and has a left Haar measure $\lambda$. First, conjugation by $s \in S_{\mathrm{Bes}}$, the Bessel subgroup, preserves $\lambda$. It scales $\lambda$ by a factor $\chi(s) > 0$, and $\chi$ is a homomorphism to a commutative group. Write $s = uh$ with $u \in \mathsf U$ and $h \in H$. Take the dilation $d$ with $T = \|u\|$. It normalises $S$ and commutes with $h$, so $\chi(s) = \chi(h \cdot d^{-1}ud)$, and $h \cdot d^{-1}ud$ has norm at most $C = 1 + r^2$. So the supremum $b$ of $\chi(t)\lambda(\text{ball of radius } 2)$ over $t$ in the Bessel subgroup is finite and positive. Left multiplication by $s$ permutes the Bessel subgroup, so $\chi(s) b = b$ and $\chi(s) = 1$. Since $S$ lies in the Bessel subgroup, $\lambda$ is right invariant. Second, right multiplication by $g \in S$ acts on the free entries by a volume preserving map, so $\nu_S$ is right invariant. By uniqueness of Haar measure $\nu_S = c\lambda$. The integral of a Gaussian in the free entries is $1$, so $c \ne 0, \infty$. A unimodular Haar measure is inversion invariant. A closed subgroup acts properly on $G_1$, and a proper action has a cutoff. $\square$

**Corollary.** The measures $\nu^0$ on $\mathsf U^0$ and $\nu$ on $\mathsf U$ are unimodular Haar.

Lean: `New.RealPlace.isUnimodularHaar_besselHaar₀` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* Apply the theorem with $p_0$ and $p_1$. The Bessel subgroup normalises $\mathsf U^0$ and $\mathsf U$ by Section 3 and Section 2. $\square$

**Remark (Formalization).** The statement for $\nu$ on $\mathsf U$ is an instance without a name in [UnipotentHaarMeasure.lean](lean:Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean#L626). It applies the same theorem. Every Haar measure on $G_1$ is $\sigma$-finite (Lean: `New.sigmaFinite_G₁`), which the integrals over $G_1$ use.

### Homogeneous balls

For $u \in \mathsf U^0$ write $u = E(\omega(u), \mu(u))$ (Lean: `New.RealPlace.eichlerVectors`, `New.RealPlace.eichlerScalars`). The vector part has degree one and the scalar part has degree two, as in a Heisenberg group.

**Definition.** For $\rho \in \mathbb R$ the *homogeneous ball* is $\Omega_\rho = \{u \in \mathsf U^0 : \|\omega(u)\| \le \rho, \ \|\mu(u)\| \le \rho^2\}$.

Lean: `New.RealPlace.homogeneousBall` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

By the group law, $\Omega_\rho \Omega_{\rho'} \subset \Omega_{\rho + \rho'}$, since $\rho^2 + \rho'^2 + \rho\rho' \le (\rho + \rho')^2$ (Lean: `New.RealPlace.mul_mem_homogeneousBall`). An element of $\mathsf U^0$ of norm at most $t$ lies in $\Omega_t$, and an element of $\Omega_\rho$ has norm at most $(1 + \rho)^2$.

**Theorem.** For $\rho > 0$,
$$\nu^0(\Omega_\rho) = \rho^{2\varrho(k + \varrho)}\, \nu^0(\Omega_1).$$

Lean: `New.RealPlace.besselHaar₀_homogeneousBall` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* In the parameters $q = (\alpha, b)$ we have $\omega = \alpha^*$ and $\mu = \frac12\alpha\alpha^* - \operatorname{sk}(b)$. The linear map $(\alpha, b) \mapsto (\rho\alpha, \rho^2 b)$ sends $u(q)$ to the element with $(\rho\omega, \rho^2\mu)$, so it maps $\Omega_1$ onto $\Omega_\rho$. Its determinant on the real vector space of dimension $2\varrho k + \varrho^2$ is $\rho^{2\varrho k} \rho^{2\varrho^2} = \rho^{2\varrho(k+\varrho)}$. $\square$

The ball $\Omega_\rho$ has positive measure for $\rho > 0$, since it is a neighbourhood of $1$, and it is compact. A consequence used below: $\nu^0(\Omega_{r^2 t + t}) \le 3\, \nu^0(\Omega_{r^2 t})$ for $t > 0$, since $(1 + r^{-2})^{2\varrho(k+\varrho)} \le (1 + r^{-2})^{r^2} \le e < 3$ (Lean: `New.RealPlace.besselHaar₀_homogeneousBall_add_le`).

### Tubes

**Definition.** Let $T \in \mathbb R$, $B \subset G_1$ and $\Omega \subset \mathsf U^0$. The set $B$ is a *tube of size $T$ with base $\Omega$* if $B$ is compact, $\Omega$ is measurable with $0 < \nu^0(\Omega) < \infty$, every $y \in B$ has $\|y\| \le T^{10}$, $uy \in B$ for all $u \in \Omega$ and all $y$ with $\|y\| \le T$, and for every $y \in G_1$
$$\nu^0\{u \in \mathsf U^0 : uy \in B\} \le 3\, \nu^0(\Omega).$$

Lean: `New.RealPlace.IsTube` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

**Theorem.** If $T \ge 8r$, there are $B$ and $\Omega$ such that $B$ is a tube of size $T$ with base $\Omega$.

Lean: `New.RealPlace.exists_tube` (Lib/DiscreteSeries/Bessel/UnipotentHaarMeasure.lean).

*Proof.* Let $\rho = r^2 T^2$, $\Omega = \Omega_\rho$ and $B = \Omega \cdot \{y : \|y\| \le T\}$. The set $B$ is compact as a product of compact sets. For $y \in B$, $\|y\| \le (1 + \rho)^2 T$, and $1 + \rho \le (8r)^2 T^2 \le T^4$, so $\|y\| \le T^9 \le T^{10}$. For the slices let $u_1 y = s z$ with $s \in \Omega$ and $\|z\| \le T$, and put $g = s^{-1} u_1$, so $z = g y$. For any $v$ in the slice, $vy = s' z'$ with $s' \in \Omega$ and $\|z'\| \le T$. Then $v g^{-1} = s' z' (gy)^{-1} = s' z' z^{-1}$. The element $z' z^{-1} = s'^{-1} v g^{-1}$ lies in $\mathsf U^0$, and it has norm at most $T^2$, since the inverse of an element of $G_1$ has the same norm. So it lies in $\Omega_{T^2}$. So $v g^{-1} \in \Omega_{\rho + T^2}$. By right invariance the slice has measure at most $\nu^0(\Omega_{\rho + T^2})$, and with $t = T^2$ this is at most $3\nu^0(\Omega_\rho)$. $\square$

The tubes turn a bound on the integral of a function over $\mathsf U^0 \backslash G_1$ into a bound on the integral over a compact set: $\int_{\mathsf U^0} \mathbf 1_B(uy)\, d\nu^0(u) \le 3\nu^0(\Omega)$ for all $y$ (Lean: `New.RealPlace.IsTube.lintegral_indicator_le`).

### The measure on $\mathsf U \backslash G_1$

**Definition.** The measure $\mu_{\mathsf U \backslash G_1}$ on $G_1$ is Haar measure on $G_1$ with the density $\beta_\nu$, where $\beta_\nu$ is a chosen cutoff for the action of $\mathsf U$ with the measure $\nu$.

Lean: `New.besselQuotMeasure` (Lib/DiscreteSeries/Bessel/Basic.lean).

By the results of [quotients and reduction theory](/chapter/reduction-theory/), for a function $F \ge 0$ on $G_1$ that is invariant on the left under $\mathsf U$, the integral $\int_{G_1} F\, d\mu_{\mathsf U \backslash G_1}$ is the integral of $F$ over $\mathsf U \backslash G_1$, and it does not depend on the cutoff (see [lintegral_orbitMeasure_lintegral](/decl/New.lintegral_orbitMeasure_lintegral/)). In particular $\int_{G_1} \int_{\mathsf U} f(uy)\, d\nu(u)\, d\mu_{\mathsf U \backslash G_1}(y) = \int_{G_1} f$ for measurable $f \ge 0$, where $\int_{G_1} f$ is the integral for the Haar measure of $G_1$ that defines $\mu_{\mathsf U \backslash G_1}$.

**Remark (Formalization).** The cutoff is chosen by `Classical.epsilon`. The source defines it as an unspecified function when no cutoff exists. Here a cutoff exists, since $\nu$ is unimodular Haar, so the chosen function is a cutoff (Lean: `New.isCutoff_chosenCutoff`). The measure on $G_1$ depends on this choice, but the integrals of left $\mathsf U$-invariant functions do not. The quotient $\mathsf U \backslash G_1$ is never formed as a space: the source works with this weighted measure on $G_1$ in its place.
