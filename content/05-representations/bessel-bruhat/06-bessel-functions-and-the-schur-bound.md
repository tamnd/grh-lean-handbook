---
title: Bessel functions and the Schur bound
lean:
  - Lib/DiscreteSeries/Bessel/Basic.lean
  - Lib/DiscreteSeries/Bessel/SchurBound.lean
  - Lib/General/Measure/IdempotentKernel.lean
  - Lib/DiscreteSeries/Bruhat/FloorGroups.lean
decls:
  - New.IsBesselFunction
  - New.convolve
  - New.IsBoundedMeasurable
  - New.Filling.besselCharMatrix
  - New.Filling.trace_besselCharMatrix_mul
  - New.Filling.simpleRootSum_inv
  - New.IsBesselFunction.enorm_integral_besselS_mul
  - New.IsBesselFunction.enorm_besselS_mul
  - New.IsBoundedMeasurable.integral_inner_translate
  - New.IsIdempotentKernel.enorm_integral_convolve_sq_le
  - New.IsBoundedMeasurable.lintegral_sq_convolve_convolve_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bessel functions and the Schur bound

A Poincaré series in Theorem B is built from a vector valued function $W$ on the real group $G_1$. The function $W$ transforms on the left by a character of the unipotent group $\mathsf U$ and by a unitary representation of the compact group $H \cong U(k)$. This section defines these functions, shows that the norm $\|W\|$ is invariant on the left under the Bessel subgroup $S = \mathsf U H$, and proves an $L^2$ bound for convolutions of $W$ with integrable functions. The bound is a form of the Schur orthogonality relations. Its input is an idempotent kernel $\psi$ with $W * \psi = W$, and its output has the factor $1/\psi(1)^2$.

### The character of the Bessel subgroup

Recall from Section 2 that $\operatorname{wave}(c) = \exp(c - \bar c) = \exp(2i \operatorname{Im} c)$ for $c \in \mathbb C$, a number of modulus $1$. For $s$ in the unitary group, $\sigma(s) = \sum_{a < \varrho} s_{f_a, f_{a+1}}$ is the sum of the entries of $s$ just above the diagonal of its block on the frame $(f_0, \dots, f_\varrho) = (e_0, \dots, e_{\varrho - 1}, z)$. Section 2 shows that $\sigma$ is additive on $S$ and vanishes on $H$. So $s \mapsto \operatorname{wave}(\sigma(s))$ is a unitary character of $S$. Additivity gives the value at an inverse.

**Lemma.** For $u \in S$, $\sigma(u^{-1}) = -\sigma(u)$.

Lean: `New.Filling.simpleRootSum_inv` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* By additivity $\sigma(u^{-1}) + \sigma(u) = \sigma(u^{-1} u) = \sigma(1)$, and $\sigma(1) = 0$ since $1 \in H$ and $\sigma$ vanishes on $H$. $\square$

The character is the exponential of a trace. This form is used when the character is integrated against a matrix coefficient. Let $J$ be the Gram matrix of the split form, indexed by the basis of the Bessel index set.

**Definition.** The matrix $C$ has the entry
$$C_{yx} = \sum_{a < \varrho} \bigl( [x = e_a][y = f_{a+1}] + [y = e^*_a]\, J_{f_{a+1}, x} \bigr),$$
where $[P]$ is $1$ if $P$ holds and $0$ otherwise, and $f_{a+1}$ is the frame vector after $e_a$.

Lean: `New.Filling.besselCharMatrix` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

**Proposition.** For every $u$ in the unitary group of $J$, over a commutative ring with an involution,
$$\operatorname{tr}(C u) = \sigma(u) + \overline{\sigma(u^{-1})}.$$

Lean: `New.Filling.trace_besselCharMatrix_mul` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* The first summand of $C$ picks the entry $u_{e_a, f_{a+1}}$. The sum of these entries is $\sigma(u)$. The second summand gives $(J u)_{f_{a+1}, e^*_a}$. Since $u$ preserves the form, $J u = (u^{-1})^* J$. The column $e^*_a$ of $J$ has a single entry $1$, in the row $e_a$, so $(J u)_{f_{a+1}, e^*_a} = \overline{(u^{-1})_{e_a, f_{a+1}}}$. The sum of these terms is $\overline{\sigma(u^{-1})}$. $\square$

For $u \in S$ the two lemmas give $\operatorname{tr}(Cu) = \sigma(u) - \overline{\sigma(u)}$, so $\operatorname{wave}(\sigma(u)) = \exp(\operatorname{tr}(C u))$. The proposition itself holds on the whole unitary group, where $\sigma$ is not additive.

### Bessel functions

Let $I$ be a finite set, and let $\rho : U(k) \to U(I)$ be a homomorphism into the unitary $I \times I$ matrices. Let $\iota : U(k) \to G_1$ be the embedding that acts on the definite block and fixes the other basis vectors. Its image is $H$.

**Definition.** A function $F : Z \to X$ on a measurable space, with values in a normed group, is *bounded measurable* if it is strongly measurable and there is a constant $C$ with $\|F(y)\| \le C$ for all $y$.

Lean: `New.IsBoundedMeasurable` (Lib/General/Measure/IdempotentKernel.lean).

**Definition (Bessel function).** A *Bessel function* for $\rho$ is a bounded measurable function $W : G_1 \to \mathbb C^I$ such that

1. $W(ny) = \operatorname{wave}(\sigma(n))\, W(y)$ for $n \in \mathsf U$ and $y \in G_1$;
2. $W(\iota(h) y) = \rho(h) W(y)$ for $h \in U(k)$ and $y \in G_1$.

Lean: `New.IsBesselFunction` (Lib/DiscreteSeries/Bessel/Basic.lean).

The two laws are stated on the generators $\mathsf U$ and $H$ of $S$. The next result shows that they control $W$ on all of $S$, in norm.

**Lemma.** Let $W$ be a Bessel function, $s \in S$, $g \in G_1$, $\beta : G_1 \to \mathbb C$ and $\mu$ a measure on $G_1$. Then
$$\Bigl\| \int \beta(y)\, W(s g y)\, d\mu(y) \Bigr\| = \Bigl\| \int \beta(y)\, W(g y)\, d\mu(y) \Bigr\|.$$

Lean: `New.IsBesselFunction.enorm_integral_besselS_mul` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* By the generation result of Section 2, $s = u\, \iota(h)$ with $u \in \mathsf U$ and $h \in U(k)$. The two laws give $W(u\, \iota(h)\, g y) = \operatorname{wave}(\sigma(u))\, \rho(h) W(gy)$ for every $y$. The scalar and the linear map $\rho(h)$ come out of the integral. The scalar has modulus $1$, and $\rho(h)$ is unitary, so neither changes the norm. $\square$

The equality is one of extended norms. If $\beta W(g \cdot)$ is not integrable, both integrals are $0$ by the convention for Bochner integrals, and the statement still holds.

**Corollary.** For a Bessel function $W$, $s \in S$ and $y \in G_1$, $\|W(sy)\| = \|W(y)\|$.

Lean: `New.IsBesselFunction.enorm_besselS_mul` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* Take $g = y$, $\beta = 1$ and $\mu$ the point mass at $1$ in the lemma. $\square$

So $\|W\|^2$ is a function on $\mathsf U \backslash G_1$, and even on $S \backslash G_1$. Its integral over $\mathsf U \backslash G_1$ is the integral against the measure $\mu_{\mathsf U \backslash G_1}$ of Section 5.

### Convolution and idempotent kernels

From here on $G$ is a locally compact group with a Haar measure, and the measure is invariant on both sides. In the application $G = G_1$.

**Definition.** For $F : G \to E$ with values in a complex Banach space and $x : G \to \mathbb C$,
$$(F * x)(y) = \int_G x(a^{-1})\, F(y a)\, da.$$

Lean: `New.convolve` (Lib/DiscreteSeries/Bessel/Basic.lean).

With $a$ replaced by $y^{-1} a$ this is $\int F(a)\, x(a^{-1} y)\, da$, the usual convolution. The integral is a Bochner integral, so its value is $0$ where the integrand is not integrable.

An [idempotent kernel](/decl/New.IsIdempotentKernel/) is a continuous integrable function $\psi$ on $G$ with $\psi(g^{-1}) = \overline{\psi(g)}$, $\psi(1) \ne 0$ and
$$\int_G \psi(z)\, \psi((zx)^{-1} y)\, dz = \frac{\psi(x^{-1})}{\psi(1)}\, \psi(y)$$
for all $x, y$. At $x = 1$ this is $\psi * \psi = \psi$ ([convolution_self](/decl/New.IsIdempotentKernel.convolution_self/)). The model is $\psi(g) = d_\pi \overline{\langle \pi(g) v, v \rangle}$ for a unit vector $v$ in a discrete series representation $\pi$ with formal degree $d_\pi$. Then $\psi(1) = d_\pi$. The chapter [discrete series through one matrix coefficient](/chapter/discrete-series/) builds such kernels.

### Orthogonality of the translates

Let $S \le G$ be a subgroup with an s-finite inversion invariant measure $\rho_S$ that has a cutoff, and let $\nu$ be the measure on $G$ that integrates left $S$-invariant functions over $S \backslash G$ (Section 5). The next result says that the right translates of $F$ in $L^2(\nu)$ have the same Gram matrix as the right translates of a matrix coefficient.

**Proposition.** Let $F : G \to E$ be bounded measurable and integrable for $\nu$. Let $c : G \to \mathbb C$ have $|c(s)| = 1$ for all $s \in G$, and let $F(sy) = c(s) F(y)$ for $s \in S$ and $y \in G$. Let $\psi$ be an idempotent kernel with $\psi(1) = d$ real and $F * \psi = F$. Then for all $a, b \in G$
$$\int_G \langle F(ya), F(yb) \rangle\, d\nu(y) = \frac{\psi(a^{-1} b)}{d} \int_G \|F(y)\|^2\, d\nu(y).$$

Lean: `New.IsBoundedMeasurable.integral_inner_translate` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* Put $k(g) = \int \langle F(y), F(yg) \rangle\, d\nu(y)$. The integrand $\langle F(y), F(yg)\rangle$ is invariant under $y \mapsto sy$ for $s \in S$, since $|c(s)| = 1$. The measure $\nu$ integrates over $S \backslash G$, and right translation by $a$ preserves this integral. So the left side is $k(a^{-1} b)$. The same shift gives $k(g^{-1}) = \overline{k(g)}$, and $k$ is bounded measurable. The law $F * \psi = F$ in the second slot gives $k(g) = \int \psi(t^{-1}) k(gt)\, dt$. With $k(g^{-1}) = \overline{k(g)}$ and $\psi(g^{-1}) = \overline{\psi(g)}$ it gives $k(g) = \int \psi(t) k(t^{-1} g)\, dt$. Put the second identity into the first and change the order of integration (Fubini). The inner integral is $\int \psi(s) \psi((st)^{-1} g)\, ds = \psi(t^{-1}) \psi(g)/d$. So $k(g) = (\psi(g)/d) \int \psi(t^{-1}) k(t)\, dt = (\psi(g)/d)\, k(1)$. Finally $k(1) = \int \|F\|^2\, d\nu$. $\square$

**Remark (Formalization).** The hypothesis $|c(s)| = 1$ is asked for every $s \in G$, not only for $s \in S$. Only the values on $S$ enter the proof. For a character of $S$, extend it by $1$ outside $S$. The Lean statement uses the Bochner integral of $\|F\|^2$ against $\nu$, which is finite here: $F$ is bounded and integrable for $\nu$.

### Schur's bound in a Hilbert space

The next theorem is abstract. It takes a family $w : G \to E$ of vectors in a Hilbert space whose Gram matrix is $\psi(a^{-1}b)/d$ times a constant, and bounds averages of the vectors $(w * x)(g)$.

**Theorem (Schur's bound).** Let $\psi$ be a bounded idempotent kernel with $\psi(1) = d$, let $x \in L^1(G)$ with $\psi * x = x$, and let $w : G \to E$ satisfy $\langle w(a), w(b) \rangle = \frac{\psi(a^{-1} b)}{d} q$ for all $a, b$, with a real constant $q$. Then for every $z \in L^1(G)$
$$\Bigl\| \int_G z(g)\, (w * x)(g)\, dg \Bigr\|^2 \le \frac{\|(w * x)(1)\|^2}{d} \int_G |z|^2.$$

Lean: `New.IsIdempotentKernel.enorm_integral_convolve_sq_le` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* Let $V$ be the average on the left, and let $\mathcal H$ be the span of the vectors $w(a)$. The Gram law makes $w$ continuous with $\|w(a)\|^2 = q$, so $w * x$ is bounded and the integrals exist. For $u \in \mathcal H$ the coefficient $g \mapsto \langle u, (w * x)(g) \rangle$ is integrable, and the orthogonality relation
$$\int_G |\langle u, (w*x)(g) \rangle|^2\, dg = \frac{\|(w*x)(1)\|^2}{d} \|u\|^2$$
holds. It comes from the Gram law and the identity $\psi * \delta_t * \psi = (\psi(t^{-1})/d)\psi$. Now $\langle u, V \rangle = \int z(g) \langle u, (w*x)(g) \rangle\, dg$. The Cauchy-Schwarz inequality gives
$$|\langle u, V \rangle|^2 \le \int |z|^2 \cdot \frac{\|(w*x)(1)\|^2}{d} \|u\|^2.$$
A vector orthogonal to $\mathcal H$ is orthogonal to each $(w*x)(g)$ and so to $V$. Hence $V$ lies in the closure of $\mathcal H$. The bound for $u \in \mathcal H$ passes to the closure by continuity, and $u = V$ gives $\|V\|^4 \le B \|V\|^2$ with $B$ the constant above. If $\|V\| \ne 0$, cancel $\|V\|^2$. $\square$

In the classical case $w(a) = \pi(a) v$, the relation in the proof is Schur's orthogonality relation for a square integrable representation, and $d$ is the formal degree. Here the relation is proved from the kernel alone.

**Remark (Formalization).** The norms are extended nonnegative reals, and the constant is $\operatorname{ofReal}(\|(w*x)(1)\|^2/d)$. Since $d = \psi(1)$ is real, $d \ge 0$ holds (Lean: `New.IsIdempotentKernel.apply_one_nonneg`), and $d \ne 0$ is part of the definition of a kernel. The integral $\int^- |z|^2$ may be $\infty$, since $z$ is only in $L^1$. Then the bound is empty.

### The bound in $L^2(S \backslash G)$

The two results combine into a bound for a function $F$ on $G$ convolved twice. The first convolution uses $x$, which absorbs $\psi$. The second uses an arbitrary $z \in L^1(G)$, and $(F * x) * \check z$, with $\check z(a) = z(a^{-1})$, is $y \mapsto \int z(a) (F*x)(ya)\, da$.

**Theorem.** Let $G$ be a locally compact Polish group with Haar measure. Let $S$, $\rho_S$ and $\nu$ be as above, let $F$ be bounded measurable and integrable for $\nu$, with $F(sy) = c(s) F(y)$ for $s \in S$, where $|c(s)| = 1$ for all $s \in G$. Let $\psi$ be a bounded idempotent kernel with $\psi(1) = d$ and $F * \psi = F$. Let $x \in L^1(G)$ with $\psi * x = x$, and let $z \in L^1(G)$. Then
$$\int_G |(F * x) * \check z|^2\, d\nu \le \frac{\int_G |x|^2}{d} \cdot \frac{1}{d} \int_G \|F\|^2\, d\nu \cdot \int_G |z|^2.$$

Lean: `New.IsBoundedMeasurable.lintegral_sq_convolve_convolve_le` (Lib/DiscreteSeries/Bessel/SchurBound.lean).

*Proof.* Let $w(a) \in L^2(\nu)$ be the class of the right translate $y \mapsto F(ya)$. It lies in $L^2(\nu)$, since $F$ is bounded and $|F(\cdot\, a)|$ has the same distribution as $|F|$ for $\nu$. By the proposition on translates, $\langle w(a), w(b) \rangle = \frac{\psi(a^{-1}b)}{d} \int \|F\|^2\, d\nu$. Put $Z = x * \check z$. Then $Z \in L^1(G)$ and $\psi * Z = Z$, and $(F * x) * \check z = F * Z$ by associativity. Let $\Phi$ be the class of $F * Z$ in $L^2(\nu)$. Fubini gives $\langle \Phi, \Phi \rangle = \langle \Phi, (w * Z)(1) \rangle$, so $\|\Phi\| \le \|(w * Z)(1)\|$. The average $\int z(g) (w*x)(g)\, dg$ is $(w * Z)(1)$. Schur's bound for $w$, $x$ and $z$, with $\|(w * x)(1)\|^2 = \frac{\int|x|^2}{d} \int \|F\|^2\, d\nu$, bounds $\|(w * Z)(1)\|^2$ by the right side. $\square$

The constant is $\|x\|_2^2 \|F\|_2^2 \|z\|_2^2 / d^2$. For a matrix coefficient kernel, $d$ is the formal degree, and the bound is good when the formal degree is large. In the application, $F$ is a Bessel function, $S$ is $\mathsf U$, $c(n) = \operatorname{wave}(\sigma(n))$, and $\nu = \mu_{\mathsf U \backslash G_1}$.

**Remark (Formalization).** The left side and the factors $\int^- \|F\|^2\, d\nu$ and $\int^- |z|^2$ are lower Lebesgue integrals of extended norms. The factors $\int |x|^2 / d$ and $1/d$ enter through $\operatorname{ofReal}$, which sends negative reals to $0$. Since $d \ge 0$ and $d \ne 0$, these factors are their real values. The factor $\int |x|^2$ is a Bochner integral, and it is $0$ if $|x|^2$ is not integrable. In the theorem $|x|^2$ is integrable: $x = \psi * x$ is bounded, since $\psi$ is bounded and $x \in L^1$.
