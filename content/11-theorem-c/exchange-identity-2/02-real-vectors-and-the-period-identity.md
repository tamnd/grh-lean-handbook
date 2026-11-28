---
title: Real vectors and the period identity
lean:
  - New/Determinant/Exchange/RealVectors.lean
decls:
  - New.Exchange.exists_isSchwartzVector_realSlice_eq
  - New.Exchange.exists_isSchwartzVector_realSlice_zero_eq
  - New.Exchange.exists_contDiff_witt
  - New.Exchange.isSchwartzVector_realBoxProd
  - New.Exchange.exists_contDiff_eventuallyEq_inv
  - New.Exchange.IsWittBump
  - New.Exchange.exists_contDiff_witt_and_bump
  - New.Exchange.mul_gram_inv_mul_of_isUnit_det
  - New.Exchange.frameProjection
  - New.Exchange.unitaryMovedFrame
  - New.Exchange.exchangeSection
  - New.Exchange.exists_isSchwartzVector_realSlice_bump
  - New.Exchange.exists_isSchwartzVector_exchangeSection
  - New.Exchange.realPairWeil_exchangeSection
  - New.Exchange.prod_conj_pow_eq_norm_div
  - New.Exchange.IsWittBump.exists_mul_fromRows_mul_eq_of_ne_zero
  - New.Exchange.IsWittBump.eventually_bump_frameProjection_ne_zero
  - New.Exchange.IsWittBump.isPeriodIdentity
  - New.Exchange.exists_rowColExchangeIdentity_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Real vectors and the period identity

The theorem "exchange from periods" of [the first part](/chapter/exchange-identity-1/#cone-images-and-the-large-triple) needs real vectors $\Phi$ for $(X, V' \oplus W_1)$ and $\Lambda$ for $(X, V')$ that satisfy the period identity. This section builds them. The tool is a smooth form of the theorem of Witt: frames near a fixed frame are moved into its span by unitary elements that depend smoothly on the frame.

### The setting

Let $X$ be a hermitian space with signs $r$, and let $D$ be an adapted splitting of $X$ as $W_1$ plus $|b|$ hyperbolic planes. Let $W_1$ have signs $s$ and even rank $|n| = 2j$, and let $D_1$ be an adapted splitting of $W_1$ as a space $W$ plus one plane. Let $V'$ have a basis indexed by $b$ and signs $t'$. At each infinite place $w$ a *frame* is a complex $(b \sqcup n) \times b$ matrix. Put $x_0 = \binom{1}{0}$, the frame of the first summand of $V' \oplus W_1$, and $J = \operatorname{diag}(t', s)$. The Gram matrix of $x_0$ is $x_0^* J x_0 = \operatorname{diag}(t')$, which is invertible.

For a real vector $v$ for $(X, V)$ and an adelic $b \times b$ or $(b \sqcup n) \times b$ matrix $x$, the *real slice* of $v$ at $x$ along $D$ is the value at the infinite components of $x$ in the mixed model of $D$. It is a real vector for $(W_1, V)$. A vector is a *Schwartz vector* if all its moments are finite, as in [the tower](/chapter/rallis-inner-product/#the-tower). We use one fact from [the Weil representation](/chapter/weil-representation/): if $\tau$ is smooth with compact support and $u(x)$ is a smooth family of real unitary points, then $x \mapsto \tau(x)\,\omega(u(x))v$ is the family of slices of a Schwartz vector, for each Schwartz $v$ (`New.Fock.MixedModel.exists_isSchwartzVector_slice_eq`).

### Prescribed slices

**Lemma.** Let $\tau \geq 0$ be smooth with compact support and $\tau(y) \neq 0$ for some $y$. Let $v$ be a Schwartz vector for $(W_1, V')$. There are $\kappa \in \mathbb{C}$ and a Schwartz vector $\Lambda$ for $(X, V')$ whose slice along $D$ at each $x$ is $\tau(x)\kappa\, v$, and whose slice at $0$ along $D^{\mathrm{sym}}$, the splitting with the two isotropic frames exchanged, is $v$.

Lean: `New.Exchange.exists_isSchwartzVector_realSlice_eq` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* The background fact gives $\Lambda$ with slices $\tau(x)\kappa\, v$ for any $\kappa$. The slice at $0$ along $D^{\mathrm{sym}}$ is the integral of all slices along $D$, against the Haar measure of the frames. Both sides are integrals of slices, and the measure is a multiple of the vacuum measure moved by the change of frame. In real and finite coordinates each integrand is a function of the real variable times one fixed function of the finite variable. So after Fubini the slice at $0$ is $\kappa \int \tau$ times $v$, up to a fixed positive factor. As $\tau \geq 0$ and $\tau(y) \neq 0$, the integral of $\tau$ is positive, and we choose $\kappa$ to make the product $1$. $\square$

**Lemma.** Taking the slice at $0$ is onto on Schwartz vectors: for an adapted splitting $A$ of $X$ over $W_1$ and a Schwartz vector $v$ for $(W_1, V')$ there is a Schwartz vector $w$ for $(X, V')$ whose slice at $0$ along $A$ is $v$.

Lean: `New.Exchange.exists_isSchwartzVector_realSlice_zero_eq` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* Apply the previous lemma to $A^{\mathrm{sym}}$ and the standard smooth bump function, which is nonzero at $0$. The splitting opposite to $A^{\mathrm{sym}}$ is $A$. $\square$

The external product $v \boxtimes v_1$ of two Schwartz vectors is a Schwartz vector (`New.Exchange.isSchwartzVector_realBoxProd`). It is an iterated integral of translates of the vacuum, and padding a vector with zeros does not increase its norm.

### A smooth theorem of Witt

**Theorem (Smooth Witt).** Let $J$ be hermitian and $x$ a frame with $\det(x^* J x) \neq 0$. There are elements $k(y)$ of $U(J)$, one for each frame $y$, such that the matrix of $k(y)$ is a smooth function of $y$ and, for $y$ near $x$, $k(y)\, x\, c = y$ for some square matrix $c$. So $y$ lies in the span of $k(y)x$.

Lean: `New.Exchange.exists_contDiff_witt` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* Put $w = (x^* J x)^{-1} x^*$, so that $y w J x = y$ for every $y$. For a square matrix $a$ put
$$L(a) = (a x w - x w a^*) J .$$
Then $L(a)^* J + J L(a) = 0$, as $J^* = J$, so $L(a)$ lies in the Lie algebra of $U(J)$ and $\exp L(a) \in U(J)$. A direct computation gives $(a - L(a))x = x\,(w a^* J x)$: the matrix $a - L(a)$ keeps the span of $x$. Put $T(a) = \exp(L(a))\,(a - L(a))$. Then $L(1) = 0$ and $T(1) = 1$. By the product rule the derivative of $T$ at $1$ is $(\mathrm{id} - L') + L' = \mathrm{id}$. By the inverse function theorem $T$ has a smooth local inverse $A$ near $1$, extended to a smooth map on all matrices. Put $z(y) = 1 - (x - y) w J$; then $z(x) = 1$ and $z(y) x = y$. Let $k(y) = \exp L(A(z(y)))$ and $c = w A(z(y))^* J x$. For $y$ near $x$,
$$k(y)\, x\, c = T(A(z(y)))\, x = z(y)\, x = y. \qquad \square$$

**Definition.** Smooth *Witt data* near $x_0$ for $J$ are a smooth map $\gamma$ on square matrices, a smooth family $k(y) \in U(J)$, and a smooth function $\sigma \geq 0$ of compact support on families of frames, one frame for each infinite place, such that $\gamma(x_0^*Jx_0) = (x_0^*Jx_0)^{-1}$, $\sigma$ is $1$ at the constant family $x_0$, and for every family $x$ with $\sigma(x) \neq 0$ and every place $w$: the Gram matrix of $x_w$ is invertible, $\gamma$ inverts it, and $k(x_w)\, x_0\, c = x_w$ for some $c$.

Lean: `New.Exchange.IsWittBump` (New/Determinant/Exchange/RealVectors.lean).

**Lemma.** If $J$ is hermitian and $\det(x_0^*Jx_0) \neq 0$, smooth Witt data near $x_0$ exist.

Lean: `New.Exchange.exists_contDiff_witt_and_bump`, `New.Exchange.exists_contDiff_eventuallyEq_inv` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* The inverse is the adjugate divided by the determinant, so near a matrix of nonzero determinant it agrees with a smooth map $\gamma$ on all matrices. Take $k$ from the smooth Witt theorem. The three conditions hold on a neighbourhood of the constant family $x_0$, by continuity of $y \mapsto y^*Jy$. A smooth bump function $\sigma$ with values in $[0, 1]$, equal to $1$ at $x_0$ and with support in that neighbourhood, exists. $\square$

### The two vectors

Write $\operatorname{pr}_\gamma(x) = x\,\gamma(x^*Jx)\,x^*Jx_0$. Where $\gamma$ inverts the Gram matrix, this is the $J$-orthogonal projection of $x_0$ to the span of $x$. It does not change when $x$ is replaced by $xC$ with $C$ invertible (`New.Exchange.mul_gram_inv_mul_of_isUnit_det`).

**Definition.** Let $k$ be a family of unitary elements, $M$ a family of natural numbers, one at each infinite place, $\kappa \in \mathbb{C}$, and $v$, $v_1$ vectors for $(W_1, V')$ and $(W_1, W_1)$. For families $y$, $x$ of frames put $x'_w = k(y_w)^{-1} x_w$, the *moved frame*, and let $(x'_w)_1$ be its upper $b \times b$ block. The *exchange section* is
$$S(y, x) = \sigma(y)\,\sigma(x')\,\kappa \prod_w \overline{\det (x'_w)_1}^{\,2M_w}\cdot \omega\bigl(1, k(y)\bigr)(v \boxtimes v_1),$$
where $\omega$ is the real Weil representation twisted by $\det^{\,j - M}$ on the unitary group of $\operatorname{diag}(t', s)$.

Lean: `New.Exchange.frameProjection`, `New.Exchange.unitaryMovedFrame`, `New.Exchange.exchangeSection` (New/Determinant/Exchange/RealVectors.lean). The invariance of the projection under $x \mapsto xC$ is `New.Exchange.mul_gram_inv_mul_of_isUnit_det` (same file).

**Lemma.** Let $(\gamma, k, \sigma)$ be smooth Witt data near $x_0$ for $J = \operatorname{diag}(t', s)$, let $N$ and $M$ be families of natural numbers, and let $v$, $v_1$ be Schwartz vectors.

1. There are $\kappa$ and a Schwartz vector $\Lambda$ for $(X, V')$ whose slice at $0$ along $D^{\mathrm{sym}}$ is $v$, and whose slice along $D$ at an adelic $b \times b$ matrix $x$ is $\sigma(x_0 x_w)_w \,\bigl|\prod_w \det(x_w)^{N_w}\bigr|^2 \kappa\, v$.
2. For every smooth map $z$ on frames and every $\kappa$ there is a Schwartz vector $\Phi$ for $(X, V' \oplus W_1)$ whose slice along $D$ at $x$ is $S(z \circ x, x)$.

Lean: `New.Exchange.exists_isSchwartzVector_realSlice_bump`, `New.Exchange.exists_isSchwartzVector_exchangeSection` (New/Determinant/Exchange/RealVectors.lean). The proof uses `New.Exchange.isSchwartzVector_realBoxProd` (same file).

*Proof.* Part 1. The function $\tau(x) = \sigma(x_0 x)\,|\prod_w \det x_w^{N_w}|^2$ is smooth and $\geq 0$. It has compact support, as $x$ is recovered from the frame $x_0 x = \binom{x}{0}$, which lies in the support of $\sigma$. At $x = 1$ it is $\sigma(x_0) = 1$. Apply the lemma on prescribed slices. Part 2. The section is a scalar $\tau(x)$ times $\omega_0(u(x))(v \boxtimes v_1)$, where $\omega_0$ is the plain Weil representation and $u(x)$ is the block matrix of the $k(z(x_w))$; the twist by $\det^{\,j - M}$ goes into $\tau$. The scalar is $\sigma(z \circ x)\,\sigma(x')$ times a polynomial in the entries of $x$, of $k(z(x))$ and of their conjugates, since $k(y)^{-1} = J k(y)^* J$. So it is smooth. On its support $x_w = k(y_w)\, x'_w$ with $y$ and $x'$ in the support of $\sigma$, so the support is compact. The background fact gives $\Phi$. $\square$

### The period identity

**Lemma.** Let $(\gamma, k, \sigma)$ be smooth Witt data near $x_0$, and let $x$ be a family of frames with $\sigma(\operatorname{pr}_\gamma \circ x) \neq 0$. Then at each place $x_w = k(\operatorname{pr}_\gamma(x_w))\, x_0\, c$ for some $c$ with $c^* \operatorname{diag}(t') c = x_w^* J x_w$. For $h$ near $1$ in the real unitary group of $J$, $\sigma$ does not vanish at the family $\operatorname{pr}_\gamma(h_w^{-1} x_0)$.

Lean: `New.Exchange.IsWittBump.exists_mul_fromRows_mul_eq_of_ne_zero`, `New.Exchange.IsWittBump.eventually_bump_frameProjection_ne_zero` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* Let $y_w = \operatorname{pr}_\gamma(x_w)$. By the Witt data $y_w = k(y_w)x_0c_0$. A projection of $x_0$ to the span of $x_w$ spans the same space as $x_w$ when its Gram matrix is invertible, so $x_w = y_w C$ and $x_w = k(y_w)x_0 c$ with $c = c_0 C$. The Gram matrix of $k(y_w)x_0c$ is $c^* \operatorname{diag}(t') c$, as $k(y_w)$ is unitary. For the second claim, $h \mapsto \sigma(\operatorname{pr}_\gamma(h^{-1}x_0))$ is continuous and equals $\sigma(x_0) = 1$ at $h = 1$, since $\gamma$ inverts the Gram matrix of $x_0$ and $\operatorname{pr}_\gamma(x_0) = x_0$. $\square$

**Theorem (The period identity).** Let $(\gamma, k, \sigma)$ be smooth Witt data near $x_0$ for $J = \operatorname{diag}(t', s)$. Let $\mathfrak{c}$ be a split tame character of weight $\mu \geq 0$ and $v_1$ a Schwartz vector for $(W_1, W_1)$. Suppose that the slice of $\Phi$ along $D$ at $x$ is $S(\operatorname{pr}_\gamma \circ x, x)$ with $M = \mu$, and that the slice of $\Lambda$ at $x$ is $\sigma(x_0x)\,|\prod_w \det x_w^{\,j + \mu_w}|^2\kappa\, v$. Then $\Phi$ and $\Lambda$ satisfy the period identity with weight $\rho(h) = \sigma(\operatorname{pr}_\gamma(h_w^{-1}x_0))_w$ and period
$$I_0 = \theta_{\mathrm{large}}\bigl(W_1, W_1;\, v_1,\, \phi_{\mathrm{col}}\bigr)(1),$$
the theta integral over $U(W_1)$ at $1$ with real part $v_1$ and, at the ramified places of $\mathfrak{c}$, the standard column datum $\phi_{\mathrm{col}}$ of the character $\chi$ of $\mathfrak{c}$ at $z = 1$.

Lean: `New.Exchange.IsWittBump.isPeriodIdentity` (New/Determinant/Exchange/RealVectors.lean). The proof uses `New.Exchange.realPairWeil_exchangeSection` and `New.Exchange.prod_conj_pow_eq_norm_div` (same file).

*Proof.* Fix a real point $h$ and put $x_{1,w} = h_w^{-1}x_0$ and $y = \operatorname{pr}_\gamma \circ x_1$. The Gram matrix of $x_{1,w}$ is $\operatorname{diag}(t')$, so $\gamma$ inverts it. If $\sigma(y) = 0$, both sides of the identity are $0$. Otherwise the lemma gives $c$ with $k(y_w)x_0 c = x_{1,w}$ and $c^*\operatorname{diag}(t')c = \operatorname{diag}(t')$, so $c = u_w$ is unitary for $t'$. Then $h_w k(y_w)$ keeps the span of $x_0$, and a unitary element that keeps this span is block diagonal: $\operatorname{diag}(u_w, q_w^{-1})\, h_w\, k(y_w) = 1$ with $q_w$ unitary for $s$ (`New.Exchange.exists_unitary_pair_of_frame`). Take $p = (u, q^{-1})$ in $U(V') \times U(W_1)$.

Let $B$ be invertible. The slice of $\Phi$ is read at $(ph)^{-1}\binom{B}{0}$, whose component at $w$ is $x_{1,w}C_w$ with $C_w = u_w^{-1}B_w$ (`New.Exchange.atRealPlace_inv_sum_mul_fromRows`). By the invariance of $\operatorname{pr}_\gamma$ the section is $S(y, x_1C)$. Its group elements cancel: $(ph)\,k(y) = 1$. Its moved frame is $k(y_w)^{-1}x_{1,w}C_w = x_0 u_w C_w = \binom{B_w}{0}$. So the moved slice is
$$\sigma(y)\,\sigma\bigl(\tbinom{B}{0}\bigr)\,\kappa\prod_w \overline{\det B_w}^{\,2\mu_w}\cdot v \boxtimes v_1$$
(`New.Exchange.realPairWeil_exchangeSection`). Here the weight of $\omega$ is $|n|/2 - \mu = j - \mu$. By the product formula of the first part, the theta functional of $f \boxtimes (\chi^{-1}\circ\det)$ at this vector is the functional at $v$ times the theta kernel of $(W_1, W_1)$ at $v_1$. Its integral over $u \in [U(W_1)]$ is the theta integral of $v_1$, which is the constant $I_0$ by the theorem on equal ranks. Last, with $\zeta$ the idele equal to $\det B$ at the infinite places and $1$ elsewhere,
$$\prod_w \overline{\zeta_w}^{\,2\mu_w} = \frac{\bigl|\prod_w \zeta_w^{\,j + \mu_w}\bigr|^2}{\nu(\zeta/\bar\zeta)\,|\zeta|^{j}}$$
(`New.Exchange.prod_conj_pow_eq_norm_div`), and $|\prod_w \det B_w^{\,j+\mu_w}|^2\kappa\, v$ times $\sigma\binom{B}{0}$ is the slice of $\Lambda$ at $B$. The two sides agree, with $\rho(h) = \sigma(y)$. $\square$

### The identity for the large triple

**Theorem (Large triple).** Let $D$ and $D_1$ be as above, with $|n|$ even, let $e \colon b \sqcup b \sqcup n \simeq m$ order the rows, and let $\mu$ be any weight. For Schwartz vectors $v$ for $(W_1, V')$ and $v_1$ for $(W_1, W_1)$ there are $\Phi$ for $(X, V' \oplus W_1)$ and $\Lambda$ for $(X, V')$ such that the slice of $\Lambda$ at $0$ along $D^{\mathrm{sym}}$ is $v$, and the row-column exchange identity holds for $(X, V' \oplus W_1, V')$ at $(\Phi, \Lambda)$ with $\ell(\mathfrak{c})$ the equal rank ratio of $v_1$.

Lean: `New.Exchange.exists_rowColExchangeIdentity_sum` (New/Determinant/Exchange/RealVectors.lean).

*Proof.* Write $|n| = 2j$. Take smooth Witt data near $x_0$ for $\operatorname{diag}(t', s)$; the Gram matrix of $x_0$ is $\operatorname{diag}(t')$, with determinant $\pm 1$. Let $M_w = \max(\mu_w, 0)$. Part 1 of the lemma with $N = j + M$ gives $\kappa$ and $\Lambda$. Part 2 with $z = \operatorname{pr}_\gamma$ gives $\Phi$.

The slices of $\Phi$ vanish outside $t'$: if the slice at $x$ is nonzero, then $\sigma(\operatorname{pr}_\gamma \circ x) \neq 0$, and the lemma gives $c$ with $c^*\operatorname{diag}(t')c$ equal to the Gram matrix of $x_w$. Let $\mathfrak{c}$ be a split tame character. Its weight is positive, so $\mu_w > 0$ and $M = \mu$. The theorem on the period identity applies, with period $I(\mathfrak{c}) = \theta_{\mathrm{large}}(W_1, W_1; v_1, \phi_{\mathrm{col}})(1)$. The weight $\rho$ is $\geq 0$ and nonzero near $1$. Part 3 of the theorem "exchange from periods" now gives the row-column exchange identity with $\ell(\mathfrak{c}) = |I(\mathfrak{c})|^2/L_*(n/2)$, which is by definition the equal rank ratio of $v_1$. It is used with the first alternative, the slices that vanish outside $t'$. $\square$

**Remark (Formalization).** The weight $\mu$ of the theorem is an arbitrary integer family. The source turns it into natural numbers by $\max(\mu, 0)$ for the construction, and uses $\mu_w > 0$, a field of every split tame character, to apply the period identity. If no split tame character of weight $\mu$ exists, the identity holds with nothing to check. The theorem needs no hypothesis on the signs, because the first alternative of "exchange from periods" holds by construction.
