---
title: The restriction to Y_m and the values of source forms
lean:
  - New/UpperBound/Divisibility/ChainValuation.lean
decls:
  - New.Data.GaugeLe.restrictToY_of_diag
  - New.Data.GaugeLe.restrictToY
  - New.Data.weylNormSq_restrictToY_le
  - New.Data.weylGauge_le_one_iff_mem_span
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The restriction to Y_m and the values of source forms

The composite lift ends with the restriction $\mathrm{res}$ from $X_m$ to $Y_m$. This section proves that $\mathrm{res}$ does not increase the $p$-adic gauge, and it bounds the archimedean norm of $\mathrm{res}$. At a prime $p \ne N$ the gauge bound is direct. At $p = N$ it needs a base point that is $\mathrm{diag}(1, \dots, 1, N)$ at the right places; this is why the normalising factor $\prod_\tau \tau(\bar\pi)^{-n_\tau}$ is in the definition of $\mathrm{res}$. The section ends with a description of the source forms of gauge at most $1$ by their polynomials.

### The restriction

Recall from [columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift) that

$$(\mathrm{res}\,F)(h) = a \cdot \mathrm{br}\big(F(\mathrm{diag}(h, 1))\big), \qquad a = \prod_\tau \tau(\bar\pi)^{-n_\tau},$$

where $\mathrm{br}$ is the chosen integer branching matrix and $n_\tau$ is the branching exponent. The branching map has the property that, over every field of characteristic $0$, for $y = \mathrm{diag}(g, z)$ at each place,

$$\mathrm{br}\cdot\rho_X(y) = \Big(\prod_\tau z_\tau^{n_\tau}\Big)\,\rho_Y(g)\cdot\mathrm{br}.$$

The gauge of $\xi$ at $g$ is $\|\rho(g^{-1})\,\iota_p\xi\|$, the largest absolute value of a coordinate. Here $g$ acts at $\tau$ through the embedding $x \mapsto \iota_p(\tau(\bar x))$ of $E$ into $\mathbb C_p$. On adeles this embedding reads the component at the place $\bar w_\tau$, where $w_\tau$ is the place above $p$ induced by $\iota_p\circ\tau$ (Section 2).

**Theorem.** Let $d \in \mathrm{U}(X_m)(\mathbb A_f)$. Suppose, for every infinite place $\tau$, that the component of $d$ read at $\tau$ is the diagonal matrix with entries $1$ at the indices of $Y_m$ and, at the last index, $N$ if $\bar w_\tau \in \Pi_N$ and $1$ otherwise. Let $\varphi$ be a form on $X_m$ with $\mathrm{GaugeLe}(d, c, \varphi)$. Then $\mathrm{GaugeLe}(1, c, \mathrm{res}\,\varphi)$.

Lean: `New.Data.GaugeLe.restrictToY_of_diag` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* Fix $h \in \mathrm{U}(Y_m)(\mathbb A_f)$, and put $y = \mathrm{diag}(h, 1)$ and $\xi = \iota_p\varphi(y)$.

*Step 1: the block form.* At $\tau$, the matrix $(yd)^{-1}$ is $\mathrm{diag}(h_\tau^{-1}, s_\tau)$ with $s_\tau = \det(d_\tau)^{-1}$. This holds because $d_\tau$ is diagonal with entries $1$ except the last.

*Step 2: intertwining.* By the branching property with $g = h^{-1}$ and $z = s$,

$$\mathrm{br}\,\rho_X((yd)^{-1})\,\xi = \Big(\prod_\tau s_\tau^{n_\tau}\Big)\,\rho_Y(h^{-1})\,\mathrm{br}\,\xi.$$

*Step 3: the scalars.* We claim $|\iota_p a| = |\prod_\tau s_\tau^{n_\tau}|$. The absolute value of $\iota_p(\tau(\bar{\bar\pi})) = \iota_p(\tau(\pi))$, read at $\bar w_\tau$, is that of $N$ if $\bar w_\tau$ divides $\pi$, and $1$ otherwise. Indeed $v_w(\pi) = e^{-1}$ at the places $w \in \Pi_N$, as $N$ is split, and $N$ has the same valuation there. So $|\iota_p\tau(\bar\pi)|$ equals $|\iota_p s_\tau^{-1}|$ for each $\tau$, and the claim follows by taking the product with exponents $-n_\tau$.

*Step 4: the bound.* By homogeneity of the gauge,

$$\|(\mathrm{res}\,\varphi)(h)\|_h = |\iota_p a|\,\|\rho_Y(h^{-1})\,\mathrm{br}\,\xi\| = \Big|\prod_\tau s_\tau^{n_\tau}\Big|\,\|\rho_Y(h^{-1})\,\mathrm{br}\,\xi\| = \|\mathrm{br}\,\rho_X((yd)^{-1})\,\xi\|,$$

by Steps 3 and 2. The matrix $\mathrm{br}$ has integer entries, and integers have $p$-adic absolute value at most $1$. By the ultrametric inequality, $\|\mathrm{br}\,\eta\| \le \|\eta\|$ for every $\eta$. So the gauge is at most $\|\rho_X((yd)^{-1})\,\xi\| = \|\varphi(y)\|_{yd} \le c$. $\square$

**Corollary.** Let $p \ne N$, and let $\varphi$ be a form on $X_m$ with $\mathrm{GaugeLe}(1, c, \varphi)$. Then $\mathrm{GaugeLe}(1, c, \mathrm{res}\,\varphi)$.

Lean: `New.Data.GaugeLe.restrictToY` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* The place $w_\tau$ lies above $p$. By the first lemma of Section 6, $\bar w_\tau \notin \Pi_N$. So the matrix of the theorem is the identity at every $\tau$, and $d = 1$ satisfies its hypothesis. $\square$

**Remark.** The general form, with a base point $d$ that is not $1$, is used in [divisibility prime by prime](/chapter/divisibility/), in the file on the valuation at the level. There the base point is a diagonal point of the required shape. The factor $a$ in $\mathrm{res}$ is the scalar that makes the bound exact: by Step 3, its absolute value cancels the scalar $\prod_\tau s_\tau^{n_\tau}$ that the branching map produces.

### The archimedean size of the restriction

For a complex vector $\xi$ of a Weyl module, $\|\xi\|^2_{\mathrm{W}} = \mathrm{Re}(\xi^* G \xi)$, where $G$ is the integer Gram matrix of the module ([integral Weyl modules and branching](/chapter/weyl-modules/)). The branching map has $\|\mathrm{br}\,\xi\|^2_{\mathrm W} \le \exp(x^{70})\|\xi\|^2_{\mathrm W}$ (`New.Data.IsBranchingMap.weylNormSq_le`).

**Proposition.** For every ring homomorphism $\sigma : \mathbb C \to \mathbb C$, every form $\varphi$ on $X_m$, and every $h \in \mathrm{U}(Y_m)(\mathbb A_f)$,

$$\big\|\sigma \circ (\mathrm{res}\,\varphi)(h)\big\|^2_{\mathrm W} \le \exp\Big(x^{70} - \Big(\sum_\tau n_\tau\Big)\log N\Big)\,\big\|\sigma\circ\varphi(\mathrm{diag}(h,1))\big\|^2_{\mathrm W}.$$

Lean: `New.Data.weylNormSq_restrictToY_le` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* The matrix $\mathrm{br}$ has integer entries, so it commutes with $\sigma$. So

$$\|\sigma\circ(\mathrm{res}\,\varphi)(h)\|^2_{\mathrm W} = |\sigma(a)|^2\,\|\mathrm{br}\,(\sigma\circ\varphi(\mathrm{diag}(h,1)))\|^2_{\mathrm W} \le |\sigma(a)|^2 \exp(x^{70})\,\|\sigma\circ\varphi(\mathrm{diag}(h,1))\|^2_{\mathrm W}.$$

For each $\tau$, the composite $\sigma\circ\tau$ is an embedding of $E$ into $\mathbb C$, and it commutes with complex conjugation, since $E$ is CM. From $\pi\bar\pi = N$ we get $|\sigma\tau(\pi)|^2 = N$, so $2\log|\sigma\tau(\bar\pi)| = \log N$. Hence

$$\log|\sigma(a)|^2 = \sum_\tau (-n_\tau) \cdot 2\log|\sigma\tau(\bar\pi)| = -\Big(\sum_\tau n_\tau\Big)\log N.$$

So $|\sigma(a)|^2 \exp(x^{70}) = \exp(x^{70} - (\sum_\tau n_\tau)\log N)$. $\square$

**Remark.** This bound is used in [the archimedean size of the composite lift](/chapter/archimedean-size/). The proposition holds for every ring homomorphism $\sigma$, not only for continuous ones, because it uses only the integrality of $\mathrm{br}$ and the identity $\pi\bar\pi = N$.

### Source forms of gauge at most one

The weight on $X_0$ has one row at each place: at an a-place it has $a$ columns of height $1$, and at the other places it has none ([weights and lift diagrams](/chapter/upper-bound-objects/#weights-and-lift-diagrams)). Its last entry is $0$. So a vector $\zeta$ of its Weyl module is a polynomial $\mathrm{poly}(\zeta)$, homogeneous of degree $a$ or $0$ in a column $z_\tau$ of $k$ variables for each place $\tau$. For a multi-exponent $\alpha = (\alpha_\tau)$ with $\alpha_\tau \in \mathbb N^{X_0}$, the multinomial monomial is

$$\mu_\alpha = \prod_\tau \frac{|\alpha_\tau|!}{\alpha_\tau!}\, z_\tau^{\alpha_\tau},$$

where $|\alpha_\tau| = \sum_b \alpha_\tau(b)$ and $\alpha_\tau! = \prod_b \alpha_\tau(b)!$. By [integral Weyl modules and branching](/chapter/weyl-modules/), for a weight with one row at each place and rank at least $2$, the coordinates of $\xi$ lie in a subring $A$ if and only if $\mathrm{poly}(\xi)$ lies in the $A$-span of the $\mu_\alpha$ with $|\alpha_\tau|$ equal to the row length at $\tau$ (`New.toPoly_mem_span_multinomialMonomial_iff`).

**Proposition.** Let $g \in \mathrm{U}(X_0)(\mathbb A_f)$ and let $\zeta$ be a vector of the Weyl module on $X_0$. Then $\|\zeta\|_g \le 1$ if and only if the polynomial $\mathrm{poly}(\iota_p\circ\zeta)$, after the substitution of $g_\tau z_\tau$ for $z_\tau$ at each $\tau$, lies in the span over $\mathcal O_{\mathbb C_p}$ of the $\mu_\alpha$ with $|\alpha_\tau| = a$ at a-places and $|\alpha_\tau| = 0$ at the other places. Here $g_\tau$ is $g$ read through $\iota_p\circ\tau$.

Lean: `New.Data.weylGauge_le_one_iff_mem_span` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* Let $z_\tau$ be $g^{-1}$ read through the embedding of the gauge at $\tau$. Since the last entry of the weight is $0$, there is no determinant factor, and the gauge is $\|\mathrm{Schur}(z)\,\iota_p\zeta\|$. Since $g$ is unitary, $g^{-1} = \bar g^{\mathsf T}$, and the embedding of the gauge is $\iota_p\circ\tau$ composed with conjugation. So $z_\tau^{\mathsf T} = g_\tau$. The polynomial of $\mathrm{Schur}(z)\,\xi$ is the polynomial of $\xi$ after the substitution of $z^{\mathsf T}$ (`New.GL.toPoly_schur`). The rank of $X_0$ is $k > 1$, and the weight has no column of height $h$ with $1 < h < k$. So the criterion above applies with $A = \mathcal O_{\mathbb C_p}$. The coordinates of a vector lie in $\mathcal O_{\mathbb C_p}$ if and only if its largest coordinate norm is at most $1$. $\square$

**Remark (Formalization).** The span is over the subring `valRingCp p` of $\mathbb C_p$, defined as the elements of norm at most $1$. The multinomial coefficients $|\alpha_\tau|!/\alpha_\tau!$ are part of the monomials $\mu_\alpha$, as in the source. The polynomial is that of the Gram pairing, $\mathrm{poly}(\xi) = \sum_i (G\xi)_i b_i$ with the basis products of minors $b_i$.
