---
title: Cone images and the large triple
lean:
  - New/Determinant/Exchange/ConeImage.lean
  - New/Determinant/Exchange/LargeTriple.lean
decls:
  - New.Exchange.HasPosMellinTransform
  - New.Exchange.exists_hasPosMellinTransform_mulVec_eq_smul
  - New.Exchange.exists_slice_eq_smul_realPairWeil
  - New.Exchange.exists_coneIntegrand_eq_smul
  - New.Exchange.thetaLarge_realPairWeil
  - New.Exchange.exists_thetaLarge_cone_eq_mul
  - New.Exchange.exists_thetaLarge_cone_eq
  - New.Exchange.thetaOnRealData
  - New.Exchange.RepresentedBy.of_conjTranspose_mul_mul
  - New.Exchange.SlicesVanishOutside
  - New.Exchange.thetaTerm_eq_and_centreCoeff_eq_zero
  - New.Exchange.thetaOnRealData_boxProd_eq_mul
  - New.Exchange.thetaLarge_eq_apply_one_of_even_rank
  - New.Exchange.equalRankThetaRatio
  - New.Exchange.RowColExchangeIdentity
  - New.Exchange.IsPeriodIdentity
  - New.Exchange.exists_centreCoeff_eq_mul_of_isPeriodIdentity
  - New.Exchange.exists_thetaLarge_eq_smul_of_isPeriodIdentity
  - New.Exchange.rowColExchangeIdentity_of_periods
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cone images and the large triple

This section assembles the exchange identity for the large triple. It has two parts. The first shows that the cone integral of [the tower](/chapter/rallis-inner-product/#the-tower) reaches every real vector, up to the theta integrals on standard data. The second reduces the exchange identity for $V = V' \oplus W_1$ to an identity of periods over $[U(W_1)]$, by the vanishing theorem of Section 5.

### The image of the cone integral

Let $W' = W \oplus H$ and $V' = V \oplus H$ with $H$ a hyperbolic plane, with adapted splittings $A$ and $X$ that define isotropic lines in the two copies of $H$. Let $x_B$ be the vector that spans the line of $X$. For $\kappa$ in the maximal compact subgroup of $U(V')$ and $a$ a family of nonzero complex numbers at the infinite places, the *cone point* is $\kappa^{-1} x_B a$. The cone integral $\operatorname{cone}_z(v')$ of a vector $v'$ for $(W', V')$ is the integral over $(\kappa, a)$ of an integrand that, at $(\kappa, a)$, is $|a|^z$ times a translate of the slice of $v'$ at the cone point. Write $|a|$ for the module of the idele that is $a$ at the infinite places and $1$ elsewhere.

**Definition.** A real function $\rho$ of $(\kappa, a)$ has a *positive Mellin transform* if for every real $z$ the function $\rho(\kappa, a)|a|^z$ is integrable and has a positive integral.

Lean: `New.Exchange.HasPosMellinTransform` (New/Determinant/Exchange/ConeImage.lean).

**Lemma.** There are a smooth function $\beta \geq 0$ of compact support and a smooth family $k(x)$ of real points of $U(V')$ such that $\beta$ of the cone point has a positive Mellin transform and, when $\beta(\kappa^{-1}x_B a) \neq 0$, the point $\kappa\, k(\kappa^{-1}x_B a)$ multiplies $x_B$ by $a$ at each infinite place.

Lean: `New.Exchange.exists_hasPosMellinTransform_mulVec_eq_smul` (New/Determinant/Exchange/ConeImage.lean).

*Proof.* Work place by place. Near $x_B$ the isotropic vectors $y$ form a smooth manifold, and by Witt's theorem there is a smooth family $k(y)$ of isometries with $k(y) x_B = y$ for isotropic $y$ near $x_B$. Take $\beta \geq 0$ smooth, nonzero at $x_B$, supported where this holds and where the squared length of $y$ at each place is within a factor $2$ of that of $x_B$. The cone point is isotropic, so $k$ of it carries $x_B$ to $\kappa^{-1}x_B a$, and $\kappa k(\cdot)$ carries $x_B$ to $x_B a$. The length condition confines $|a_w|$ to a compact annulus, so $\beta$ of the cone point has compact support. It is continuous, nonnegative and nonzero at $(1, 1)$, so its products with $|a|^z$ have positive integrals. $\square$

**Lemma.** Let $\beta$ be smooth of compact support, $k(x)$ a smooth family of real points of $U(V')$ and $v$ a Schwartz vector for $(W, V')$. Then some Schwartz vector $v'$ for $(W', V')$ has the slice $\beta(x)\, k(x) v$ at every $x$ along $A$.

Lean: `New.Exchange.exists_slice_eq_smul_realPairWeil` (New/Determinant/Exchange/ConeImage.lean).

*Proof.* The twisted Weil representation is the plain one times powers of the determinants of $k(x)$; these are smooth and are absorbed into $\beta$. A smooth family of compact support of Schwartz vectors is the family of slices of a Schwartz vector in the mixed model along $A$. $\square$

**Theorem.** Let $A$ and $X$ be adapted and the rank of $W$ even. There is $\rho$ with a positive Mellin transform such that each Schwartz vector $v$ for $(W, V)$ has a Schwartz vector $v'$ for $(W', V')$ whose cone integrand at $(\kappa, a)$ is $\rho(\kappa, a) |a|^z$ times a translate of $v$ by a real point $h$ of $U(V)$, for every $z$.

Lean: `New.Exchange.exists_coneIntegrand_eq_smul` (New/Determinant/Exchange/ConeImage.lean).

*Proof.* Write $v$ as the zero term of a vector $v^B$ along $\operatorname{Hom}(W, B)$; every Schwartz vector is such a zero term. By the two lemmas take $v'$ with slices $\beta(x) k(x) v^B$. At the cone point, $\kappa k$ multiplies $x_B$ by $a$, so the integrand is $\beta$ of the cone point times $|a|^{z}$ times $|a|^{\operatorname{card} n/2}$ times the zero term of a translate of $v^B$, which is a translate of $v$. Put $\rho = \beta(\text{cone point})\, |a|^{\operatorname{card} n/2}$; the shift of the exponent keeps the positive Mellin transform. $\square$

**Lemma.** The theta integral $\theta_{\mathrm{large}}(v, \Phi)$ does not change when a real point $h$ of $U(V)$ acts on $v$ by the Weil representation twisted by $\det^{\lfloor n/2 \rfloor - \mu}$.

Lean: `New.Exchange.thetaLarge_realPairWeil` (New/Determinant/Exchange/ConeImage.lean).

*Proof.* The theta integral is over $[U(V)]$, and the twist is the one under which the kernel is invariant on the left. Right translation by $h$ keeps the measure. $\square$

**Theorem (Cone image).** Let $A$ and $X$ be adapted, the rank of $W$ even, and $\sigma$ an order of the rows. There is a positive function $B$ on $\mathbb{R}$, analytic on the line, such that each Schwartz vector $v$ for $(W, V)$ has a Schwartz vector $v'$ for $(W', V')$ with
$$\theta_{\mathrm{large}}(\operatorname{cone}_z v', \Phi_y) = B(z)\, \theta_{\mathrm{large}}(v, \Phi_y)$$
for all $z > 0$, every split tame character $\mathfrak{c}$ of weight $\mu$, every standard row datum $\Phi_y$ and every point $g$. For a fixed $z > 0$ the factor can be taken to be $1$.

Lean: `New.Exchange.exists_thetaLarge_cone_eq_mul`, `New.Exchange.exists_thetaLarge_cone_eq` (New/Determinant/Exchange/ConeImage.lean).

*Proof.* Put $B(z) = \int \rho\, |a|^z$. It is positive. A Mellin transform that converges for every exponent is analytic, by differentiation under the integral sign in a strip. Exchange the cone integral with the integral over $[U(V)]$; the integrand of the inner integral is $\rho|a|^z$ times the theta integral of a translate of $v$, which by the lemma equals $\theta_{\mathrm{large}}(v, \Phi_y)$. For the second statement apply the first to $B(z)^{-1} v$. $\square$

### Theta terms along a parabolic

Now let $D$ split $X$ as $W_1$ plus $b$ hyperbolic planes, and let $V$ be any space with signs $t$. The *theta functional on real data* $\theta_{\alpha,\gamma}(F, x, p)$ sends a real datum $\varphi$ of $(W_1, V)$ to $\theta(\varrho(x)\, \omega_{\alpha,\gamma}(p)(\varphi \otimes F))$: the datum with finite part $F$, moved by the Weil representation at $p$ and by the Heisenberg translation by $x$.

Lean: `New.Exchange.thetaOnRealData` (New/Determinant/Exchange/LargeTriple.lean).

**Lemma.** If $q^*Tq$ is represented by $t'$ at every infinite place, and $q$ is invertible, then $T$ is represented by $t'$.

Lean: `New.Exchange.RepresentedBy.of_conjTranspose_mul_mul` (New/Determinant/Exchange/LargeTriple.lean).

*Proof.* If $q^*Tq = y^*\operatorname{diag}(t')y$ at $w$, then $T = (yq^{-1})^* \operatorname{diag}(t')(yq^{-1})$ there. $\square$

**Definition.** A real vector $v$ for $(X, V)$ has *slices that vanish outside* $t'$ if the real slice of $v$ along $D$ at $x$ is $0$ whenever the Gram matrix $x^* \operatorname{diag}(t) x$ is not represented by $t'$.

Lean: `New.Exchange.SlicesVanishOutside` (New/Determinant/Exchange/LargeTriple.lean).

**Proposition (Terms of a standard datum).** Let $\Phi(y) = \varepsilon\, \chi^{-1}(\det(y (K|I) N))$ on integral $y$, read through the adapted frame of $D$ at the ramified places, and $f = v \otimes \Phi$. Let $\beta' = \beta\upsilon^{b}$, and $p = n(c, z)\, m(q, g)$ a point of the parabolic of $D$. Then:

(a) the terms of the theta kernel of $f$ at $p$ are integrable over $[U(V)]$;

(b) the term of a rational frame $x$ at $k$ is $\psi(\tfrac12 \operatorname{tr}(z x^*Jx))\, \chi_V(\det q)^{-1} |\det q|^{a/2}$, times a vacuum factor or $0$ as the finite part of $k^{-1}Y$ is integral or not, times the theta functional on real data of $(W_1, V)$ at the real slice of $v$ at $k^{-1}Y$, where $x' q = \lambda Y$ in standard coordinates;

(c) if $v$ has slices that vanish outside $t'$, and $T$ is not represented by $t'$, then the coefficient at $\jmath T$ of the theta integral of $f$ vanishes at $p$.

Lean: `New.Exchange.thetaTerm_eq_and_centreCoeff_eq_zero` (New/Determinant/Exchange/LargeTriple.lean).

*Proof.* The point $p$ maps the span of the frame and $W_1$ to itself by a block triangular matrix with diagonal blocks $q$ and $g$. The Weil representation of the parabolic in the mixed model acts by the character $\psi(\frac12\operatorname{tr}(z\,\cdot))$, by $\chi_V(\det q)^{-1}|\det q|^{a/2}$ and by translation; this gives (b). The finite part is a standard datum and is bounded by the indicator of the integral matrices, which gives (a) from the integrability of the real part. For (c), the coefficient at $\jmath T$ is the sum of the terms of the frames $x$ with Gram matrix $T$. A nonzero term needs a nonzero real slice at $k^{-1}Y$, whose Gram matrix is $T$ conjugated by an invertible matrix; by hypothesis it is represented by $t'$, and by the lemma so is $T$. So every term is $0$. $\square$

**Lemma (Product formula).** On the pair $(W_1, V' \oplus W_1)$, with characters $\alpha$ and $\alpha\beta$, the theta functional on real data of $f \boxtimes F$ at the translation $(c; 0)$ and the point $(g, u \oplus l)$, evaluated at $\varphi \otimes v$, is the theta functional of $(W_1, V')$ at $f$, $c$, $(g, u)$ evaluated at $\varphi$, times the theta kernel of $(W_1, W_1)$ with characters $\alpha, \alpha$ at $(g, l)$ for $v \otimes F$.

Lean: `New.Exchange.thetaOnRealData_boxProd_eq_mul` (New/Determinant/Exchange/LargeTriple.lean).

*Proof.* The datum is a product along $V' \oplus W_1$. The Weil representation, the Heisenberg operator and $\theta$ act factor by factor, and on the second factor the translation is by $0$. $\square$

### Equal ranks

**Theorem (Equal ranks).** Let $W_1$ have even rank, and let an adapted splitting split a hyperbolic plane off $W_1$. For a split tame character $\mathfrak{c}$ and a Schwartz vector $v$, the theta integral of $(W_1, W_1)$ on $v$ and the datum $\chi^{-1}\circ\det$ on integral invertible matrices is constant on $U(W_1)$.

Lean: `New.Exchange.thetaLarge_eq_apply_one_of_even_rank` (New/Determinant/Exchange/LargeTriple.lean).

*Proof.* The theta integral $F$ is automorphic. It is right invariant under the points supported on the ramified places and their conjugates, since the datum $\chi^{-1}\circ\det$ is moved by a character that the twist cancels, and it is right invariant under the standard level elsewhere. Its constant term along the plane at a Levi point $m(u, x)$ does not depend on the torus part $u$: with no first block the row datum is $\chi^{-1}\circ\det$ itself, and the factor at the ramified places is $1$. By the substitute for strong approximation of [Volume 6](/chapter/siegel-weil/#the-formula-in-weils-range), an automorphic function with these invariances is constant. $\square$

**Definition.** The *equal rank ratio* of a vector $v$ for $(X, X)$ is $|\theta_{\mathrm{large}}(v, \chi^{-1}\circ\det)(1)|^2 / L_*(\lfloor m/2 \rfloor)$, where $L_*(e) = \prod_{w \in S} q_w^{e^2} \prod_{1 \leq i \leq e} |L^S(i, \nu)|^2$, with $S$ the ramified places and $\nu$ the character of $\mathfrak{c}$. For negative $e$, $L_*(e) = L_*(-e)^{-1}$.

Lean: `New.Exchange.equalRankThetaRatio` (New/Determinant/Exchange/LargeTriple.lean).

### The exchange identity from periods

**Definition (Row-column exchange identity).** For Schwartz vectors $v$ for $(X, V)$ and $y$ for $(X, V')$, and a function $\ell$ of the split tame characters, the *row-column exchange identity* holds if there is a real $C$ such that for every $\mathfrak{c}$ some $c \in \mathbb{C}$ satisfies

(a) $C\|c\|^2 = L_*(\operatorname{rk} V - \lfloor \operatorname{rk} X/2 \rfloor)\, \ell(\mathfrak{c})$, and

(b) $\theta_{\mathrm{large}}(v, \Phi_z) = c\, \theta_{\mathrm{small}}(y, \Psi_z)$ for every integral $z$, with $\Phi_z$ the standard row datum and $\Psi_z$ the standard column datum of $z$.

Lean: `New.Exchange.RowColExchangeIdentity` (New/Determinant/Exchange/LargeTriple.lean).

No sign is asked of $C$. By (a), $C > 0$ as soon as $\ell(\mathfrak{c}) > 0$ for one $\mathfrak{c}$.

**Definition (Period identity).** Let $V = V' \oplus W_1$ with $W_1$ of rank $n$, and $\gamma = \nu^{-1}\upsilon^{\lfloor n/2 \rfloor}$. The real vectors $v$ for $(X, V)$ and $v'$ for $(X, V')$ satisfy the *period identity* with weight $\rho$ and period $I_0$ if for each real point $h$ of $U(V)$ there is $p \in U(V') \times U(W_1)$ such that for every invertible $B$, character $\beta$, vector $f$, matrix $x$ and points $g$, $y$: the integral over $u \in [U(W_1)]$ of the theta functional on real data for $f \boxtimes (\chi^{-1}\circ\det)$ at $(x, 0)$ and $(g, y \oplus u)$, with characters $\gamma$ and $\gamma\beta$, at the slice of $v$ at $(ph)^{-1}(B, 0)$ moved by $ph$, equals
$$\frac{\rho(h)\, I_0}{\nu(\zeta/\bar\zeta)\, |\zeta|^{n/2}}\ \theta_{\gamma,\beta}(f, x, (g, y))(\text{slice of } v' \text{ at } B),$$
where $\zeta$ is the idele equal to $\det B$ at the infinite places and $1$ elsewhere.

Lean: `New.Exchange.IsPeriodIdentity` (New/Determinant/Exchange/LargeTriple.lean).

**Theorem (Exchange from periods).** Let $D$ split $X$ as $W_1$, of even rank, plus a hyperbolic space, and let $D_1$ split $W_1$ as $W$ plus a hyperbolic plane, both adapted. Let $v$, $v'$ be Schwartz vectors and $\rho \geq 0$, nonzero near $1$. Suppose that $v$ has slices that vanish outside $t'$, or that $t' = -1$, some sign of $s$ is $1$, and $2\operatorname{neg}(s) \leq \operatorname{card} n$. Then:

1. there is $K > 0$ such that, for every $\mathfrak{c}$ and every period identity with weight $\rho$ and period $I_0$, there is $C$ with $\|C\| = K\|I_0\|$ such that the coefficients at $\jmath T$ of the two theta integrals on the standard data of the frame of $D$ satisfy $\text{large} = C \cdot \text{small}$ at every $n(c, z)m(q, g)$ with $(T, q)$ a self-dual test pair for $V'$;
2. with the same $K$ and $C$, $\theta_{\mathrm{large}}(v, \Phi_z) = C\,\theta_{\mathrm{small}}(v', \Psi_z)$ for every integral $z$;
3. if the period identity holds for every $\mathfrak{c}$ with period $I(\mathfrak{c})$, the row-column exchange identity holds with $\ell(\mathfrak{c}) = \|I(\mathfrak{c})\|^2 / L_*(n/2)$ and constant $K^{-2}$.

Lean: `New.Exchange.exists_centreCoeff_eq_mul_of_isPeriodIdentity`, `New.Exchange.exists_thetaLarge_eq_smul_of_isPeriodIdentity`, `New.Exchange.rowColExchangeIdentity_of_periods` (New/Determinant/Exchange/LargeTriple.lean).

*Proof.* Part 1, case (a) of the test pair. Each coefficient is the integral of one term of the theta kernel, by the proposition on terms. On the large side unfold the integral over the rational stabiliser modulo $U(V)$ in stages through $U(V') \times U(W_1)$, with the weight $\rho$ cut off at the finite places; the constant $R \neq 0$ of the unfolding enters $K$. Up to a constant of modulus $1$, the row datum is the standard datum of the local frame of $D$. The product formula splits the integrand, and the period identity computes the inner integral over $[U(W_1)]$. The scalars agree: $\det B$ splits into an infinite and a finite factor, both of absolute value $1$ at the finite places, and on a unit $\zeta$ of $\hat O$, $\chi^{-1}(\bar\zeta) = \chi^{-1}(\zeta)\nu(\zeta/\bar\zeta)$. The result is $C$ times the coefficient of the small side, with $\|C\| = K\|I_0\|$. Case (b) of the test pair. The small side vanishes by part (c) of the proposition on terms, as every Gram matrix of $V'$ is represented by $t'$. The large side vanishes by part (c) if the slices of $v$ vanish outside $t'$. Otherwise $t' = -1$, and it vanishes by [the theorem of Section 6](/chapter/exchange-identity-1/#coefficients-at-indices-that-are-not-negative). Its hypotheses hold: the signs of $V$ have $b + \operatorname{neg}(s)$ negative entries, and the weight $\lfloor n/2\rfloor - \mu_w$ is less than $n - \operatorname{neg}(s)$, since $\mu_w > 0$ and $2\operatorname{neg}(s) \leq n$.

Part 2. By Section 4 there are a space $M$ and an equivariant lift $\mathcal{D}$ with $\mathcal{D}\Psi_z = \theta_{\mathrm{large}}(v, \Phi_z) - C\,\theta_{\mathrm{small}}(v', \Psi_z)$ for the matched standard pair of Section 2. Both theta integrals are automorphic, so the coefficients of $\mathcal{D}$ at the frame datum are the differences of part 1, and they vanish at self-dual lattices. The theorem of Section 5 on matched data gives $\mathcal{D}\Psi_z = 0$.

Part 3. Apply part 2 to every $\mathfrak{c}$ with $I_0 = I(\mathfrak{c})$; it gives $c = C_{\mathfrak{c}}$. Take the real constant $K^{-2}$. Then $K^{-2}\|C_{\mathfrak{c}}\|^2 = \|I(\mathfrak{c})\|^2$, and $\operatorname{card}(b \sqcup n) - \lfloor m/2 \rfloor = n/2$, as $m = 2b + n$. So (a) reads $\|I(\mathfrak{c})\|^2 = L_*(n/2) \cdot \|I(\mathfrak{c})\|^2/L_*(n/2)$, which holds as $L_*(n/2) > 0$. $\square$

**Remark (Formalization).** The constant of part 3 is $K^{-2}$, and $K$ comes from an existence statement; it is not computed. The sign alternative is the hypothesis `h_vanish_or_signs`, with the bound $2\operatorname{neg}(s) \leq \operatorname{card} n$ and no extra margin.
