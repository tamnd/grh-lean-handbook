---
title: Vanishing descends
lean:
  - New/Determinant/Exchange/VanishingDescends.lean
decls:
  - New.Exchange.ThetaLargeVanishes
  - New.Exchange.ThetaLargeVanishes.congr_spaces
  - New.Exchange.negCount_sumElim_hyperbolicSigns_unit
  - New.Exchange.ThetaLargeVanishes.of_add_plane
  - New.Exchange.ThetaLargeVanishes.of_add_planes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Vanishing descends

The exchange identity has a constant $C$ and a factor $c$ with $C|c|^2 = L_*(e)\,\ell(\mathfrak{c})$, where $\ell(\mathfrak{c})$ is the equal rank ratio. The identity is useful only if $\ell(\mathfrak{c}) \neq 0$ for some vector. This section proves that vanishing of the large theta integral passes from $(W \oplus H, V \oplus H)$ down to $(W, V)$. Section 5 uses it to show $\ell(\mathfrak{c}) \neq 0$. If the ratio were $0$ at every vector, a large theta integral would vanish, the vanishing would descend to a pair $(J, 0)$, and there the integral of the vacuum is a volume, which is not $0$.

The tool is analytic continuation. The constant term along the new line is a value of Tate's integral. For the vectors of the cone image theorem of [the first part](/chapter/exchange-identity-1/#cone-images-and-the-large-triple), this integral is the theta integral of $(W, V)$ times factors that have no zero at the point in question. So if the theta integral above vanishes, the one below vanishes too.

### The property

**Definition.** Let $W$, $V$ be hermitian spaces with signs $s$, $t$, let $\sigma \colon b \sqcup r \simeq n$ order the rows of the data, and let $\mathfrak{c}$ be a split tame character. The large theta integral of $(W, V)$ *vanishes* for $\mathfrak{c}$ if
$$\theta_{\mathrm{large}}\bigl(W, V;\, v,\, \phi_{\mathrm{row}}(\sigma, \chi, y)\bigr)(g) = 0$$
for every Schwartz vector $v$, every integral $b \times n$ matrix $y$ at the ramified places of $\mathfrak{c}$, and every point $g$ of the adelic unitary group of $W$.

Lean: `New.Exchange.ThetaLargeVanishes` (New/Determinant/Exchange/VanishingDescends.lean).

**Lemma.** If the large theta integral of $(W, V)$ vanishes for $\mathfrak{c}$, and $W_1$, $V_1$ have the signs of $W$, $V$, then the large theta integral of $(W_1, V_1)$ vanishes for $\mathfrak{c}$.

Lean: `New.Exchange.ThetaLargeVanishes.congr_spaces` (New/Determinant/Exchange/VanishingDescends.lean).

*Proof.* By the change of space theorem of Section 3, the integral for $(W_1, V_1)$ at $g$ is $u$ times the integral for $(W, V)$ at $\gamma g$, with $|u| = 1$. The second factor is $0$. $\square$

**Lemma.** Adding a hyperbolic plane, with one sign $+1$ and one sign $-1$, to signs $\varepsilon$ adds one minus sign.

Lean: `New.Exchange.negCount_sumElim_hyperbolicSigns_unit` (New/Determinant/Exchange/VanishingDescends.lean).

*Proof.* The count of minus signs of a concatenation is the sum of the counts, and the plane has one. $\square$

### Three facts from the tower

The proof uses three results of [the tower](/chapter/rallis-inner-product/#the-tower) and of the first part. We state them in the form used. Let $A$ and $X$ be adapted splittings $W' = W \oplus H$ and $V' = V \oplus H$, with $\operatorname{rk} W$ even, and put $e = \operatorname{rk} V - \operatorname{rk} W/2$.

1. *Cone image.* There is a positive real analytic function $B$ on $\mathbb{R}$ such that every Schwartz vector $v$ for $(W, V)$ has a Schwartz vector $v'$ for $(W', V')$ with $\theta_{\mathrm{large}}(W, V; \operatorname{cone}_x(v')) = B(x)\,\theta_{\mathrm{large}}(W, V; v)$ for all $x > 0$, all $\mathfrak{c}$ of weight $\mu$, all standard data and all $g$ (`New.Exchange.exists_thetaLarge_cone_eq_mul`).
2. *Tate's integral.* There are numbers $\varepsilon_\beta$, for the two sides $\beta$ of Poisson's formula, with $|\varepsilon_\beta|$ a positive constant independent of $\mathfrak{c}$, such that for each Schwartz $v'$, each integral $y$ and each $g$ there is a real analytic function $\mathcal{Z}$ on $\mathbb{R}$ with: the constant term along $A$ of $\theta_{\mathrm{large}}(W', V'; v', \phi_{\mathrm{row}}(y\pi_W))$ at $(1, g)$ is $\mathcal{Z}(e+1)$, and for $x \geq 1$
$$\mathcal{Z}(x) = \varepsilon_{\mathrm{true}}\,P(x)\,L^S(x, \nu)\,\theta_{\mathrm{large}}(W, V; \operatorname{cone}_x(v'), \phi_{\mathrm{row}}(y))(g).$$
Here $P(x) = |\varpi|^x \prod_{w \in S} q_w^{\,x - 1/2} > 0$, with $\varpi$ a fixed idele, and $\nu$, $S$ are the character and the ramified places of $\mathfrak{c}$ (`New.Exchange.exists_zetaIntegral`).
3. *Continuation.* If $k \leq \mu_w$ at every infinite place, then $x \mapsto L^S(x, \nu)$ for $x \geq 1$ extends to a real analytic function $\Lambda$ on $(-k, \infty)$ with no zero at the integers $j > -k$ (`New.Exchange.exists_analytic_extension_ne_zero`, [Volume 6](/chapter/rallis-inner-product/#the-tower)).

### One plane

**Theorem (Vanishing descends along a plane).** Let $A$ and $X$ be adapted splittings $W' = W \oplus H$ and $V' = V \oplus H$. Let $\operatorname{rk} W$ be even and let $k$ be a natural number with $k \leq \mu_w$ at every infinite place and $-k \leq \operatorname{rk} V - \operatorname{rk} W/2$. If the large theta integral of $(W', V')$ vanishes for $\mathfrak{c}$ with the ordering $\sigma'$, then that of $(W, V)$ vanishes for $\mathfrak{c}$ with the ordering $\sigma$. Both orderings are arbitrary.

Lean: `New.Exchange.ThetaLargeVanishes.of_add_plane` (New/Determinant/Exchange/VanishingDescends.lean).

*Proof.* Fix a Schwartz vector $v$, an integral $y$ and $g$, and let $I = \theta_{\mathrm{large}}(W, V; v, \phi_{\mathrm{row}}(y))(g)$. We show $I = 0$.

Step 1. Fact 1 gives $B$ and a Schwartz vector $v'$ for $v$. Fact 3 gives $\Lambda$. Fact 2, for $v'$, $y$ and $g$, gives $\varepsilon$ and $\mathcal{Z}$.

Step 2. Put $R(x) = \varepsilon_{\mathrm{true}}\,P(x)\,\Lambda(x)\,B(x)\,I$. It is real analytic on $(-k, \infty)$, as a product of analytic functions: $P$ is a product of exponentials, $\Lambda$ is analytic there, $B$ is analytic everywhere, and $I$ is a constant. For $x \geq 1$, $\Lambda(x) = L^S(x, \nu)$ and, by Fact 1 with $x > 0$, $B(x)\, I = \theta_{\mathrm{large}}(W, V; \operatorname{cone}_x(v'))$. So by Fact 2, $\mathcal{Z}(x) = R(x)$ for $x \geq 1$.

Step 3. The two analytic functions $\mathcal{Z}$ and $R$ agree on a neighbourhood of $2$, which lies in the connected interval $(-k, \infty)$. By the identity theorem they agree on all of $(-k, \infty)$.

Step 4. The point $e + 1$ is an integer with $-k < e + 1$, since $-k \leq e$. By Fact 2, $\mathcal{Z}(e+1)$ is the constant term along $A$ of $\theta_{\mathrm{large}}(W', V'; v', \phi_{\mathrm{row}}(y\pi_W))$. The datum $y\pi_W$ is integral, as the projection $\pi_W$ in an adapted frame is integral. So the integrand of the constant term is $0$ by hypothesis, and $\mathcal{Z}(e+1) = 0$. Hence $R(e+1) = 0$.

Step 5. In $R(e+1)$ the factor $\varepsilon_{\mathrm{true}}$ is nonzero, as its modulus is positive. $P(e+1) > 0$. $\Lambda(e+1) \neq 0$ by Fact 3, as $e + 1 > -k$. $B(e+1) > 0$. So $I = 0$. $\square$

The point of the hypothesis $-k \leq e$ is now clear. The value $e + 1$ may lie to the left of $1$, where $L^S$ is not given by its Euler product. The continuation $\Lambda$ reaches it only if $e + 1 > -k$, and the weight $\mu$ bounds how far to the left the continuation is free of zeros at integers.

### Many planes

**Theorem (Vanishing descends along planes).** Let $j \geq 1$. Let $W'$ have the rank of $W$ plus $2j$ and $j$ more minus signs than $W$, and let $V'$ have $j$ more minus signs than $V$. Let $\operatorname{rk} W$ be even, and let $k \leq \mu_w$ at every infinite place with $-k \leq \operatorname{rk} V - \operatorname{rk} W/2$. If the large theta integral of $(W', V')$ vanishes for $\mathfrak{c}$, then that of $(W, V)$ vanishes for $\mathfrak{c}$.

Lean: `New.Exchange.ThetaLargeVanishes.of_add_planes` (New/Determinant/Exchange/VanishingDescends.lean).

*Proof.* Induction on $j$, for all $W$, $V$ at once.

Case $j = 1$. The orderings give $|b| + \operatorname{rk} V = \operatorname{rk} W$ and $|b| + \operatorname{rk} V' = \operatorname{rk} W'$, so $\operatorname{rk} V' = \operatorname{rk} V + 2$. By the lemma on adapted splittings of Section 3 there are spaces $W_1$, $V_1$ with the signs of $W'$, $V'$ and adapted splittings $A$ of $W_1$ over $W$ and $X$ of $V_1$ over $V$, each with one plane. By the lemma on the change of space, the vanishing holds for $(W_1, V_1)$. Apply the theorem for one plane.

Case $j + 1$ with $j \geq 1$. Let $W_+ = H \oplus W$ and $V_+ = H \oplus V$, the standard hyperbolic sums. Their ranks are those of $W$, $V$ plus $2$, and they have one more minus sign each. So $W'$ has the rank of $W_+$ plus $2j$ and $j$ more minus signs, and the same holds for $V'$ over $V_+$. The rank of $W_+$ is even, and
$$\operatorname{rk} V_+ - \operatorname{rk} W_+/2 = (\operatorname{rk} V - \operatorname{rk} W/2) + 1 \geq -k.$$
By induction the vanishing holds for $(W_+, V_+)$. The standard splittings of $W_+$ over $W$ and $V_+$ over $V$ are adapted. Apply the theorem for one plane. $\square$

**Remark (Formalization).** The hypothesis on the weight is $k \leq \mu_w$ for a natural number $k$, so $k = 0$ is always allowed. Then the theorem needs $\operatorname{rk} V \geq \operatorname{rk} W/2$. Section 5 uses the theorem with $J$ positive definite of rank $2k$, $k \leq \mu_w$ at every place, $2k + 1$ planes, and the bottom pair $(J, 0)$. There $\operatorname{rk} V - \operatorname{rk} W/2 = -k$, the extreme case of the hypothesis. This is why the size of the weight enters. The vanishing is stated for one character $\mathfrak{c}$ at a time and for all standard data of $\mathfrak{c}$, so no uniformity in $\mathfrak{c}$ is needed.

### Example: a point outside the Euler product

Let $\mu_w = 1$ at every infinite place, so $k = 1$ is allowed. Let $W$ have rank $4$ and $V$ rank $1$. Then $e = 1 - 2 = -1 \geq -k$. The point $e + 1 = 0$ lies outside the region of the Euler product. Fact 3 says that $\Lambda(0) \neq 0$, because $0 > -1$. With $V$ of rank $0$ instead, $e = -2 < -1$, and the theorem does not apply. If $\mu_w \geq 2$ everywhere, it applies again.
