---
title: Removing planes
lean:
  - New/Determinant/Exchange/RemovingPlanes.lean
decls:
  - New.Exchange.neg_mem_neg_Gamma_iff
  - New.Exchange.isForm_neg_iff_and_integral_neg
  - New.Exchange.exists_thetaLarge_eq_mul_thetaLarge
  - New.Exchange.exists_thetaLarge_thetaSmall_eq_circle_mul
  - New.Exchange.exists_isBaseAdapted
  - New.Exchange.realSlice_zero_congr
  - New.Exchange.realSlice_zero_comp
  - New.Exchange.homSlice_localDatum_stdColDatum
  - New.Exchange.theta_zeroTerm_stdColDatum_eq_zero
  - New.Exchange.integral_thetaSmall_lineRadical_eq_mul_thetaSmall
  - New.Exchange.RowColExchangeIdentity.congr_second_space
  - New.Exchange.RowColExchangeIdentity.of_planeConstantTerm_eq
  - New.Exchange.RowColExchangeIdentity.cone
  - New.Exchange.RowColExchangeIdentity.dualCone
  - New.Exchange.exists_rowColExchangeIdentity_removing_plane
  - New.Exchange.exists_rowColExchangeIdentity_removing_planes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Removing planes

Section 2 gives the exchange identity for a large triple $(X, V' \oplus W_1, V')$. This section moves an identity for $(W', V', U)$ down to $(W, V, U)$, where $W' = W \oplus H$ and $V'$ is $V$ plus one hyperbolic plane $H$. We take the constant term along the new isotropic line on both sides. On the side of $U$ the constant term is the theta integral of the zero term of the real vector. On the side of $V'$ it is the theta integral of a cone integral, by the tower of [Volume 6](/chapter/rallis-inner-product/#the-tower). The constant changes by one factor $L^\sharp$, and the ratio $\ell$ does not change.

Throughout, $\mathfrak{c}$ is a split tame character of weight $\mu$, $\chi$ is its character at the ramified places, and the standard data are as in [the first part](/chapter/exchange-identity-1/). The identity $\mathrm{RC}(W, V, U; x, y; \ell)$ means: $x$ and $y$ are Schwartz vectors, and there is a real $D$ such that for every $\mathfrak{c}$ some $c$ has $D|c|^2 = L_*(\operatorname{rk} V - \operatorname{rk} W/2)\,\ell(\mathfrak{c})$ and $\theta_{\mathrm{large}}(W, V; x, \phi_{\mathrm{row}}(z)) = c\,\theta_{\mathrm{small}}(W, U; y, \phi_{\mathrm{col}}(z))$ for all integral $z$. The half is rounded down.

### Change of space

The identity depends on the spaces only through their signs. Two facts give this.

**Lemma.** Passing to the opposite signs, by the identity on matrices, keeps forms of a given type and integrals over the quotient, if it matches the rational points of the two spaces.

Lean: `New.Exchange.isForm_neg_iff_and_integral_neg`, `New.Exchange.neg_mem_neg_Gamma_iff` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The rational points of $W$ and of the opposite space are the same matrices, as the point of the opposite space is a scalar multiple of that of $W$. So left invariance, the bound of moderate growth, the type and the quotient measure agree. $\square$

**Theorem.** Let $W, W_1$ have the same signs, and also $V, V_1$ and $V', V'_1$. There is a point $\gamma$ of the adelic unitary group of $W$, which depends only on the spaces, such that for every $\mathfrak{c}$ the integrals $\theta_{\mathrm{large}}$ for $(W_1, V_1)$ and $\theta_{\mathrm{small}}$ for $(W_1, V'_1)$ at $g$ are the integrals for $(W, V)$ and $(W, V')$ at $\gamma g$, times numbers of modulus one that do not depend on the vector, the datum or $g$.

Lean: `New.Exchange.exists_thetaLarge_thetaSmall_eq_circle_mul`, `New.Exchange.exists_thetaLarge_eq_mul_thetaLarge` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* By the theorem of Landherr (`New.Space.exists_x_eq_and_ratEmbed_conj_eq`, [Volume 4](/chapter/adeles-hermitian-spaces/)) there are $c \in \mathrm{GL}_n(E)$ and $\gamma$ with $W.x = c^{-1}\,W_1.x\,\gamma$. Under this change of point the Weil representations of the two pairs differ by the action of $\gamma$ and by a character of modulus one. The theta kernel is a sum over rational points, and $c$ is a bijection of the rational points. So both theta integrals move to $\gamma g$, up to a factor of modulus one. $\square$

**Corollary.** If $\mathrm{RC}(W, V, U; x, y; \ell)$ holds and $V_1$ has the signs of $V$, then $\mathrm{RC}(W, V_1, U; x, y; \ell)$ holds.

Lean: `New.Exchange.RowColExchangeIdentity.congr_second_space` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* Take $W_1 = W$ and $\gamma = 1$ in the first step of the proof above. Then $\theta_{\mathrm{large}}(W, V_1) = a\,\theta_{\mathrm{large}}(W, V)$ with $|a| = 1$. Replace $c$ by $ac$; its modulus does not change. $\square$

**Lemma.** If the signs $t$ have the rank and the number of minus signs of $W$ plus $|p|$ planes, there is a space with signs $t$ and an adapted splitting of it over $W$ with $|p|$ planes.

Lean: `New.Exchange.exists_isBaseAdapted` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The signs of $W \oplus H^{|p|}$ have the same rank and the same number of minus signs as $t$, as each plane has one sign of each kind. So there is a bijection of the index sets that carries one family of signs to the other. Relabel $W \oplus H^{|p|}$ along it. The splitting of the relabelled space has the frame of the standard splitting with the rows permuted, so it is adapted. $\square$

### Zero terms

For an adapted splitting $A$ of $W'$ over $W$, the *zero term* of a real vector $y$ for $(W', U)$ is its slice at $0$ in the mixed model of $A$. Two facts are used.

**Lemma.** (a) If $A$, $B$ are adapted splittings of $W'$ over $W$, the frame of $B$ consists of columns of the frame of $A$, and their inclusions of $W$ agree, then $A$ and $B$ have the same zero term. (b) If $A$ splits $W'$ over $W$ and $B$ splits $W$ over $V'$, then the zero term along the composite splitting is the zero term along $B$ of the zero term along $A$.

Lean: `New.Exchange.realSlice_zero_congr`, `New.Exchange.realSlice_zero_comp` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* (a) The columns of the frame of $B$ are columns of the isotropic frame of $A$, so the two frames are orthogonal, and the zero term depends only on this frame up to such changes. (b) Zero terms of adelic data compose. Real vectors are compared with adelic data that have them as real part and the vacuum elsewhere. The zero term of the vacuum is the vacuum, so the real parts compose too. $\square$

### The side of $U$

**Lemma.** Let $A$ split one plane off $W'$ over $W$ and be adapted, let $y$ be a Schwartz vector for $(W', U)$, and let $z$ be integral at the ramified places. Let $\pi_W$ be the projection to $W$ in the frame of $A$. The integral over the radical of the line, at the Levi point $(1, g)$, of $\theta_{\mathrm{small}}(W', U; y, \phi_{\mathrm{col}}(z\pi_W))$ is $\kappa_A\,\theta_{\mathrm{small}}(W, U; y_0, \phi_{\mathrm{col}}(z))(g)$. Here $y_0$ is the zero term of $y$ along $A$ and $\kappa_A \neq 0$ is the factor by which slices of $A$ multiply the vacuum.

Lean: `New.Exchange.integral_thetaSmall_lineRadical_eq_mul_thetaSmall` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* Step 1, the slices. The slice along $A$ of the datum with real part $y$ and finite part $\phi_{\mathrm{col}}(z\pi_W)$ at $x$ is $0$ unless the finite part of $x$ is integral. Then it is $\kappa_A$ times the datum with real part the slice of $y$ at $x$ and finite part $\phi_{\mathrm{col}}(z)$ (`New.Exchange.homSlice_localDatum_stdColDatum`). This holds because $\pi_W$ read at the ramified places is the transpose of the inclusion of $W$ at the conjugate places. So the datum reads only the block of columns along $W$.

Step 2, the expansion. The constant term along the radical is a sum over rational vectors $x$ of $U$ of terms of the slices at $x$. A term with $x$ anisotropic is $0$ by definition.

Step 3, isotropic $x \neq 0$. Then $x$ spans the line of a splitting of $U$ over a space $U_0$. The term is the theta functional of $(W, U_0)$ on the zero term along this line of a translate of a datum with finite part $\phi_{\mathrm{col}}$. This functional is invariant under adelic translations along the line. The datum $\phi_{\mathrm{col}}$ lives on matrices of full rank. Such a matrix does not annihilate the line, so a translation moves the datum by a nontrivial character, and the invariant functional kills it (`New.Exchange.theta_zeroTerm_stdColDatum_eq_zero`).

Step 4. Only $x = 0$ remains. By Step 1 at $x = 0$ it is $\kappa_A$ times the theta integral of $(W, U)$ at $y_0$. $\square$

### Descent along one plane

**Lemma (Descent from a constant term).** Let $A$ split $W' = W \oplus H$ and $X$ split $V' = V \oplus H$, both adapted. Let $e = \operatorname{rk} V - \operatorname{rk} W/2$, $z > 0$ and $C$ real. Let $x_\beta$ be the cone integral of $x$ with exponent $z$ on the side $\beta$ of Poisson's formula. Suppose that for every $\mathfrak{c}$ there is $\gamma \neq 0$ with $|\gamma|^2 L_*(e) = C\,L_*(e+1)$, such that for integral $w$ and all $g$ the constant term along $A$ of $\theta_{\mathrm{large}}(W', V'; x, \phi_{\mathrm{row}}(w))$ at $(1, g)$ is $\gamma\,\theta_{\mathrm{large}}(W, V; x_\beta, \phi_{\mathrm{row}}(w))(g)$. Then $\mathrm{RC}(W', V', U; x, y; \ell)$ implies $\mathrm{RC}(W, V, U; x_\beta, y_0; \ell)$.

Lean: `New.Exchange.RowColExchangeIdentity.of_planeConstantTerm_eq` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The cone integral of a Schwartz vector is a Schwartz vector for $z > 0$, and so is a slice. Let $D$ and $c$ be the data of the identity above, so $D|c|^2 = L_*(e')\ell(\mathfrak{c})$ with $e' = \operatorname{rk} V' - \operatorname{rk} W'/2$. The ranks give $e' = e + 1$. Take the new constant $D' = DC/|\kappa_A|^2$ and the new factor $c' = c\kappa_A/\gamma$. Then
$$D'|c'|^2 = \frac{C\,D|c|^2}{|\gamma|^2} = \frac{C\,L_*(e+1)\,\ell(\mathfrak{c})}{|\gamma|^2} = L_*(e)\,\ell(\mathfrak{c}).$$
For the identity of theta integrals, take the constant term along $A$ of the identity for $(W', V', U)$ at the datum $w\pi_W$, which is integral. The left side becomes $\gamma\,\theta_{\mathrm{large}}(W, V; x_\beta)$ by hypothesis. The right side becomes $c\kappa_A\,\theta_{\mathrm{small}}(W, U; y_0)$ by the lemma on the side of $U$. Divide by $\gamma \neq 0$. $\square$

**Theorem (Removing a plane by the cone).** Let $\operatorname{rk} W$ be even, $A$, $X$ as above, and $\operatorname{rk} V - \operatorname{rk} W/2 = z \geq 0$ an integer. Then $\mathrm{RC}(W', V', U; x, y; \ell)$ implies $\mathrm{RC}(W, V, U; \operatorname{cone}_{z+1}(x), y_0; \ell)$.

Lean: `New.Exchange.RowColExchangeIdentity.cone` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The tower (`New.Exchange.exists_planeConstantTerm_eq_thetaLarge_cone`, [Volume 6](/chapter/rallis-inner-product/#the-tower)) gives $C_0 > 0$ and, for each $\mathfrak{c}$, $\gamma$ with $|\gamma| = C_0\,L^\sharp(z+1)$ such that the constant term at $(1, g)$ is $\gamma$ times the theta integral at $\operatorname{cone}_{z+1}(x)$. As $L^\sharp(z+1) > 0$, $\gamma \neq 0$. By $L_*(z+1) = L^\sharp(z+1)^2 L_*(z)$,
$$|\gamma|^2 L_*(z) = C_0^2\,L^\sharp(z+1)^2 L_*(z) = C_0^2\,L_*(z+1).$$
Apply the lemma with $C = C_0^2$ and $\beta$ the first side. $\square$

**Theorem (Removing a plane by the dual cone).** With the same data, if $\operatorname{rk} V - \operatorname{rk} W/2 = -(z+1) < 0$, then $\mathrm{RC}(W', V', U; x, y; \ell)$ implies $\mathrm{RC}(W, V, U; \operatorname{cone}^\vee_{z+1}(x), y_0; \ell)$.

Lean: `New.Exchange.RowColExchangeIdentity.dualCone` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The same, with the tower result for the other side of Poisson's formula. Now $e = -(z+1)$ and $e + 1 = -z$. By $L_*(-z) = L^\sharp(z+1)^2 L_*(-(z+1))$ we get $|\gamma|^2 L_*(-(z+1)) = C_0^2 L_*(-z)$. $\square$

The two cases are needed because $L^\sharp$ is formed from the Euler product. The book uses it only at points $\geq 1$, and Poisson's formula is applied before the integral is computed.

**Lemma (One plane).** Let $\operatorname{rk} W$ be even, $A$ an adapted splitting $W' = W \oplus H$, and let $V'$ have one minus sign more than $V$, with $\operatorname{rk} U + \operatorname{rk} V = \operatorname{rk} W$ and $\operatorname{rk} U + \operatorname{rk} V' = \operatorname{rk} W'$. Then $\mathrm{RC}(W', V', U; x, y; \ell)$ implies $\mathrm{RC}(W, V, U; x_0, y_0; \ell)$ for some $x_0$.

Lean: `New.Exchange.exists_rowColExchangeIdentity_removing_plane` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* The ranks give $\operatorname{rk} V' = \operatorname{rk} V + 2$. By the lemma on adapted splittings there is a space $V_1$ with the signs of $V'$ and an adapted splitting of $V_1$ over $V$ with one plane. By the corollary the identity holds for $(W', V_1, U)$. The integer $\operatorname{rk} V - \operatorname{rk} W/2$ is $z$ or $-(z+1)$ for some natural $z$. Apply the cone or the dual cone theorem. $\square$

### Descent along many planes

**Theorem (Removing planes).** Let $\operatorname{rk} W$ be even, let $A$ split $W'$ as $W$ plus $|p| \geq 1$ hyperbolic planes and be adapted, and let $V'$ have $|p|$ minus signs more than $V$, with the rank conditions $\operatorname{rk} U + \operatorname{rk} V = \operatorname{rk} W$ and $\operatorname{rk} U + \operatorname{rk} V' = \operatorname{rk} W'$. Then $\mathrm{RC}(W', V', U; x, y; \ell)$ implies $\mathrm{RC}(W, V, U; x_0, y_0; \ell)$ for some $x_0$, where $y_0$ is the zero term of $y$ along $A$.

Lean: `New.Exchange.exists_rowColExchangeIdentity_removing_planes` (New/Determinant/Exchange/RemovingPlanes.lean).

*Proof.* Strong induction on $d = |p|$. If $d = 1$, index the plane by a one-point set. This gives an adapted splitting $B$ with the same frame columns and inclusion as $A$. By part (a) of the lemma on zero terms, $B$ and $A$ have the same zero term. Apply the lemma for one plane.

If $d = d' + 2$, split $p$ as $d' + 1$ planes and one plane. There is an adapted splitting $B$ of $W'$ over $W \oplus H$ with $d'+1$ planes, such that $B$ followed by the standard splitting of $W \oplus H$ over $W$ has the frame columns and inclusion of $A$. Let $Y = V \oplus H$. Its signs have one minus sign more than those of $V$, so $V'$ has $d'+1$ more than $Y$, and $\operatorname{rk}(W \oplus H)$ is even. By induction, the identity holds for $(W \oplus H, Y, U)$ at some $x_1$ and the zero term of $y$ along $B$. By induction again, with one plane, it holds for $(W, V, U)$ at some $x_0$ and the zero term along the standard splitting of the zero term along $B$. By part (b), this is the zero term along the composite, and by part (a) it is the zero term along $A$. $\square$

**Remark (Formalization).** The vector $x_0$ is an iterated cone or dual cone integral of $x$. The theorem forgets it and keeps only its existence, because later steps need only the vector $y_0$ on the small side. The cone integral at each step uses the weight $\mu$ of the fixed family of characters, and the constant $D$ changes at each step by $C_0^2/|\kappa_A|^2$, which does not depend on $\mathfrak{c}$. The theorem has no hypothesis on $\mu$. Signs enter only through the counts of minus signs, so the spaces $V$, $V'$ are free up to their signs.

### Example: one plane

Let $W$ have rank $2$, and let $U$ and $V$ have rank $1$. Then $\operatorname{rk} V - \operatorname{rk} W/2 = 0$. Add one plane: $W' = W \oplus H$ of rank $4$ and $V'$ of rank $3$ with one minus sign more than $V$. The theorem on cones applies with $z = 0$. Here $|\gamma|^2 = C_0^2 L^\sharp(1)^2$, and $L_*(1) = L^\sharp(1)^2 L_*(0)$ with $L_*(0) = 1$. The constant $D$ changes to $D C_0^2/|\kappa_A|^2$. With two planes, $W'$ has rank $6$ and $V'$ rank $5$. The first step goes down to $(W \oplus H, V \oplus H)$, where $\operatorname{rk} - \operatorname{rk}/2 = 3 - 2 = 1$, so the cone has exponent $2$. The second step goes down to $(W, V)$, where this number is $0$, so the cone has exponent $1$.
