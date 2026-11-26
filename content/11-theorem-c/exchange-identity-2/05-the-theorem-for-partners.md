---
title: The theorem for partners
lean:
  - New/Determinant/Exchange/TheoremForPartners.lean
decls:
  - New.Exchange.adjointDatum
  - New.Exchange.IsSchwartzVector.adjointDatum
  - New.Exchange.neg_mem_flipSpace_Gamma_iff
  - New.AreMatched.right_eq_pow_mul_apply_smul
  - New.Exchange.exists_localDatum_adjointDatum_eq_smul
  - New.Exchange.exists_mul_thetaSmall_adjointDatum_eq_mul_integral
  - New.Exchange.thetaLarge_eq_smul_of_areMatched
  - New.Exchange.exists_rowColExchangeIdentity_of_even_rank
  - New.Exchange.exchange_of_matches
  - New.Exchange.integral_thetaOnRealData_eq_zero
  - New.Exchange.isSchwartzVector_realPairWeil
  - New.Exchange.thetaLargeVanishes_of_equalRankThetaRatio_eq_zero
  - New.Exchange.exists_equalRankThetaRatio_ne_zero
  - New.Exchange.eq_mul_of_integral_pairTheta
  - New.Exchange.exists_thetaLarge_eq_mul_quotMeasure
  - New.Exchange.exists_quotMeasure_mul_eq_mul_integral_pairTheta
  - New.Exchange.exists_equalRankThetaRatio_sq_eq
  - New.Exchange.exists_equalRankThetaRatio_const_ne_zero
  - New.Exchange.exists_equalRankThetaRatio_add_plane
  - New.Exchange.equalRankThetaRatio_eq_of_signs_eq
  - New.Exchange.exists_equalRankThetaRatio_eq_const
  - New.Exchange.spaceChar_mul_spaceChar_eq_iff
  - New.Exchange.exists_areMatched_modDatum_eq
  - New.Exchange.exchange_theorem
  - New.Exchange.exchange_identity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The theorem for partners

This section proves the exchange identity of Section 1. It has three parts. First, the identity on standard data for $(W, V, U^-)$ comes down the tower and passes to all matched data and to the pair $(U, W)$. Second, the equal rank ratio of a good vector is a nonzero constant. Third, data modulo $\mathfrak{m}$ are lifted to matched data, and the splitting characters are twisted.

For a space $W$ of even rank and a Schwartz vector $z$ for $(W, W)$, the theta integral $I(z)$ of $(W, W)$ with the datum $\chi^{-1}\circ\det$ is constant, by the theorem on equal ranks of [the first part](/chapter/exchange-identity-1/#cone-images-and-the-large-triple). The *equal rank ratio* is $r_W(z) = |I(z)(1)|^2 / L_*(\operatorname{rk} W/2)$. It is $\geq 0$.

### The adjoint datum

Let $U^-$ be the opposite space of $U$, with signs $-u$. Passing to adjoint maps carries data for $(U, W)$ to data for $(W, U^-)$. On finite adelic matrices it is the conjugate transpose times a fixed integral unit $\epsilon$ of norm $-1$. On real data it gives a vector $y^{\mathrm{ad}}$ for each $y$.

**Lemma.** (a) If $y$ is a Schwartz vector, so is $y^{\mathrm{ad}}$. (b) The identity on matrices carries the rational points of $U$ onto those of $U^-$. (c) If $\Phi$, $\Psi$ are matched for $\chi$ and $\varepsilon$ is a unit, then $\Psi(X) = \chi(\varepsilon)^{|b|}\,\Psi(\varepsilon X)$.

Lean: `New.Exchange.adjointDatum`, `New.Exchange.IsSchwartzVector.adjointDatum`, `New.Exchange.neg_mem_flipSpace_Gamma_iff`, `New.AreMatched.right_eq_pow_mul_apply_smul` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* (a) The real change of coordinates swaps the two indices of each coordinate and keeps its modulus, so it keeps the norm. It also keeps the vacuum measure. So every moment of $y^{\mathrm{ad}}$ is the same moment of $y$. (b) The point of $U^-$ is the conjugate inverse of the point of $U$ up to sign, and the condition on rational points is the same. (c) $\varepsilon X = X \cdot \varepsilon 1_b$, and the matching law for right multiplication by $\varepsilon 1_b \in \mathrm{GL}_b(O)$ gives the factor $\chi(\det \varepsilon 1_b) = \chi(\varepsilon)^{|b|}$. $\square$

**Lemma (Adjoint data).** Let $\operatorname{rk} W$ be even and $\gamma = \nu^{-1}\upsilon^{\operatorname{rk} W/2}$. For each Schwartz $y$ for $(U, W)$ there is $d$ with $|d| = 1$ such that for all matched $\Phi$, $\Psi$ with $\Psi$ Schwartz-Bruhat on left invertible matrices and all $g$,
$$\gamma(\det g)\,\theta_{\mathrm{small}}(W, U^-; y^{\mathrm{ad}}, \Psi)(g) = d \int_{[U(U)]} \theta^{U, W}_{\gamma, \gamma}(y, \Psi)(h, g)\, dh.$$

Lean: `New.Exchange.exists_localDatum_adjointDatum_eq_smul`, `New.Exchange.exists_mul_thetaSmall_adjointDatum_eq_mul_integral` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* By part (c) with $\varepsilon = \epsilon$, the datum with real part $y^{\mathrm{ad}}$ and finite part $x \mapsto \Psi(x^T)$ at the conjugate places is $a = \chi(\epsilon)^{|b|}$ times the adjoint image of the datum with real part $y$ and $\Psi$ at the ramified places. The flip theorem of [the Weil representation](/chapter/weil-representation/) says that the theta kernels of $(U, W)$ and $(W, U^-)$ agree under the adjoint, up to a factor $d_0$ of modulus one. The integral over $[U(U^-)]$ is the integral over $[U(U)]$, by part (b) and the change of sign of Section 3. The characters agree: $\gamma(\det g)$ times the characters of $\theta_{\mathrm{small}}$ give $\gamma, \gamma$. Take $d = a d_0$. $\square$

### From standard data to matched data

**Lemma.** Let $\operatorname{rk} W$ be even, $v$, $y$ Schwartz vectors and $c \in \mathbb{C}$. Suppose that $\theta_{\mathrm{large}}(W, V; v, \phi_{\mathrm{row}}(z)) = c\,\theta_{\mathrm{small}}(W, U; y, \phi_{\mathrm{col}}(z))$ for every integral $z$. Then for all matched $\Phi$, $\Psi$ with $\Psi$ locally constant, $\Psi$ is Schwartz-Bruhat on the left invertible matrices and $\theta_{\mathrm{large}}(v, \Phi) = c\,\theta_{\mathrm{small}}(y, \Psi)$.

Lean: `New.Exchange.thetaLarge_eq_smul_of_areMatched` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* The theorem on the equivariant difference of [the first part](/chapter/exchange-identity-1/#the-equivariant-difference) gives a space $M$ and an equivariant lift $\mathcal{D}$ with $\mathcal{D}\Psi = \theta_{\mathrm{large}}(v, \Phi) - c\,\theta_{\mathrm{small}}(y, \Psi)$ for matched pairs. The first columns of the identity form a primitive matrix, so there is an integral $z$ with $\phi_{\mathrm{col}}(z)$ matched with $\phi_{\mathrm{row}}(z)$. By hypothesis $\mathcal{D}\phi_{\mathrm{col}}(z) = 0$, so $\phi_{\mathrm{col}}(z) \in M \cap \ker\mathcal{D}$. The space $M \cap \ker \mathcal{D}$ is stable under the translations of an equivariant lift. By the theorem [one standard datum suffices](/chapter/exchange-identity-1/#stable-spaces-and-self-dual-lattices) it contains every matched $\Psi$. So $\mathcal{D}\Psi = 0$. $\square$

### Down the tower

**Lemma (Identity at even rank).** Let $W_0 = H \oplus W$, let $\operatorname{rk} W = |b| + |r|$ be even, and let $\operatorname{neg}(u) + \operatorname{neg}(s) = |b| + \operatorname{neg}(t)$. For Schwartz vectors $z$ for $(W_0, W_0)$ and $y$ for $(W, U)$ there is $v$ for $(W, V)$ with $\mathrm{RC}(W, V, U; v, y; r_{W_0}(z))$.

Lean: `New.Exchange.exists_rowColExchangeIdentity_of_even_rank` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Let $A$ be the standard splitting of $W_0$ over $W$. By Section 2 there is a Schwartz $w$ for $(W_0, U)$ with zero term $y$ along $A$. Let $X = H^{|b|} \oplus W_0$ with its standard splitting $D$. The theorem on the large triple of Section 2, for $D$, $A$, $V' = U$ and $v = w$, $v_1 = z$, gives $x$ and $x'$ with $\mathrm{RC}(X, U \oplus W_0, U; x, x'; r_{W_0}(z))$ and with the slice of $x'$ at $0$ along $D^{\mathrm{sym}}$ equal to $w$. The composite of $D^{\mathrm{sym}}$ and $A$ splits $X$ over $W$ with $|b| + 1$ planes. By part (b) of the lemma on zero terms, the zero term of $x'$ along it is the zero term of $w$ along $A$, which is $y$. The space $U \oplus W_0$ has $\operatorname{neg}(u) + 1 + \operatorname{neg}(s) = (|b| + 1) + \operatorname{neg}(t)$ minus signs. So the theorem on removing planes of Section 3 applies with $|p| = |b| + 1$. $\square$

**Theorem (Exchange for matched data).** Let $W_0 = H \oplus W$, let $\operatorname{rk} W = |b| + |r|$ be even, and let $\operatorname{neg}(s) = \operatorname{neg}(t) + \operatorname{neg}(u)$. For Schwartz vectors $z$ for $(W_0, W_0)$ and $y$ for $(U, W)$ there are $C$ and a Schwartz $v$ for $(W, V)$ such that every $\mathfrak{c}$ has $c$ with:

(a) $C|c|^2 = L_*(\operatorname{rk} V - \operatorname{rk} W/2)\, r_{W_0}(z)$;

(b) for all matched $\Phi$, $\Psi$ with $\Psi$ locally constant and all $g$,
$$\int_{[U(V)]} \theta^{W,V}_{\gamma, 1}(v, \Phi)(g, h)\,dh = c\int_{[U(U)]}\theta^{U,W}_{\gamma,\gamma}(y, \Psi)(h, g)\,dh.$$

Lean: `New.Exchange.exchange_of_matches` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* The opposite space $U^-$ has $\operatorname{neg}(-u) = |b| - \operatorname{neg}(u)$, so $\operatorname{neg}(-u) + \operatorname{neg}(s) = |b| + \operatorname{neg}(t)$. The lemma at even rank for $(W, V, U^-)$ and the vector $y^{\mathrm{ad}}$ gives $v$, $C$ and, for each $\mathfrak{c}$, a factor $c_0$. Let $d$ be the factor of the lemma on adjoint data, and $c = c_0 d$; then $|c| = |c_0|$ and (a) holds. For (b), the lemma on matched data gives $\theta_{\mathrm{large}}(v, \Phi) = c_0\,\theta_{\mathrm{small}}(W, U^-; y^{\mathrm{ad}}, \Psi)$. The left side of (b) is $\gamma(\det g)\,\theta_{\mathrm{large}}(v, \Phi)(g)$, as the second character enters as its inverse at $\det g$. Multiply by $\gamma(\det g)$ and use the lemma on adjoint data. $\square$

### The equal rank ratio

Let $J$ be positive definite of rank $2k$, and $Y = H \oplus J$.

**Lemma (Non-vanishing).** Let $k \leq \mu_w$ at every infinite place. For each $\mathfrak{c}$ there is a Schwartz $v$ with $r_Y(v) \neq 0$.

Lean: `New.Exchange.exists_equalRankThetaRatio_ne_zero`, `New.Exchange.thetaLargeVanishes_of_equalRankThetaRatio_eq_zero`, `New.Exchange.integral_thetaOnRealData_eq_zero`, `New.Exchange.isSchwartzVector_realPairWeil` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Suppose $r_Y(v) = 0$ for all Schwartz $v$. Then $I(v) = 0$ for all $v$, as $I(v)$ is constant and $L_* > 0$.

Step 1. The theta integral of $(H^{2k} \oplus Y, J^- \oplus Y)$ vanishes on all Schwartz vectors and standard data. Each period of the period identity, for the standard splitting with $V' = J^-$ and $W_1 = Y$, is an integral over $[U(Y)]$ of a theta functional on real data. Expand the real vector $w$ into coherent states. Each coherent state for $J^- \oplus Y$ is the product of a coherent state for $J^-$ and one for $Y$. So the integral is $I$ of a superposition of vectors for $(Y, Y)$, which is a Schwartz vector, and it is $0$. The real Weil action keeps Schwartz vectors, as it keeps all moments up to a constant. So the period identity holds with period $0$ and weight $1$. The sign alternative of "exchange from periods" holds: $J^-$ has all signs $-1$, $Y$ has a sign $1$, and $2\operatorname{neg}(Y) = 2 \leq 2k + 2$. Part 2 of that theorem gives $\theta_{\mathrm{large}} = C\,\theta_{\mathrm{small}}$ with $|C| = K \cdot 0$. So $\theta_{\mathrm{large}} = 0$.

Step 2. The pair $(H^{2k} \oplus Y, J^- \oplus Y)$ has $2k + 1$ planes over $(J, 0)$. Its first space has $2k+1$ minus signs, and its second has $2k + 1$ more minus signs than the zero space. The rank of $J$ is even, and $0 - 2k/2 = -k$. By the theorem of Section 4 with $j = 2k + 1$, the theta integral of $(J, 0)$ vanishes.

Step 3. The theta integral of $(J, 0)$ at the vacuum and the datum $\phi_{\mathrm{row}}(1)$, whose value at the empty matrix is $1$, is the volume of $[U(J)]$, which is positive. This contradicts Step 2. $\square$

**Lemma (The identity used twice).** For each Schwartz $v$ for $(Y, Y)$ there is $D$ with $r_Y(v)^2 = D$ for all $\mathfrak{c}$ of weight $\mu$.

Lean: `New.Exchange.exists_equalRankThetaRatio_sq_eq`, `New.Exchange.exists_thetaLarge_eq_mul_quotMeasure`, `New.Exchange.exists_quotMeasure_mul_eq_mul_integral_pairTheta`, `New.Exchange.eq_mul_of_integral_pairTheta` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Let $Z$ be the zero space, and $\mathrm{vol} > 0$ the volume of $[U(Z)]$. Apply the exchange for matched data twice, with $W = J$ and $z = v$.

First, to $(J, J, Z)$ with $y$ the vacuum: it gives $B$ and $y'$ with $\theta_{\mathrm{large}}(J, J; y', \chi^{-1}\circ\det)(g) = c_1\,\mathrm{vol}$ and $B|c_1|^2 = L_*(k)\,r_Y(v)$. Here $2k - k = k$, and the theta kernel of $(Z, J)$ is $1$.

Second, to $(J, Z, J)$ with the vector $y'$: it gives $C$ and $x$ in the Fock space $\mathbb{C}$ of $(J, Z)$. With $\xi$ the theta functional at $x$, $\mathrm{vol}\cdot\xi = c_2 \int \theta^{J,J}_{\gamma,\gamma}(y')(h, g)\,dh$ and $C|c_2|^2 = L_*(-k)\,r_Y(v)$.

The theta kernel of $y'$ is integrated over each group. By Fubini both orders agree, and so $\mathrm{vol}\cdot\xi = c_2 c_1\,\mathrm{vol}$, that is $\xi = c_1 c_2$. As $L_*(k)L_*(-k) = 1$,
$$r_Y(v)^2 = L_*(k)\,r_Y(v)\cdot L_*(-k)\,r_Y(v) = B|c_1|^2\cdot C|c_2|^2 = BC|\xi|^2.$$
The numbers $B$, $C$, $\xi$ do not depend on $\mathfrak{c}$. $\square$

**Lemma (The first floor).** If $k \leq \mu_w$ at every place, some Schwartz $v$ has $r_Y(v) = C$ for one $C \neq 0$ and all $\mathfrak{c}$.

Lean: `New.Exchange.exists_equalRankThetaRatio_const_ne_zero` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* If there is no $\mathfrak{c}$, take the vacuum and $C = 1$. Otherwise fix $\mathfrak{c}_0$ and take $v$ with $r_Y(v) \neq 0$ at $\mathfrak{c}_0$. Its square is the same for all $\mathfrak{c}$, and $r_Y(v) \geq 0$. So $r_Y(v)$ is the same nonzero number for all $\mathfrak{c}$. $\square$

**Lemma (Adding a plane).** Let $\operatorname{rk} W = 2d$ and let $A$ be an adapted splitting $W' = W \oplus H$. Each Schwartz $v$ for $(W, W)$ has a Schwartz $v'$ for $(W', W')$ and $C > 0$ with $r_{W'}(v') = C\,r_W(v)$ for all $\mathfrak{c}$. If $Y_1$ has the signs of a space $Y$ of even rank with an adapted splitting over some space, then $r_{Y_1} = r_Y$.

Lean: `New.Exchange.exists_equalRankThetaRatio_add_plane`, `New.Exchange.equalRankThetaRatio_eq_of_signs_eq` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* The tower, with $V = W$ and $z = d$, gives $C_0 > 0$ and $\kappa$ with $|\kappa| = C_0\,L^\sharp(d+1)$, such that the constant term of $I(v')$ is $\kappa$ times the theta integral at $\operatorname{cone}_{d+1}(v')$. The cone image theorem of the first part, in the form with a fixed exponent, gives $v'$ whose cone has the theta integrals of $v$. The function $I(v')$ is constant, so it equals its constant term: $I(v')(1) = \kappa\, I(v)(1)$. With $L_*(d+1) = L^\sharp(d+1)^2 L_*(d)$, we get $r_{W'}(v') = C_0^2\, r_W(v)$. For the second claim, the change of space of Section 3 moves the point and multiplies by a number of modulus one, and $I$ is constant. $\square$

**Theorem (The value of the equal rank ratio).** Let $\operatorname{rk} W = 2k + 2\operatorname{neg}(s)$ and $k \leq \mu_w$ at every infinite place. There are a Schwartz $z$ for $(H \oplus W, H \oplus W)$ and $C_0 \neq 0$ with $r_{H \oplus W}(z) = C_0$ for all $\mathfrak{c}$ of weight $\mu$.

Lean: `New.Exchange.exists_equalRankThetaRatio_eq_const` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Induction on $q = \operatorname{neg}(s)$. If $q = 0$, all signs are $1$ and $H \oplus W$ has the signs of $H \oplus J$ with $J$ standard of rank $2k$. Apply the first floor and the invariance under signs. If $q + 1$, let $W_0 = H^q \oplus J$ with $J$ of rank $2k$; it has $q$ minus signs and rank $2k + 2q$. By induction there is $z_0$ for $H \oplus W_0$ with constant ratio $C$. There is a space $Y$ with the signs of $H \oplus W$ and an adapted splitting over $H \oplus W_0$ with one plane. Adding a plane gives $z$ with ratio $C'C \neq 0$ on $Y$, and on $H \oplus W$ by the invariance under signs. $\square$

### Data modulo an ideal

**Lemma.** Let $\operatorname{card} N = p + q$ be even. The space characters satisfy $\alpha_p\,\alpha'_q = (\nu\circ(z \mapsto z/\bar z))^{-1}$ if and only if $\alpha\alpha' = \nu^{-1}\upsilon^{\operatorname{card} N/2}$.

Lean: `New.Exchange.spaceChar_mul_spaceChar_eq_iff` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Space characters multiply, so the left side is the space character of $\alpha\alpha'$ in rank $p + q$. The space character of the rank twist of $\nu^{-1}$ is the inverse base change of $\nu$, and base change is injective. $\square$

**Lemma (Lifting).** Let $\mathfrak{c}$ be ramified exactly at the primes of $\mathfrak{m}$, and let $\Phi$, $\Psi$ be matched over $O_E/\mathfrak{m}$ for the product $\chi$ of the residue characters. There are $\Phi'$, $\Psi'$ on matrices over the completions, matched over the local integers for $\chi_{\mathfrak{c}}$, with $\Psi'$ locally constant, that give the same adelic data as $\Phi$ and $\Psi$ for every real vector.

Lean: `New.Exchange.exists_areMatched_modDatum_eq` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Reduction modulo $\mathfrak{m}$ reads only the components at the primes of $\mathfrak{m}$, so it factors through a ring map $\pi$ from the local integers $O$ onto $O_E/\mathfrak{m}$. It is onto, and it detects units, as it is compatible with the residue maps. On units $\chi_{\mathfrak{c}} = \chi\circ\pi$, since both are the product of the residue characters. Let $\Phi'$, $\Psi'$ be $\Phi\circ\pi$, $\Psi\circ\pi$ on integral matrices and $0$ elsewhere. Matching lifts along such a $\pi$. $\Psi'$ is locally constant, as the lift of a function modulo $\mathfrak{m}$ is Schwartz-Bruhat. The data agree by definition of the lift. $\square$

**Theorem (Exchange theorem).** Under hypotheses 1 to 4 of Section 1 and for a Schwartz $v$ for $(V', W)$, there are $C$ and a Schwartz $x$ for $(W, V)$ such that for every $\nu$ tame for $(\mathfrak{m}, \mu, \chi)$ there is $c \neq 0$ with $|c|^2 = C\,L_{\mathfrak{m}}(\nu, e)$ and, for matched $\Phi$, $\Psi$ modulo $\mathfrak{m}$,
$$\int_{[U(V)]}\theta^{W,V}_{\gamma, 1}(\operatorname{modDatum}(\Phi, x)) = c\int_{[U(V')]}\theta^{V',W}_{\gamma,\gamma}(\operatorname{modDatum}(\Psi, v)).$$

Lean: `New.Exchange.exchange_theorem` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof.* Let $q = \operatorname{neg}(s)$. The ranks give $|n| = 2|b| + 2e$, so $|n|$ is even. Put $k = |n|/2 - q$; by hypothesis 3, $|n| = 2k + 2q$. By hypothesis 4, $k \leq \mu_w$. The value of the equal rank ratio gives $z$ and $C_0 \neq 0$. The exchange for matched data, for $(W, V, V')$ and $y = v$, gives $C_1$ and $x$. Let $\nu$ be tame for $(\mathfrak{m}, \mu, \chi)$. It defines a split tame character $\mathfrak{c}$ with ramified set the primes of $\mathfrak{m}$. Its weight is positive: hypotheses 3 and 4 give $2\mu_w \geq |n| - 2q \geq 2$. The modulus has no prime together with its conjugate. Then $L_*(e) = L_{\mathfrak{m}}(\nu, e)$ and $|a| - |n|/2 = e$, so $C_1|c|^2 = L_{\mathfrak{m}}(\nu, e)\,C_0$. The right side is nonzero, so $C_1 \neq 0$ and $c \neq 0$, and $|c|^2 = (C_0/C_1)\,L_{\mathfrak{m}}(\nu, e)$. Lift $\Phi$, $\Psi$ and apply (b). $\square$

Lean: `New.Exchange.exchange_identity` (New/Determinant/Exchange/TheoremForPartners.lean).

*Proof of the exchange identity of Section 1.* Take $C$, $x$ from the exchange theorem. If $C \leq 0$, no tame $\nu$ exists: it would give $|c|^2 > 0$ and $C\,L_{\mathfrak{m}}(\nu, e) \leq 0$. Then $C = 1$ works. Otherwise $C > 0$, and $C\,L_{\mathfrak{m}}(\nu, e) = |c|^2 \neq 0$. Let $\alpha$, $\alpha'$ satisfy the condition on space characters. By the last lemma $\alpha\alpha' = \gamma$, so $\alpha' = \gamma\alpha^{-1}$. By the twist law of the theta kernel, changing the second character of $\theta^{W,V}$ from $1$ to $\alpha$ multiplies it by $d = \alpha(\det g)^{-1}$. Changing the first character of $\theta^{V',W}$ from $\gamma$ to $\gamma\alpha^{-1}$ also multiplies it by $d$. Both sides of the exchange theorem are multiplied by $d$. $\square$

**Remark (Formalization).** Three points. First, hypothesis 3 has the margin $+2$, and it is used only to give $\mu_w \geq 1$ in the construction of $\mathfrak{c}$. The rest of the proof needs $2\operatorname{neg}(s) \leq |n|$, which makes $k$ a natural number. Research note e §4.3 states the hypothesis with $+2$, as the source does. A form with $2\operatorname{neg}(s) \leq |n|$ and $\mu > 0$ would also follow from this proof. Second, the constant of the exchange theorem is $C_0/C_1$ and may be $\leq 0$ only if no tame character exists; the exchange identity then replaces it by $1$. Third, the first floor needs a character to fix the vector, so the vector $z$ depends on the choice of one character $\mathfrak{c}_0$. The constants $B$, $C$, $\xi$ come from existence statements and are not computed.
