---
title: First properties and decay
lean:
  - Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean
  - Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean
  - Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean
  - Lib/DiscreteSeries/Haar/TotalMass.lean
  - Lib/General/LinearAlgebra/MinorProducts.lean
decls:
  - New.dsCoeff_one
  - New.dsCoeff_of_mem_maxCompactU
  - New.dsCoeff_polar
  - New.dsCoeff_inv
  - New.dsCoeff_neg
  - New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose
  - New.HCParam.splitCoeff
  - New.splitCoeff_eq_dsCoeff
  - New.HCParam.analyticAt_dsCoeff
  - New.casimir_dsCoeffSmooth
  - New.integral_conj_weightMinors_lowestKType_mul_dsCoeff
  - New.integral_conj_weightMinors_mul_dsCoeff_eq_zero
  - New.norm_det_blockDiagPart
  - New.sq_le_norm_det_blockDiagPart
  - New.fischer_inequality
  - New.norm_dsCoeff_sq_mul_det_pow_le_one
  - New.DiscreteSeries.norm_dsCoeff_le_pow
  - New.DiscreteSeries.norm_dsCoeff_le_one
  - New.DiscreteSeries.integral_decay_le
  - New.integrable_two_div_norm_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## First properties and decay

This section proves the properties of $c_\lambda$ that do not need the formal degree. The first group is read off from the integral over $K$: the value at $1$, the values on $K$, the symmetries, the independence of the splitting, analyticity and the Casimir equation, and the projections to $K$-types. The second group is the decay: $|c_\lambda(g)| \le (2/\|g\|)^c$ for each $c$ up to the gap, and the integrability of $(2/\|g\|)^c$ for $c > 8n^2$. Together they make $c_\lambda$ square integrable when the gap is large. Throughout, $l = 2\lambda$ is a parameter of gap $h$ for the signs $\varepsilon$, $G = U(\operatorname{diag}\varepsilon)$, and $\|g\|$ is the operator norm of $g$ on $\mathbb C^n$.

### Values on $K$ and symmetries

**Theorem.** For every integer vector $l$, $c_\lambda(1) = 1$.

Lean: `New.dsCoeff_one` (Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean).

*Proof.* At $g = 1$ the block diagonal part is $1$ and $a_g^{-1}g = 1$. The denominator is $m_{-(\lambda+\rho)}(k^*k) = m_{-(\lambda+\rho)}(1) = 1$, and the numerator is $|m_\Lambda(k)|^2$. Its integral is the normalising constant $\int_K |m_\Lambda|^2$, which is positive. $\square$

**Theorem.** If $l$ has some gap and $k \in K$, then $c_\lambda(k) = m_\Lambda(k)$.

Lean: `New.dsCoeff_of_mem_maxCompactU` (Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean).

So on $K$ the function $c_\lambda$ is the coefficient of a highest weight vector of the $K$-type $\Lambda$: the classical property of the coefficient of a unit vector of weight $\Lambda$ in the lowest $K$-type.

Each $g \in G$ has a polar decomposition $g = kz$ with $k \in K$ and $z \in G$ positive definite (`New.exists_polar`). For such factors the coefficient has an explicit integral.

**Theorem.** Let $l$ have gap $h$, let $p, q \in K$, and let $z \in G$ be positive definite. Then

$$c_\lambda(p z q^{-1}) = \frac{1}{\int_K |m_\Lambda|^2}\int_K \frac{m_\Lambda(pu)\,\overline{m_\Lambda(qu)}}{m_{-(\lambda+\rho)}(u^* z u)}\,du.$$

Lean: `New.dsCoeff_polar` (Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean).

**Theorem.** Let $l$ have gap $h$ and $g \in G$. Then $c_\lambda(g^{-1}) = \overline{c_\lambda(g)}$, and $c_{-\lambda}(g) = \overline{c_\lambda(g)}$.

Lean: `New.dsCoeff_inv`, `New.dsCoeff_neg` (Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean).

*Proof.* For $g \in G$ each principal minor of $g^{-1}$ is the conjugate of the same minor of $g$, so $m_w(g^{-1}) = \overline{m_w(g)}$ and $m_{-w}(g) = \overline{m_w(g)}$ (`New.weightMinors_unitary_inv`, `New.weightMinors_unitary_neg`). Write $g = kz$ as above. Then $g^{-1} = z^{-1}k^{-1}$, and $z^{-1}$ is positive definite. Put both in the polar formula. The change of variables $u \mapsto k^{-1}u$ in $K$ and the rule for $m_w(g^{-1})$ show that the two integrands are conjugate. For $-\lambda$, the vectors $\Lambda$ and $\lambda + \rho$ change sign with $l$, and the rule for $m_{-w}$ conjugates the integrand. $\square$

The first identity is the property $\langle \pi(g^{-1})v, v\rangle = \overline{\langle \pi(g)v, v\rangle}$ of a coefficient of a unitary representation. The second is the passage to the contragredient representation, whose parameter is $-\lambda$.

### Independence of the splitting

The definition of $c_\lambda(g)$ uses one splitting $g = a_g \cdot (a_g^{-1}g)$. The source proves that every splitting of the same kind gives the same value. A matrix $z$ is *accretive* if $z + z^*$ is positive definite.

**Theorem.** Let $l$ have gap $m$, and let $g \in G$ be a product $g = p z q^*$ with $p, q$ block diagonal for the signs and $z$ accretive. Then

$$c_\lambda(g) = \frac{1}{\int_K |m_\Lambda|^2}\int_K \frac{m_\Lambda(pk)\,\overline{m_\Lambda(qk)}}{m_{-(\lambda+\rho)}(k^* z k)}\,dk.$$

Lean: `New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose` (Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean).

*Proof.* The idea is that the integrand is a density on the flag variety of the complexified group $K_{\mathbb C}$. Let $I(p, r)$ be the integral over $K$ for the splitting data $(p, r)$. For a parameter with a gap, the integrand is invariant under the triangular subgroup of $K_{\mathbb C}$ in the sense that $I(px, x^*r) = I(p, r)$ for invertible block diagonal triangular $x$; this is where the gap enters, through the dominance of $\Lambda$ and $-(\lambda + \rho)$ for the compact roots (`New.HCParam.HasGap.isKDominant_lowestKType`, `New.HCParam.HasGap.isKDominant_neg_paramAddRho`). The function $I$ is holomorphic. Polarization of the invariance shows that the derivative of $I$ in $p$ vanishes in all block diagonal directions (`New.fderiv_splittingIntegral_eq_zero`). The block diagonal $a$ with $a^{-1}g$ accretive form a convex set, so the value is constant on it (`New.flenstedJensen_eq_of_accretive`). A splitting $g = pzq^*$ gives such an $a$, namely $a = pq^{-1}$, and the change of variables in $K$ turns the integral for $a$ into the integral in the statement. $\square$

The source also defines the function $\tilde c_\lambda$ on all matrices: at a matrix $g$ with $a^{-1}g$ accretive for some block diagonal $a$, it is Flensted-Jensen's integral at $(a, a^{-1}g)$ for one such $a$, and it is $0$ at other matrices.

Lean: `New.HCParam.splitCoeff` (Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean).

**Theorem.** If $l$ has gap $h$ and $g \in G$, then $\tilde c_\lambda(g) = c_\lambda(g)$.

Lean: `New.splitCoeff_eq_dsCoeff` (Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean).

**Remark (Formalization).** The definition of $\tilde c_\lambda$ takes the factor $a$ with `choose`, so the value depends on an arbitrary choice unless the independence theorem applies. For a parameter with a gap it applies on the whole open set where $\tilde c_\lambda$ is not $0$ by definition, and $\tilde c_\lambda$ is then holomorphic there (`New.analyticOnNhd_splitCoeff`). Off this set the value $0$ is a junk value. On $G$ the two functions agree, so the choice does not enter any statement about $c_\lambda$.

### Analyticity and the Casimir equation

**Theorem.** For every integer vector $l$ and every $g \in G$, the function $c_\lambda$ on complex $n \times n$ matrices is complex analytic at $g$.

Lean: `New.HCParam.analyticAt_dsCoeff` (Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean).

The block diagonal part is linear in $g$, and the integrand is analytic in $g$ near each point of $G$, uniformly in $k$. So one can differentiate under the integral sign. No gap is needed here. Because $c_\lambda$ is analytic on a neighbourhood of $G$, the source can regard it as a smooth function on $G$ (`New.HCParam.dsCoeffSmooth`), with a cutoff that is $1$ on $G$.

Let $E_{ab}$ be the matrix units of $\mathfrak{gl}_n(\mathbb C)$. They act on smooth functions on $G$ as right derivatives (`New.rightDeriv`). The Casimir operator is $\Omega = \sum_{a,b} E_{ab}E_{ba}$.

**Theorem.** Let $l$ have gap $h$. Then $\Omega c_\lambda = \kappa_\lambda c_\lambda$, with $\kappa_\lambda = |\lambda|^2 - |\rho|^2$ the value of Section 3.

Lean: `New.casimir_dsCoeffSmooth` (Lib/DiscreteSeries/FlenstedJensen/CasimirEigenfunction.lean).

*Proof.* Near a point $g_0$, freeze the block diagonal factor at $a = a_{g_0}$. By the independence of the splitting, $c_\lambda(g)$ is the average over $k \in K$ of $\Phi_k(g) = m_\Lambda(ak)\overline{m_\Lambda(k)}/m_{-(\lambda+\rho)}(k^*a^{-1}gk)$. For fixed $k$, the function $g \mapsto 1/m_{-(\lambda+\rho)}(k^* a^{-1} g k)$ is a lowest weight vector of weight $\lambda + \rho$ for the basis $kE_{ab}k^{-1}$ of $\mathfrak{gl}_n$: the derivatives in the directions $kE_{ab}k^{-1}$ with $l_a < l_b$ kill it, and the direction $kE_{aa}k^{-1}$ multiplies it by $(\lambda + \rho)_a$ (`New.fderiv_flenstedJensen_integrand_single`). The Casimir operator does not depend on the basis, so it acts on such a vector by the scalar that the classical computation gives for a lowest weight vector of weight $\lambda + \rho$ (`New.apply_casimirK_rightDeriv_of_lowest_weight`). The source checks that this scalar is $\kappa_\lambda$ (`New.casimirValue_eq_casimirKValue_paramAddRho`). Average over $k$. $\square$

### The $K$-types of $c_\lambda$

For an order $o$ on the indices (an integer vector), a weight $\nu$ is *$K$-dominant for $o$* if $\nu_j \le \nu_i$ whenever $\varepsilon_i = \varepsilon_j$ and $o_i < o_j$ (`New.IsKDominant`). The *root cone* of $l$ is the set of integer vectors $\beta$ with $o \cdot \beta \le 0$ for every $o$ that strictly reverses the order of $l$ (`New.HCParam.rootCone`). It is the cone spanned by the roots that are positive for $l$.

**Theorem.** Let $l$ have gap $h$, and let $x, b \in G$. Then

$$\int_K \overline{m_\Lambda(k)}\,c_\lambda(xkb)\,dk = \Big(\int_K |m_\Lambda|^2\Big)\,c_\lambda(x)\,c_\lambda(b).$$

If $\nu$ is $K$-dominant for $-l$ and $\nu - \Lambda$ is not in the root cone of $l$, then $\int_K \overline{m_\nu(k)}\,c_\lambda(xkb)\,dk = 0$.

Lean: `New.integral_conj_weightMinors_lowestKType_mul_dsCoeff`, `New.integral_conj_weightMinors_mul_dsCoeff_eq_zero` (Lib/DiscreteSeries/FlenstedJensen/PsiKTypes.lean).

For the coefficient of a unit vector $v$ of the lowest $K$-type, the first identity says that $\int_K \overline{\langle \pi(k)v, v\rangle}\,\pi(k)\,dk$ is $\int_K|m_\Lambda|^2$ times the projection onto $\mathbb C v$; that is, the $K$-type $\Lambda$ occurs once. The second says that the $K$-types of the representation lie in $\Lambda$ plus the cone of positive roots, a consequence of Blattner's formula (Hecht and Schmid, Invent. Math. 31 (1975)).

*Proof.* The source proves the identity for $b$ near $1$ first. There it writes $c_\lambda(xkb)$ as Flensted-Jensen's integral and averages over a circle in $K$ that is chosen with an order $o$ opposite to $l$ (`New.exists_order_dotProduct_eq_natCast`): the average multiplies the contribution of the weight $\nu$ by a natural number power of a parameter $t$, with exponent $o \cdot (\nu - \Lambda)$, and the exponent is $0$ only for $\nu = \Lambda$. Both sides are analytic in $b$ (`New.analyticAt_integral_conj_weightMinors_mul_dsCoeff`), so the identity holds for every $b \in G$. $\square$

### Fischer's inequality and the block diagonal part

The decay of $c_\lambda$ rests on a classical inequality for positive matrices.

**Theorem (Fischer's inequality).** Let $z$ be a positive semidefinite matrix, and let an index set $R$ be the disjoint union of $P$ and $Q$. Then $|\Delta_R(z)| \le |\Delta_P(z)|\,|\Delta_Q(z)|$.

Lean: `New.fischer_inequality` (Lib/General/LinearAlgebra/MinorProducts.lean).

See Horn and Johnson, *Matrix Analysis* (Cambridge University Press, 1985), Section 7.8.

**Theorem.** Let $g \in G$ and let $\sigma$ be a sign. Then $|\det a_g| = |\Delta_{\{i : \varepsilon_i = \sigma\}}(g)|^2$. If $n \ge 1$, then $(\|g\|/2)^2 \le |\det a_g|$.

Lean: `New.norm_det_blockDiagPart`, `New.sq_le_norm_det_blockDiagPart` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

*Proof.* The matrix $a_g$ has the two diagonal blocks of $g$, so $\det a_g$ is the product of the two principal minors for the two signs. For $g \in G$ the minor on the complement of a set is $\det g$ times the conjugate of the minor on the set (`New.U.principalMinor_compl`), and $|\det g| = 1$. So the two minors have the same absolute value. This gives the first claim.

For the second, write $g = kz$ with $k \in K$ and $z \in G$ positive definite. The factor $k$ changes neither $\|g\|$ nor $|\det a_g|$. Let $J = \operatorname{diag}\varepsilon$. From $z^*Jz = J$ and $z^* = z$ we get $z^{-1} = JzJ$, so $a_z = (z + JzJ)/2 = (z + z^{-1})/2$. So $\det a_z = \prod_x (x + x^{-1})/2$ over the eigenvalues $x$ of $z$. Each factor is $\cosh \log x \ge 1$. The numbers $\|z\|$ and $\|z\|^{-1} = \|z^{-1}\|$ are eigenvalues of $z$, and their factors are both $(\|z\| + \|z\|^{-1})/2$. If they are distinct eigenvalues, $\det a_z \ge ((\|z\| + \|z\|^{-1})/2)^2 \ge (\|z\|/2)^2$. If they are equal, then $\|z\| = 1$ and $\det a_z \ge 1 \ge (1/2)^2$. $\square$

### Decay

**Theorem.** Let $l$ have gap $h$, let $c \le h$ be a natural number, and let $g \in G$. Then $|c_\lambda(g)|^2\,|\det a_g|^c \le 1$.

Lean: `New.norm_dsCoeff_sq_mul_det_pow_le_one` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

*Proof.* Let $D = |\det a_g|^c$, and write $g = kz$ with $z$ positive definite.

Step 1. Let $y \in G$ be positive definite. Then $|\det a_y|^c \le |m_{-(\lambda+\rho)}(y)|^2$ (`New.norm_det_blockDiagPart_pow_le`). Let $\mu = \lambda + \rho$ and $v = \mu + c$. Then $m_v = m_\mu \cdot \det^c$, and $a = a_y = (y + y^{-1})/2$ is positive definite. The claim reduces to $|m_v(a)| \le |m_\mu(a)\,m_\mu(y)\,m_v(y^{-1})|$. Write each product of minors as a finite product over $t$ in a range $-B < t \le B$. For each $t$, Fischer's inequality, applied first to $a$ and then to $y$, gives

$$|\Delta_{\{t \le v\}}(a)| \le |\Delta_{\{t \le \mu\}}(a)|\,|\Delta_{\{t \le \mu\}}(y)|\,|\Delta_{\{v < t\}}(y)|$$

(`New.norm_principalMinor_blockDiagPart_le`). This step needs that all indices $i$ with $\mu_i < t \le v_i$ have the same sign, so that $a$ and $y$ agree on the block of these indices. This is where the gap enters: for $c \le h$ two indices of opposite sign cannot both satisfy $\mu_i < t \le \mu_i + c$. Jacobi's identity for complementary minors and $|\det y| = 1$ give $|\Delta_{\{v < t\}}(y)| = |\Delta_{\{t \le v\}}(y^{-1})|$. Multiply over $t$.

Step 2. For $u \in K$, the matrix $u^* z u$ is a positive definite element of $G$, and $|\det a_{u^*zu}| = |\det a_z| = |\det a_g|$, since $u$ and $k$ are block diagonal. So Step 1 gives $\sqrt D \le |m_{-(\lambda+\rho)}(u^*zu)|$.

Step 3. By the polar formula with $p = k$ and $q = 1$, $c_\lambda(g)$ is the integral of $F(u) = m_\Lambda(ku)\overline{m_\Lambda(u)}/m_{-(\lambda+\rho)}(u^*zu)$, divided by $\int_K|m_\Lambda|^2$. By Step 2 and $2|xy| \le |x|^2 + |y|^2$,

$$|F(u)| \le \frac{|m_\Lambda(ku)|^2 + |m_\Lambda(u)|^2}{2\sqrt D}.$$

By the invariance of $du$, both squares have the integral $\int_K|m_\Lambda|^2$. So $|c_\lambda(g)| \le 1/\sqrt D$. $\square$

**Corollary.** Let $l$ have gap $h$ and $g \in G$. Then $|c_\lambda(g)| \le 1$. If $n \ge 1$ and $c \le h$ is a natural number, then $|c_\lambda(g)| \le (2/\|g\|)^c$.

Lean: `New.DiscreteSeries.norm_dsCoeff_le_one`, `New.DiscreteSeries.norm_dsCoeff_le_pow` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

*Proof.* Take $c = 0$ in the theorem for the first claim. For the second, combine the theorem with $(\|g\|/2)^2 \le |\det a_g|$. $\square$

**Example.** In $U(1,1)$ with $k = w_2 - w_1$, $c_\lambda(g) = g_{11}^{-k}(\det g)^{w_2}$ by Section 3, and $h = k - 1$. Write $|g_{11}| = \cosh t$ with $t \ge 0$. Then $|g_{22}| = \cosh t$, $|\det a_g| = \cosh^2 t$, and $\|g\| = e^t$. The theorem says $\cosh^{2c - 2k} t \le 1$, which holds for $c \le k$. The corollary says $\cosh^{-k} t \le (2e^{-t})^c$, which holds for $c \le k$ since $\cosh t \ge e^t/2$ and $\cosh t \ge 1$. In this case the bound of the theorem holds for $c = k$, one more than the gap.

### Integrability of the decay

**Theorem.** Let $J$ be a hermitian involution of size $n \ge 1$, let $S$ be a topological group with a right invariant measure $\nu$ that is finite on compact sets, and let $j : S \to U(J)$ be a proper homomorphism. Let $c > 8n^2$ be a natural number and $y \in U(J)$. Then $s \mapsto (2/\|j(s)y\|)^c$ is $\nu$-integrable, and

$$\int_S \Big(\frac{2}{\|j(s)y\|}\Big)^c d\nu(s) \le 16^c\,\nu\{s : \|j(s) - 1\| \le 1\}.$$

Lean: `New.DiscreteSeries.integral_decay_le` (Lib/DiscreteSeries/Haar/TotalMass.lean).

*Proof.* The key step is a covering bound (`New.DiscreteSeries.measure_ball_le_covering`): for $R \ge 1$, the set $\{s : \|j(s)y\| \le R\}$ has measure at most $(3R^2)^{2n^2}$ times the measure of the ball $B = \{s : \|j(s) - 1\| \le 1\}$. To prove it, take a maximal family $M$ of points $s$ in the set whose matrices $j(s)y$ are separated by $1/R$. A packing bound in the real vector space of matrices, of dimension $2n^2$, bounds the size of $M$. By maximality, the right translates of $B$ by the points of $M$ cover the set. Then integrate by layers: $\|j(s)y\| \ge 1$ for elements of $U(J)$, and $c > 8n^2$ makes the layer sum converge with the stated constant. $\square$

**Corollary.** If $n \ge 1$ and $c > 8n^2$ is a natural number, then $g \mapsto (2/\|g\|)^c$ is integrable on $G$.

Lean: `New.integrable_two_div_norm_pow` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

Take $S = G$, $j$ the identity and $y = 1$. With the decay bound this shows: if $l$ has gap $h$ with $2h > 8n^2$, then $|c_\lambda|^2 \le (2/\|g\|)^{2h}$ is integrable on $G$. A large gap $500n^3 + A$ is much more than this. The extra size is used for the module $U(\mathfrak g)c_\lambda$ in Section 5, whose elements need decay with room to spare.

**Remark (Formalization).** The constants $8n^2$ and $16^c$ are not sharp, and the source does not need sharp ones. In $U(1,1)$ the example above shows that $|c_\lambda(g)|^2 = \cosh^{-2k} t$, while the measure is $\sinh 2t\,dt$ times the measure of $K \times K$ (Section 2). So $|c_\lambda|^2$ is integrable as soon as $k \ge 2$, that is, for gap $h \ge 1$. The source asks for a gap of order $n^3$ because its proof of orthogonality in Section 5 needs the decay of all of $U(\mathfrak g)c_\lambda$, not only of $c_\lambda$.
