---
title: The weight at one real place
lean:
  - New/Spanning/RemainingTerms/OneRealPlace.lean
decls:
  - New.frameVolume
  - New.frameVolume_pos
  - New.frameVolume_mul_left
  - New.volumeRatio
  - New.volumeRatio_inv
  - New.volumeRatio_mul_left
  - New.RealPlace.volumeRatio_eq_norm_det
  - New.RealPlace.norm_det_eq_norm_det_mul_inclMatrix
  - New.RealPlace.IsNegativeBasis
  - New.RealPlace.IsNegativeBasis.volumeRatio_eq
  - New.RealPlace.IsTriangularBasis
  - New.RealPlace.exists_isTriangularBasis
  - New.RealPlace.IsTriangularBasis.norm_det_mul_le_volumeRatio
  - New.RealPlace.differenceX₀_eq_add
  - New.RealPlace.exists_common_vector_of_normOnePairOccursFrom
  - New.RealPlace.norm_det_subframeBlock
  - New.RealPlace.IsTriangularBasis.norm_last_le
  - New.RealPlace.IsTriangularBasis.norm_last_sq_eq_one_add_dotProduct_differenceX₀
  - New.RealPlace.IsTriangularBasis.norm_last_sq_le
  - New.RealPlace.IsTriangularBasis.norm_det_le
  - New.RealPlace.exists_majorant_volumeRatio_inv_pow
  - New.RealPlace.frameX₀Part_unipotentOf_inv_mul
  - New.ostrowski_taussky
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The weight at one real place

This section works at one real place. The group is $G_1 = U(\varrho + k, \varrho + 1)$ of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/). Its form $J_1$ has the $\varrho$ hyperbolic planes, the identity on $X_0$ and $h(z, z) = -1$. The matrix $F$ (`frameCols`) has the frame vectors $f_0, \dots, f_\varrho$ as columns, and $V_-$ is the $-1$ eigenspace of $J_1$. For $\gamma \in G_1$, the matrix of the products of $f$ with $\gamma f$ is $Z = F^*J_1\gamma F$ (`New.realFrameGram γ`). The length $\ell(y)$ (`New.besselLength`) and the box $\operatorname{Box}(\rho)$ (`New.frameBox`) are defined in [the length and the boxes](/chapter/bessel-real-place/).

### The volume ratio

**Definition (Frame volume).** For $y \in G_1$, put $\operatorname{vol}(y) = |\det(((1 - J_1)F)^*\,y^{-1}F)|$. Up to a constant factor, this is the volume of the projection of the frame to the negative space $yV_-$.

Lean: `New.frameVolume` (New/Spanning/RemainingTerms/OneRealPlace.lean).

**Lemma.** $\operatorname{vol}(y) > 0$. If $u \in \mathsf U^0$ (`besselU0`, the unipotent elements that fix the frame), then $\operatorname{vol}(uy) = \operatorname{vol}(y)$.

Lean: `New.frameVolume_pos`, `New.frameVolume_mul_left` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Let $v$ be in the kernel of the matrix, and put $w = y^{-1}Fv$. The products of $w$ with the columns of $(1 - J_1)F$ vanish, so $J_1 w = w$ and $h(w, w) = |w|^2$. The element $y^{-1}$ keeps the form, so $h(w, w) = h(Fv, Fv) = -|v_\varrho|^2 \leq 0$. Hence $w = 0$, so $Fv = 0$ and $v = F^*Fv = 0$. For the second claim, $u^{-1}F = F$, so $(uy)^{-1}F = y^{-1}F$. $\square$

**Definition (Volume ratio).** For $\gamma, y \in G_1$, put $\nu_\gamma(y) = \operatorname{vol}(\gamma^{-1}y)/\operatorname{vol}(y)$. This is the ratio of the volumes of the projections of $\gamma f$ and of $f$ to $yV_-$.

Lean: `New.volumeRatio` (New/Spanning/RemainingTerms/OneRealPlace.lean).

**Lemma.** $\nu_\gamma(y) > 0$, $\nu_{\gamma^{-1}}(\gamma^{-1}y) = \nu_\gamma(y)^{-1}$, and $\nu_\gamma(uy) = \nu_{u^{-1}\gamma}(y)$ for $u \in \mathsf U^0$. The map $\nu_\gamma$ is measurable.

Lean: `New.volumeRatio_inv`, `New.volumeRatio_mul_left` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* The first claim follows from the lemma above. The second claim is the definition with $\gamma^{-1}$ and $\gamma^{-1}y$. For the third, $\operatorname{vol}(uy) = \operatorname{vol}(y)$, and $\gamma^{-1}uy = (u^{-1}\gamma)^{-1}y$. $\square$

The third identity is the reason for the form of the results below. A move of the point $y$ by $u$ is the same as the replacement of $\gamma$ by $u^{-1}\gamma$. So the point $y$ stays fixed, and $\gamma$ changes.

Let $P_y$ be the left inverse of $F$ that vanishes on the orthogonal complement of $yV_-$ (`frameLeftInverse y`). Then $\nu_\gamma(y) = |\det(P_y\gamma F)|$.

Lean: `New.RealPlace.volumeRatio_eq_norm_det` (New/Spanning/RemainingTerms/OneRealPlace.lean).

The matrix $P_y\gamma F$ writes the projection of $\gamma f$ in the basis given by the projection of $f$.

### Shared vectors cancel

The next lemma is a fact about determinants.

**Lemma (Triangular change of basis).** Let $e: \{0, \dots, m-1\} \to \{0, \dots, n-1\}$, let $N$ be an $n \times n$ matrix and let $p$ be an $n \times m$ matrix with $p^*E = 1$, where $E$ is the inclusion matrix of $e$. Suppose that for every $b$ outside the range of $e$ there are $x, x'$ with $Nx' = x$, $p^*x = 0$, $|x_b| = 1$, $x'_b = 1$, and $x_a = x'_a = 0$ for $a > b$. Then $|\det N| = |\det(p^*NE)|$.

Lean: `New.RealPlace.norm_det_eq_norm_det_mul_inclMatrix` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Put $M = 1 + (NE - E)p^*$. For each $b$ we find $x, x'$ with $Nx' = Mx$, $|x_b| = 1$, $x'_b = 1$, and $x_a = x'_a = 0$ for $a > b$. If $b = e(l)$, take $x = x'$ the unit vector at $b$; then $Mx = x + (NE - E)u_l = Nx$, where $u_l$ is the unit vector at $l$. If $b$ is outside the range, take the given pair; then $Mx = x = Nx'$. So $NX' = MX$, where $X$ and $X'$ are upper triangular, the diagonal of $X'$ is $1$, and the diagonal of $X$ has modulus $1$. Hence $|\det N| = |\det M|$. By Sylvester's identity, $\det M = \det(1 + p^*(NE - E)) = \det(p^*NE)$, as $p^*E = 1$. $\square$

Now let $\gamma$ have norm-one pairs from level $j$, and put $i = \min(\varrho, j)$. The *subframe* is $f_0, \dots, f_{i-1}, z$. Its matrix of columns is $F_i$ (`subframeCols`), and its block of $Z$ is $B = B_i(Z)$ (`subframeBlock`).

**Definition (Negative basis).** A matrix $\omega$ with $i + 1$ columns is a *negative basis* for $\gamma, y$ (`IsNegativeBasis`) if the columns of $y^{-1}\omega$ lie in $V_-$, the columns of $\omega$ are orthogonal to every vector $fx = \gamma fx'$ with $x_\varrho = 0$, and $\det(F_i^*J_1\omega) \neq 0$.

Lean: `New.RealPlace.IsNegativeBasis` (New/Spanning/RemainingTerms/OneRealPlace.lean).

A vector $fx = \gamma fx'$ with $x_\varrho = 0$ lies in $I = A \cap \gamma A$. So the second field says that $\omega$ is orthogonal to $I$.

**Theorem (The weight modulo $I$).** Let $\gamma$ have norm-one pairs from level $j$, let $i = \min(\varrho, j)$, and let $\omega$ be a negative basis. Then

$$\nu_\gamma(y) = \frac{|\det((\gamma F_i)^*J_1\omega)|}{|\det(F_i^*J_1\omega)|}.$$

Lean: `New.RealPlace.IsNegativeBasis.volumeRatio_eq` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Put $N = P_y\gamma F$, so $\nu_\gamma(y) = |\det N|$. Put $Q = F^*J_1\omega$, the products of the frame with $\omega$, and let $E$ be the inclusion of the subframe indices. Then $F_i^*J_1\omega = E^*Q$, and this matrix is invertible. The columns of $\omega$ lie in $yV_-$. So the product of any vector with a column of $\omega$ equals the product of its projection to $yV_-$ with that column. The projection of $\gamma f$ is $(\text{projection of } f)N$. Hence $(\gamma F)^*J_1\omega = N^*Q$.

Put $p = Q(E^*Q)^{-1}$, so $p^*E = 1$. Let $b$ be outside the subframe, so $i \leq b < \varrho$. Then $b \geq j$, and the norm-one pairs give $fx = \gamma fx'$ with $x'_b = 1$, $|x_b| = |c| = 1$, and $x_a = x'_a = 0$ for $a > b$. In particular $x_\varrho = 0$. So $\omega$ is orthogonal to $fx$, that is $Q^*x = 0$ and $p^*x = 0$. The projections of $\gamma fx'$ and of $fx$ agree, so $Nx' = x$. The lemma on triangular changes of basis gives $|\det N| = |\det(p^*NE)|$. Here $p^*NE = (Q^*E)^{-1}Q^*NE = (Q^*E)^{-1}(E^*N^*Q)^* = (Q^*E)^{-1}((\gamma F_i)^*J_1\omega)^*$. Take determinants and moduli. $\square$

### A triangular basis

**Definition (Triangular basis).** Let $\det B \neq 0$, and put $W = ZEB^{-1}$ (`dualProducts`). A pair $(\omega, L)$ is a *triangular basis* at $y$ for $Z$ (`IsTriangularBasis`) if the columns of $y^{-1}\omega$ lie in $V_-$, $\omega^*J_1\omega = -1$, $F^*J_1\omega = WL$, $L$ is lower triangular and $\det L \neq 0$.

Lean: `New.RealPlace.IsTriangularBasis` (New/Spanning/RemainingTerms/OneRealPlace.lean).

**Lemma.** If $\det B \neq 0$, then a triangular basis exists at every $y \in G_1$.

Lean: `New.RealPlace.exists_isTriangularBasis` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Put $\omega_0 = J_1P_y^*W$. Then $y^{-1}\omega_0$ lies in $V_-$, and $F^*J_1\omega_0 = W$. On $V_-$ the form is minus the Euclidean product, so $\omega_0^*J_1\omega_0 = -(y^{-1}\omega_0)^*(y^{-1}\omega_0)$. The matrix $y^{-1}\omega_0$ is injective, because $E^*F^*J_1\,y\,(y^{-1}\omega_0) = E^*W = 1$. So its Gram matrix is positive definite. The Cholesky form of the Gram-Schmidt process gives a lower triangular $L$ with $L^*(y^{-1}\omega_0)^*(y^{-1}\omega_0)L = 1$. Put $\omega = \omega_0L$. $\square$

Since $E^*W = 1$, the products of the subframe with $\omega$ are $F_i^*J_1\omega = L$. Since $Z^*x = -x'_\varrho u_\varrho$ for a shared vector $fx = \gamma fx'$, and $x'_\varrho = 0$ when $x_\varrho = 0$, a triangular basis is a negative basis. The entry $L_{ll}$ is the product of the moved frame vector $y^{-1}f$ at the index $l$ of the subframe with the unit vector $y^{-1}\omega_l$ of $V_-$. So $|L_{ll}| \leq \|y^{-1}f\|$.

**Lemma.** For $y \in \operatorname{Box}(\rho)$, $|\det L| \leq \rho^{i+1}$. Also $|\det L| = |\det L_1|\,|L_{zz}|$, where $L_1$ is the leading block of order $i$ and $L_{zz}$ the last diagonal entry.

Lean: `New.RealPlace.IsTriangularBasis.norm_det_le`, `New.RealPlace.IsTriangularBasis.norm_det_eq_mul_norm_last` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* $L$ is triangular, so $\det L$ is the product of the diagonal entries. Each entry has modulus at most $\rho$ by the bound above. $\square$

### The lower bound

The *image basis* is $\omega' = \gamma F_iB^{-1}L$ (`imageBasis`). It spans the image of the subframe, and its products with the subframe of $f$ are also $L$. The matrix $v = X^*(\omega' - \omega)$ (`differenceX₀`) holds the $X_0$-coordinates of $\omega' - \omega$, where $X$ is the matrix of the basis of $X_0$. The products of the frame with $\omega' - \omega$ vanish. A vector with this property has no $e^*_a$ and no $z$ coordinates, so its Gram matrix is that of its $X_0$-part: $(\omega' - \omega)^*J_1(\omega' - \omega) = v^*v$.

**Lemma (Ostrowski and Taussky).** Let $H$ and $\Theta + \Theta^* - H$ be positive semidefinite complex $m \times m$ matrices. Then $|\det H| \leq 2^m|\det\Theta|$.

Lean: `New.ostrowski_taussky` (Lib/General/Analysis/GaussianIntegral.lean).

*Proof.* If $\det H = 0$ there is nothing to show. Otherwise $H$ is positive definite. Let $\lambda$ be an eigenvalue of $H^{-1}(2\Theta)$ with eigenvector $v$. Then $\lambda v^*Hv = 2v^*\Theta v$. Take real parts: $\operatorname{Re}\lambda\, v^*Hv = v^*(\Theta + \Theta^*)v \geq v^*Hv$. So $|\lambda| \geq \operatorname{Re}\lambda \geq 1$. Hence $|\det(H^{-1}2\Theta)| \geq 1$. $\square$

**Theorem (A lower bound for the ratio).** Let $\gamma$ have norm-one pairs from level $j$, $i = \min(\varrho, j)$, $Z = F^*J_1\gamma F$, $\delta = \det B \neq 0$, and let $(\omega, L)$ be a triangular basis at $y$. Then

$$|\delta|\,|\det(1 + vv^*)| \leq 2^{i+1}|\det L|^2\,\nu_\gamma(y).$$

Lean: `New.RealPlace.IsTriangularBasis.norm_det_mul_le_volumeRatio` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Put $K = \omega^*J_1\omega'$. Expand $v^*v = (\omega' - \omega)^*J_1(\omega' - \omega)$ and use $\omega^*J_1\omega = -1$:

$$-K - K^* - (1 + v^*v) = -\omega'^*J_1\omega'.$$

The form is negative semidefinite on the span of $\gamma f$, so the right side is positive semidefinite. Apply the lemma of Ostrowski and Taussky with $\Theta = -K$ and $H = 1 + v^*v$: $|\det(1 + v^*v)| \leq 2^{i+1}|\det K|$. Next, $K = ((\gamma F_i)^*J_1\omega)^*B^{-1}L$. By the theorem on the weight modulo $I$, with $F_i^*J_1\omega = L$, we get $|\det((\gamma F_i)^*J_1\omega)| = \nu_\gamma(y)|\det L|$. Hence $|\det K| = \nu_\gamma(y)|\det L|^2/|\delta|$. Finally $\det(1 + v^*v) = \det(1 + vv^*)$. $\square$

### Translates and the last column

The $X_0$-part of $\gamma f$ is $X^*\gamma F$ (`frameX₀Part γ`).

**Lemma (The translates).** Let $\det B \neq 0$. If $X^*\gamma F_i = X^*\gamma_0F_i + A^*B_{<i}$, where $B_{<i}$ is the first $i$ rows of $B$, then $v(\gamma) = v(\gamma_0) + A^*L_{<i}$.

Lean: `New.RealPlace.differenceX₀_eq_add` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* $X^*\omega'(\gamma) = X^*\gamma F_iB^{-1}L$, and $B_{<i}B^{-1}L = L_{<i}$. $\square$

**Lemma.** For a unipotent $q$ of $G_1$ with parameters $q = (a, b)$, $X^*(q^{-1}\gamma)F = X^*\gamma F + a^*\Xi_0(Z)$.

Lean: `New.RealPlace.frameX₀Part_unipotentOf_inv_mul` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* The inverse of a unitary element is $J_1q^*J_1$. Compare the entries in the block form of $q$. $\square$

So a move of the point changes the $X_0$-part of the frame by $a^*$ times the isotropic rows. This is the form of the hypothesis of the lemma on the translates.

**Lemma (A common vector).** Let $\gamma$ have norm-one pairs from level $i \leq \varrho$. There are $x$ and $c$ with $|x_\varrho| = 1$, $c_i = 1$, $\gamma F_ic = Fx$ and $Bc = -x_\varrho u_i$.

Lean: `New.RealPlace.exists_common_vector_of_normOnePairOccursFrom` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Take the shared vector at the index $\varrho$, with coefficient $1$ at $\gamma z$. Subtract the shared vectors at the indices $b = \varrho - 1, \dots, i$, in this order, to make the coefficients of $\gamma f_b$ zero. This does not change $x_\varrho$. Then $Z y = F^*J_1Fx = -x_\varrho u_\varrho$, and its subframe part is $Bc$. $\square$

**Lemma.** Let $\gamma$ have norm-one pairs from level $j \leq \varrho + 1$, with $i = \min(\varrho, j)$. Then $|\det B| = |D_j|$.

Lean: `New.RealPlace.norm_det_subframeBlock` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* If $j = \varrho + 1$, then $B = Z$. If $j \leq \varrho$, then $i = j$. Take $c$ from the lemma on a common vector. Since $c_i = 1$, Cramer's rule says that the last column of $B$ can be replaced by $Bc = -x_\varrho u_i$ without a change of the determinant. Expand along this column: $\det B = -x_\varrho D_j$, and $|x_\varrho| = 1$. $\square$

**Lemma (The last column).** Let $\det B \neq 0$ and let $v_z$ be the last column of $v$.

1. If $i = \varrho$ and $\ell(y) \leq \theta$, then $|L_{zz}| \leq \theta$, for every $Z$.
2. If $\gamma$ has norm-one pairs from level $i$, then $|L_{zz}|^2 = 1 + |v_z|^2$.
3. If $\gamma$ has norm-one pairs from level $j$ and $\ell(y) \leq \theta$, then $|L_{zz}|^2 \leq \theta^{2(j - i)}|\det(1 + v_zv_z^*)|$.

Lean: `New.RealPlace.IsTriangularBasis.norm_last_le`, `New.RealPlace.IsTriangularBasis.norm_last_sq_eq_one_add_dotProduct_differenceX₀`, `New.RealPlace.IsTriangularBasis.norm_last_sq_le` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* (1) Take $u \in \mathsf U$ with $\|uy\| \leq \theta$ ([length](/chapter/bessel-real-place/)). The last vector $\omega_z$ is orthogonal to $A$, since $L$ is triangular. The vector $u^{-1}z$ is $z$ plus a vector of $A$. So $L_{zz} = h(z, \omega_z) = h(u^{-1}z, \omega_z)$, and its modulus is at most $\|(uy)^{-1}\|\,\|y^{-1}\omega_z\| \leq \theta \cdot 1$. Here $\|g^{-1}\| = \|g\|$ on $G_1$.

(2) Take $x, c$ from the lemma on a common vector. Then $\omega'_z = \gamma F_iB^{-1}L u_i = t\,fx$ with $t = -L_{zz}/x_\varrho$. So $h(\omega'_z, \omega'_z) = -|t|^2 = -|L_{zz}|^2$. The difference $\omega'_z - \omega_z$ is orthogonal to the frame, hence to $\omega'_z$. So $-1 = h(\omega_z, \omega_z) = -|L_{zz}|^2 + |v_z|^2$.

(3) If $j \leq \varrho$, then $i = j$, and (2) gives the claim, with $\det(1 + v_zv_z^*) = 1 + |v_z|^2$. If $j = \varrho + 1$, then $i = \varrho$, and (1) gives $|L_{zz}|^2 \leq \theta^2 \leq \theta^2\det(1 + v_zv_z^*)$. $\square$

### The majorant

**Theorem (One real place).** Let $y \in \operatorname{Box}(\rho)$, $\ell(y) \leq \theta$, $j \leq \varrho + 1$, $i = \min(\varrho, j)$ and $k \geq 7$. Let $\gamma_0$ have norm-one pairs from level $j$, let $Z = F^*J_1\gamma_0F$, and let $\delta = \det B \neq 0$. Then there is a measurable $\varphi \geq 0$ on $(\mathbb C^\kappa)^i$ with

$$\int\varphi \leq \frac{(2\rho^2)^{(i+1)i}\,(2^{i+1}\theta^{2(j-i)})^k}{|\delta|^{k+i}},$$

such that $\nu_\gamma(y)^{-(k+i)} \leq \varphi(A)$ for every $\gamma$ with norm-one pairs from level $j$, matrix $Z$, and $X^*\gamma F_i = X^*\gamma_0F_i + A^*B_{<i}$.

Lean: `New.RealPlace.exists_majorant_volumeRatio_inv_pow` (New/Spanning/RemainingTerms/OneRealPlace.lean).

*Proof.* Take a triangular basis $(\omega, L)$ at $y$, and put $v_0 = v(\gamma_0)$. The last row of $L_{<i}$ is zero above the diagonal, so by the lemma on the translates the last column of $v(\gamma)$ is $v_z$ of $v_0$, and the first $i$ columns are $v_{0,<i} + A^*L_1$. Put $G = 1 + v_zv_z^*$, $c = v_{0,<i}^*$, and

$$C = \Bigl(\frac{2^{i+1}|\det L|^2}{|\delta|}\Bigr)^{k+i},\qquad \varphi(A) = C\,|\det(G + (L_1^*A + c)^*(L_1^*A + c))|^{-(k+i)}.$$

Then $1 + v(\gamma)v(\gamma)^* = G + (L_1^*A + c)^*(L_1^*A + c)$, and the lower bound for the ratio gives $\nu_\gamma(y)^{-(k+i)} \leq \varphi(A)$. The matrix $G$ is positive definite, and $\det L_1 \neq 0$. Hua's bound ([Hua's integral](/chapter/discrete-series/), in the form `New.lintegral_norm_det_add_inv_pow_le`) gives $\int\varphi \leq C|\det L_1|^{-2k}|\det G|^{-k}$, since $k \geq 7$. Now $|\det L| = |\det L_1|\,|L_{zz}|$, so

$$C|\det L_1|^{-2k}|\det G|^{-k} = \frac{2^{(i+1)(k+i)}|\det L|^{2i}}{|\delta|^{k+i}}\Bigl(\frac{|L_{zz}|^2}{|\det G|}\Bigr)^k.$$

Bound $|\det L|^{2i} \leq \rho^{2i(i+1)}$ and $|L_{zz}|^2/|\det G| \leq \theta^{2(j-i)}$. $\square$

**Remark (Formalization).** The integral is a lower Lebesgue integral of a function with values in $[0, \infty]$, and the bound is `ENNReal.ofReal` of a real number. If $\rho < 0$ or $\theta < 0$ were allowed, the real bound might be negative and `ofReal` would give $0$. The hypotheses exclude this: $y \in \operatorname{Box}(\rho)$ forces $\rho \geq 1$, and $\ell(y) \leq \theta$ forces $\theta \geq 1$. The source does not state $\rho \geq 1$ or $\theta \geq 1$ as hypotheses.
