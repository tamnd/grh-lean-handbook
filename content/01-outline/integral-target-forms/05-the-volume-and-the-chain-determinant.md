---
title: The volume and the chain determinant
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/IntegralTargetForms.lean
  - New/Determinant/Chain/NormOfChain.lean
  - New/Determinant/Twist/LongForms.lean
decls:
  - New.TwistedLattice.volume
  - New.TwistedLattice.volume_ne_zero
  - New.Data.chainDeterminant
  - New.Data.volume_targetLattice
  - New.Data.injective_lift_targetLattice
  - New.Data.chainDeterminant_pos
  - New.Data.liftDeterminant
  - New.Data.liftDeterminant_pos
  - New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct
  - New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq
  - New.Data.exists_chainDeterminant_one_div_eq
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio
  - New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div
  - New.Data.heightLe_chainDeterminant_one_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volume and the chain determinant

A twisted lattice has one map $\Theta_\xi$ for each twist, but its covolume is measured through $\Theta_1$ only. The volume $Z(\xi)$ converts a Gram determinant of the family $\Theta_\xi y$ into one of $\Theta_1 y$. This section identifies the volume of the target lattice with the chain determinant and states the factorization of $Z(\vartheta)/Z(1)$ that Volume 11 proves.

### The volume of a twist

Let $V$ be a finite-dimensional complex inner product space and $L$ a twisted lattice on $V$.

**Definition (Volume).** The volume of $L$ at the twist $\xi$ is $Z(\xi) = \det(\Theta_\xi^* \Theta_\xi)$, the Gram determinant of the images under $\Theta_\xi$ of an orthonormal basis of $V$.

Lean: `New.TwistedLattice.volume` (New/Reduction/Lattices/TwistedLattice.lean).

The source defines $Z(\xi)$ as the square of the norm determinant of $\Theta_\xi$, read as a complex number. If the target of $\Theta_\xi$ is finite-dimensional, it equals $\det(\Theta_\xi^*\Theta_\xi)$ (`New.TwistedLattice.volume_eq_det_adjoint_comp`). For every family $w_1, \dots, w_d$ of $d = \dim V$ vectors,
$$\det\big(\langle \Theta_\xi w_i, \Theta_\xi w_k\rangle\big) = Z(\xi) \cdot \det\big(\langle w_i, w_k\rangle\big).$$

**Lemma (Injective maps have nonzero volume).** If $\Theta_\xi$ is injective, then $Z(\xi) \neq 0$.

Lean: `New.TwistedLattice.volume_ne_zero` (New/Reduction/Lattices/TwistedLattice.lean).

### The volume of the target lattice

The space $T$ of target forms has the Petersson inner product of forms on $U(Y_0)$, and it is finite-dimensional. So the target lattice has volumes.

**Definition (Chain determinant).** For an $m$-fold twist $\vartheta$, the chain determinant is $Z(\vartheta) = \det(\Theta_\vartheta^*\Theta_\vartheta)$, the square of the norm determinant of $\Theta_\vartheta$.

Lean: `New.Data.chainDeterminant` (New/Determinant/Chain/NormOfChain.lean).

**Lemma (The volume is the chain determinant).** For every $m$-fold twist $\vartheta$, the volume of the target lattice at $\vartheta$ is the chain determinant $Z(\vartheta)$.

Lean: `New.Data.volume_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* Both sides are the square of the norm determinant of $\Theta_\vartheta$. The lemma holds by definition. $\square$

**Remark (Formalization).** The lemma is proved by `rfl`. The two definitions are written in different files, one for an abstract twisted lattice and one for the chain, and the lemma records that they agree. So every statement of Volume 11 about the chain determinant is a statement about the volume of the target lattice.

**Lemma (The maps are injective).** For every $m$-fold twist $\vartheta$, the map $\Theta_\vartheta$ of the target lattice is injective.

Lean: `New.Data.injective_lift_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The map is $\iota_\vartheta$ composed with the inclusion of $T$ into the principal forms. Both are injective, the first by the theorem on the chain in Section 3. $\square$

**Theorem (The chain determinant is positive).** For every $m$-fold twist $\vartheta$, $Z(\vartheta)$ is a positive real number.

Lean: `New.Data.chainDeterminant_pos` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* $Z(\vartheta)$ is the square of a real number, the norm determinant of $\Theta_\vartheta$. It is nonzero since $\Theta_\vartheta$ is injective. $\square$

**Remark (Formalization).** The volume has the type of a complex number. The statement $0 < Z(\vartheta)$ uses the partial order on $\mathbb{C}$ in which $0 < z$ means that $z$ is a positive real number.

### The single lifts

For $1 \leq j \leq m$ let $W_j$ be the diagonal hermitian space of rank $r$ over $E$ with the sign $+1$ on the basis vectors with basis number less than $k + j - 1$ and the sign $-1$ on the others (Lean: `New.Data.spaceW`, `New.Data.signsW`, New/UpperBound/Objects/Rows.lean and New/UpperBound/Objects/LabelsAndIndexTypes.lean). There is a theta lift from the good forms on $W_j$ for the twist $\vartheta^j$, the *good lift* (`New.Data.goodLift`), treated in [the single theta lifts](/chapter/single-theta-lifts/). The good forms on $W_j$ have dimension $d_T$ (`New.Data.targetDim_eq_finrank_goodForms_spaceW`).

**Definition (Lift determinant).** For an $m$-fold twist $\vartheta$ and $1 \leq j \leq m$, the lift determinant $Z_j(\vartheta)$ is the volume $\det(u^* u)$ of the good lift $u$ at $j$ for the twist $\vartheta^j$.

Lean: `New.Data.liftDeterminant` (New/Determinant/Chain/NormOfChain.lean).

**Theorem (Lift determinants are positive).** For every $m$-fold twist $\vartheta$ and $1 \leq j \leq m$, $Z_j(\vartheta)$ is a positive real number.

Lean: `New.Data.liftDeterminant_pos` (New/Determinant/Chain/NormOfChain.lean).

### The factorization

The next theorem is the main result of [the chain determinant](/chapter/chain-determinant/) in Volume 11.

**Theorem (Norm of the chain).** There are a constant $C > 0$, an integer $e$ and complex numbers $c(\vartheta)$ such that for every $m$-fold twist $\vartheta$
$$|c(\vartheta)| = C \cdot \Big( (\mathrm{Nm}\,Q)^{e/2} \prod_{0 < i < j \leq m} \rho_{ij}(\vartheta) \Big), \qquad \Theta_\vartheta^* \Theta_\vartheta = c(\vartheta)\, c_Q^m \, R(\vartheta).$$
Here $R(\vartheta)$ is the product over $1 \leq j \leq m$ of the series of Rallis' formula for the $j$-th lift at $\vartheta^j$, acting on $T$ (`New.Data.rallisProduct`). The number $c_Q$ is
$$c_Q = (\mathrm{Nm}\,Q)^{rt} \prod_{w \in Q} \prod_{t < i \leq t + r} (1 - q_w^{-i}).$$
The number $\rho_{ij}(\vartheta)$ is the product over $1 \leq z \leq t$ of ratios of Hecke values of the character $\mu_j/\mu_i$ at $\vartheta^{j-i}$, where $\mu_j$ is the character of the $j$-th lift at the trivial twist (`New.Data.quotientRatio`).

Lean: `New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct` (New/Determinant/Chain/NormOfChain.lean).

**Remark (Formalization).** In the proof the source first gets numbers $c(\vartheta)$ with $\langle\Theta_\vartheta y, \Theta_\vartheta y'\rangle = c(\vartheta) c_Q^m \langle y, R(\vartheta) y'\rangle$. If $c(1) = 0$, the injectivity of $\Theta_1$ forces $T = 0$, and then any factor serves. So the theorem does not need $d_T > 0$. The exponent $e/2$ is a real power of the positive integer $\mathrm{Nm}\,Q$, so it is defined for odd $e$ too. The height bounds below do not need the value of $e$.

Take determinants on $T$. The determinants of the Rallis series cancel against those in the lift determinants, which have the same series, one lift at a time (`New.Data.exists_normDet_goodLift_sq_eq`). So does the factor $c_Q$. What is left is a statement about numbers.

**Theorem (Factorization of the determinant).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$, $Z(\vartheta) > 0$, $Z_j(\vartheta) > 0$ for $1 \leq j \leq m$, and
$$\frac{Z(\vartheta)}{Z(1)} = \Big( (\mathrm{Nm}\,Q)^{e/2} \prod_{0 < i < j \leq m} \rho_{ij}(\vartheta) \Big)^{d_T} \prod_{j=1}^{m} \frac{Z_j(\vartheta)}{Z_j(1)}.$$

Lean: `New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` (New/Determinant/Chain/NormOfChain.lean).

The lower bound uses the inverse.

**Corollary (The inverse ratio).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$
$$\frac{Z(1)}{Z(\vartheta)} = \Big( (\mathrm{Nm}\,Q)^{e/2} \prod_{0 < i < j \leq m} \rho_{ij}(\vartheta) \Big)^{-d_T} \prod_{j=1}^{m} \frac{Z_j(1)}{Z_j(\vartheta)}.$$

Lean: `New.Data.exists_chainDeterminant_one_div_eq` (New/Determinant/Twist/LongForms.lean).

### The height of the inverse ratio

The lattice inequality needs a bound for the height of the family $\iota \mapsto Z(1)/Z(\xi_\iota)$, for one twist $\xi_\iota$ for each $\iota$, with $\xi_\iota$ allowed at the prime of $\iota$. A family of $m$-fold twists $\theta$ *has small ratios* if $\mathrm{Nm}\,Q$ of $\theta(\iota)$ is prime to the prime of $\iota$ for every $\iota$, and if for every ramified critical pair the inverse ratios of $L$-values at the powers $\theta(\iota)^{\pm j}$, $1 \leq j \leq m$, form families of height at most $x_1$ (`New.Data.HasSmallRatios`). Heights are those of [twisted lattices](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers).

**Lemma (The scalar has small height).** Let $\theta$ have small ratios. Then for every integer $e$ the family
$$\iota \longmapsto \Big( (\mathrm{Nm}\,Q_{\theta(\iota)})^{e/2} \prod_{0 < i < j \leq m} \rho_{ij}(\theta(\iota)) \Big)^{-1}$$
has height at most $m \cdot m \cdot (t \cdot x_1)$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` (New/Determinant/Chain/NormOfChain.lean).

**Theorem (Single lifts at good twists).** There is a family $\theta$ of $m$-fold twists with small ratios such that for every $1 \leq j \leq m$ the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most
$$d_T \Big( \frac{f a \log^4 b}{m} - k \cdot A_{\mathrm{dir}} \Big),$$
where $A_{\mathrm{dir}}$ is the direction amount of the data (`D.directionAmount`).

Lean: `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (New/Determinant/Twist/LongForms.lean).

Volume 11 proves this in [the volume of a lift and its height](/chapter/lift-volume-height/). The twists come from a regular family, which [twists and critical pairs](/chapter/twists-critical-pairs/) constructs. The bound has the negative term $-d_T k A_{\mathrm{dir}}$. This sign is what Theorem C turns into the main amount.

**Theorem (The inverse ratio has small height).** Let $\theta$ have small ratios, and let the families $Z_j(1)/Z_j(\theta(\iota))$ satisfy the bounds of the last theorem. Then the family $\iota \mapsto Z(1)/Z(\theta(\iota))$ has height at most
$$d_T \big( b + f a \log^4 b - A_{\mathrm{main}} \big),$$
where $A_{\mathrm{main}} = m k A_{\mathrm{dir}}$ is the main amount.

Lean: `New.Data.heightLe_chainDeterminant_one_div` (New/Determinant/Twist/LongForms.lean).

*Proof.* Write $Z(1)/Z(\theta(\iota))$ by the corollary on the inverse ratio. The scalar has height at most $m^2 t x_1 \leq b$, by the lemma on the scalar and the sizes of the data. Its $d_T$-th power has height at most $d_T b$. The product of the $m$ ratios of single lifts has height at most $m d_T (f a \log^4 b / m - k A_{\mathrm{dir}}) = d_T (f a \log^4 b - A_{\mathrm{main}})$. Heights add under products. $\square$

So the volume term of the lattice inequality is $b_{\mathrm{volume}} = d_T(b + f a \log^4 b - A_{\mathrm{main}})$. Its main part is $-d_T A_{\mathrm{main}}$. The next section shows how this negative term becomes the lower bound of Theorem C.
