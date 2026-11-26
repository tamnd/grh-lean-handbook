---
title: Good forms and the factorization
lean:
  - New/Determinant/Chain/NormOfChain.lean
decls:
  - New.normDet_sq_eq_pow_mul_det
  - New.Data.normDet_goodLift_sq_pos
  - New.Data.liftDeterminant_pos
  - New.Data.chainDeterminant_pos
  - New.Data.range_tupleIdem_le
  - New.Data.singleLift_asAlgebraHom
  - New.Data.range_goodLift_le
  - New.Data.exists_normDet_goodLift_sq_eq
  - New.Data.exists_chainDeterminant_eq_pow_mul_prod_liftDeterminant
  - New.Data.exists_div_chainDeterminant_one_eq
  - New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Good forms and the factorization

This section takes determinants. It first passes from the operator identity of one lift ([the norm of one lift](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift)) to the good forms. Then it divides the determinant of the chain by the determinants of the single lifts.

### Determinants of Gram forms

**Lemma (Determinant of a Gram form).** Let $u \colon U \to V$ be a linear map of finite dimensional complex inner product spaces, $S$ an endomorphism of $U$ and $a \in \mathbb{C}$ with $\langle u x, u y\rangle = a\,\langle x, S y\rangle$ for all $x, y$. Then $\det(u^*u) = a^{\dim U}\det S$.

Lean: `New.normDet_sq_eq_pow_mul_det` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* For all $x, y$, $\langle x, u^*u\,y\rangle = \langle u x, u y\rangle = \langle x, a S y\rangle$. So $u^*u = aS$. Take determinants: $\det(aS) = a^{\dim U}\det S$. In Lean, $\det(u^*u)$ is the square of the norm determinant of $u$. $\square$

**Lemma (Positivity).** Let $1 \leq j \leq m$. For every tame character $\vartheta$ the square of the norm determinant of the good lift at $j$ is positive. For every $m$-fold twist $\vartheta$, $Z_j(\vartheta) > 0$ and $Z(\vartheta) > 0$.

Lean: `New.Data.normDet_goodLift_sq_pos`, `New.Data.liftDeterminant_pos`, `New.Data.chainDeterminant_pos` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* The norm determinant of $u$ is the square root of $\det(u^*u) \geq 0$. It is $0$ exactly when $u$ has a nonzero kernel. The single lift is injective on the forms of level $J_M$ ([injectivity](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift)), so its restriction to the good forms is injective. The chain $\iota_\vartheta$ is injective (Section 6), so $\Theta_\vartheta$ is injective. A nonzero real number has a positive square. $\square$

### The lift keeps the good forms

The good forms are the image of the central idempotent $e_0$ of the group algebra of $\mathsf{G}_M$ ([labels and the good idempotent](/chapter/upper-bound-objects/#labels-and-the-good-idempotent)). Here $e_0$ is the sum of the orthogonal idempotents $e_c$ of the good tuple families $c$.

**Lemma (Pieces of the good idempotent).** Let $f$ be a representation of the group algebra of $\mathsf{G}_M$ and $c$ a good tuple family. Then the range of $f(e_c)$ is in the range of $f(e_0)$.

Lean: `New.Data.range_tupleIdem_le` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* The idempotents $e_c$ are orthogonal and $c$ is one of the families of the sum, so $e_c\,e_0 = e_c$. The element $e_0$ is central, so $e_0\,e_c = e_c$. Then $f(e_c) = f(e_0)\,f(e_c)$, and its range is in the range of $f(e_0)$. $\square$

**Lemma (The lift commutes with the group algebra).** Let $\vartheta$ be a tame character, $1 \leq j \leq m$, $x$ an element of the group algebra of $\mathsf{G}_M$ and $y$ a form of level $J_M$ on $W_j$. Then $\Theta_{j,\vartheta}(x\cdot y) = x\cdot\Theta_{j,\vartheta}\,y$, with the action on forms on the larger space of the pair on the right.

Lean: `New.Data.singleLift_asAlgebraHom` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Both actions are sums $\sum_g x(g)\,g$ over the finite group $\mathsf{G}_M$. The lift is linear, and it commutes with each group element $g$ by part 3 of the equivariance theorem ([the lift and its adjoint](/chapter/single-theta-lifts/#the-lift-and-its-adjoint)). $\square$

**Lemma (Range of the good lift).** Let $\vartheta$ be a tame character, $1 \leq j \leq m$, and $N$ a subspace of the forms on the larger space of the pair. Suppose that $N$ contains $\Theta_{j,\vartheta}\,y$ for every good Hecke eigenform $y$ on $W_j$ such that $\Theta_{j,\vartheta}\,y$ is in the range of $e_c$ for some good tuple family $c$. Then $N$ contains the range of the good lift.

Lean: `New.Data.range_goodLift_le` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* A good form is $e_0\,y$ for a form $y$ of level $J_M$. So it is enough to show $\Theta_{j,\vartheta}(e_0\,y) \in N$ for every $y$. The joint eigenspaces of the Hecke operators span the forms of level $J_M$ ([eigensystems and projectors](/chapter/equal-multiplicities/#eigensystems-and-projectors)). So we can take $y$ in the eigenspace of a system $p$. Write $e_0\,y = \sum_c e_c\,y$. Each piece $e_c\,y$ is in the range of $e_0$ by the previous lemma, so it is good. It is in the eigenspace of $p$, because the group algebra of $\mathsf{G}_M$ commutes with the Hecke operators. Its lift is $e_c\,\Theta_{j,\vartheta}\,y$, by the previous lemma, so it is in the range of $e_c$. The hypothesis puts each lift in $N$, and $N$ is closed under sums. $\square$

### The norm of the good lift

**Proposition (Norm of the good lift).** Let $1 \leq j \leq m$. There is $A \neq 0$ such that for every tame character $\vartheta$
$$|\det|^2\big(\Theta_{j,\vartheta}|_{\mathrm{good}}\big) = (A\,c_Q)^{d_T}\,\det\big(R_{j,\vartheta}\big|_T\big).$$

Lean: `New.Data.exists_normDet_goodLift_sq_eq` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Take $A = c_j$ from the theorem on the norm of one lift. Let $x, y$ be good forms on $W_j$. The operator $R_{j,\vartheta}$ acts on the good forms ([the Rallis operator as a Hecke operator](/chapter/equal-multiplicities/#the-rallis-operator-as-a-hecke-operator)). So
$$\langle\Theta_{j,\vartheta}x, \Theta_{j,\vartheta}y\rangle = \langle x, \Theta_{j,\vartheta}^*\Theta_{j,\vartheta}\,y\rangle = A\,c_Q\,\langle x, R_{j,\vartheta}\,y\rangle,$$
and the right side is an inner product of good forms. The lemma on Gram determinants gives the determinant of $R_{j,\vartheta}$ on the good forms on $W_j$, times $(A c_Q)$ to the dimension of those forms. This dimension is $d_T$ ([equal multiplicities](/chapter/equal-multiplicities/)). The determinant of $R_{j,\vartheta}$ on the good forms on $W_j$ is its determinant on the good forms on $Y_0$, which are the target forms (`New.Data.det_rallisOnGood_eq`, same section). $\square$

### The factorization

**Theorem (Determinant of the chain).** There are $C > 0$ and $e \in \mathbb{Z}$ such that for every $m$-fold twist $\vartheta$
$$Z(\vartheta) = \Big(C\,(\mathrm{Nm}\,Q)^{e/2}\prod_{0<i<j\leq m}\rho_{ij}(\vartheta)\Big)^{d_T}\prod_{j=1}^m Z_j(\vartheta).$$

Lean: `New.Data.exists_chainDeterminant_eq_pow_mul_prod_liftDeterminant` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Take $C$, $e$ and $c$ from the theorem on the norm of the chain, and $A_j$ from the proposition for each $j$. The constant of the theorem is $C\,|\prod_j A_j|^{-1} > 0$. Let $D_j = \det(R_{j,\vartheta^j}|_T)$. The determinant is multiplicative, so $\det R(\vartheta) = \prod_j D_j$. The powers $\vartheta^j$ have the modulus $Q$, so they have the same $c_Q$. Then
$$Z(\vartheta) = \det\big(c(\vartheta)\,c_Q^m\,R(\vartheta)\big) = \big(c(\vartheta)\,c_Q^m\big)^{d_T}\prod_j D_j = \Big(\frac{c(\vartheta)}{\prod_j A_j}\Big)^{d_T}\prod_j (A_j c_Q)^{d_T}D_j,$$
and the last product is $\prod_j Z_j(\vartheta)$. The numbers $Z(\vartheta)$ and $Z_j(\vartheta)$ are squares of real numbers, so they are their own absolute values. Take absolute values of both sides and use $|c(\vartheta)| = C(\mathrm{Nm}\,Q)^{e/2}\prod\rho_{ij}(\vartheta)$. $\square$

**Corollary (Division by the trivial twist).** There is $e \in \mathbb{Z}$ such that for every $m$-fold twist $\vartheta$, $Z(\vartheta)/Z(1)$ is the right side of the factorization theorem of Section 1.

Lean: `New.Data.exists_div_chainDeterminant_one_eq` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* At $\vartheta = 1$ the set $Q$ is empty, so $\mathrm{Nm}\,Q = 1$, and the product of the $\rho_{ij}(1)$ is $1$ (Section 6). So $Z(1) = C^{d_T}\prod_j Z_j(1)$. Divide, and cancel $C^{d_T} \neq 0$. $\square$

The factorization theorem of Section 1 is this corollary together with the positivity lemma.

Lean: `New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` (New/Determinant/Chain/NormOfChain.lean).

### The height of the scalar

**Proposition (Height of the scalar).** Let $\theta$ be a family of $m$-fold twists with small ratios, indexed by the isomorphisms $\iota \colon \mathbb{C} \to \overline{\mathbb{Q}}_\ell$, and let $e \in \mathbb{Z}$. Then the inverses of $(\mathrm{Nm}\,Q)^{e/2}\prod_{0<i<j\leq m}\rho_{ij}$ at $\theta(\iota)$ have height at most $m \cdot m \cdot (t\,x_1)$.

Lean: `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Each $\rho_{ij}$ is a ramified ratio (Section 6). The theorem on heights of products of ratios (Section 3) gives the height bound $\#P\cdot t\,x_1$, with $P$ the set of pairs. By Section 6, $\#P \leq m \cdot m$. A height bound may be increased. $\square$

**Remark (Formalization).** The constants $A_j$ come from `choose`. In the file, `Fintype.ofFinite` is a local instance of low priority (line 51, finding F-026). The proof of the lemma on the lift and the group algebra seals `Finset.univ`, so that definitional checks do not unfold the finite sums.
