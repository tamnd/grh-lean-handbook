---
title: The lift and its adjoint
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
  - New/UpperBound/Objects/AuxiliaryPair.lean
  - New/UpperBound/Objects/Rows.lean
  - New/OneLift/HeckeValues/CharacterLift.lean
decls:
  - New.DescentPair.FitsParams
  - New.Data.fitsParams_descentPair
  - New.DescentPair.FitsParams.isArrow_fockDatum
  - New.DescentPair.FitsParams.isArrow_swap_fockDatum
  - New.DescentPair.thetaLift
  - New.DescentPair.ofAlgForm_thetaLift
  - New.DescentPair.coe_thetaLift
  - New.Data.principalForms
  - New.Data.singleLift_apply
  - New.Data.ofAlgForm_singleLift
  - New.LevelPlaces.LevelForm.inner_eq_petersson
  - New.DescentPair.inner_thetaLift
  - New.DescentPair.isForm_normalizedDescent
  - New.Data.inner_singleLift
  - New.Data.coe_adjoint_singleLift
  - New.Data.adjoint_singleLift_apply
  - New.Data.normalizedDescent_eq_zero_iff
  - New.DescentPair.integrable_smul_vectorKernelForm
  - New.DescentPair.thetaLift_eq_integral
  - New.Data.singleLift_eq_integral
  - New.DescentPair.formAction
  - New.DescentPair.coe_formAction
  - New.DescentPair.omega_fockDatum_eq_inv_prod_smul
  - New.DescentPair.normalizedDescent_mul_eq_normalizedDescent_formAction
  - New.DescentPair.thetaLift_formRep
  - New.Data.principalRep
  - New.Data.singleLift_principalRep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The lift and its adjoint

This section defines the lift $\Theta_W$ of a descent pair and the single lift $\Theta_{j,\vartheta}$. It proves three facts. The descent $\theta$ is the adjoint of the lift. The lift is the integral of $y(g)\,\theta_W(g, \cdot)$ over $[U(W)]$. The lift commutes with the finite group of the chosen places.

### Parameters that fit the pair

The theta lift by the datum of the highest vector sends forms of one type on $W$ to forms of one type on $V$. The types are given by parameters at the infinite places. The lift is defined only for a parameter $l$ on $W$ that fits the pair.

**Definition (Fitting parameters).** A doubled parameter $l$ on $W$ fits the descent pair if four conditions hold.

1. The parameters $l$ on $W$ and $l' = \mathrm{paramV}$ on $V$ correspond, for the weights $r_-$ and $\lfloor n/2\rfloor$ plus the weight of $\mu$.
2. At every infinite place the basis vectors of each sign are numbered from $0$ by decreasing $\pm l$.
3. $k^+(\tau, i) = 0$ when $i$ exceeds the number $r_+$ of plus signs of $W$.
4. $k^-(\tau, i) = 0$ when $i$ exceeds the number $r_-$ of minus signs of $W$.

Lean: `New.DescentPair.FitsParams` (New/UpperBound/Objects/AuxiliaryPair.lean).

**Lemma.** For every tame character $\vartheta$ and every $1 \leq j \leq m$, the doubled target parameter $2\varsigma$ fits the $j$-th descent pair.

Lean: `New.Data.fitsParams_descentPair` (New/UpperBound/Objects/Rows.lean).

The proof is a count in Volume 9, in [the objects of the upper bound](/chapter/upper-bound-objects/). This chapter uses the lemma as a black box.

**Lemma.** Let $l$ fit the pair. Then the datum $\phi_{v^+}$ of the highest vector is an arrow from the type of $l$ on $W$ to the type of $\mathrm{paramV}$ on $V$. For the transposed kernel, it is an arrow from the conjugate type on $V$ to the conjugate type on $W$.

Lean: `New.DescentPair.FitsParams.isArrow_fockDatum` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.FitsParams.isArrow_swap_fockDatum` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Volume 9 shows that a fitting parameter makes the Fock vector of $P_{v^+}$ an edge between the two discrete series types (`New.DescentPair.FitsParams.isEdge`). An edge with a finite datum in the finite part gives an arrow in both directions, by [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). $\square$

An arrow from $e$ to $e'$ means that every form of type $e$ is of rapid decay and that its theta lift is a form of type $e'$. Volume 6 defines the lift of forms `New.formLift` for any datum. When the datum is an arrow, it agrees with the integral $\int y(g)\,\theta(g, h)\,dg$.

### The lift of a pair

**Definition (The lift of a pair).** Let $l$ fit the pair. The lift $\Theta_W$ sends a form $y$ of type $l$ on $W$ to the algebraic form on $V$ whose function on $U(V)(\mathbb{A})$ is the theta lift of $y$ by $\phi_{v^+}$.

Lean: `New.DescentPair.thetaLift` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.ofAlgForm_thetaLift` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.coe_thetaLift` (New/Determinant/Norms/AdjointThetaLift.lean).

The lift lands in the forms on $V$ of the pair, that is, in the forms on which the level $K$ acts by $\chi_K$. Lean proves this inside the definition. Volume 9 shows that $(1, k)$ for $k \in K$ multiplies the datum $\phi_{\overline{v^+}}$ by $\chi_K(k)$, and an arrow carries this law to the lifted form.

**Remark (Formalization).** The lift `New.formLift` of Volume 6 is defined for every datum by left inverses of inclusions of function spaces. Off arrows its values are not the integral. Here the datum is an arrow by the lemma above, so the definition is the integral. Lean then reads the lifted function as an algebraic form by the linear equivalence `New.Space.toAlgForm` for the Harish-Chandra parameter $\mathrm{paramV}$. Its inverse is `ofAlgForm`, the map $\Xi \mapsto \Xi^\natural$ of Section 2.

**Definition (Forms of level $J_M$).** On a space $V$ of rank $r$ with signs $s$, the forms of level $J_M$ are the forms of the doubled parameter $2\varsigma$ that are fixed by $J_M$. Here $J_M$ is the group of integral points that reduce to $1$ at every chosen place and has no condition elsewhere.

Lean: `New.Data.principalForms` (New/UpperBound/Objects/Rows.lean).

**Lemma.** For $1 \leq j \leq m$ and a form $y$ of level $J_M$ on $W_j$, $\Theta_{j,\vartheta}y = \Theta_W y$ for the $j$-th pair, and $(\Theta_{j,\vartheta}y)^\natural$ is the theta lift of $y$ by $\phi_{v^+}$.

Lean: `New.Data.singleLift_apply` (New/Determinant/Norms/AdjointThetaLift.lean), `New.Data.ofAlgForm_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The `dite` in the definition takes its first branch. The second claim is the lemma for $\Theta_W$. $\square$

### The descent is the adjoint

The inner product on $V$ is a class sum. To compare it with the integral over $[U(V)]$ the proof uses one lemma from a later chapter.

**Lemma (Class sums and Petersson products).** Let $V$ be standard, let $l$ be twice the Harish-Chandra parameter of the weight $(\kappa, e)$, and let $\Xi$, $\Xi'$ be algebraic forms of weight $(\kappa, e)$ on which a level $K = \mathrm{levelOf}(H)$ acts by a character. Then

$$\langle\Xi, \Xi'\rangle = [K_0 : K]\cdot d_\kappa\cdot\langle\Xi^\natural, \Xi'^\natural\rangle_{\mathrm{Pet}},$$

where $K_0$ is the stabilizer of the standard lattice and $d_\kappa$ is the dimension of the weight.

Lean: `New.LevelPlaces.LevelForm.inner_eq_petersson` (New/OneLift/HeckeValues/CharacterLift.lean).

The lemma is a general fact on definite spaces. The Petersson product is an integral over $[U(V)]$. It splits into a sum over the classes and an integral over the compact real group, and the Schur orthogonality relations give $d_\kappa$. The source places it in the file of [Hecke values of character lifts](/chapter/hecke-values/).

**Theorem (Adjointness).** Let $l$ fit the pair, let $y$ be a form of type $l$ on $W$, and let $\Xi$ be a form on $V$. Then

$$\langle\Theta_W y, \Xi\rangle = \langle y, \theta\Xi\rangle_{\mathrm{Pet}},$$

with the class sum product on $V$ and the Petersson product on $W$. The descent $\theta\Xi$ is a form of type $l$ on $W$.

Lean: `New.DescentPair.inner_thetaLift` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.isForm_normalizedDescent` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Let $c = [K_0 : K]\,d_\kappa$ and $\phi = \phi_{v^+}$.

1. By the lemma on class sums, $\langle\Theta_W y, \Xi\rangle = c\,\langle(\Theta_W y)^\natural, \Xi^\natural\rangle_{\mathrm{Pet}}$.
2. The function $(\Theta_W y)^\natural$ is the theta lift $L_\phi y$. So the right side is $c\,\langle L_\phi y, \Xi^\natural\rangle_{\mathrm{Pet}}$.
3. The datum is an arrow in both directions. The adjointness of theta lifts in Volume 6 (`New.IsArrow.inner_formLift_adjoint`) gives $\langle L_\phi y, \Xi^\natural\rangle = \langle y, \overline{L'_\phi\,\overline{\Xi^\natural}}\rangle$, where $L'$ is the lift by the transposed kernel.
4. Volume 9 shows that $\theta\Xi = c\cdot\overline{L'_\phi\,\overline{\Xi^\natural}}$ (`New.DescentPair.normalizedDescent_eq_smul_star_lift_swap`). So $c$ times the last product is $\langle y, \theta\Xi\rangle_{\mathrm{Pet}}$.

The descent is $c$ times a lift by an arrow, and the conjugate of a form is a form of the conjugate type. So $\theta\Xi$ is a form of type $l$. $\square$

The two factors $c$ cancel. This is why the descent carries the factor $[K_0 : K]\,d_\kappa$: with it, $\theta$ is the exact adjoint for the class sum product on $V$.

**Theorem (The adjoint of the single lift).** Let $1 \leq j \leq m$. For a form $y$ of level $J_M$ on $W_j$ and a form $\Xi$ on $V_j$, $\langle\Theta_{j,\vartheta}y, \Xi\rangle = \langle y, \theta\Xi\rangle_{\mathrm{Pet}}$. The adjoint $\Theta_{j,\vartheta}^*\Xi$ is the form on $W_j$ whose function is $\theta\Xi$. At each $g$ its value is $\langle\theta_W(g, \cdot), \Xi\rangle$.

Lean: `New.Data.inner_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean), `New.Data.coe_adjoint_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean), `New.Data.adjoint_singleLift_apply` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The first claim is the adjointness theorem for the $j$-th pair and $l = 2\varsigma$. For the second, the adjoint is a map into the forms of level $J_M$. So it is enough to show that $\theta\Xi$ has level $J_M$. Let $k \in J_M$. Its reduction $s$ at the chosen places is $1$. The equivariance below gives $\theta\Xi(gk) = \theta(\rho(1)\Xi)(g) = \theta\Xi(g)$. So $\theta\Xi$ is a form of level $J_M$. It has the same inner products with all $y$ as the adjoint, so it is the adjoint. The third claim is the theorem of Section 2. $\square$

**Corollary.** Let $1 \leq j \leq m$. A form $\Xi$ on $V_j$ has $\theta\Xi = 0$ if and only if $\langle\Theta_{j,\vartheta}y, \Xi\rangle = 0$ for every form $y$ of level $J_M$ on $W_j$.

Lean: `New.Data.normalizedDescent_eq_zero_iff` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* $\theta\Xi = 0$ if and only if $\Theta_{j,\vartheta}^*\Xi = 0$. An adjoint vanishes at $\Xi$ if and only if $\langle y, \Theta^*\Xi\rangle = \langle\Theta y, \Xi\rangle$ is $0$ for all $y$. $\square$

So the kernel of the descent is the orthogonal complement of the range of the lift. The chapter [the comparison operator, part 1](/chapter/comparison-operator-1/) uses this: a good form on $V_j$ that is orthogonal to all good lifts has descent $0$.

### The lift as an integral of the kernel

**Theorem.** Let $l$ fit the pair and let $y$ be a form of type $l$ on $W$. The function $g \mapsto y(g)\,\theta_W(g, \cdot)$, with values in the finite dimensional space of forms on $V$, is integrable on $[U(W)]$, and

$$\Theta_W y = \int_{[U(W)]} y(g)\,\theta_W(g, \cdot)\,dg.$$

For $1 \leq j \leq m$ and $y$ of level $J_M$ on $W_j$, the same holds for $\Theta_{j,\vartheta}y$.

Lean: `New.DescentPair.integrable_smul_vectorKernelForm` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.thetaLift_eq_integral` (New/Determinant/Norms/AdjointThetaLift.lean), `New.Data.singleLift_eq_integral` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Take an orthonormal basis $b_i$ of the forms on $V$. The coordinate of $y(g)\,\theta_W(g, \cdot)$ on $b_i$ is $y(g)\,\overline{\langle b_i, \theta_W(g, \cdot)\rangle}$, which is $y(g)\,\overline{\theta b_i(g)}$ by Section 2. Both $y$ and $\theta b_i$ are forms on $W$, so they are square integrable, and the product is integrable. A finite sum of integrable functions is integrable.

For the formula, the map $\Xi \mapsto \Xi^\natural(h)$ is injective on forms after evaluation at all $h$. Evaluation at $h$ is a continuous linear map, so it commutes with the integral. By Section 2, $\theta_W(g, \cdot)^\natural(h) = \theta(\omega(g, h)\phi_{v^+})$. So the right side at $h$ is $\int y(g)\,\theta(\omega(g, h)\phi_{v^+})\,dg$, the theta lift of $y$ at $h$. This is $(\Theta_W y)^\natural(h)$. $\square$

The same chapter uses the integral formula for the single lift.

### Equivariance under the chosen places

The finite group $\mathsf{G}_M = \prod_{w \in M}\mathrm{GL}_r(k_w)$ acts on both sides. On the forms of level $J_M$ on $W$ it acts through integral lifts of its elements: $s$ acts as right translation by any integral $k$ with reduction $s$.

**Definition (The action on forms on $V$).** For $s \in \mathsf{G}_M$, let $k'(s)$ be a lift to the integral points of $U(V)$ of the family that is $\mathrm{diag}(s_w, 1)$ at each $w \in M$, with $s_w$ on the rows of $\iota$, and $1$ at each $w \in Q$. Then $s$ acts on a form $\Xi$ on $V$ by

$$\rho(s)\Xi = \Bigl(\prod_{w \in M}\psi_w(\det s_w)\Bigr)\cdot R(k'(s))\,\Xi,$$

with $R$ the right translation of algebraic forms of weight $(\kappa, e)$.

Lean: `New.DescentPair.formAction` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.coe_formAction` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma.** Let $k$ be an integral point of $U(W)(\mathbb{A}_f)$ with reduction $s$ at the chosen places. Then $\omega((1, k), (1, k'(s)))$ multiplies $\phi_\xi$ by $\chi(s)^{-1}$, where $\chi(s) = \prod_{w \in M}\psi_w(\det s_w)$.

Lean: `New.DescentPair.omega_fockDatum_eq_inv_prod_smul` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The finite points act only on the finite part $\Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ of the datum. Volume 9 computes the action of such a pair on the block datum (`New.DescentPair.omega_blockDatum_eq_smul`). At the places of $M$ the block datum is the indicator of the inclusion matrix, and the pair $(s_w, \mathrm{diag}(s_w, 1))$ fixes it up to the character. $\square$

**Theorem (Equivariance).** Let $k$ be integral in $U(W)(\mathbb{A}_f)$ with reduction $s$ at the chosen places.

1. For every form $\Xi$ on $V$ and every $g$, $\theta\Xi(g k) = \theta(\rho(s)\Xi)(g)$.
2. If $l$ fits the pair, then $\Theta_W(R(k)y) = \rho(s)\,\Theta_W y$ for every form $y$ of type $l$.
3. For $1 \leq j \leq m$ and $s \in \mathsf{G}_M$, $\Theta_{j,\vartheta}$ intertwines the action of $\mathsf{G}_M$ on forms of level $J_M$ on $W_j$ with $\rho$.

Lean: `New.DescentPair.normalizedDescent_mul_eq_normalizedDescent_formAction` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.thetaLift_formRep` (New/Determinant/Norms/AdjointThetaLift.lean), `New.Data.principalRep` (New/UpperBound/Objects/Rows.lean), `New.Data.singleLift_principalRep` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Let $c = \chi(s)$. It is a product of values of characters of finite order, so $\bar c = c^{-1}$ and $c \neq 0$.

For part 1, write $\theta\Xi$ as $[K_0 : K]\,d_\kappa$ times the conjugate of the transposed lift of $\overline{\Xi^\natural}$. The transposed lift is equivariant: translating its input by $(1, k'(s))$ and its datum by $(k'(s), k)$ translates its output by $k$. By the lemma, the pair scales the datum by $c^{-1}$. The form $\rho(s)\Xi$ is $c$ times the translate of $\Xi$ by $k'(s)$, and its conjugate brings $\bar c = c^{-1}$. The two scalars match.

For part 2, the lift by an arrow commutes with translations when the datum is moved by the same point. Moving $k$ to the datum and adding $k'(s)$ on $V$ gives $c^{-1}$ times the datum. So $\Theta_W(R(k)y) = c\,R(k'(s))\Theta_W y = \rho(s)\Theta_W y$, after $c\cdot c^{-1} = 1$.

Part 3 is part 2 for the $j$-th pair, with $k$ an integral lift of $s$. $\square$

The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) uses part 3 to show that the single lift commutes with the action of the group algebra of $\mathsf{G}_M$, and so with the idempotent $e_0$.
