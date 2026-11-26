---
title: Weil operators and their cocycle
lean:
  - Lib/Weil/Construction/HeisenbergModel.lean
  - Lib/Weil/Construction/WeilOperators.lean
decls:
  - New.Heisenberg.MultiplierAction
  - New.Heisenberg.IsVacuum.weilOp
  - New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp
  - New.Heisenberg.IsVacuum.weilOp_mul
  - New.Heisenberg.IsVacuum.modelInner_weilOp
  - New.Heisenberg.IsVacuum.cocycleRadical
  - New.Heisenberg.IsVacuum.weilRep
  - New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul
  - New.Heisenberg.IsVacuum.conj_delta_mul_weilRep_vacElem
  - New.Heisenberg.IsVacuum.continuous_weilRep
  - New.Heisenberg.OrthogonalSum.weilRep_tmul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Weil operators and their cocycle

This section lets a group $G$ act on the Heisenberg datum of [Section 2](/chapter/weil-representation/#the-heisenberg-datum-and-its-vacuum). Each element of $G$ gets an operator on the model, and the product of three such operators is a scalar. The section computes the scalar as a double integral of the vacuum. When the scalar is $1$, the operators form a true representation, the Weil representation of the action. Sections 4 and 5 prove that the scalar is $1$ for the unitary groups at the real and at the finite places.

Throughout, $W$, $\beta$, $\mu$ and $e$ are as in the definition of [the model](/decl/New.Heisenberg.IsVacuum.Model/), and $\rho(y)$ is the Heisenberg operator.

### Multiplier actions

In the classical theory, a symplectic automorphism $g$ of $W$ gives a new representation $\rho^g(y) = \rho(g y)$ of the Heisenberg group with the same central character. By the Stone-von Neumann theorem there is a unitary operator $\omega(g)$ with $\omega(g)\rho(y)\omega(g)^{-1} = \rho(g y)$, unique up to a scalar of modulus one. The source writes this operator down and fixes the scalar with a function $\Delta$, the multiplier.

**Definition (Multiplier action).** Let $G$ be a topological group that acts continuously on $W$ by group automorphisms, and let $c \colon G \times G \to \mathbb{C}$. A multiplier action of $G$ with cocycle $c$ consists of the following data and conditions.

1. $\beta(g x, g y) = \beta(x, y)$ for all $g \in G$ and $x, y \in W$.
2. Each $g \in G$ preserves the measure $\mu$.
3. A continuous function $\Delta \colon G \to \mathbb{C}$ with $\Delta(1) = 1$ and $\Delta(g^{-1}) = \overline{\Delta(g)}$.
4. For all $g, h \in G$,
$$\Delta(g)\,\Delta(h)\,\Delta((g h)^{-1}) \int_W \int_W e(h x)\, e(g h y)\, \beta(x, y)\, e(x + y)\, d\mu(y)\, d\mu(x) = c(g, h).$$

If no cocycle is given, then $c = 1$.

Lean: `New.Heisenberg.MultiplierAction` (Lib/Weil/Construction/HeisenbergModel.lean).

The condition (4) does not constrain $\Delta$ much when $c$ is arbitrary: it is then the definition of $c$. The condition with $c = 1$ is a real condition. It says that $\Delta(g)\Delta(h)\Delta((gh)^{-1})$ is the inverse of an explicit double integral. At $h = 1$ the double integral is $\int\!\int e(x) e(g y) \beta(x, y) e(x + y)$, and condition (4) with $c = 1$ forces $\Delta(g) \neq 0$ for every $g$. So for an action with cocycle $1$ the multiplier never vanishes.

### The Weil operators

**Definition (Weil operator).** For a multiplier action $B$ with multiplier $\Delta$ and $g \in G$, the Weil operator of $g$ is the bounded operator on the model
$$\omega(g) v = \Delta(g) \int_W v(y)\, \rho(g y) e\, d\mu(y).$$

Lean: `New.Heisenberg.IsVacuum.weilOp` (Lib/Weil/Construction/WeilOperators.lean).

The integral converges in the model, since $\rho(g y)$ is an isometry and $v$ is integrable. The operator has norm at most $|\Delta(g)|\,\|e\|$. The substitution $y \mapsto g y$ preserves $\mu$, so the value of $\omega(g) v$ at $x$ is
$$\Delta(g) \int_W v(y)\, \beta(g y, x)\, e(x - g y)\, d\mu(y).$$
Compare this with the definition of the model: $\omega(g)$ replaces the reproducing kernel $\beta(y, x) e(x - y)$ by its image under $g$ in one variable. The translation law $\omega(g)\rho(y) = \rho(g y)\omega(g)$ follows from the change of variables $y' = y + y_0$ in the integral.

Lean: `New.Heisenberg.IsVacuum.weilRep_eq_integral`, `New.Heisenberg.IsVacuum.weilRep_apply_eq_integral` (Lib/Weil/Construction/WeilOperators.lean).

**Theorem (The cocycle relation).** For a multiplier action with cocycle $c$ and all $g, h \in G$,
$$\omega((g h)^{-1})\,\omega(g)\,\omega(h) = c(g, h) \cdot 1.$$

Lean: `New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* Each Weil operator satisfies $\omega(k)\rho(y) = \rho(k y)\omega(k)$. So the product $P = \omega((gh)^{-1})\omega(g)\omega(h)$ satisfies $P\rho(y) = \rho((gh)^{-1} g h y) P = \rho(y) P$. By [Schur's lemma for the model](/decl/New.Heisenberg.IsVacuum.eq_smul_one_of_commute/), $P$ is the scalar $(P e)(0)$. Write $P_k(w)$ for the operator $v \mapsto \int w(y)\rho(k y) v\,d\mu(y)$. The three integrals that make up $(P e)(0)$ can be put together with the rule $P_k(P_l(w) v)(x) = P_{kl}(w)(P_k(v)(x))$, which is a change of variables. Then $P_1(w) v = v(0) w$ by [the Moyal lemma](/decl/New.Heisenberg.IsVacuum.integrated_eq_smul/). After these steps $(P e)(0)$ is $\Delta(g)\Delta(h)\Delta((gh)^{-1})$ times the double integral of condition (4), and this is $c(g, h)$. $\square$

This is the step in which the source avoids the Schrödinger model. The usual proof that $\omega(g)\omega(h) = \omega(gh)$ on the unitary group compares $\omega$ with a Schrödinger model on a Siegel parabolic subgroup of a split space. It then uses the Iwasawa decomposition and the sum $V \oplus V^-$. Here the scalar is an explicit integral, and Sections 4 and 5 compute it place by place.

**Corollary.** Assume that $c(g, 1) = 1$ for every $g$. Then $\omega(1) = 1$, and for all $g, h \in G$,
$$\omega(g)\,\omega(h) = c(g, h)\,\omega(g h).$$
Each $\omega(g)$ preserves the inner product of the model: $\langle \omega(g) v, \omega(g) w \rangle = \langle v, w \rangle$.

Lean: `New.Heisenberg.IsVacuum.weilOp_one`, `New.Heisenberg.IsVacuum.weilOp_mul`, `New.Heisenberg.IsVacuum.modelInner_weilOp` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* $\omega(1) = \Delta(1) \int v(y)\rho(y) e\,d\mu(y) = v$ by [superposition](/decl/New.Heisenberg.IsVacuum.map_eq_integral/). The [cocycle relation](/decl/New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp/) for the pair $((gh)^{-1}, 1)$ gives $\omega(gh)\omega((gh)^{-1}) = c((gh)^{-1}, 1) = 1$. Multiply the cocycle relation for $(g, h)$ on the left by $\omega(gh)$. For the inner product, the cocycle relation for $(g, 1)$ gives $\omega(g^{-1})\omega(g) = 1$. A computation with the formula for the value of $\omega(g)$ and the identity $\Delta(g^{-1}) = \overline{\Delta(g)}$ shows that $\omega(g^{-1})$ is the adjoint of $\omega(g)$ for the inner product. So $\langle \omega(g) v, \omega(g) w \rangle = \langle v, \omega(g^{-1})\omega(g) w\rangle = \langle v, w \rangle$. $\square$

**Proposition (The radical of the cocycle).** Assume that $c(g, 1) = 1$ for every $g$. Then
$$c(g, h)\, c(g h, k) = c(h, k)\, c(g, h k)$$
for all $g, h, k$. The set of the $s \in G$ with $c(g, s) = 1$ for every $g \in G$ is a subgroup of $G$.

Lean: `New.Heisenberg.IsVacuum.cocycleRadical` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* Apply $(\omega(g)\omega(h))\omega(k) = \omega(g)(\omega(h)\omega(k))$ to the vacuum, use the [corollary](/decl/New.Heisenberg.IsVacuum.weilOp_mul/) on both sides, and pair the result with the unit vector $\omega(ghk)e$. This gives the identity. If $s$ and $t$ are in the set, the identity for $(g, s, t)$ gives $c(g, st) = c(gs, t)\,c(g, s) / c(s, t) = 1$. If $s$ is in the set, the identity for $(g, s^{-1}, s)$ gives $c(g, s^{-1}) = 1$. $\square$

Section 5 uses this subgroup at the finite places. There the source proves $c(g, s) = 1$ for generators $s$ of the finite unitary group, and the subgroup property gives it for all $s$.

### The Weil representation of an action with cocycle 1

**Definition (Weil representation).** For a multiplier action $A$ with cocycle $1$, the Weil representation is the homomorphism $\omega \colon G \to \mathrm{End}(\mathcal{H}_e)$ that sends $g$ to the Weil operator of $g$.

Lean: `New.Heisenberg.IsVacuum.weilRep` (Lib/Weil/Construction/WeilOperators.lean).

It is a homomorphism by the [corollary](/decl/New.Heisenberg.IsVacuum.weilOp_mul/) with $c = 1$. The source records its main properties.

1. Each $\omega(g)$ preserves the inner product.
2. $\omega(g)\rho(x) v = \rho(g x)\omega(g) v$.
3. $\|\omega(g)\| \le \|e\|\,|\Delta(g)|$ for the $L^1$ norm.

Lean: `New.Heisenberg.IsVacuum.modelInner_weilRep`, `New.Heisenberg.IsVacuum.weilRep_heisenbergOp`, `New.Heisenberg.IsVacuum.norm_weilRep_le` (Lib/Weil/Construction/WeilOperators.lean).

**Proposition (Elements that fix the vacuum).** Let $A$ be a multiplier action with cocycle $1$, and let $g \in G$ with $e(g y) = e(y)$ for every $y$. Then for every $v$ in the model and every $x \in W$,
$$(\omega(g) v)(x) = \Delta(g)\, v(g^{-1} x).$$

Lean: `New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* Since $g$ preserves $\beta$ and $e$, the kernel satisfies $\beta(g y, x) e(x - g y) = \beta(y, g^{-1}x) e(g^{-1}x - y)$. So the value of $\omega(g) v$ at $x$ is $\Delta(g)$ times the reproducing integral of $v$ at $g^{-1} x$. $\square$

**Proposition (The overlap with the vacuum).** For a multiplier action with cocycle $1$ and every $g \in G$,
$$\overline{\Delta(g)}\,(\omega(g) e)(0) = 1.$$

Lean: `New.Heisenberg.IsVacuum.conj_delta_mul_weilRep_vacElem`, `New.Heisenberg.IsVacuum.integrated_moveBy_vacElem_eq_smul` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* Let $T$ be a surjective bounded operator that preserves the inner product and satisfies $T\rho(y) = \rho(g y) T$. Apply $T$ to [the Moyal lemma](/decl/New.Heisenberg.IsVacuum.integrated_eq_smul/) with $w$ the preimage of $e$. This gives $\int v(y)\rho(gy)e\,d\mu(y) = \overline{(Te)(0)}\,Tv$. Take $T = \omega(g)$, which is surjective with inverse $\omega(g^{-1})$. Then $\omega(g) e = \Delta(g)\overline{(\omega(g)e)(0)}\,\omega(g)e$. The vector $\omega(g)e$ is a unit vector for the inner product, since $\langle e, e \rangle = e(0) = 1$. So $\Delta(g)\overline{(\omega(g)e)(0)} = 1$, and the claim is its conjugate. $\square$

So the overlap $\langle e, \omega(g) e\rangle$ is $\overline{\Delta(g)}^{-1}$. This is how the source fixes the scalar in $\omega(g)$: the multiplier is the conjugate of the inverse of the vacuum coefficient. If $g$ fixes the vacuum, then the [last proposition](/decl/New.Heisenberg.IsVacuum.weilRep_apply_of_vacuum_smul/) gives $(\omega(g)e)(0) = \Delta(g)$, and so $|\Delta(g)| = 1$.

**Theorem (Continuity).** Let $A$ be a multiplier action with cocycle $1$ of a first countable group $G$. Then $(g, v) \mapsto \omega(g) v$ is continuous on $G \times \mathcal{H}_e$.

Lean: `New.Heisenberg.IsVacuum.continuous_weilRep` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* The map $v \mapsto \int v(y)\rho(gy)e\,d\mu(y)$ is Lipschitz with the constant $\|e\|$ for every $g$. So it is enough to prove continuity in $g$ for a fixed $v$. This follows from dominated convergence, since $\rho$ is isometric and continuous, the action of $G$ on $W$ is continuous, and $\Delta$ is continuous. $\square$

**Remark (Formalization).** The multiplier $\Delta$ is a datum of the action, not a consequence of it. The classical theory defines $\omega(g)$ up to a scalar and then chooses the scalar, for example by the Weil index or by a splitting of the metaplectic cover. Here the choice is the function $\Delta$, and condition (4) with $c = 1$ is the claim that this choice gives a true representation. The two constructions of Sections 4 and 5 give $\Delta$ by a formula and prove condition (4). The cocycle $c$ in the general structure has the default value $1$, and the source uses a general $c$ only in [the cocycle relation](/decl/New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp/) and the results that follow from it in this section. No metaplectic cover appears anywhere in the source.

### Orthogonal sums

The adelic space of Section 6 is a product of the real and the finite parts, and the vacuum is a product. The source has a general rule for this case.

An orthogonal sum is an isomorphism $\varphi \colon W_1 \times W_2 \to W$ of topological groups such that $\beta(\varphi x, \varphi y) = \beta_1(x_1, y_1)\beta_2(x_2, y_2)$ and $e(\varphi x) = e_1(x_1)e_2(x_2)$, where $e_1$ and $e_2$ are vacua. Then the product $v \otimes w$ of model vectors, the function $\varphi(a, b) \mapsto v(a) w(b)$, lies in the model of $e$. Norms and inner products are multiplicative on products, and the product of the two vacua is the vacuum.

Lean: `New.Heisenberg.OrthogonalSum`, `New.Heisenberg.OrthogonalSum.tmul`, `New.Heisenberg.OrthogonalSum.norm_tmul`, `New.Heisenberg.OrthogonalSum.modelInner_tmul`, `New.Heisenberg.OrthogonalSum.tmul_vacElem` (Lib/Weil/Construction/WeilOperators.lean).

**Proposition (Products of Weil operators).** Let $W$ be the orthogonal sum of $W_1$ and $W_2$, all three locally compact. Let $A$, $A_1$ and $A_2$ be multiplier actions with cocycle $1$ of groups $G$, $G_1$ and $G_2$ on $W$, $W_1$ and $W_2$. Let $g \in G$, $g_1 \in G_1$, $g_2 \in G_2$ with $g\varphi(x) = \varphi(g_1 x_1, g_2 x_2)$ for every $x$, and with $\Delta(g) = \Delta_1(g_1)\Delta_2(g_2)$. Then
$$\omega(g)(v \otimes w) = \omega_1(g_1) v \otimes \omega_2(g_2) w.$$

Lean: `New.Heisenberg.OrthogonalSum.weilRep_tmul` (Lib/Weil/Construction/WeilOperators.lean).

*Proof.* Evaluate both sides at $\varphi(a, b)$. The integral over $W$ that defines $\omega(g)$ is an integral over $W_1 \times W_2$, since $\varphi$ carries the product measure to $\mu$. The integrand is a product of a function of $y_1$ and a function of $y_2$, so Fubini's theorem splits the integral. $\square$

The file also proves Wiener's bound for sums of coefficients along a lattice, and the transport of the model along an isomorphism that preserves $\beta$ and $e$. Section 6 uses Wiener's bound to prove that the series $\sum_{\gamma} \langle f', \rho(\gamma) f\rangle$ over the rational vectors converges absolutely. The transport also preserves the measure: an isomorphism $\varphi$ with $e \circ \varphi = e'$ carries $\mu'$ to $\mu$, since both Haar measures give $|e|^2$ the integral $1$.

Lean: `New.Heisenberg.IsVacuum.wiener_bound`, `New.Heisenberg.IsVacuum.transport`, `New.Heisenberg.IsVacuum.measurePreserving_equiv` (Lib/Weil/Construction/WeilOperators.lean).
