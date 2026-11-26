---
title: The central action and the projection bound
lean:
  - New/OneLift/HeckeValues/CentralAction.lean
decls:
  - New.LValueData.centralRep
  - New.LValueData.normalizedCentralOp
  - New.LValueData.coe_centralRep_apply
  - New.LValueData.inner_centralRep_centralRep
  - New.LValueData.inner_normalizedCentralOp
  - New.LValueData.normalizedCentralOp_kernelForm
  - New.LValueData.normalizedCentralOp_trivialLift
  - New.LValueData.commute_algFormRep_scalarFin
  - New.LValueData.algFormRep_scalarFin_apply_comm
  - New.LValueData.centralRep_mem_range_groupAlgAction
  - New.LValueData.centralRep_heckePolyOnForms
  - New.LValueData.normalizedCentralOp_inv_mem_integralForms
  - New.LValueData.sum_normalizedCentralOp_mem_ker_normalizedDescent
  - New.LValueData.isOrthogonalToFalseLifts_sum_normalizedCentralOp_inv
  - New.Selmer.DenominatorLe.norm_card_mul_inner_starProjection_le
  - New.Selmer.DenominatorLe.norm_inner_starProjection_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The central action and the projection bound

Let $Y$ be lift data from $U(1)$ to the definite group of rank $N$, as in [the data, the kernel and the lift](/chapter/character-lifts/#the-data-the-kernel-and-the-lift). The lift is $\varphi_Y = \sum_{[g]} \theta_Y(g)/\#\mathrm{Aut}(g)$, a class sum over $U(1)(E)\backslash U(1)(\mathbb{A}_f)/K_M$ with $K_M = $ `Y.chosenLevel`. The test forms of [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms) are orthogonal to the false lifts in the kernel $Z = \ker\theta^*$ of the descent. The denominator bound `DenominatorLe` is a statement about the line $L = \mathbb{C}\varphi_Y$. This section connects the two. It shows that a bound on the line $L$ bounds $\langle\mathrm{pr}_L\,\Xi, \mathrm{pr}_L\,\Xi'\rangle$ for two test forms, at the cost of the $\ell$-part of the class number of $U(1)$ at the level $K_M$.

The difficulty is that a test form is orthogonal to the false lifts inside $Z = \ker\theta^*$, while `DenominatorLe` for $L$ asks for orthogonality to the false lifts inside $L^\perp$. The two spaces differ: $L^\perp$ contains $Z$, but $L^\perp$ also contains the forms whose descent is a function on $U(1)$ orthogonal to the constant. The tool that closes the gap is the action of $U(1)(\mathbb{A}_f)$ on forms on $U(N)$ through the centre.

### The action

**Definition (Central action).** For $z \in U(1)(\mathbb{A}_f)$, `Y.centralRep z` is right translation of forms on $U(N)$ by the scalar matrix $\det z \cdot 1_N$. The normalized operator is

$$T_z = \nu_V(\det z)\cdot\mathrm{centralRep}(z),$$

with $\nu_V = $ `Y.descentPair.charV` the character of the descent pair.

Lean: `New.LValueData.centralRep` (New/OneLift/HeckeValues/CentralAction.lean), `New.LValueData.normalizedCentralOp` (New/OneLift/HeckeValues/CentralAction.lean).

**Lemma (Underlying form).** The algebraic form of `centralRep z y` is `algFormRep` of the scalar matrix `scalarFin n (det z)` applied to the algebraic form of $y$.

Lean: `New.LValueData.coe_centralRep_apply` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* This is the definition. $\square$

**Lemma (Unitarity).** $\langle\mathrm{centralRep}(z)x, \mathrm{centralRep}(z)y\rangle = \langle x, y\rangle$.

Lean: `New.LValueData.inner_centralRep_centralRep` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* The inner product of `O.FormV` is a constant times the smooth pairing of the two forms. The smooth pairing is invariant under right translation (`smoothPairing_formTranslation`, see [algebraic forms](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups)). $\square$

**Lemma (Adjoint).** $\langle x, T_z y\rangle = \langle T_{z^{-1}}x, y\rangle$.

Lean: `New.LValueData.inner_normalizedCentralOp` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* By unitarity, applied to $\mathrm{centralRep}(z^{-1})x$ and $y$, the adjoint of $\mathrm{centralRep}(z)$ is $\mathrm{centralRep}(z^{-1})$. The value $\nu_V(\det z)$ has absolute value $1$, so its complex conjugate is $\nu_V(\det z^{-1})$. The inner product is conjugate linear in the first variable, and the two scalars match. $\square$

**Lemma (Translation of the kernel).** For $z, g \in U(1)(\mathbb{A}_f)$, $T_{z^{-1}}\,\theta_Y(g) = \theta_Y(gz)$.

Lean: `New.LValueData.normalizedCentralOp_kernelForm` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* Put $\nu = \det z^{-1}$, a unitary finite idele. The scalar matrix of $\nu$ in rank $1$ is $z^{-1}$. The pair $(z^{-1}, \nu\cdot 1_N)$ acts on $\mathrm{Hom}(W, V)$ trivially, since $x \mapsto \nu x\nu^{-1}$ is the identity. So the twisted Weil action of this pair on the block datum $f_Y$ is a number: by `pairWeilFinite_scalarFin` it is $\chi^{-1}$ with $\chi = \nu_V(\det z^{-1})$. The kernel value $\theta_Y(g)(k\,\nu 1_N)$ is the jet of $\omega(g, k\,\nu 1_N)f_Y$. Move the scalar to the first factor with the identity above. This gives $\chi\,\theta_Y(g)(k\,\nu 1_N) = \theta_Y(gz)(k)$, which is the claim. $\square$

**Theorem (The lift is fixed).** $T_z\,\varphi_Y = \varphi_Y$ for every $z \in U(1)(\mathbb{A}_f)$.

Lean: `New.LValueData.normalizedCentralOp_trivialLift` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* $T_z$ is linear, so it commutes with the class sum (`map_classSum`). By the previous lemma for $z^{-1}$, $T_z\theta_Y(g) = \theta_Y(gz^{-1})$. The class sum of $g \mapsto \theta_Y(gz^{-1})$ is $\varphi_Y$ by the translation lemma of [the data, the kernel and the lift](/chapter/character-lifts/#the-data-the-kernel-and-the-lift) (`trivialLift_eq_stdClassSum_translate`). $\square$

This is the theta form of a simple fact. $\varphi_Y$ is the lift of the constant function $1$ on $U(1)$, and $1$ is fixed by every translation of $U(1)$. The centre of $U(N)$ is the image of $U(1)$, and the Weil representation intertwines the two actions up to the character $\nu_V$.

### Compatibility with the false lifts

**Lemma (Scalars commute).** On algebraic forms of the weight of $Y$, translation by a scalar matrix commutes with translation by every $g \in G_f$. In particular `algFormRep (scalarFin n ν) (algFormRep g φ) = algFormRep g (algFormRep (scalarFin n ν) φ)`.

Lean: `New.LValueData.commute_algFormRep_scalarFin` (New/OneLift/HeckeValues/CentralAction.lean), `New.LValueData.algFormRep_scalarFin_apply_comm` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* A scalar matrix commutes with every matrix (`commute_scalarFin`), and `algFormRep` is a homomorphism. $\square$

**Lemma (Images of the group algebra).** If $y$ lies in the image of `groupAlgAction e` for an element $e$ of the group algebra of the residue units at the chosen places, so does $\mathrm{centralRep}(z)y$.

Lean: `New.LValueData.centralRep_mem_range_groupAlgAction` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* `formAction g` is a number times a right translation. So it commutes with $\mathrm{centralRep}(z)$, by the previous lemma. Apply the lemma on invariant images of [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms). $\square$

**Lemma (Hecke polynomials).** Let $w$ be a split place ($\bar w \neq w$) with $w$ off the conjugate closure of the places of $Y$, and let $X \in \mathbb{C}$. Then $\mathrm{centralRep}(z)$ commutes with $H_w(X) = \sum_i (-X)^i q^{i(i-1)/2}T_{w,i}$ on `O.FormV`.

Lean: `New.LValueData.centralRep_heckePolyOnForms` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* $H_w(X)$ is `heckePolyOp` of the translation action. Each $T_{w,i}$ is a finite sum of translations. An operator that commutes with every translation commutes with each $T_{w,i}$ (`map_heckePolyOp`). Scalar translations do so by the lemma on scalars. $\square$

**Lemma (Integrality).** Let $\ell$ be a prime, $j$ an embedding $\mathbb{C} \to \mathbb{C}_\ell$, and $z$ integral above $\ell$ (`integralAbove Unit ℓ`). If $\Xi$ is integral at $j$, so is $T_{z^{-1}}\Xi$.

Lean: `New.LValueData.normalizedCentralOp_inv_mem_integralForms` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* Put $k = \det z^{-1}\cdot 1_N$. The entries of $k$ and $k^{-1}$ are $0$ or the entries of $z^{-1}$ and $z$, so $k$ is integral above $\ell$. The value $\nu_V(\det z^{-1})$ has $j$-norm $1$, because the character has a weight and $z$ is integral above $\ell$ (`norm_apply_detFin_eq_one`). So the gauge of $(T_{z^{-1}}\Xi)(g) = \nu_V(\det z^{-1})\,\Xi(gk)$ at $g$ is the gauge of $\Xi(gk)$ at $g$. The gauge does not change under right translation by an element integral above $\ell$ (`weylGauge_mul_of_mem_integralAbove`). So it is the gauge at $gk$, which is at most $1$. $\square$

### From the line to the kernel of the descent

From here on assume that the stabilisers `classAut` of all classes of $U(1)$ at the level $K_M$ are trivial, and let $s(c)$ be a representative of the class $c$.

**Proposition (Averages are in the kernel).** If $y \perp \varphi_Y$, then $\sum_c T_{s(c)}y \in \ker\theta^*$.

Lean: `New.LValueData.sum_normalizedCentralOp_mem_ker_normalizedDescent` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* Step 1. The kernel $\theta_Y$ is invariant on the right under $K_M$ and on the left under the rational points, so $\theta_Y(c_{\mathrm{out}}) = \theta_Y(s(c))$ for the chosen representative $c_{\mathrm{out}}$. With trivial stabilisers, $\varphi_Y = \sum_c\theta_Y(s(c))$.

Step 2. By the theorem on the fixed lift for $g^{-1}$ and the lemma on the kernel, $\sum_c T_{s(c)^{-1}}\theta_Y(g) = T_{g^{-1}}\sum_c\theta_Y(s(c))$, since $T_{s(c)^{-1}}\theta_Y(g) = \theta_Y(g\,s(c)) = T_{g^{-1}}\theta_Y(s(c))$. So it is $T_{g^{-1}}\varphi_Y = \varphi_Y$.

Step 3. At the point $(x, g)$ the descent of a form $u$ is $\langle\theta_Y(g), u\rangle$, by the lemma on descent as an inner product of [descent and the theta lift of one](/chapter/character-lifts/#the-descent-and-the-theta-lift-of-one). With the adjoint lemma, the descent of $\sum_c T_{s(c)}y$ at $(x, g)$ is $\langle\sum_c T_{s(c)^{-1}}\theta_Y(g), y\rangle = \langle\varphi_Y, y\rangle = 0$. $\square$

**Proposition (Transfer of orthogonality).** Let $e$ be an element of the group algebra of the residue units at the chosen places. If $\Xi$ is orthogonal to the false lifts for $e$ and $\ker\theta^*$, then $\sum_c T_{s(c)^{-1}}\Xi$ is orthogonal to the false lifts for $e$ and $L^\perp$.

Lean: `New.LValueData.isOrthogonalToFalseLifts_sum_normalizedCentralOp_inv` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* Let $w$ be split off the level and $y$ a false lift for $e$ and $L^\perp$ at $w$: $y$ lies in the image of $e$, in the kernel of $H_w(x_w)$, and $y \perp \varphi_Y$. For every $z$, $T_z y$ lies in the image of $e$ and in the kernel of $H_w(x_w)$, by the two lemmas on compatibility. So $\sum_c T_{s(c)}y$ lies in the image of $e$ and the kernel of $H_w(x_w)$, and it lies in $\ker\theta^*$ by the previous proposition. It is a false lift for $e$ and $\ker\theta^*$. So $\langle\sum_c T_{s(c)}y, \Xi\rangle = 0$. By the adjoint lemma this is $\langle y, \sum_c T_{s(c)^{-1}}\Xi\rangle = 0$. $\square$

### The projection bound

**Theorem (Bound with the class number).** Let $\iota : \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. Assume `DenominatorLe ι O e₀ L β` with $e_0 = $ `tupleIdem Unit (X − 1)` and $L = \mathbb{C}\varphi_Y$, and assume that all stabilisers at $K_M$ are trivial. Let $\Xi$, $\Xi'$ be test forms above $\ell$. Then, with $h = \#\mathrm{StdClasses}(K_M)$,

$$\big|\iota\big(h\cdot\langle\Xi, \mathrm{pr}_L\,\Xi'\rangle\big)\big| \leq e^\beta.$$

Lean: `New.Selmer.DenominatorLe.norm_card_mul_inner_starProjection_le` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* If $\varphi_Y = 0$, the projection is $0$ and the claim is $0 \leq e^\beta$. Assume $\varphi_Y \neq 0$, so $\dim L = 1$.

Step 1 (representatives). Choose representatives $s(c)$ of the classes that are integral above $\ell$ (`exists_reps_integralAbove`). Put $\Xi'' = \sum_c T_{s(c)^{-1}}\Xi'$. By the lemma on integrality, $\Xi''$ is integral at every embedding above $\ell$. By the transfer of orthogonality, $\Xi''$ is orthogonal to the false lifts for $e_0$ and $L^\perp$.

Step 2 (the projection). $\mathrm{pr}_L\,u = \langle\varphi_Y, u\rangle\varphi_Y/\|\varphi_Y\|^2$. By the adjoint lemma and the fixed lift, $\langle\varphi_Y, T_{s(c)^{-1}}\Xi'\rangle = \langle T_{s(c)}\varphi_Y, \Xi'\rangle = \langle\varphi_Y, \Xi'\rangle$. So $\mathrm{pr}_L\,\Xi'' = h\cdot\mathrm{pr}_L\,\Xi'$.

Step 3 (the line). `DenominatorLe` gives an operator $\Lambda$ on $L$. On a line, $\Lambda = \mu\cdot\mathrm{id}$ for a number $\mu$, and $\det\Lambda = \mu$. The bound on the determinant reads $e^{-\beta} \leq |\iota\mu|$, since $\dim L\cdot\#\mathrm{Unit} = 1$. The second clause of `DenominatorLe` for $\Xi''$ and the integral form $\Xi$ gives $|\iota\mu|\cdot|\iota\langle\Xi, \mathrm{pr}_L\,\Xi''\rangle| \leq 1$.

Step 4. Combine: $|\iota\langle\Xi, \mathrm{pr}_L\,\Xi''\rangle| \leq e^\beta$, and by Step 2 the left side is $|\iota(h\,\langle\Xi, \mathrm{pr}_L\,\Xi'\rangle)|$. $\square$

**Theorem (Projection bound).** Under the same hypotheses,

$$\big|\iota\langle\mathrm{pr}_L\,\Xi, \mathrm{pr}_L\,\Xi'\rangle\big| \leq \exp\big(\beta + v_\ell(h)\log\ell\big).$$

Lean: `New.Selmer.DenominatorLe.norm_inner_starProjection_le` (New/OneLift/HeckeValues/CentralAction.lean).

*Proof.* $|\iota h| = \ell^{-v_\ell(h)}$, because $\iota$ followed by the inclusion into $\mathbb{C}_\ell$ extends the $\ell$-adic norm of $\mathbb{Q}$ (`PadicComplex.norm_extends`). Divide the previous bound by $|\iota h|$. The projection is self-adjoint and idempotent, so $\langle\Xi, \mathrm{pr}_L\,\Xi'\rangle = \langle\mathrm{pr}_L\,\Xi, \mathrm{pr}_L\,\Xi'\rangle$. Finally $\ell^{v_\ell(h)} = \exp(v_\ell(h)\log\ell)$. $\square$

This is the bound that [character-lifts](/chapter/character-lifts/#point-forms-and-tested-forms) announces: a bound $\beta$ for the line gives the second condition of `HasDenominatorsLe` of [regular families](/chapter/twists-critical-pairs/#regular-families-of-twists), with the extra term $v_\ell(h)\log\ell$.

**Remark (Formalization).** The representatives $s(c)$ are obtained from an existence statement, so they are chosen and not explicit. The statement does not depend on them. The hypothesis that all stabilisers are trivial is used only in Step 1 of the proposition on averages, to write $\varphi_Y$ as a plain sum over classes. The class number $h$ is `Nat.card (StdClasses Y.chosenLevel)`, which is positive. The theorem is stated with `open scoped Classical`, which only supplies decidability for the idempotent `tupleIdem`.
