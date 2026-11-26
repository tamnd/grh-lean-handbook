---
title: The Rallis operator as a Hecke operator
lean:
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - New/Determinant/Norms/AdjointThetaLift.lean
decls:
  - New.Data.rallisTerm
  - New.Data.rallisOperator
  - New.Data.hasSum_inner_rallisOperator
  - New.Data.exists_heckeAlgebra_inner_eq_inner_translate
  - New.Data.exists_rallisTerm_eq_inner
  - New.Data.exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm
  - New.Data.exists_hecke_eq_rallisOperator
  - New.Data.rallisOnGood
  - New.Data.coe_rallisOnGood_apply
  - New.Data.det_rallisOnGood_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Rallis operator as a Hecke operator

Theorem C compares the norms of theta lifts from $Y_0$ and from the spaces $W_j$. By Rallis' inner product formula such a norm is an inner product $\langle y, R\,y \rangle$, where $R$ is an operator on forms of principal level given by an infinite series of translations. This section proves that $R$ acts on $\mathcal{A}_M(V)$ as an element of $\mathcal{H}$, with one element for two spaces at once. So $R$ preserves the good forms, and the theorem on equal determinants of the last section applies to it. The result is used in [the chapter on the chain determinant](/chapter/chain-determinant/) of Volume 11.

Throughout, $\vartheta$ is a tame character of the data and $j$ is a lift index. Both are fixed. The section uses objects of Theorem C, but only through the two facts recalled in the first subsection.

### The series of Rallis' formula

Let $Q = \pi_M Q$ be the modulus of the twist for $\vartheta$, and let $A$ be the set of finite places that do not divide $Q$ and are not conjugate to a place that divides $Q$. The chosen places all divide $Q$. Let $L_A$ be the group of finite points that are integral at the places of $A$ (`New.localLevel`). [The Rallis series](/chapter/rallis-inner-product/#the-inner-product-formula) is a sum over the cosets $q \in G_f / L_A$, and the representative $\gamma_q$ (`New.SiegelWeil.cosetRep`) of $q$ is the component of a point of $q$ at the places of $A$. So $\gamma_q$ is supported on $A$: its component at every place outside $A$ is $1$.

For a coset $q$ and forms $z, y \in \mathcal{A}_M(V)$, let

$$t_q(z, y) = \frac{\mathrm{mc}(\gamma_q)}{N}\,\langle z, \gamma_q\, y\rangle, \qquad N = \#\big(\mathrm{Mat}_{(r+t) \times r}(\mathcal{O}/Q)\big).$$

Here $\mathrm{mc}(\gamma) = \big(\chi_V(\det \gamma)\,\nu(\gamma)^{r+t}\big)^{-1}$ is the vacuum coefficient for the rank $r + t$ of the space $V_j$ and the character $\chi_V$ of the $j$-th descent pair, $\nu$ is the multiplier, and $\gamma_q$ acts on forms by right translation.

Lean: `New.Data.rallisTerm` (New/Determinant/Norms/AdjointThetaLift.lean).

**Theorem (The Rallis operator).** For every hermitian space $V$ of rank $r$ there is an endomorphism $R_V$ of $\mathcal{A}_M(V)$ that sends each $y$ to its Rallis series. For all $z, y \in \mathcal{A}_M(V)$ the series $\sum_q N\,t_q(z, y)$ converges to $\langle z, R_V\,y\rangle$.

Lean: `New.Data.rallisOperator`, `New.Data.hasSum_inner_rallisOperator` (New/Determinant/Norms/AdjointThetaLift.lean).

This is proved in [the chapter on single theta lifts](/chapter/single-theta-lifts/) of Volume 11, from the summability of the Rallis series in [the inner product formula](/chapter/rallis-inner-product/#the-inner-product-formula). The convergence is of a series indexed by an infinite set, in Mathlib's sense of `HasSum`: the net of finite partial sums converges. The rank condition $2r < r + t$ gives it.

**Remark (Formalization).** `New.Data.rallisOperator` is defined by `Exists.choose` from the existence of an endomorphism that sends each form to its series. Such an endomorphism is unique, as a form is determined by its inner products. So the choice is harmless. All statements of this section use only the property of the theorem above.

### One coset gives a Hecke operator

**Lemma (Translations).** Let $\gamma \in G^M$. There is $p \in \mathcal{H}$ such that, for every hermitian space $V$ of rank $r$ and all $z, y \in \mathcal{A}_M(V)$,

$$\langle z, p_V\, y\rangle = \langle z, \gamma\, y\rangle.$$

Lean: `New.Data.exists_heckeAlgebra_inner_eq_inner_translate` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

The operator $y \mapsto \gamma y$ does not keep $\mathcal{A}_M(V)$, since $\gamma$ need not normalise $J_M$. Its matrix coefficients on $\mathcal{A}_M(V)$ are those of the averaged operator, which does.

*Proof.* Let $K = K_0 \cap G^M$, a compact subgroup of $G^M$, as $G^M$ is closed in $G_f$ and $K_0$ is compact. Let $H = K \cap \gamma K \gamma^{-1}$. It is open in $K$, so the index $n = [K : H]$ is finite. Choose representatives $k_1, \dots, k_n$ of $K/H$ and let

$$a = \sum_{i=1}^{n} k_i\,\gamma \in \mathbb{C}[G^M].$$

Let $\rho$ be a representation of $G^M$ and $y$ a vector fixed by $K$. For $h \in H$ the element $\gamma^{-1} h \gamma$ lies in $K$, so $\rho(k h \gamma) y = \rho(k\gamma)\rho(\gamma^{-1}h\gamma) y = \rho(k\gamma)y$. So $\rho(k\gamma)y$ depends only on the coset $kH$, and $\rho(a)y = \sum_{kH \in K/H} \rho(k\gamma)y$. Left translation by an element of $K$ permutes the cosets, so $\rho(a)y$ is fixed by $K$. By the test for sphericity of [the section on Hecke operators](/chapter/equal-multiplicities/#hecke-operators-away-from-the-level), $a \in \mathcal{S}$. Let $T \in \mathcal{H}$ act as $a$ and put $p = n^{-1}T$.

Let $z, y \in \mathcal{A}_M(V)$. Each $k \in K$ lies in $J_M$, as it is integral and $1$ at the chosen places, so $k$ fixes $z$. The action of $G_f$ on forms is unitary. So $\langle z, k\gamma y\rangle = \langle k^{-1} z, \gamma y\rangle = \langle z, \gamma y\rangle$. Summing over the $n$ cosets gives $\langle z, T_V y\rangle = n\,\langle z, \gamma y\rangle$. Divide by $n$. $\square$

**Lemma (One term).** For each coset $q$ there is $p \in \mathcal{H}$ such that $t_q(z, y) = \langle z, p_V\,y\rangle$ for every $V$ and all $z, y \in \mathcal{A}_M(V)$.

Lean: `New.Data.exists_rallisTerm_eq_inner` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* The representative $\gamma_q$ is supported on $A$. A chosen place divides $Q$, so it is not in $A$, and the component of $\gamma_q$ there is $1$. So $\gamma_q \in G^M$. Apply the lemma on translations to $\gamma_q$, and multiply the operator by the scalar $\mathrm{mc}(\gamma_q)/N$. $\square$

### The limit of the series

**Lemma (Sums of terms).** Let $V$ and $V'$ be hermitian spaces of rank $r$, and suppose that $l$ has gap $\Delta$ for their signs. Let $\alpha, \alpha' \in \mathbb{C}$, and let $B$ and $B'$ be functions on pairs of forms of principal level on $V$ and on $V'$ such that

$$\sum_q \alpha\, t_q(z, y) = B(z, y), \qquad \sum_q \alpha'\, t'_q(z, y) = B'(z, y)$$

for all $z, y$, where $t'_q$ is the term on $V'$. Then there is $p \in \mathcal{H}$ with $B(z, y) = \alpha \langle z, p_V\,y\rangle$ on $V$ and $B'(z, y) = \alpha'\langle z, p_{V'}\,y\rangle$ on $V'$.

Lean: `New.Data.exists_heckeAlgebra_eq_mul_inner_of_hasSum_rallisTerm` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Let $X$ be the space of pairs $(\beta, \beta')$ of functions, with $\beta$ on pairs of forms on $V$ and $\beta'$ on pairs of forms on $V'$. It is a finite-dimensional complex vector space, since $\mathcal{A}_M(V)$ and $\mathcal{A}_M(V')$ are. Let $N_X \subseteq X$ be the image of the linear map

$$\mathcal{H} \to X, \qquad p \mapsto \big((z, y) \mapsto \alpha\langle z, p_V\,y\rangle,\ (z, y) \mapsto \alpha'\langle z, p_{V'}\,y\rangle\big).$$

It is a subspace of a finite-dimensional space, so it is closed. By the lemma on one term, the pair $(\alpha t_q, \alpha' t'_q)$ lies in $N_X$ for each $q$, and so do the finite partial sums. The hypothesis says that these partial sums converge to $(B, B')$ in $X$, coordinate by coordinate. So $(B, B') \in N_X$, which is the claim. $\square$

The proof does not need a bound for the operators $p$ of the single terms. It needs only that all of them lie in one finite-dimensional space of pairs of operators. This is why it treats two spaces at once: one $p$ must serve both.

**Theorem (The Rallis operator lies in $\mathcal{H}$).** Let $l$ have gap $\Delta$ for the signs of $V$ and of $V'$. There is $p \in \mathcal{H}$ with $p_V = R_V$ and $p_{V'} = R_{V'}$.

Lean: `New.Data.exists_hecke_eq_rallisOperator` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* By the theorem on the Rallis operator, the hypotheses of the lemma on sums hold with $\alpha = \alpha' = N$, $B(z, y) = \langle z, R_V y\rangle$ and $B'(z, y) = \langle z, R_{V'}y\rangle$. The lemma gives $p$ with $\langle z, R_V y\rangle = N\langle z, p_V y\rangle$ on $V$, and likewise on $V'$. So $Np \in \mathcal{H}$ has the same matrix coefficients as $R$ on both spaces. An operator on a finite-dimensional inner product space is determined by its matrix coefficients. $\square$

### The Rallis operator on good forms

**Definition (Rallis operator on good forms).** Let $l$ have gap $\Delta$ for the signs of $V$. The restriction of $R_V$ to $\mathcal{G}(V)$ is an endomorphism $R_V^{\mathcal{G}}$ of $\mathcal{G}(V)$.

Lean: `New.Data.rallisOnGood`, `New.Data.coe_rallisOnGood_apply` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

The restriction is defined because $R_V = p_V$ for some $p \in \mathcal{H}$, by the theorem with $V' = V$, and $p_V$ keeps $\mathcal{G}(V)$ since $\mathcal{H}$ commutes with $\bar G$.

**Theorem (Equal determinants of the Rallis operator).** Let $l$ have gap $\Delta$ for the signs of $V$ and of $V'$. Then

$$\det R_V^{\mathcal{G}} = \det R_{V'}^{\mathcal{G}}.$$

Lean: `New.Data.det_rallisOnGood_eq` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Take $p \in \mathcal{H}$ with $p_V = R_V$ and $p_{V'} = R_{V'}$. Then $R_V^{\mathcal{G}}$ and $R_{V'}^{\mathcal{G}}$ are the restrictions of $p$ to the good forms of $V$ and of $V'$. The theorem on equal determinants of [the section on equal traces](/chapter/equal-multiplicities/#equal-traces-and-equal-multiplicities) applies. $\square$

Here it matters that one $p$ serves both spaces. The theorem on equal determinants compares one element of $\mathcal{H}$ on two spaces. If the lemma on sums gave one $p$ for $V$ and another for $V'$, nothing could be compared.

**Remark (Formalization).** In the theorems of this section the gap hypotheses are type class arguments, as in the last section. The proof of the theorem with $V' = V$ inside the definition of `rallisOnGood` is a proof term, so the definition does not depend on a choice of $p$. Different choices give the same restriction, as $p_V = R_V$ for each.

### How Theorem C uses it

In [the chapter on the chain determinant](/chapter/chain-determinant/) the determinant of $R^{\mathcal{G}}$ on $Y_0$ is compared with the determinant on $W_j$, through the theorem above with $V = Y_0$ and $V' = W_j$. The theorem on equal dimensions gives the second fact that Theorem C needs there: the two spaces of good forms have the same dimension $d_T$. Lean uses both in New/Determinant/Chain/NormOfChain.lean. This volume does not use the Rallis operator again.
