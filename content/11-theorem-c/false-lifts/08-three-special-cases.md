---
title: Three special cases
lean:
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
decls:
  - New.Rows.coeff_labelIdem_X_sub_one
  - New.Rows.hyperplaneSum_mul_labelIdem_X_sub_one
  - New.Rows.hyperplaneSum_apply_eq_zero_of_rank_one
  - New.Rows.stdClassSum_gramForm_eq_zero_of_rank_one
  - New.Rows.algFormRep_conj_block_apply_eq_self
  - New.Rows.stdClassSum_period_eq_zero
  - New.Rows.DividedSplitting.algFormRep_conj_block_eq_self
  - New.Rows.DividedSplitting.stdClassSum_inner_productForm_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Three special cases

The main theorem of [Section 7](/chapter/false-lifts/#periods-of-false-lifts) has general hypotheses on $\vartheta$, $C$ and the level. The later chapters use it in three forms. In rank one, condition 1 follows from $\Xi \in \mathrm{range}(e_0)$, so the theorem applies to the false lifts of [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms) directly. For point forms and for product forms, the level condition must be checked. All results are in `New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean`, namespace `New.Rows`.

### Rank one

Let $k$ be a finite field. The group algebra $\mathbb{C}[GL_1(k)]$ has the label idempotents of [Green's characters](/chapter/finite-gln/#greens-characters-with-squarefree-labels). The polynomial $X - 1$ is a label of degree $1$: it is monic, irreducible, so squarefree, and has the root $1 \neq 0$.

**Lemma (The idempotent of $X - 1$).** For every $s \in GL_1(k)$, the coefficient of $s$ in `labelIdem Unit (X - 1)` is $1/\#GL_1(k)$. So this idempotent is the mean over the group.

Lean: `New.Rows.coeff_labelIdem_X_sub_one` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* The label character of $X - 1$ is the character of the root $1$, the rank one part of the trivial determinant character (`labelChar_X_sub_C`). Its value at every $s$ is $1$. The label idempotent has the coefficients $\chi(s)/\#G$ for this character $\chi$ when the polynomial is a label. $\square$

**Lemma (The hyperplane sum kills the mean).** Let $\chi \neq 1$ be a character of $k^\times$ and $\lambda \neq 0$ a row of length one. Then $\sigma_{\chi,\lambda} \cdot e = 0$ in $\mathbb{C}[GL_1(k)]$, where $\sigma_{\chi,\lambda} = \sum_s \chi(\det s)^{-1}s$ is the hyperplane sum of [Section 2](/chapter/false-lifts/#hyperplane-sums-and-block-ratios) and $e$ is the idempotent of $X - 1$.

Lean: `New.Rows.hyperplaneSum_mul_labelIdem_X_sub_one` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* In rank one, $s = 1 + u\lambda$ with $u \in k$. Since $\lambda \neq 0$, the map $u \mapsto 1 + u\lambda$ is a bijection from $k$ onto $k$, and $s$ is invertible for all $u$ except one. So $s$ runs once over $k^\times$, and the sum of the coefficients of $\sigma_{\chi,\lambda}$ is $\sum_{t \in k^\times}\chi(t)^{-1} = 0$, as $\chi^{-1} \neq 1$. For every $s$, $s\,e = e$, because $e$ is the mean. So $\sigma_{\chi,\lambda}\,e = \big(\sum_s \chi(\det s)^{-1}\big)e = 0$. $\square$

**Lemma (Condition 1 in rank one).** Let $O$ be a descent pair with $W$ a line, and let $\psi_v \neq 1$ at all chosen places. Let $\Xi$ lie in the range of $e_0 = $ `tupleIdem Unit (fun _ ↦ X - 1)`, the tensor product over $v \in M$ of the idempotents of $X - 1$. Then for every family of rows $(\lambda_v)$ with some $\lambda_i \neq 0$, the tensor product of the hyperplane sums $\sigma_{\psi_v, \lambda_v}$ kills $\Xi$. So $\Xi$ satisfies condition 1.

Lean: `New.Rows.hyperplaneSum_apply_eq_zero_of_rank_one` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* Write $\Xi = e_0\,y$. The action of the group algebra is an algebra homomorphism, so the tensor product of the hyperplane sums acts on $\Xi$ by the product $(\bigotimes_v\sigma_{\psi_v,\lambda_v})\cdot e_0$. Products of pure tensors are computed factor by factor, and the factor at $i$ is $0$ by the last lemma (`piTensorElem_mul_eq_zero`). $\square$

**Theorem (Periods of false lifts from a line).** Let $r = 1$, let $O$ fit $l_0$, and let $\psi_v \neq 1$ at all places of $O$. Let $\Xi$ be a false lift at $w$: $\Xi \in \mathrm{FL}_w(e_0, \ker\theta^*)$ in the notation of [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms). Let $\varepsilon : N \sqcup l \simeq n$ with $2\#N + 5 < n$. Then, with $\vartheta$, $C$, $h_1$, $x$ and $f$ as in the main theorem, $f$ is left invariant under the rational points and $\mathrm{classSum}_K f = 0$ for every level $K$ that fixes $f$.

Lean: `New.Rows.stdClassSum_gramForm_eq_zero_of_rank_one` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* The definition of $\mathrm{FL}_w$ gives $\Xi \in \mathrm{range}(e_0)$, $H_w(x_w)\Xi = 0$ and $\theta^*\Xi = 0$. The last lemma gives condition 1. For $r = 1$ the rank condition $2r + 2\#N + 3 < n$ is $2\#N + 5 < n$. Apply the main theorem. $\square$

### Point forms

Recall from [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms) the point lift $A = $ `pointLift hY e'` and the point form at $h$, supported on the class of $hA$.

**Lemma (Conjugates of the second block fix forms).** Let $\varepsilon : N \sqcup l \simeq n$, $x$ supported at the chosen places, and $e' : r \hookrightarrow n$ with $e' = \varepsilon \circ \mathrm{inl} \circ \beta$ for a map $\beta : r \to N$. Let $A$ be in $K_0$, with $\bar A_v\,\iota = Y_v$ at the chosen places and $\bar A_v^{\mathsf T}\iota_{e'} = \iota$ at the twist places, where $\iota$ is the inclusion matrix of `O.incl`. Let $k \in K_0(U(I_l))$ with $m = x^{-1}(1, k)x \in K_0$ and $\bar m_v Y_v = Y_v$ at the chosen places. Then right translation by $(xA)^{-1}(1, k)(xA)$ fixes every form $\Xi$ in `O.FormV`.

Lean: `New.Rows.algFormRep_conj_block_apply_eq_self` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* Let $c = A^{-1} m A \in K_0$. Then $(xA)^{-1}(1,k)(xA) = c$.

At a chosen place $v$: $\bar c_v\,\iota = \bar A_v^{-1}\bar m_v Y_v = \bar A_v^{-1}Y_v = \iota$.

At a twist place $v$: $x$ is $1$ at $v$, so $\bar m_v$ is the reduction of $(1, k)$, the block matrix $\mathrm{diag}(1, \bar k_v)$ after $\varepsilon$. The rows $e'$ lie in the block $N$, where this matrix is the identity. So $\bar m_v^{\mathsf T}\iota_{e'} = \iota_{e'}$. Then $\bar c_v^{\mathsf T}\iota = \bar A_v^{\mathsf T}\bar m_v^{\mathsf T}(\bar A_v^{\mathsf T})^{-1}\iota = \bar A_v^{\mathsf T}\bar m_v^{\mathsf T}\iota_{e'} = \bar A_v^{\mathsf T}\iota_{e'} = \iota$.

So $c$ satisfies the hypotheses of the lemma on triangular elements of [Section 4](/chapter/false-lifts/#the-bottom-of-the-tower) with $s_v = 1$ at every place. It acts on $\Xi$ as the block $1$, that is, trivially. $\square$

**Remark (Formalization).** The Lean proof runs under `set_option backward.isDefEq.respectTransparency false`. The option is local to this lemma. It lets `rw` and `simp` match products in $U(I_n)(\mathbb{A}_f)$ across the coercions from the level $K_0$. It changes the elaboration, not the statement.

**Corollary (Periods against point forms vanish).** Let the hypotheses on $O$, $\Xi$, $\varepsilon$, the rank and $C$ be those of the corollary on kernel vectors in Section 7. Let the matrices $Y_v$ have independent columns, let the rows $e' = \varepsilon\circ\mathrm{inl}\circ\beta$ lie in the block $N$, let the places of $\mathfrak m$ lie in $O.\mathrm{places}$, and let $x$ be supported at the chosen places. Put

$$f(h) = \big\langle \text{pointForm}\big(\mathrm{diag}(h_1, h)x\big)\big(C(\text{kernelVector}(g, h))\big),\ \Xi\big\rangle.$$

Let every $k \in K$ be in $K_0$, fix $\Psi$, and have $x^{-1}(1,k)x \in K_0$ with reductions that fix the $Y_v$. Then $\mathrm{classSum}_K f = 0$.

Lean: `New.Rows.stdClassSum_period_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* By `inner_pointForm`, $f(h) = \langle C(\text{kernelVector}(g, h)), \Xi(\mathrm{diag}(h_1, h)\,xA)\rangle$ with $A$ the point lift. The point $xA$ is supported on $O.\mathrm{places}$, as $x$ and $A$ are. The point lift has the properties of the last lemma (`isPointLift_pointLift`). So for $k \in K$ the conjugate $(xA)^{-1}(1, k)(xA)$ fixes $\Xi$. Apply the corollary on kernel vectors with $xA$ in place of $x$. $\square$

### Product forms

Let $V$ be a divided splitting of $I_n = I_N \oplus I_l$, and $L = \gamma\mathcal O^n$ a divided lattice, as in [divided lattices](/chapter/comparison-operator-1/#divided-lattices). The point $\gamma$ is supported at the chosen places, and $\varpi\mathcal O^n \subseteq L \subseteq \mathcal O^n$ there. The product form $V.\text{productForm}\ L\ (x, h)\ y\ \eta$ of [descent of product forms](/chapter/comparison-operator-1/#descent-of-product-forms) is supported on the class of $\mathrm{diag}(x, h)\gamma$, with the Cartan product of $y$ and $\eta$ as its value.

**Lemma (The second block near a divided lattice).** Let $k \in K_0(U(I_l))$ be $1$ modulo the square $\mathfrak m_M^2$ of the product of the chosen places. Then right translation by $\gamma^{-1}(1, k)\gamma$ fixes every $\Xi$ in `O.FormV`.

Lean: `New.Rows.DividedSplitting.algFormRep_conj_block_eq_self` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* The element $(1, k)$ is $1$ modulo $\mathfrak m_M^2$. Since $L$ lies between $\varpi\mathcal O^n$ and $\mathcal O^n$, the conjugate $m = \gamma^{-1}(1, k)\gamma$ is in $K_0$, and its reductions at the chosen places are $1$ (`DividedLattice.reduceAt_conj_eq_one`). So $\bar m_v\iota = \iota$. The divided splitting puts the indices of $W$ into $N$, so $\iota = \iota_{e'}$ with $e' = \varepsilon\circ\mathrm{inl}\circ\beta$. Apply the last lemma but one with $A = 1$, $Y_v = \iota$ and $e'$. $\square$

**Corollary (Slices of false lifts are orthogonal to theta kernels).** Let the hypotheses on $O$, $\Xi$ and the rank be those of the main theorem, and let $\varpi$ generate $\mathfrak m_M^2$. For every divided lattice $L$, $x \in U(I_N)(\mathbb{A}_f)$, $y$ of weight `O.colsPlus`, character $b$, datum $\Psi$ modulo $\varpi$ and $g$,

$$\mathrm{classSum}_{K(\varpi)}\Big(h \mapsto \big\langle V.\text{productForm}\ L\ (x, h)\ y\ \overline{\text{kernelVector}(g, h)},\ \Xi\big\rangle\Big) = 0,$$

where $K(\varpi)$ is the principal level of $\varpi$ in $U(I_l)$ and the kernel vector has weight `O.colsMinus`.

Lean: `New.Rows.DividedSplitting.stdClassSum_inner_productForm_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* Let $C(\zeta) = \text{cartanProduct}(\varepsilon, 1, y, \bar\zeta)$. It is conjugate linear. It is equivariant: let $g$ be real with $g_\tau = \mathrm{diag}(1, u_\tau)$ after $\varepsilon$. As $g_\tau$ is unitary, $g_\tau^{-1} = g_\tau^*$. The columns of $\bar g_\tau$ in the first block are those of $1$, and in the second block they are those of $1$ times $u_\tau$. The Cartan product is multiplicative in the matrix (`schur_mul_schur`), so $\rho(g)\,C(\zeta) = C(\rho(u)\zeta)$. The inner product of a class form with $\Xi$ is the inner product of its value with the value of $\Xi$ (`inner_classForm`). So the function is the one of the corollary on kernel vectors, with $\varepsilon$, $x$ in place of $h_1$, and the point $\gamma$.

The places of $\mathfrak m_M^2$ are the chosen places. The point $\gamma$ is supported at the chosen places. An element of $K(\varpi)$ is in $K_0$ and is $1$ modulo $\varpi$, so it fixes every $\Psi$ modulo $\varpi$, and by the last lemma $\gamma^{-1}(1,k)\gamma$ fixes $\Xi$. Apply the corollary on kernel vectors. $\square$

This is the form used in [the comparison operator, part 2](/chapter/comparison-operator-2/) for property 3 of the comparison operator.
