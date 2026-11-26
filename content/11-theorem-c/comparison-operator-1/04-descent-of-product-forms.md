---
title: Descent of product forms
lean:
  - New/OneLift/ComparisonOperator/GluedLattices.lean
  - New/OneLift/ComparisonOperator/GluedForms.lean
decls:
  - New.Rows.DividedSplitting.productForm
  - New.Rows.DividedSplitting.reduceAt_liftMod_congruenceGroup
  - New.Rows.kernelClassSum
  - New.Rows.kernelClassSum_smul
  - New.Rows.letterPoly_schur_inclMatrix_mulVec
  - New.Rows.fockPoly_cartanProduct
  - New.Rows.DividedSplitting.normalizedDescent_classForm_mul
  - New.Rows.DividedSplitting.prod_twist_det_eq_inv_mul_charOfTamePart
  - New.Rows.DividedSplitting.normalizedDescent_productForm
  - New.Rows.DividedSplitting.normalizedDescent_stdClassSum_productForm
  - New.Rows.DividedSplitting.denominatorExponent
  - New.Rows.DividedSplitting.norm_schur_diagonal_piecewise_inv_le
  - New.Rows.DividedSplitting.norm_schur_inv_cols_le_weylGauge
  - New.Rows.DividedSplitting.weylGauge_cartanProduct_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Descent of product forms

We now compute the descent $\theta^*$ to $W$ of a form on $V$ that lives on the class of $(h, h')\gamma$ and has a product of two vectors as its value. On a glued lattice the answer is a finite sum of products of a kernel for $(W, V'')$ and a kernel for $(W, V^\circ)$. We also bound the $p$-adic gauge of the product at $(h, h')\gamma$. The class forms $\delta_h(v)$ and their descent are in [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms). The theta kernels and the gauge are in [theta kernels and gauges](/chapter/theta-kernels-gauges/).

### Product forms

Let $V$ be a divided splitting and $L$ a divided lattice with point $\gamma$. Let $y$ be a vector of weight $O.\mathrm{colsPlus}$ on $V''$ and $\eta$ one of weight $O.\mathrm{colsMinus}$ on $V^\circ$. The *Cartan product* $y \cdot \eta$ includes $y$ and $\eta$ in the letters $n$ along $\varepsilon$ and projects $y \otimes \eta$ to the weight of $V$.

**Definition (Product form).** For $(h, h') \in G_f(N) \times G_f(m)$ and $y$, the *product form* is the linear map $\eta \mapsto \delta_{(h,h')\gamma}(y\cdot\eta)$. Here $(h, h')$ is the block diagonal point along $\varepsilon$, and $\delta_x(v)$ is the class form supported on the class of $x$ with value $v$.

Lean: `New.Rows.DividedSplitting.productForm` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Definition (Kernel summed over classes).** For a $c \times m$ matrix $w$ modulo $\varpi^2$, $e : r \hookrightarrow m$, a character $b$ and a family $y(h)$, the kernel $\mathcal{K}_b(w, e, y)(g)$ is the sum over the classes $h$ of the row fixing level of $w$ and $e$ of the theta kernel of $(W, I_m)$ at $(g, h)$. Its datum $\Psi_{w,e}$ at $\sigma$ modulo $\varpi^2Q$ is $\chi(\det\sigma_e)$ if $w\sigma \equiv w\iota_e$ modulo $\varpi^2$, and $0$ otherwise, with $\chi$ the product of the tame characters at the places of $\varpi^2Q$. Its polynomial is that of $y(h)$ in the columns of sign $1$.

Lean: `New.Rows.kernelClassSum` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Lemma (Linearity).** $\mathcal{K}_b(w, e, c\,y) = c\,\mathcal{K}_b(w, e, y)$ for $c \in \mathbb{C}$.

Lean: `New.Rows.kernelClassSum_smul` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The theta kernel is linear in the polynomial, and the class sum is linear. $\square$

### The polynomial of a product

**Lemma (Renaming rows).** Let $f : N \to n$ and let $\kappa$ have no column of a height $h$ with $\#N \leq h < \#n$. Then the letter polynomial of $\mathrm{schur}_\kappa(\iota_f)\,y$ is the letter polynomial of $y$ with the rows of its variables renamed along $f$.

Lean: `New.Rows.letterPoly_schur_inclMatrix_mulVec` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The Schur matrix of $A$ acts on polynomials by the substitution of $A^T$, times a power of a determinant. The hypothesis on $\kappa$ makes that power $0$. The substitution of $\iota_f^T$ sends the variable in row $i$ to the variable in row $f(i)$. $\square$

**Lemma (Polynomial of a Cartan product).** If $O.\mathrm{colsPlus}$ and $O.\mathrm{colsMinus}$ have no columns of the excluded heights (condition 3 of a divided splitting), then
$$\mathrm{fockPoly}(y\cdot\eta) = \mathrm{rename}_{\varepsilon\circ\mathrm{inl}}\bigl(P^{+}(y)\bigr)\cdot\mathrm{rename}_{\varepsilon\circ\mathrm{inr}}\bigl(P^{-}(\eta)\bigr),$$
where $P^{+}$ is the letter polynomial in the basis vectors of $W$ of sign $1$, and $P^{-}$ that in those of sign $-1$.

Lean: `New.Rows.fockPoly_cartanProduct` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The Fock polynomial is read on the image under the mixed Cartan map. On a Cartan product this image is the tensor of $\mathrm{schur}(\iota_{\varepsilon\circ\mathrm{inl}})y$ and $\mathrm{schur}(\iota_{\varepsilon\circ\mathrm{inr}})\eta$, and the polynomial of a tensor $u \otimes u'$ is the product of the two letter polynomials. Apply the lemma on renaming rows to each factor. $\square$

### The descent

**Lemma (Descent of a class form on a divided lattice).** For $v$ of the weight of $V$, $h \in G_f(n)$ and $g$,
$$\theta^*\bigl(\delta_{h\gamma}(v)\bigr)(g) = \overline{c_\gamma\cdot\mathrm{modKernel}\bigl(W, V, \nu_W, \nu_V, \varpi^2Q, \Psi_\gamma, \mathrm{fockPoly}(\bar v)\bigr)(g, h)},$$
where $\Psi_\gamma(S)$ is $0$ unless $\bar G_L\bar S = \bar\varpi\,\iota_{O.\mathrm{incl}}$, and is then $\prod_{t}\mu_t(\det S_{O.\mathrm{incl}})$ over the twist places $t$, with $\mu_t$ the tame part of $O$ at $t$.

Lean: `New.Rows.DividedSplitting.normalizedDescent_classForm_mul` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* By the descent of a class form, the left side is the conjugate of the theta kernel at $(g, h\gamma)$ with the datum $\Psi_0$ of $O$. Write the point as $(g, h)(1, \gamma)$. The point $\gamma$ is supported on the chosen places, so it lies in $G_f$ at the places of $\varpi^2Q$ and is $1$ at the twist places. On the finite mixed model such a point acts by the scalar $\chi(\det\gamma)/\sqrt{|\det\gamma|}^{\,r}$ and by the substitution $x \mapsto \gamma^{-1}x$ ([the Weil representation](/chapter/weil-representation/)). As $\gamma$ is $1$ at the twist places, the determinant over the places of $\varpi^2Q$ equals the determinant $\delta$ over the chosen places, and the scalar is $c_\gamma$. It remains to compare the data. The datum $\Psi_0$ at $\gamma^{-1}x$ is $0$ unless $\gamma^{-1}x$ is integral at the places of $\varpi^2Q$ and $\varpi\gamma^{-1}x \equiv \varpi\iota$ modulo $\varpi^2$. Two facts give the comparison.

1. If $\gamma^{-1}x$ is integral at the places of $\varpi^2Q$, so is $x$. Indeed $x = \gamma(\gamma^{-1}x)$, and $\bar\varpi\gamma$ is integral, with $\bar\varpi_w = 1$ at the places $w$ of $\varpi^2Q$, since no conjugate of such a place is chosen.
2. If $x$ is integral and $\bar G_L\bar x = \bar\varpi\iota$, then $\gamma^{-1}x$ is integral there. Indeed $\varpi^2\gamma^{-1}x = \varpi(\varpi\gamma^{-1})x \equiv \varpi^2\iota \equiv 0$ modulo $\varpi^2$, and the lemma on divisibility by $\varpi^2$ applies.

On the common support the two conditions agree, as $\varpi(\gamma^{-1}x) = (\varpi\gamma^{-1})x$. The values agree, as $\gamma^{-1}$ is $1$ at the twist places, so $\gamma^{-1}x$ and $x$ have the same components there. $\square$

**Lemma (Lifts of $\Gamma$).** For $Y \in \Gamma$, the chosen lift $\mathrm{liftMod}(Y) \in K_0$ reduces to $1$ at every chosen place.

Lean: `New.Rows.DividedSplitting.reduceAt_liftMod_congruenceGroup` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The lift reduces to $Y$ modulo $\varpi^2$, and $\bar\varpi Y = \bar\varpi 1$. Apply the lemma on multiplication by $\varpi$ of Section 2. $\square$

**Lemma (The tame factor).** Let $Y \in \Gamma$, $k = \mathrm{liftMod}(Y)$, and let $x$ be modulo $\varpi^2Q$ such that the rows $S$ of $xY$ on $N$ have $w_sS = w_s\iota_e$. Then
$$\prod_t \mu_t(\det x_{O.\mathrm{incl}}) = \Bigl(\prod_t \mu_t(\det k_t)\Bigr)^{-1}\chi\bigl(\det (xk)_{\varepsilon(\mathrm{inl}(e\,\cdot))}\bigr).$$

Lean: `New.Rows.DividedSplitting.prod_twist_det_eq_inv_mul_charOfTamePart` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The character $\chi$ is the product of the $\mu_w$ over all places $w$ of $\varpi^2Q$. The rows $\bar\varpi 1$ of $w_s$ give $\bar\varpi S = \bar\varpi\iota_e$, so $S_e$ reduces to $1$ at every chosen place, and the chosen factors of $\chi(\det S_e)$ are $1$. The lift $k$ lies in $G_f$ supported on the places of $\varpi^2$, so $k$ is $1$ at every twist place, and $k_t = 1$ there. At a twist place $t$ the factor is therefore $\mu_t(\det x_{O.\mathrm{incl}})$, because $\varepsilon(\mathrm{inl}(e\,i)) = O.\mathrm{incl}\,i$. $\square$

The inverse factor $\prod_t\mu_t(\det k_t)$ is $1$ by the same reason. The source keeps it in the statement.

**Theorem (Descent of a product form).** Let $L$ be glued for $s$, and let $bb' = \nu_V$. Then
$$\theta^*\bigl(\mathrm{productForm}_L(h, h')(y)(\eta)\bigr)(g) = \overline{c_\gamma\sum_{Y \in \Gamma}\mathcal{K}''_{Y}\,\mathcal{K}^\circ_Y},$$
with
$$\mathcal{K}''_Y = \mathrm{modKernel}(W, I_N, \nu_W, b, \varpi^2Q, \Psi_{w_s, e}, P^{+}(\bar y))(g\,k_Y, h),$$
$$\mathcal{K}^\circ_Y = \mathrm{modKernel}(W, I_m, \nu_W, b', \varpi^2, [\,\cdot = \iota_z], P^{-}(\bar\eta))(g\,k_Y, h'),$$
where $k_Y = \mathrm{liftMod}(Y)$ and $[\,\cdot = \iota_z]$ is the indicator of $\iota_z$.

Lean: `New.Rows.DividedSplitting.normalizedDescent_productForm` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* Apply the lemma on the descent of a class form on a divided lattice to $v = y\cdot\eta$ and the point $(h, h')$. On the right side, view the datum modulo $\varpi^2$ as a datum modulo $\varpi^2Q$, join the two kernels by the rule for orthogonal sums $V'' \oplus V^\circ$ (the characters multiply to $bb' = \nu_V$), and move $k_Y$ from $g$ into the finite datum. Then both sides are values of the same bilinear form in a datum and a polynomial. For the data: by the indicator lemma of Section 3, the datum $\Psi_\gamma$ is the sum over $Y$ of the indicators that $xY$ is block normalised. Block normalised means $x_{\varepsilon(\mathrm{inr}\,\cdot)}Y = \iota_z$ and $w_s(xY)_{\varepsilon(\mathrm{inl}\,\cdot)} = w_s\iota_e$, and these are the supports of the two data on the right. On the support the values agree by the lemma on the tame factor, and the lift $k_Y$ is $1$ at the chosen places by the lemma on lifts. For the polynomials: conjugation commutes with the Cartan product, so $\overline{y\cdot\eta} = \bar y\cdot\bar\eta$, and the lemma on the polynomial of a Cartan product splits the Fock polynomial. $\square$

**Corollary (Sum over classes).** Under the same hypotheses, for a family $\varphi$ on $G_f(N)$,
$$\theta^*\Bigl(\sum_{h}\mathrm{productForm}_L(h, h')(\varphi(h))(\eta)\Bigr)(g) = \overline{c_\gamma\sum_{Y \in \Gamma}\mathcal{K}_b(w_s, e, \bar\varphi)(g\,k_Y)\,\mathcal{K}^\circ_Y},$$
where $h$ runs over the classes of the row fixing level of $w_s$ and $e$.

Lean: `New.Rows.DividedSplitting.normalizedDescent_stdClassSum_productForm` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The descent and the evaluation at $g$ are linear. Apply the theorem to each class and exchange the two finite sums. $\square$

### The denominator

Fix a prime $p$, a $p$-adic place $\iota : \mathbb{C} \to \mathbb{C}_p$ and $M \in \mathbb{N}$, $M \neq 0$. The gauge $\mathrm{gauge}_\kappa(h, \xi)$ is the largest $p$-adic absolute value of a coordinate of $h^{-1}$ applied to $\iota\circ\xi$ in the weight $\kappa$.

**Definition (Denominator exponent).** With $c^{+}_\tau(h)$ and $c^{-}_\tau(h)$ the numbers of columns of height $h$ of the two diagrams at $\tau$,
$$e_V = \sum_\tau\Bigl(\#a\sum_{h < \#N}c^{+}_\tau(h) + \#m\sum_{h < \#m}c^{-}_\tau(h)\Bigr).$$

Lean: `New.Rows.DividedSplitting.denominatorExponent` (New/OneLift/ComparisonOperator/GluedForms.lean).

**Lemma (A diagonal matrix).** For a set $S$ of indices, every entry of the Schur matrix of weight $\kappa$ of $\mathrm{diag}(M^{-1}$ on $S$, $1$ elsewhere$)$ has $p$-adic norm at most $\|M\|^{-\sum_\tau\#S\,c_\tau}$, where $c_\tau$ is the number of columns of $\kappa_\tau$ of height below the size.

Lean: `New.Rows.DividedSplitting.norm_schur_diagonal_piecewise_inv_le` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The matrix is diagonal, and its entry at a filling $i$ is $M^{-k}$ with $k$ the number of entries of $i$ in $S$. These entries lie in the first $\#S$ rows of the tableau, and a row has at most one box in each column. So $k \leq \#S\,c_\tau$ at each $\tau$. As $\|M\| \leq 1$, the bound follows. $\square$

**Lemma (One block of columns).** Let $M$ lie in the ideal $(\varpi)$. Let $f : l \to n$, let $\kappa$ have no column of height in $[\#l, \#n)$, and suppose that after an invertible change $K$ of the $f$-columns, the columns of $\bar G_L$ outside $S$ are killed by $\bar\varpi$. If the $f$-columns of $g^{-1}$ are those of $h^{-1}$ placed along $f$, then the Schur matrix of the $f$-columns of $(g\gamma)^{-1}$ sends $\iota\circ v$ to a vector of norm at most $\|M\|^{-\sum_\tau\#S\,c_\tau}\,\mathrm{gauge}_\kappa(h, v)$.

Lean: `New.Rows.DividedSplitting.norm_schur_inv_cols_le_weylGauge` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* Lift $K$ to an integral $k \in K_0$ and replace $h$ by $hk$; the gauge does not change, as $k$ is integral. Write the $f$-columns of $(g\gamma)^{-1}$ as $A\,\Delta\,h^{-1}$, where $\Delta = \mathrm{diag}(M^{-1}$ on $S$, $1$ elsewhere$)$ and $A$ is $\gamma^{-1}$ on the $f$-columns times $k$, with the columns in $S$ multiplied by $M$. The matrix $A$ is integral. Indeed $\varpi A$ is integral and vanishes modulo $\varpi$: in the columns of $S$ because $\varpi \mid M$, in the others because $\bar\varpi$ kills them modulo $\varpi^2$. The Schur matrix of an integral matrix does not increase norms. The diagonal matrix costs the factor of the last lemma. $\square$

**Theorem (Denominator of a product).** Let $M \in (\varpi)$, $M \neq 0$, and let $L$ be glued for $s$. Then
$$\mathrm{gauge}\bigl((h, h')\gamma,\ y\cdot\eta\bigr) \leq \|M\|^{-e_V}\,\mathrm{gauge}^{+}(h, y)\,\mathrm{gauge}^{-}_{\bar\iota}(h', \bar\eta),$$
where the last gauge is taken through the conjugate embedding $\iota\circ\mathrm{conj}$.

Lean: `New.Rows.DividedSplitting.weylGauge_cartanProduct_le` (New/OneLift/ComparisonOperator/GluedForms.lean).

*Proof.* The Cartan product is an integral matrix applied to the tensor of two Schur images, one for each block of $\varepsilon$. So the norm is at most the product of the two norms. For the block $N$ use the last lemma with $S$ the range of $\mathrm{dividedEmb}$, which property 3 of a glued lattice provides. For the block $m$ use it with $S$ the whole of $m$, which needs no hypothesis. The block $m$ is read through $\iota\circ\mathrm{conj}$, because $(g\gamma)$ is unitary: the transpose of $(g\gamma)^{-1}$ is the conjugate of $g\gamma$. $\square$

**Remark (Formalization).** The lift $\mathrm{liftMod}(Y)$ is chosen by the library. The theorem holds for this chosen lift. Its proof uses only that the lift reduces to $Y$ modulo $\varpi^2$ and is supported on the places of $\varpi^2$. The file seals `Finset.sum` and `Finset.univ` in two proofs. This only stops definitional unfolding and does not change any statement. The exponent $e_V$ uses $\#a$ for each column of $V''$: a column has distinct entries, so at most $\#a$ of them lie in the range of $\mathrm{dividedEmb}$.
