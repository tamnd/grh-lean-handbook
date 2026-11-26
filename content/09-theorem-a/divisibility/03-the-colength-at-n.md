---
title: The colength at N
lean:
  - New/UpperBound/Divisibility/ColengthAtLevel.lean
decls:
  - New.colengthDvd_span_pow_monomials
  - New.mul_sum_monomials_apply
  - New.Data.sumDegreeOf
  - New.Data.sumDegreeOf_eq
  - New.Data.mul_sumDegreeOf_le
  - New.Data.integralFormsAt_one_le
  - New.Data.exists_mul_dualPointN_mem_integralAbove
  - New.Data.colengthDvd_integralFormsAt_diagPointN
  - New.Data.upOperator_mem_integralFormsAt
  - New.Data.colengthDvd_comap_upOperator_pow
  - New.Data.exists_colengthDvd_upIntegralForms_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The colength at N

At $p = N$ the divisibility holds on the module $\mathcal A'$ of forms with $\mathrm{Up}^{m/2}\varphi$ integral for $L_0$. This section shows that $\mathcal A'$ is not much smaller than $\mathcal A_\iota$: its colength divides $N^e$ with $e \le mfbD_X$. The proof compares three lattices of values, $L_0 \subset \mathrm{std} \subset L_0^\vee$, and it bounds the cost of each step by a mean degree of the weight. The colength relation $\mathrm{ColengthDvd}(M, M', z)$ says that every finite family in $M$ is carried into $M'$ by a square matrix whose determinant divides $z$ ([colength](/chapter/twisted-lattices/)).

### The model case: monomials

The values of a source form lie in a Weyl module. Its basis vectors are families of tableaux, and a diagonal matrix acts on a tableau as on a monomial. So the model is the space of polynomials of degree $a$ in $k$ variables. Changing the lattice $\mathbb Z_N^k$ to the lattice with last coordinate in $N\mathbb Z_N$ multiplies the monomial $z^\alpha$ by $N^{\alpha_k}$.

**Lemma (Monomials).** Let $O$ be a valuation domain, $N \in O$, and $i$ one of $k$ variables. In the free $O$-module on the monomials $z^\alpha$ of degree $a$ in $k$ variables, the colength of the span of the vectors $N^{\alpha_i} z^\alpha$ divides $N^{\sum_\alpha \alpha_i}$.

Lean: `New.colengthDvd_span_pow_monomials` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* The diagonal matrix with entries $N^{\alpha_i}$ carries $z^\alpha$ to $N^{\alpha_i}z^\alpha$. Its determinant is $N^{\sum_\alpha \alpha_i}$. Apply the theorem on images of square matrices ([colength](/chapter/twisted-lattices/)). $\square$

**Lemma (Mean degree of monomials).** $k \sum_\alpha \alpha_i = a \cdot \#\{\alpha\}$, where $\alpha$ runs over the monomials of degree $a$ in $k$ variables.

Lean: `New.mul_sum_monomials_apply` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* The swap of $z_i$ and $z_j$ permutes the monomials and exchanges $\alpha_i$ and $\alpha_j$. So $\sum_\alpha \alpha_j = \sum_\alpha \alpha_i$ for all $j$. Hence $k\sum_\alpha \alpha_i = \sum_j \sum_\alpha \alpha_j = \sum_\alpha \sum_j \alpha_j = a\cdot\#\{\alpha\}$. $\square$

**Example.** Let $k = 2$ and $a = 2$. The monomials are $z_1^2$, $z_1z_2$, $z_2^2$, with exponents $2, 1, 0$ in $z_1$. The sum is $3 = a \cdot 3/k$. The span of $N^2z_1^2$, $Nz_1z_2$, $z_2^2$ has colength $N^3$, which is $N$ to the dimension times the mean degree $a/k = 1$.

So the cost of one change of lattice is $N^{D a/k}$ in a space of dimension $D$. The source repeats this argument with tableaux in place of monomials. The model is not used later.

### The summed degree

Source forms are determined by their values at representatives of the double cosets $c$ of the level $K_0$. A value lies in a Weyl module whose basis is indexed by families $w = (w_\tau)_{\tau\in\Phi}$ of tableaux. For a variable $u$ of $X_0$, let $\deg_u(w_\tau)$ be the number of entries of $w_\tau$ equal to $u$.

**Definition (The summed degree).** For a variable $u$ of $X_0$, $\ell(u) = \sum_{(c, w)} \sum_{\tau\in\Phi} \deg_u(w_\tau)$, where $(c, w)$ runs over the pairs of a double coset and a basis family.

Lean: `New.Data.sumDegreeOf` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

**Lemma.** $\ell(u) = \ell(u')$ for all variables $u$, $u'$ of $X_0$.

Lean: `New.Data.sumDegreeOf_eq` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* Let $A = \mathrm{diag}(2 \text{ at } u, 1 \text{ elsewhere})$ composed with the transposition of the columns $u$ and $u'$, and let $B$ be the permutation matrix of that transposition. Then $AB = \mathrm{diag}(2 \text{ at } u)$ and $BA = \mathrm{diag}(2 \text{ at } u')$. The Schur functor of a diagonal matrix acts diagonally on the tableaux, by the product of the entries over the boxes. So $\det \mathbb S(\mathrm{diag}(2 \text{ at } u)) = 2^{\sum_w \sum_\tau \deg_u(w_\tau)}$. As $\det(\mathbb S(A)\mathbb S(B)) = \det(\mathbb S(B)\mathbb S(A))$, the exponents for $u$ and $u'$ agree. Summing over the classes multiplies both by the class number. $\square$

**Proposition (The mean degree).** $k\,\ell(u) \le D_X\,f a$, where $D_X$ is the dimension of the space of source forms.

Lean: `New.Data.mul_sumDegreeOf_le` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* The pairs $(c, w)$ form a basis of the source forms, as the automorphism group of each class is trivial ([source forms](/chapter/upper-bound-objects/)). So there are $D_X$ pairs. The space $X_0$ has $k$ variables, so by the lemma $k\,\ell(u) = \sum_{u'} \ell(u') = \sum_{(c,w)} \sum_\tau \sum_{u'} \deg_{u'}(w_\tau)$. The inner sum is the number of boxes of $w_\tau$, which is at most $a$, the size of the weight at each place. So the total is at most $D_X f a$. $\square$

### Three lattices

**Lemma ($\mathcal A_\iota \subset \mathcal A^\vee$).** A source form integral at $1$ is integral at $\delta_0^\vee$.

Lean: `New.Data.integralFormsAt_one_le` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* We have $\delta_0^\vee = d^{-1}$ with $d = \delta_0(\Sigma_N \setminus \Pi_N)$. By the lemma on the image of a diagonal point, $d$ acts at each $\tau$ by a diagonal matrix with entries $1$ and $N$, which is integral. The gauge at $g\,d^{-1}$ of a value is the norm of the Schur functor of these integral matrices applied to the vector whose norm is the gauge at $g$. A polynomial representation of an integral matrix does not increase the norm. So the gauge at $g\delta_0^\vee$ is at most the gauge at $g$, which is at most $1$. $\square$

**Lemma (Adapted representatives).** For every finite adelic point $c$ there is a rational point $\gamma$ such that $\gamma c \delta_0^\vee$ is integral above $N$ and $\delta_0(\Sigma_N)^{-1}\gamma c \delta_0$ is integral above $N$.

Lean: `New.Data.exists_mul_dualPointN_mem_integralAbove` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* By weak approximation above $N$, for finite adelic points $h$ and $t$ there is a rational point $\gamma$ such that $\gamma h$ and $t\,\gamma h\,t^{-1}$ are integral above $N$ ([the p-adic gauge](/chapter/automorphic-forms/)). Take $h = c\delta_0^\vee$ and $t = \delta_0(\Sigma_N)^{-1}$. Since $\delta_0^\vee = \delta_0\,\delta_0(\Sigma_N)^{-1}$, we get $\gamma c\delta_0^\vee\,t^{-1} = \gamma c\delta_0$, and the second condition is the claim. $\square$

**Theorem (From $L_0^\vee$ to $L_0$).** The colength of $\mathcal A^L$ in $\mathcal A^\vee$ divides $N^{\ell}$, where $\ell = \ell(e_\ast)$ is the summed degree in the last variable.

Lean: `New.Data.colengthDvd_integralFormsAt_diagPointN` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* For each double coset $c$ fix a representative $\bar c$ and a rational $\gamma_c$ as in the lemma, and put $r_c = \gamma_c\bar c$. Evaluation $\mathrm{ev}(\varphi) = (\varphi(r_c)_w)_{(c,w)}$ is an $\mathcal O_\iota$-linear map from forms to $\mathbb C^J$, where $J$ is the set of pairs. Let $A$ be the diagonal matrix with entries $N^{\sum_\tau \deg_\ast(w_\tau)}$. Its determinant is $N^{\ell}$, so the colength of the image of $A$ in $\mathcal O_\iota^J$ divides $N^\ell$. Pull this back by $\mathrm{ev}$ (part 4 of the calculus of colength). Two facts are needed.

First, $\mathrm{ev}$ maps $\mathcal A^\vee$ into $\mathcal O_\iota^J$. Indeed $r_c\delta_0^\vee$ is integral above $N$, so the gauge at $r_c\delta_0^\vee$ is the norm of the coordinates of $\varphi(r_c)$, and it is at most $1$.

Second, if $\varphi$ is a source form and $\mathrm{ev}(\varphi) = A y$ with $y$ integral, then $\varphi \in \mathcal A^L$. Every $g$ is $\gamma\,\bar c\,k$ with $\gamma$ rational and $k \in K_0$. The gauge is invariant under rational points on the left, and $\varphi(\gamma\bar c k) = \gamma\cdot\varphi(\bar c)$. So the gauge of $\varphi(g)$ at $g\delta_0$ equals the gauge of $\varphi(r_c)$ at $r_c k\delta_0$. Now $\delta_0^{-1}k\delta_0$ is integral above $N$, as it is mirabolic (Section 2). With $d = \delta_0(\Sigma_N)^{-1}$, the point $d\,r_c k\delta_0$ is integral above $N$, so the gauge at $r_c k\delta_0$ equals the gauge at $d^{-1}$. By the lemma on the image of a diagonal point, $d^{-1}$ acts at each $\tau$ by $\mathrm{diag}(1,\dots,1,N)$, so the gauge at $d^{-1}$ of the value $\varphi(r_c) = Ay$ is $\|\mathbb S(\mathrm{diag}(1,\dots,1,N))^{-1}Ay\|$. On the basis vector $w$ the matrix $\mathbb S(\mathrm{diag}(1,\dots,1,N))$ is $N^{\sum_\tau\deg_\ast(w_\tau)}$, which is the entry of $A$. So the gauge is $\|y\| \le 1$. $\square$

**Lemma ($\mathrm{Up}$ from $L_0$ to $L_0^\vee$).** $\mathrm{Up}$ maps $\mathcal A^L$ into $\mathcal A^\vee$.

Lean: `New.Data.upOperator_mem_integralFormsAt` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* By Section 2, $\mathrm{Up}\,\varphi$ is a source form. Its value at $g$ is $\sum_y \psi_N(y_\ast)\,\varphi(g g'_y)$, with $g'_y = \delta_0^\vee k_y\delta_0^{-1}$ and $k_y$ the point with component $g_y$ at $\Sigma_N$. The coefficients $\psi_N(y_\ast)$ are roots of unity, of norm $1$. The gauge is ultrametric. So it suffices that the gauge of $\varphi(gg'_y)$ at $g\delta_0^\vee$ is at most $1$. Since $k_y$ is integral above $N$, this gauge equals the gauge at $g\delta_0^\vee k_y = gg'_y\delta_0$, which is at most $1$ as $\varphi \in \mathcal A^L$. $\square$

### The colength of $\mathcal A'$

**Proposition.** For every $i \ge 0$, the colength in $\mathcal A_\iota$ of $\{\varphi : \mathrm{Up}^i\varphi \in \mathcal A^L\}$ divides $N^{\ell(i+1)}$.

Lean: `New.Data.colengthDvd_comap_upOperator_pow` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* Induction on $i$. For $i = 0$: $\mathcal A_\iota \subset \mathcal A^\vee$, and the colength of $\mathcal A^L$ in $\mathcal A^\vee$ divides $N^\ell$. Restrict to $\mathcal A_\iota$ (part 4 of the calculus of colength, with the identity map). For the step, the set $\{\mathrm{Up}^i\varphi \in \mathcal A^L\}$ is mapped by $\mathrm{Up}^{i+1}$ into $\mathcal A^\vee$, by the last lemma. Pull back the colength $N^\ell$ of $\mathcal A^L$ in $\mathcal A^\vee$ by $\mathrm{Up}^{i+1}$. This gives the colength $N^\ell$ of $\{\mathrm{Up}^{i+1}\varphi\in\mathcal A^L\}$ in $\{\mathrm{Up}^{i}\varphi\in\mathcal A^L\}$. Compose with the induction hypothesis (part 3). $\square$

**Theorem (The prime $N$, colength).** There is $e \le mfbD_X$ such that the colength of $\mathcal A'$ in $\mathcal A_\iota$ divides $N^e$.

Lean: `New.Data.exists_colengthDvd_upIntegralForms_pow` (New/UpperBound/Divisibility/ColengthAtLevel.lean).

*Proof.* Take $i = \varrho + 1$ in the proposition, so $e = \ell(\varrho+2)$. By the mean degree, $k\ell \le D_Xfa$. By the sizes of the data, $(\varrho+2)a \le mbk$ ([the data and their sizes](/chapter/data-and-sizes/)). So $k e = k\ell(\varrho+2) \le D_X f (\varrho+2)a \le D_X f\,mbk$. Divide by $k > 0$. $\square$

**Remark.** The bound $e \le mfbD_X$ is generous. The mean degree gives $e \le (\varrho+2)faD_X/k$, and $a/k$ is small. Section 7 pays $mfb\,D_X$ at $N$, and the witness of the theorem allows twice that.
