---
title: The period of a Poincaré series at deep level
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean
decls:
  - New.Exchange.integrable_mul_indicator
  - New.Exchange.integral_norm_mul_indicator
  - New.Exchange.integral_mul_indicator_mul_eq_smul_realConv
  - New.Exchange.poincareKernel
  - New.Exchange.poincareKernel_mul_inlLine
  - New.Exchange.integral_norm_poincareKernel_le
  - New.Exchange.tsum_div_norm_pow_le_of_separated
  - New.Exchange.norm_poincare_period_sub_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The period of a Poincaré series at deep level

We keep the setting of Section 3. This section proves that the period over $V$ of a Poincaré series on $Z = V \oplus \langle 1 \rangle$ is its identity term, up to an error of relative size $10/d$.

### Indicator functions of a level

The level $J(a)$, $a \neq 0$, is an open compact subgroup of $G_f$. Write $\mathrm{vol}\,J(a)$ for its volume. The *real convolution* of $\psi$ on $G_\infty$ and $F$ on $G$ is $(\psi \ast F)(x) = \int_{G_\infty} \psi(r) F(x(r, 1))\, dr$ ([realConv](/decl/New.realConv/)).

**Lemma.** Let $a \neq 0$ and let $\psi$ be integrable on $G_\infty$. Then $h \mapsto \psi(h_\infty)\,1_{J(a)}(h_f)$ is integrable on $G$, and the integral of its absolute value is $(\int_{G_\infty}|\psi|)\cdot \mathrm{vol}\,J(a)$.

Lean: `New.Exchange.integrable_mul_indicator`, `New.Exchange.integral_norm_mul_indicator` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The Haar measure on $G$ is the product of those on $G_\infty$ and $G_f$. The function is a product of an integrable function of $h_\infty$ and the indicator function of a set of finite measure in $h_f$. Fubini's theorem for a product gives both claims. $\square$

**Lemma.** Let $a \neq 0$ and let $F$ have level $J(a)$. Then for every $x$,

$$\int_G \psi(h_\infty)\, 1_{J(a)}(h_f)\, F(xh)\, dh = \mathrm{vol}\,J(a) \cdot (\psi \ast F)(x).$$

Lean: `New.Exchange.integral_mul_indicator_mul_eq_smul_realConv` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* For $h_f \in J(a)$ the level gives $F(xh) = F(x(h_\infty, 1))$. So the integrand is $\psi(h_\infty)F(x(h_\infty,1))\cdot 1_{J(a)}(h_f)$. Integrate over $h_f$ first. $\square$

### The kernel

**Definition (Poincaré kernel).** For $\varphi$ on $G_\infty$ and a subgroup $K$ of $G_f$, put $P_{\varphi,K}(g) = \varphi(g_\infty)\, 1_K(g_f)$.

Lean: `New.Exchange.poincareKernel` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

The Poincaré series of $P$ with centre $x \oplus 1$ is $h \mapsto \sum_{\gamma \in \Gamma_Z} P((x\oplus 1)^{-1}\gamma (h\oplus 1))$, restricted to $V$. Its period against $F$ is the integral of this series times $F(h)$ over $\Gamma_V \backslash G(E,s)$.

**Lemma.** If $g_f \in J(a)$, then $P_{\varphi, J(a)}(g(h\oplus 1)) = \varphi(g_\infty\,\iota(h_\infty))\, 1_{J(a)}(h_f)$.

Lean: `New.Exchange.poincareKernel_mul_inlLine` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* The real part of $g(h \oplus 1)$ is $g_\infty\,\iota(h_\infty)$. As $g_f \in J(a)$, the product $g_f (h\oplus 1)_f$ lies in $J(a)$ if and only if $(h \oplus 1)_f$ does. By the lemma of Section 3 on $\iota_V$, this holds if and only if $h_f \in J(a)$. $\square$

**Lemma (One term).** Let $a \neq 0$, $8(n+1)^2 < A$, and let every $l_w$ have a large gap for $2A$. Let $\varphi = \psi_{l,\alpha,\omega}$. Let $g$ and $k$ be such that the finite part of $g(k \oplus 1)$ lies in $J(a)$. Let $t > 0$ with $t \leq \prod_w \|(g(h\oplus 1))_w\|$ for every $h$. Then $h \mapsto P_{\varphi,J(a)}(g(h \oplus 1))$ is integrable on $G(E,s)$, and

$$\int |P_{\varphi,J(a)}(g(h\oplus 1))|\, dh \leq \mathrm{vol}\,J(a)\cdot C_A(\alpha,\omega)\, t^{-A}.$$

Lean: `New.Exchange.integral_norm_poincareKernel_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Translate $h$ by $k$. The previous lemma, applied to $g(k\oplus 1)$, gives $P(g((kh)\oplus 1)) = \psi(h_\infty)\,1_{J(a)}(h_f)$ with the slice $\psi(r) = \varphi((g(k\oplus 1))_\infty\, \iota(r))$. The bound $t$ holds along this slice, as it holds for all $h$. The lemma on integrable slices of Section 3 gives $\int|\psi| \leq C_A t^{-A}$. The previous lemmas on indicator functions give integrability and the value $(\int|\psi|)\,\mathrm{vol}\,J(a)$. The Haar measure is invariant under the translation by $k$. $\square$

### The packing bound

**Lemma (Packing bound).** Let $X$ be a real normed space of finite dimension $D_X$ with $D_X + 2 \leq A$. Let $(c_i)_{i \in I}$ be points of $X$ with $\|c_i - c_j\| \geq d^2$ for $i \neq j$. Let $\|c_{i_0}\| \leq d$ for one index $i_0$, and let $d \geq 10$. Then the sum of $(d/\|c_i\|)^A$ over $i \neq i_0$ converges, and it is at most $10/d$.

Lean: `New.Exchange.tsum_div_norm_pow_le_of_separated` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* For $i \neq i_0$, $\|c_i\| \geq \|c_i - c_{i_0}\| - \|c_{i_0}\| \geq d^2 - d \geq d^2/2$, since $d \geq 2$. The mutual distances of these points are at least $d^2 \geq d^2/2$. The packing lemma of the source (`New.tsum_inv_pow_le_of_separated`, Lib/General/Analysis/PackingAndSobolev.lean) says: if points have norms and mutual distances at least $\rho > 0$ and $D_X + 2 \leq A$, then $\sum \|c_i\|^{-A}$ converges and is at most $(5/\rho)^A$. With $\rho = d^2/2$,

$$\sum_{i \neq i_0} \Big(\frac{d}{\|c_i\|}\Big)^A \leq \Big(\frac{5d}{d^2/2}\Big)^A = \Big(\frac{10}{d}\Big)^A \leq \frac{10}{d},$$

as $10/d \leq 1$ and $A \geq 1$. $\square$

### The theorem

**Theorem (Period at deep level).** Let $E$ have a primitive root of unity of order $5040$. Let $F$ be automorphic on $V$ of level $J(a)$, $a \neq 0$, with $|F| \leq S$. Let $0 \leq R \leq |\Phi_w(a)|$ for every $w$. Let

$$2f(n+1) + 2 \leq A, \qquad 8(n+1)^2 < A,$$

and let every $l_w$ have a large gap for $2A$. Let $x \in G(E,s)$, and let $d$ satisfy $d^2 \leq R\,\lambda(V,x)$, $f \leq d$ and $10 \leq d$. Let $\varphi = \psi_{l,\alpha,\omega}$ and $\psi(r) = \varphi(\iota(r))$. Then $\psi$ is integrable on $G_\infty$, and

$$\Big|\int_{\Gamma_V\backslash G} \sum_{\gamma \in \Gamma_Z} P_{\varphi,J(a)}\big((x\oplus 1)^{-1}\gamma(h \oplus 1)\big)\, F(h)\, d\mu_V(h) - \mathrm{vol}\,J(a)\cdot(\psi \ast F)(x)\Big| \leq \mathrm{vol}\,J(a) \cdot C_A(\alpha,\omega)\cdot S \cdot \frac{10}{d}.$$

Lean: `New.Exchange.norm_poincare_period_sub_le` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Write $T_\gamma(h) = P((x\oplus 1)^{-1}\gamma(h\oplus 1))\, F(h)$. Every local operator norm is at least $1$, so $t = 1$ is a lower bound for the products of norms in the slice lemma. This gives the integrability of every slice, and of $\psi$ in particular.

*Step 1: the cosets that count.* Choose representatives $C$ of the left cosets of $\iota_V(\Gamma_V)$ in $\Gamma_Z$ with $1 \in C$. Let $W \subseteq C$ be the set of $\gamma$ for which some $k$ puts the finite part of $(x\oplus 1)^{-1}\gamma(k \oplus 1)$ in $J(a)$. Choose such a $k_\gamma$ for each $\gamma \in W$. The base coset $\gamma_0 = 1$ lies in $W$ with $k = x$. Choose a last column $y_\gamma$ for each $\gamma$, and put $c_\gamma = $ the archimedean coordinates of $y_\gamma$ at $x \oplus 1$. These are points of a complex space of dimension $f(n+1)$, so of real dimension $2f(n+1)$.

*Step 2: the columns are separated.* Let $\gamma \neq \gamma'$ in $W$. If $y_\gamma = y_{\gamma'}$, then $\gamma^{-1}\gamma'$ lies in the image of $\iota_V$ by the lemma on equal last columns, so $\gamma$ and $\gamma'$ represent the same coset, a contradiction. So $y_\gamma \neq y_{\gamma'}$. The separation lemma of Section 3, with the elements $k_\gamma$ and $k_{\gamma'}$, gives $\|c_\gamma - c_{\gamma'}\| \geq R\,\lambda(V,x) \geq d^2$. The base column has $\|c_{\gamma_0}\| \leq f \leq d$. The real dimension satisfies $2f(n+1) + 2 \leq A$. So the packing bound gives $\sum_{\gamma \neq \gamma_0} (d/\|c_\gamma\|)^A \leq 10/d$, with convergence.

*Step 3: the terms off the base.* Let $\gamma \in W$, $\gamma \neq \gamma_0$. Then $\|c_\gamma\| > 0$. By the last lemma on last columns in Section 3, $\|c_\gamma\|/d \leq \|c_\gamma\|/f \leq \prod_w\|((x\oplus 1)^{-1}\gamma(h \oplus 1))_w\|$ for every $h$. The lemma on one term with $t = \|c_\gamma\|/d$ and $|F| \leq S$ give

$$\int_G |T_\gamma| \leq \mathrm{vol}\,J(a)\cdot C_A \cdot S\cdot (d/\|c_\gamma\|)^A.$$

Each $T_\gamma$ with $\gamma \in W$ is integrable, as a product of an integrable function and a bounded one.

*Step 4: unfolding.* For fixed $h$, the term $p(g) = P((x\oplus 1)^{-1} g (h \oplus 1))F(h)$ vanishes at $g = \sigma\,\iota_V(\delta)$ unless $\sigma \in W$: if it does not vanish, $k = \delta h$ puts the finite part in $J(a)$. The coset lemma and the automorphy $F(\delta h) = F(h)$ give

$$\sum_{\gamma \in \Gamma_Z} T_\gamma(h) = \sum_{(\sigma,\delta) \in W \times \Gamma_V} T_\sigma(\delta h).$$

By Steps 2 and 3, the integrals $\int_G|T_\sigma|$ have a finite sum over $W$. The lemma on unfolding of a family turns the period into $\sum_{\sigma \in W} \int_G T_\sigma$.

*Step 5: the base term.* Substitute $h \mapsto xh$. The lemma on the kernel with $g = 1$ gives $P((x\oplus 1)^{-1}((xh) \oplus 1)) = \varphi(\iota(h_\infty))\, 1_{J(a)}(h_f)$. The lemma on indicator functions gives $\int_G T_{\gamma_0} = \mathrm{vol}\,J(a) \cdot (\psi \ast F)(x)$.

*Step 6.* The difference of the period and the base term is $\sum_{\gamma \neq \gamma_0} \int_G T_\gamma$. By Steps 3 and 2 its absolute value is at most $\mathrm{vol}\,J(a)\cdot C_A\cdot S \cdot 10/d$. $\square$

**Remark (Formalization).** The representatives $C$, the elements $k_\gamma$ and the last columns $y_\gamma$ are chosen with the axiom of choice (`Classical.skolem`). The bound does not depend on the choice. The sum over $\Gamma_Z$ is a `tsum`. The proof shows that the period integral is the sum of a summable family, so the `tsum` has its true value and is not the junk value $0$. The hypothesis $d \geq f$ is used only for $\|c_{\gamma_0}\| \le d$ and the bound $\|c_\gamma\|/d \le \prod_w \|\cdot\|$.

### An example

Let $f = 1$, $V$ of rank $1$, and $a$ with $|a| = R$. Then $c_\gamma$ lies in $\mathbb{C}^2 \cong \mathbb{R}^4$, and the packing bound needs only $A \geq 6$. The slice lemma needs $A > 32$. If $\lambda(V, x) = 1$, then $d = \sqrt R$ is allowed for $R \geq 100$. The error is then $10/\sqrt R$ of the main constant: the deeper the level, the better the identity term approximates the period.
