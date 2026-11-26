---
title: The vanishing criterion
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean
decls:
  - New.Exchange.norm_prod_conj_dsCoeff_inv_mul_sub_le
  - New.Exchange.HasDeepLevelSizes
  - New.Exchange.HasDeepLevelSizes.sixteen_le
  - New.Exchange.HasDeepLevelSizes.beta_le_m
  - New.Exchange.HasDeepLevelSizes.pow_places_le_div
  - New.Exchange.HasDeepLevelSizes.sq_le_pow_mul_firstMinimum
  - New.Exchange.typeKernelMajorant
  - New.Exchange.integral_typeKernelMajorant_le
  - New.Exchange.norm_typeKernel_inv_mul_sub_le
  - New.Exchange.norm_le_half_of_firstMinimum_lt
  - New.Exchange.poincare_period_translatedCoeff_eq_zero
  - New.Exchange.norm_realConv_translatedCoeff_le
  - New.Exchange.norm_dsKernel_mul_pow_le
  - New.Exchange.integral_translatedCoeff_mul_eq_prod
  - New.Exchange.realConv_translatedCoeff_mul
  - New.Exchange.norm_le_half_of_le_firstMinimum
  - New.Exchange.eq_zero_of_petersson_translate_eq_zero
  - New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The vanishing criterion

Let $V$ be a hermitian space of rank $n$ over the field $E$ of the data $D$, and $Z = V \oplus \langle 1 \rangle$. Let $l$ be the parameters of the forms on $V$ and $l'$ those of the forms on $Z$. This section proves: a form $y$ on $V$ that is orthogonal to the restrictions of all forms of deep level on $Z$, translated by a real point $\omega$, is zero.

### Background for the criterion

- The kernel of type $l$ is $e_l(g) = \prod_w d(l_w)\,\overline{c_{l_w}(g_w)}$, with $d$ the formal degree. It is a cusp kernel ([typeKernel](/decl/New.typeKernel/), [isCuspKernel_typeKernel](/decl/New.isCuspKernel_typeKernel/)). A *form of type $l$* is a bounded automorphic function fixed by right convolution with $e_l$.
- Rank one formula: for a form $F$ of type $l$ and $u \in G_\infty$, $\int e_l(z) F(g(z,1)(u,1))\,dz = (\overline{e_l(u)}/e_l(1))\,F(g)$ (`New.Space.IsForm.realConv_translate`, [forms of a type](/chapter/automorphic-forms/)).
- Kernel forms: for a cusp kernel $e$ of order $B > 8n^2$, a point $x$ and a level $K$, there is a form $Q$ of type $e$ and level $K$ with $\overline{Q(g)} = \sum_{\gamma} e((x\gamma g)_\infty)\,1_K((x\gamma g)_f)$ (`New.Space.exists_kernel_form`, [the trace formula](/chapter/trace-formula/)).
- Cusp estimate: let $y$ be a form of level $K(M)$, and $\lambda(V, x) < (\delta/(M\kappa^2))^n$ with $\kappa = \kappa(E, n, N)$ the cusp constant. If $|y(x(u,1)) - y(x)| \le C$ for all $u$ with $\mathrm{dist}(u,1) \le \delta$, then $|y(x)| \le C$ ([IsForm.norm_le_of_firstMinimum_lt](/decl/New.Space.IsForm.norm_le_of_firstMinimum_lt/)).
- Halving: if $f \le B$ and every bound $S \ge c$ of $f$ gives the bound $\max(S/2, c)$, then $f \le c$ (`New.le_of_halving`, Lib/General/Analysis/MeanValueAndTaylor.lean).
- Local bounds on $U(n)$ ([first properties and decay](/chapter/discrete-series/)): $|c_l| \le 1$; $|c_l(xg) - c_l(x)| \le 100(n+L+1)^5\|g - 1\|$ if $|l_i| \le L$ (`norm_dsCoeff_sub_le`); and $\int d(l)(2/\|g\|)^c\,dg \le 8(2000(n+L+1)^6)^{2n^2}2^c$ for $c > 8n^2$ (`integral_tail_le`).

### The sizes

**Definition (Deep level sizes).** Let $A, L, N \in \mathbb{N}$ and $\beta, m \in \mathbb{R}$. Write $f$ for the number of infinite places of $E$, $M$ for the level of the data, $\kappa$ for the cusp constant of rank $n$ and $\mathfrak b$ for the generator of the deep level (`New.Data.gridLevelGen`). The sizes hold if

1. $8(n+1)^2 < A$, $N < A$ and $2f(n+1) + 2 \le A$;
2. $M\kappa^2 \le \beta$, $2000(n + L + 1)^6 \le \beta$ and $f \le \beta$;
3. $\beta^{20A(f+1)} \le m$;
4. $m^{3n+2} \le |\Phi_w(\mathfrak b)|$ for every infinite place $w$.

Lean: `New.Exchange.HasDeepLevelSizes` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

The number $m$ here is a real radius. It is not the number $m$ of lifts of the data.

**Lemma.** Under the sizes, $16 \le \beta \le m$.

Lean: `New.Exchange.HasDeepLevelSizes.sixteen_le`, `New.Exchange.HasDeepLevelSizes.beta_le_m` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* $2000(n+L+1)^6 \ge 2000 \ge 16$. As $\beta \ge 1$ and $20A(f+1) \ge 1$, $\beta \le \beta^{20A(f+1)} \le m$. $\square$

**Lemma.** Under the sizes,

$$\big(8(2000(n+L+1)^6)^{2n^2}\,2^{2A}\big)^f \le \frac{m}{16\beta}\Big/\big(\beta^N(2\beta)^{3A}\big)^f.$$

Lean: `New.Exchange.HasDeepLevelSizes.pow_places_le_div` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Each factor $8$, $2000(n+L+1)^6$, $2$ is at most $\beta$. So the left side times $16\beta(\beta^N(2\beta)^{3A})^f$ is at most $\beta^e$ with $e = 1 + 1 + f(1 + 2n^2 + 2A + N + 6A)$, using $16 \le \beta$ and $2 \le \beta$. By $8(n+1)^2 < A$ and $N < A$, $1 + 2n^2 + 2A + N + 6A \le 20A$, so $e \le 20A(f+1)$. The bound $\beta^{20A(f+1)} \le m$ finishes. $\square$

**Lemma.** Under the sizes, if $(m^{-2}/(M\kappa^2))^n \le \lambda(V)$, then $m^2 \le m^{3n+2}\lambda(V)$.

Lean: `New.Exchange.HasDeepLevelSizes.sq_le_pow_mul_firstMinimum` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* $M\kappa^2 \le \beta \le m$. So $\lambda(V) \ge (m^{-2}/m)^n = m^{-3n}$, and $m^{3n+2}\lambda(V) \ge m^2$. $\square$

### The kernel varies slowly

**Lemma (Lipschitz bound).** Let every $l_w$ have a large gap for $4A$ and entries $|l_{w,i}| \le L$. Let $2000(n+L+1)^6 \le \beta$, $f \le \beta$ and $\mathrm{dist}(u, 1) \le \delta$. Then for every $z$,

$$\Big|\prod_w \overline{c_{l_w}((u^{-1}z)_w)} - \prod_w \overline{c_{l_w}(z_w)}\Big| \le \beta(\beta\delta).$$

Lean: `New.Exchange.norm_prod_conj_dsCoeff_inv_mul_sub_le` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* As $\overline{c_l(g)} = c_l(g^{-1})$, each factor changes from $c(z_w^{-1})$ to $c(z_w^{-1}u_w)$. The Lipschitz bound gives a change of at most $100(n+L+1)^5\|u_w - 1\| \le \beta\delta$. Each factor has modulus at most $1$. A product of $f \le \beta$ factors of modulus at most $1$ changes by at most $f$ times the largest change of a factor. $\square$

**Definition (Majorant).** $\mu_A(u) = \prod_w d(l_w)\,(2/\|u_w\|)^{2A}$.

Lean: `New.Exchange.typeKernelMajorant` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

**Lemma.** Under the sizes, with large gaps for $4A$ and $|l_{w,i}| \le L$, $\mu_A$ is integrable and

$$\int \mu_A \le \frac{m}{16\beta}\Big/\big(\beta^N(2\beta)^{3A}\big)^f.$$

Lean: `New.Exchange.integral_typeKernelMajorant_le` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* The integral of a product of functions of separate places is the product of the local integrals. Each is at most $8(2000(n+L+1)^6)^{2n^2}2^{2A}$ by the tail bound with $c = 2A > 8n^2$. The lemma `pow_places_le_div` finishes. $\square$

**Lemma.** Under the same hypotheses, if $\mathrm{dist}(u,1) \le m^{-2}$, then

$$|e_l(u^{-1}z) - e_l(z)| \le (\mu_A(u^{-1}z) + \mu_A(z))\,\beta/m.$$

Lean: `New.Exchange.norm_typeKernel_inv_mul_sub_le` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Write $e_l = d\cdot\psi$ with $d = \prod_w d(l_w) > 0$, $\mu_A = d\cdot\theta$ with $\theta(g) = \prod_w (2/\|g_w\|)^{2A}$. The decay bound with exponent $4A$ gives $|\psi| \le \theta^2$. Put $a = \psi(u^{-1}z)$, $b = \psi(z)$. The Lipschitz bound gives $|a - b| \le \beta^2 m^{-2}$, and $|a - b| \le |a| + |b| \le \theta(u^{-1}z)^2 + \theta(z)^2$. Multiply the two bounds: $|a - b|^2 \le (\beta/m)^2(\theta(u^{-1}z) + \theta(z))^2$. Take square roots and multiply by $d$. $\square$

### The cusp

**Lemma (Halving in the cusp).** Assume the sizes, large gaps for $4A$ and $|l_{w,i}| \le L$. Let $y$ be a form of type $l$ on $V$ with level $K(M)$ and $|y| \le S$. If $\lambda(V, x) < (m^{-2}/(M\kappa^2))^n$, then $|y(x)| \le S/2$.

Lean: `New.Exchange.norm_le_half_of_firstMinimum_lt` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* By the cusp estimate with $\delta = m^{-2}$, it suffices to show $|y(x(u,1)) - y(x)| \le S/2$ for $\mathrm{dist}(u, 1) \le m^{-2}$. As $y = e_l \ast y$, and after the substitution $z \mapsto u^{-1}z$ in the first integral,

$$y(x(u,1)) - y(x) = \int \big(e_l(u^{-1}z) - e_l(z)\big)\,y(x(z,1))\,dz.$$

By the previous lemma the absolute value is at most $S\,(\beta/m)\int(\mu_A(u^{-1}z) + \mu_A(z))\,dz = 2S(\beta/m)\int\mu_A$. The integral is at most $m/(16\beta)$. So the difference is at most $S/8 \le S/2$. $\square$

### Away from the cusp

**Lemma (The period is zero).** Let $8(n+1)^2 < A$ and let every $l'_w$ have a large gap for $2A$. Let $K$ be a level on $Z$. Let $y$ satisfy $\langle y, \varphi((\cdot \oplus 1)\omega)\rangle = 0$ for every form $\varphi$ of type $l'$ and level $K$ on $Z$. Then for all $x$ and $\alpha$,

$$\int_{\Gamma_V\backslash G} \sum_{\gamma\in\Gamma_Z} P_{\psi_{l',\alpha,\omega},K}\big((x\oplus 1)^{-1}\gamma(h\oplus 1)\big)\,y(h)\,d\mu_V(h) = 0.$$

Lean: `New.Exchange.poincare_period_translatedCoeff_eq_zero` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Let $d' = \prod_w d(l'_w) \ne 0$ and $c = ((x \oplus 1)(\alpha, 1))^{-1}$. The cusp kernel $e_{l'}$ has order $2A > 8(n+1)^2$. The kernel form lemma gives a form $Q$ of type $l'$ and level $K$ with $\overline{Q(g)} = \sum_\gamma e_{l'}((c\gamma g)_\infty)1_K((c\gamma g)_f)$. At $g = (h \oplus 1)(\omega, 1)$ each term is $d'$ times the term of the Poincaré series. So $d'$ times the period is the Petersson product $\langle Q((\cdot\oplus 1)\omega), y\rangle$, the conjugate of $\langle y, Q((\cdot \oplus 1)\omega)\rangle = 0$. $\square$

**Lemma (The smoothing is small).** Assume the sizes and large gaps for $2A$ of $l'$. Let $y$ be automorphic on $V$ of level $J(\mathfrak b)$, $|y| \le S$, orthogonal as above to the forms of type $l'$ and level $J(\mathfrak b)$. If $m^2 \le m^{3n+2}\lambda(V, x)$, then the slice $\psi(r) = \psi_{l',\alpha,\omega}(\iota(r))$ is integrable and

$$|(\psi \ast y)(x)| \le C_A(\alpha, \omega)\,S\,(10/m).$$

Lean: `New.Exchange.norm_realConv_translatedCoeff_le` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Apply the period theorem of Section 4 with $a = \mathfrak b$, $R = m^{3n+2}$, $d = m$. Its hypotheses hold: $R \le |\Phi_w\mathfrak b|$ by size 4; $d^2 = m^2 \le R\lambda(V, x)$; $f \le \beta \le m$; $10 \le 16 \le m$; and the bounds on $A$ are sizes. The period is $0$ by the previous lemma. So $\mathrm{vol}\,J(\mathfrak b)\,|(\psi\ast y)(x)| \le \mathrm{vol}\,J(\mathfrak b)\,C_A S (10/m)$. Divide by the positive volume. $\square$

**Lemma.** Let $l$ have a large gap for $4A$, $16 \le \beta$ and $\|\omega\|^2 \le \beta$. Then for $r \in U(\mathrm{diag}\,s)$,

$$|d(l)\overline{c_l(r)}|\,\big(2(\|\iota(r)\omega\|\,\|\omega\|)^2\big)^A 16^A \le d(l)\,(2/\|r\|)^{2A}(2\beta)^{3A}.$$

Lean: `New.Exchange.norm_dsKernel_mul_pow_le` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* The decay bound gives $|c_l(r)| \le (2/\|r\|)^{4A}$. Also $\|\iota(r)\omega\| \le \|r\|\|\omega\|$. With $\|\omega\|^2 \le \beta$ and $16 \le \beta$, the left side is at most $d(l)(2/\|r\|)^{4A}(2(\|r\|\beta)^2)^A\beta^A = d(l)(2/\|r\|)^{2A}(2\beta)^{3A}$. $\square$

**Lemma.** If every $l_w$ has a large gap for $4A$, then

$$\int_{G_\infty} \psi_{l',\omega,\omega}(\iota(z))\,\frac{\overline{e_l(z)}}{e_l(1)}\,dz = \prod_w \int_{U(\mathrm{diag}\,s)} c_{l_w}(r)\,\overline{c_{l'_w}(\omega_w^{-1}\iota(r)\omega_w)}\,dr.$$

Lean: `New.Exchange.integral_translatedCoeff_mul_eq_prod` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* $e_l(1) = \prod_w d(l_w)$ as $c_l(1) = 1$. The formal degrees are positive and cancel. The integrand is a product of functions of separate places. $\square$

**Lemma.** $(\psi_{l',\alpha,\omega}\circ\iota) \ast y$ at $x(u,1)$ equals $(\psi_{l',\iota(u)\alpha,\omega}\circ\iota)\ast y$ at $x$.

Lean: `New.Exchange.realConv_translatedCoeff_mul` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Substitute $z \mapsto u^{-1}z$. Then $\alpha^{-1}\iota(u^{-1}z) = (\iota(u)\alpha)^{-1}\iota(z)$. $\square$

**Lemma (Halving away from the cusp).** Assume the sizes, large gaps for $4A$ of $l$ and for $2A$ of $l'$, $|l_{w,i}| \le L$, $\|\omega_w\|^2 \le \beta$, and the pairing bound

$$v \le \beta^N\Big|\int_{U(\mathrm{diag}\,s)} c_{l_w}(r)\,\overline{c_{l'_w}(\omega_w^{-1}\iota(r)\omega_w)}\,dr\Big| \quad \text{for every } w,$$

with $v = \mathrm{vol}\{r : \|r - 1\| \le 1\}$. Let $y$ be a form of type $l$ and level $J(\mathfrak b)$, $|y| \le S$, orthogonal to all $\varphi((\cdot\oplus 1)\omega)$ for $\varphi$ of type $l'$ and level $J(\mathfrak b)$. If $(m^{-2}/(M\kappa^2))^n \le \lambda(V,x)$, then $|y(x)| \le S/2$.

Lean: `New.Exchange.norm_le_half_of_le_firstMinimum` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Let $\psi = \psi_{l',\omega,\omega}\circ\iota$ and $\eta = \int\psi(z)\,\overline{e_l(z)}/e_l(1)\,dz$. By Fubini and the rank one formula,

$$\int e_l(u)\,(\psi\ast y)(x(u,1))\,du = \eta\, y(x).$$

By the product lemma and the pairing bound, $|\eta| \ge (v/\beta^N)^f$. By the translation lemma, $(\psi \ast y)(x(u,1))$ is the smoothing at $x$ with $\alpha = \iota(u)\omega$. The smoothing lemma bounds it by $C_A(\iota(u)\omega,\omega)\,S\,(10/m)$. With the kernel bound lemma at each place,

$$|e_l(u)|\,|(\psi\ast y)(x(u,1))| \le \mu_A(u)\,((2\beta)^{3A}v)^f\,S\cdot 10/m.$$

Integrate and use the bound for $\int\mu_A$:

$$(v/\beta^N)^f|y(x)| \le \frac{m}{16\beta}\Big/(\beta^N(2\beta)^{3A})^f\cdot((2\beta)^{3A}v)^f\cdot\frac{10S}{m}.$$

The constants cancel, and $16\beta|y(x)| \le 10S$. As $\beta \ge 16$, $|y(x)| \le 10S/256 \le S/2$. $\square$

### The criterion and its corollary

**Theorem (Vanishing criterion).** Assume the sizes, large gaps for $4A$ of $l$ and for $2A$ of $l'$, $|l_{w,i}| \le L$, $\|\omega_w\|^2 \le \beta$, and the pairing bound at every $w$. Let $y$ be a form of type $l$ on $V$ of level $J_M$, the chosen level of the data. If $\langle y, \varphi((\cdot\oplus 1)\omega)\rangle = 0$ for every form $\varphi$ of type $l'$ on $Z$ of level $J(\mathfrak b)$, then $y = 0$.

Lean: `New.Exchange.eq_zero_of_petersson_translate_eq_zero` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* The generators $M$ and $\mathfrak b = \pi_M^{b}$ are divisible by $\pi_M$, so $y$ has level $K(M)$ and $J(\mathfrak b)$. Let $S$ bound $|y|$. At each $x$, either $\lambda(V,x) < (m^{-2}/(M\kappa^2))^n$ and the cusp lemma gives $|y(x)| \le S/2$, or the other halving lemma gives it. So every bound $S$ halves. The form is bounded. The halving lemma with $c = 0$ gives $|y| \le 0$. $\square$

**Corollary.** Let the signs of $l'$ be $(s, 1)$. Assume the size conditions as separate hypotheses, the gaps and entry bounds, and that at each place $w$ some $\omega_w$ with $\|\omega_w\|^2 \le \beta$ satisfies the pairing bound. Then there is a real point $g$ such that every form $y$ of type $l$ and level $J_M$ on $V$, orthogonal to all $\varphi((\cdot\oplus 1)g)$ for $\varphi$ of type $l'$ and level $J(\mathfrak b)$, is $0$.

Lean: `New.Exchange.exists_forall_eq_zero_of_petersson_restrict_eq_zero` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* Choose $\omega_w$ at each place and put $g = (\omega_w)_w$. Apply the theorem. $\square$

**Remark (Formalization).** The point $g$ is chosen with `choose`, place by place. The corollary states the space $Z$ through a reindexing by the signs $t = (s, 1)$, which is removed by `subst`. The source names related work in its docstring: Prasad and Schulze-Pillot (2008), Harris (2014) and Muić (2015). It does not use them in the proofs.
