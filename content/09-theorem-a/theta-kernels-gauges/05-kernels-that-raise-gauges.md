---
title: Kernels that raise gauges
lean:
  - New/UpperBound/Kernels/ThetaLiftGauge.lean
decls:
  - New.weylGauge_add_le_max
  - New.Kernel.raises
  - New.Kernel.smul_mem_raises
  - New.Kernel.omega_mem_raises_iff
  - New.diagonalWeight
  - New.diagonalWeight_nonneg
  - New.diagonalWeight_one
  - New.Parameters.pairWeil_mem_standardData
  - New.Parameters.omega_mem_raises_of_schurJet_le
  - New.Parameters.omega_mem_raises_of_jet_minorProd_le
  - New.Parameters.mem_raises_of_standardData
  - New.Parameters.mem_raises_predictedDivisibility
  - New.Parameters.smul_mem_raises_of_dvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kernels that raise gauges

This section turns $p$-adic bounds for single jets into a statement about a whole kernel. The statement is: the kernel maps a vector of gauge $1$ at a point $g$ to a vector of gauge at most $c$ at a point $h$, for all $g$ and $h$ at once. The proof moves both points to the identity, where the claim is an entrywise bound for the jet matrix.

### The model case

Let $M$ be a matrix with entries in $\mathbb{C}_p$, and let $\xi$ be a vector. Put $\|\xi\| = \max_i |\xi_i|_p$. If every entry of $M$ has $|M_{ij}|_p \le c$ with $c \ge 0$, then $\|M\xi\| \le c\,\|\xi\|$. The reason is the ultrametric inequality: $|\sum_j M_{ij}\xi_j|_p \le \max_j |M_{ij}|_p |\xi_j|_p$. No factor for the number of terms appears. So a matrix of $p$-integral jets maps integral vectors to integral vectors. The rest of the section reduces the kernel to this case. This is the bound `New.norm_mulVec_le_of_nonneg`.

### The gauge

Fix a prime $p$ and a ring map $\iota_p : \mathbb{C} \to \mathbb{C}_p$. For an infinite place $\tau$ of $E$, $\iota_\tau$ is the embedding $z \mapsto \iota_p(\tau(\bar z))$ of $E$ into $\mathbb{C}_p$, extended to the finite adeles; this is `New.weightEmbedding` with `New.adeleExtension`. Let $G_f^{(n)}$ be the finite adelic unitary group of rank $n$. The gauge of a vector $\xi$ of weight $(\kappa, e)$ at a point $g \in G_f^{(n)}$ is
$$\|\xi\|_{g} = \big\|\rho_{\kappa,e}\big((\iota_\tau(g^{-1}))_\tau\big)\,\iota_p(\xi)\big\|,$$
where $\rho_{\kappa,e}$ is the action on the Weyl module of weight $(\kappa, e)$ and the norm is the maximum norm. This is [`New.weylGauge`](/decl/New.weylGauge/) of [automorphic forms](/chapter/automorphic-forms/). Three facts from that chapter are used. For a rational point $\gamma$, $\|\gamma\xi\|_{\gamma g} = \|\xi\|_g$. For $k$ integral above $p$, $\|\xi\|_{gk} = \|\xi\|_g$. For $z \in \mathbb{C}$, $\|z\xi\|_g = |\iota_p z|_p\,\|\xi\|_g$. The fourth fact is weak approximation: for $g$ and $d$ there is a rational $\gamma$ with $\gamma g$ and $d\gamma g d^{-1}$ integral above $p$.

**Lemma (The gauge is ultrametric).** For all $g$, $\xi$ and $\eta$, $\|\xi + \eta\|_g \le \max(\|\xi\|_g, \|\eta\|_g)$.

Lean: `New.weylGauge_add_le_max` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The map $\iota_p$ is additive and the matrix acts linearly, so the vector inside the norm is a sum. The maximum norm on $\mathbb{C}_p^m$ is ultrametric. $\square$

### Raising gauges

Let $k$ be an abstract kernel, as in [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/): data $S$ with an action $\omega$ of $G_f^{(n)} \times G_f^{(n')}$, and a jet map $\Phi \mapsto k(\Phi)$ from $S$ to linear maps from vectors of weight $(\kappa, e)$ in rank $n$ to vectors of weight $(\kappa, e_a)$ in rank $n'$.

**Definition (Raising gauges).** For base points $d \in G_f^{(n)}$, $d' \in G_f^{(n')}$ and a real number $c$, the set $\mathrm{raises}(d, d', c)$ is the set of data $\Phi \in S$ such that
$$\|k(\omega(g, h)\Phi)\,\xi\|_{h d'} \le \max(c, 0)\,\|\xi\|_{g d}$$
for all $g \in G_f^{(n)}$, $h \in G_f^{(n')}$ and all vectors $\xi$. It is an additive submonoid of $S$.

Lean: `New.Kernel.raises` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof that it is a submonoid.* For $\Phi = 0$ the left side is $\|0\| = 0$, and the right side is at least $0$. If $\Phi$ and $\Psi$ are members, then $k(\omega(g,h)(\Phi + \Psi))\xi$ is the sum of the two images. By the lemma its gauge is at most the larger of the two gauges, so at most $\max(c, 0)\|\xi\|_{gd}$. $\square$

**Remark (Formalization).** The factor is $\max(c, 0)$, not $c$. With $c$ the set would be empty for $c < 0$, since a gauge is at least $0$, and $0$ would not be a member. With $\max(c, 0)$ the set is a submonoid for every real $c$. A statement "$\Phi \in \mathrm{raises}(1, 1, c)$" with $c < 0$ says the same as with $c = 0$: the kernel of every translate is $0$ in gauge, so it is $0$ after $\iota_p$. The map $\iota_p$ comes from the instance `New.PadicPlace`. It is a ring map and need not be continuous; only its values on finitely many numbers enter each statement.

**Lemma (Scalars).** If $\Phi \in \mathrm{raises}(d, d', B)$ and $z \in \mathbb{C}$ has $|\iota_p z|_p\,B \le B'$, then $z\Phi \in \mathrm{raises}(d, d', B')$.

Lean: `New.Kernel.smul_mem_raises` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The jet map and $\omega(g,h)$ are linear, and the gauge scales by $|\iota_p z|_p$. So the left side for $z\Phi$ is $|\iota_p z|_p$ times the left side for $\Phi$, which is at most $|\iota_p z|_p \max(B, 0)\|\xi\|_{gd}$. This equals $\max(|\iota_p z|_p B, 0)\|\xi\|_{gd}$, and $\max(|\iota_p z|_p B, 0) \le \max(B', 0)$. $\square$

**Lemma (Translates).** $\omega(g_0, h_0)\Phi \in \mathrm{raises}(g_0 d, h_0 d', B)$ if and only if $\Phi \in \mathrm{raises}(d, d', B)$.

Lean: `New.Kernel.omega_mem_raises_iff` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* $\omega$ is a representation, so $\omega(g,h)\omega(g_0,h_0) = \omega(g g_0, h h_0)$. If $\Phi$ is a member, apply its condition at $(g g_0, h h_0)$: the gauges are at $h h_0 d'$ and $g g_0 d$, as needed. Conversely, apply the condition for $\omega(g_0,h_0)\Phi$ at $(g g_0^{-1}, h h_0^{-1})$. $\square$

### The diagonal weight

At a diagonal point the action on the Weyl module is diagonal. The weight of a row records its entries.

**Definition (Diagonal weight).** Let $u_\tau \in \mathbb{C}_p^{n}$ for each place $\tau$, let $e$ be integer exponents and let $i$ be a filling of the diagrams $\kappa$ by elements of $n$. Then
$$\mathrm{dw}_e(u, i) = \prod_{\tau \in \Phi}\Big(\prod_{b \in n}|u_{\tau,b}|_p\Big)^{e_\tau}\prod_{h < |n|}\prod_{j < \kappa(\tau,h)}\prod_{t < h}|u_{\tau, i_\tau(h,j,t)}|_p.$$
It is at least $0$, and for $u = 1$ it is $1$.

Lean: `New.diagonalWeight`, `New.diagonalWeight_nonneg`, `New.diagonalWeight_one` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Each factor is a power of a real number at least $0$, or a product of such. For $u = 1$ every factor is $1$. $\square$

The first factor is $|\det u_\tau|_p^{e_\tau}$. The second runs over the boxes of the filling $i_\tau$ and takes the entry of $u_\tau$ at the index in the box. The Schur matrix of $\mathrm{diag}(u_\tau)_\tau$ is the diagonal matrix with these products of entries, by the lemma `schur_diagonal_eq_prod` of [Weyl modules](/chapter/weyl-modules/). So $\mathrm{dw}_e(u, i)$ is the absolute value of the diagonal entry of $\rho_{\kappa,e}(\mathrm{diag}\,u)$ at the row $i$.

### Standard data are stable

Standard data are those of [the integral vacuum and tight frames](/chapter/integral-vacuum/): the combinations, with coefficients $z$ with $|\iota_p z|_p \le 1$, of translates of the integral vacuum by the vectors that $\delta$ makes integral above $p$. Their stability under $\omega(g)$ for $g$ integral above $p$ is in [the count and the divisibility of standard data](/chapter/normal-forms/). The kernel uses the action $\omega_{a,b}$ of pairs, [`New.pairWeil`](/decl/New.pairWeil/), which is $\omega$ of a point times a value of the pair character.

**Lemma (Stability under integral pairs).** Let $a$ and $b$ be automorphic characters of $E$ with weights. Let $F$ be standard for $\delta$ on $H = \mathrm{Hom}(V_n, V_{n'})$. If $g \in G_f^{(n)}$ and $h \in G_f^{(n')}$ are integral above $p$, then $\omega_{a,b}((1, g), (1, h))F$ is standard for $\delta$.

Lean: `New.Parameters.pairWeil_mem_standardData` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The datum is $\chi_{a,b}((1,g),(1,h))\,\omega(x)F$, where $x$ is the point of the unitary group of $H$ given by the pair; its infinite part is trivial. The character value is a product of values of $a$ and $b$ at determinants of $g$ and $h$. A character with a weight has $|\iota_p|_p = 1$ at the determinant of a point integral above $p$, by [class field theory](/chapter/class-field-theory/). So the scalar has $|\iota_p|_p \le 1$. The point $x$ is integral above $p$, since its components above $p$ are built from those of $g$ and $h$. Standard data are stable under $\omega(x)$, and under scalars of norm at most $1$, since they form a module over $\{z : |\iota_p z|_p \le 1\}$. $\square$

### The reduction to the identity

The theta kernel `New.thetaKernel` of scale $c$ has the jet map $\Psi \mapsto \mathrm{schurJet}_\kappa(J_c\Psi)$, the matrix of jets of $J_c\Psi$ along the entries of the Schur matrix of the variables. Its action is $\omega_{a,b}$ at finite points. It is equivariant for rational points: $\rho(\varepsilon)\,k(\Psi)\xi = k(\omega(\gamma,\varepsilon)\Psi)(\rho(\gamma)\xi)$.

**Theorem (Gauges from an entrywise bound).** Let $k$ be the theta kernel of scale $c \in \mathbb{C}$ and weight $(\kappa, e)$ lifting from rank $n$ to rank $n'$, with characters $a$, $b$ of exponents $e_a$, $e_b$, at any level. Let $\Psi \in V^{\mathrm{fin}}$ be standard for $\delta$. Let $x, y \in G_f^{(n')}$ be integral above $p$, and let $d \in G_f^{(n')}$ with $\iota_\tau(d) = \mathrm{diag}(u_\tau)$ for each place $\tau$. Assume that
$$\mathrm{dw}_{e_a}(u, i')\,\big|\iota_p\big(\mathrm{schurJet}_\kappa(J_c f)_{i', i}\big)\big|_p \le B$$
for every standard datum $f$ for $\delta$ and all fillings $i'$, $i$. Then $\omega(1, x d y)\Psi \in \mathrm{raises}(1, 1, B)$.

Lean: `New.Parameters.omega_mem_raises_of_schurJet_le` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Fix $g$, $g'$ and $\xi$. We must bound the gauge at $g'$ of $v = k(\omega(g, g' x d y)\Psi)\xi$.

*Step 1: weak approximation.* Choose a rational $\gamma$ with $g_0 = \gamma g$ integral above $p$. Choose a rational $\varepsilon$ such that $g_1 = \varepsilon g' x d$ and $d g_1 d^{-1}$ are integral above $p$.

*Step 2: a new datum.* Put $\Psi' = \omega(g_0, g_1 y)\Psi$ and $\eta = \rho(\gamma)\xi$. The points $g_0$ and $g_1 y$ are integral above $p$, so $\Psi'$ is standard for $\delta$ by the stability lemma.

*Step 3: the left side.* By invariance under rational points, $\|v\|_{g'} = \|\rho(\varepsilon)v\|_{\varepsilon g'}$. By equivariance, $\rho(\varepsilon)v = k(\omega(\gamma, \varepsilon)\omega(g, g' x d y)\Psi)\,\eta = k(\Psi')\eta$. Now $\varepsilon g' = g_1 d^{-1} x^{-1} = d^{-1}\cdot (d g_1 d^{-1}) x^{-1}$, and $(d g_1 d^{-1})x^{-1}$ is integral above $p$. So $\|v\|_{g'} = \|k(\Psi')\eta\|_{d^{-1}}$.

*Step 4: the matrix at $d^{-1}$.* The gauge at $d^{-1}$ uses $\rho_{\kappa,e_a}(\iota_\tau(d))_\tau = \rho_{\kappa,e_a}(\mathrm{diag}\,u)$. This is the scalar $\prod_\tau (\prod_b u_{\tau,b})^{e_{a,\tau}}$ times the diagonal matrix with the products of $u$ over the boxes. So $\|k(\Psi')\eta\|_{d^{-1}} = \|A\,\iota_p(\eta)\|$, where $A$ is $\iota_p(\mathrm{schurJet}_\kappa(J_c\Psi'))$ with the row $i'$ multiplied by these factors. The entry $A_{i',i}$ has absolute value $\mathrm{dw}_{e_a}(u, i')\,|\iota_p(\mathrm{schurJet}_\kappa(J_c\Psi')_{i',i})|_p$, which is at most $B \le \max(B, 0)$ by the hypothesis for $f = \Psi'$.

*Step 5: the model case.* By the ultrametric matrix bound, $\|A\,\iota_p(\eta)\| \le \max(B, 0)\|\iota_p(\eta)\| = \max(B, 0)\|\eta\|_1$.

*Step 6: back to $g$.* Since $g_0$ is integral above $p$, $\|\eta\|_1 = \|\eta\|_{g_0} = \|\rho(\gamma)\xi\|_{\gamma g} = \|\xi\|_g$. $\square$

**Remark (Formalization).** The hypothesis is for every standard datum $f$, not for $\Psi$ only. The proof applies it to $\Psi'$, which depends on $g$, $g'$ and on the choices of $\gamma$ and $\varepsilon$. The hypothesis on $d$ fixes $u$ from $d$: $\iota_\tau(d)$ must be exactly diagonal at every place.

The next form of the theorem replaces a Schur entry by a product of minors. A Schur entry is a polynomial in the minors of the variable matrix. By [the count and the divisibility of standard data](/chapter/normal-forms/), there are $p$-integral matrices $w_\tau$ such that $|\mathrm{schurJet}_\kappa(G)_{i',i}|_p \le |\partial_{\mathrm{minorProd}(i', w)}G|_p$ for every power series $G$ over $\mathbb{C}_p$. Here $\mathrm{minorProd}(i', w)$ is the product, over the places $\tau$ and the columns of height $h < |n'|$, of the minors of $Z_\tau w_\tau$ on the rows that $i'$ puts in the column and the first $h$ columns.

**Corollary (Gauges from minors).** Keep the setting of the theorem, and assume instead that
$$\mathrm{dw}_{e_a}(u, i')\,\big|\partial_{\mathrm{minorProd}(i', w)}\,\iota_p(J_c f)\big|_p \le B$$
for every standard datum $f$ for $\delta$, every filling $i'$ and all $p$-integral $w_\tau$. Then $\omega(1, x d y)\Psi \in \mathrm{raises}(1, 1, B)$.

Lean: `New.Parameters.omega_mem_raises_of_jet_minorProd_le` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* We check the hypothesis of the theorem. Let $f$ be standard and $G = \iota_p(J_c f)$. Applying the ring map $\iota_p$ to a Schur jet gives the Schur jet of $G$, because the Schur entries have integer coefficients. Choose $w$ for $G$, $i'$ and $i$ as above. Then $\mathrm{dw}_{e_a}(u, i')\,|\iota_p(\mathrm{schurJet}_\kappa(J_c f)_{i',i})|_p \le \mathrm{dw}_{e_a}(u, i')\,|\partial_{\mathrm{minorProd}(i',w)}G|_p \le B$, since the diagonal weight is at least $0$. $\square$

### Explicit factors

At $x = d = y = 1$ and $u = 1$ the diagonal weight is $1$, and the two results give bounds from the $p$-adic bounds for single jets.

**Theorem (Standard data raise gauges by a power).** Let $\delta \ne 0$ in $\mathcal{O}_K$, $c \in \mathbb{C}$, and let $\Phi \in V^{\mathrm{fin}}$ be standard for $\delta$. For the theta kernel of scale $c\,t_0$,
$$\Phi \in \mathrm{raises}\Big(1, 1, \Big(\frac{|\iota_p c|_p}{|\iota_p(\bar\delta\, d)|_p}\Big)^{\mathrm{boxes}(\kappa, |n'|)}\Big).$$

Lean: `New.Parameters.mem_raises_of_standardData` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Write $\Phi = \omega(1, 1\cdot 1\cdot 1)\Phi$ and apply the theorem with $x = d = y = 1$ and $u = 1$. Let $f$ be standard for $\delta$. The entry $(i', i)$ of the Schur matrix of the variables is a polynomial $Q$ with integer coefficients, so with coefficients in $\{z : |\iota_p z|_p \le 1\}$. It is homogeneous of degree $\mathrm{boxes}(\kappa, |n'|)$, by the homogeneity of Schur entries in [Weyl modules](/chapter/weyl-modules/). The Schur jet entry is $\partial_Q J_{c t_0} f$. By [the count and the divisibility of standard data](/chapter/normal-forms/), $|\iota_p(\partial_Q J_{c t_0} f)|_p \le |\iota_p(c/(\bar\delta d))|_p^{l}$ for $Q$ integral and homogeneous of degree $l$. This is the bound, and $|\iota_p(c/(\bar\delta d))|_p = |\iota_p c|_p/|\iota_p(\bar\delta d)|_p$. $\square$

**Theorem (One lift at a non-split prime).** Let $p$ be a prime that does not split in $K$, that is $\chi_K(p) \ne 1$. Let $|\iota_p c|_p \le 1$ and let $\Phi \in V^{\mathrm{fin}}$ be standard for $\delta = 1$. Put $N = |n'|$, and let $D$ be the predicted divisibility of [the count and the divisibility of standard data](/chapter/normal-forms/) for $d$, $p$, the partner place, $\kappa$ and $N$. For the theta kernel of scale $c\,t_0$,
$$\Phi \in \mathrm{raises}\Big(1, 1, p^{-(D - f N^3(1 + \log_p \max(\mathrm{boxes}(\kappa, N), 1)))}\Big).$$

Lean: `New.Parameters.mem_raises_predictedDivisibility` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Apply the corollary with $x = d = y = 1$ and $u = 1$. The diagonal weight is $1$. By [the count and the divisibility of standard data](/chapter/normal-forms/), for $f$ standard for $1$ and $p$-integral $w$, the jet of $\iota_p(J_{c t_0} f)$ along $\mathrm{minorProd}(i', w)$ has absolute value at most the stated power of $p$. $\square$

**Remark (Formalization).** The exponent is a real number. If $D$ is small, the exponent is positive and the factor is more than $1$; the statement is still true. The logarithm is $\log_p$ of the natural number $\max(\mathrm{boxes}(\kappa, N), 1)$, so it is at least $0$ and it is not the junk value $\log 0$.

**Corollary (Integer multiples).** Let $N \ne 0$ and $d_0$ be natural numbers, let $|\iota_p c|_p \le 1$, and let $F \in V^{\mathrm{fin}}$ with $d_0 F$ standard for $N$. If $d_0 (N d)^{\mathrm{boxes}(\kappa, |n'|)}$ divides $M$, then $M F \in \mathrm{raises}(1, 1, 1)$ for the theta kernel of scale $c\,t_0$.

Lean: `New.Parameters.smul_mem_raises_of_dvd` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Write $M = d_0 (N d)^{L} q$ with $L = \mathrm{boxes}(\kappa, |n'|)$. Then $MF = ((Nd)^L q)(d_0F)$. By the theorem with $\delta = N$, $d_0F \in \mathrm{raises}(1, 1, (|\iota_p c|_p/|\iota_p(Nd)|_p)^L)$, since $\bar N = N$. By the lemma on scalars it is enough that $|\iota_p((Nd)^L q)|_p\,(|\iota_p c|_p/|\iota_p(Nd)|_p)^L \le 1$. The left side is $|\iota_p q|_p\,|\iota_p c|_p^L \le 1$, because $|\iota_p c|_p \le 1$ and $q$ is an integer. $\square$

**Remark (Formalization).** In the source $d$ in the statement is the natural number $d_0$; it is not the prime $d$ of $K$, which appears as `P.d`. If $d_0 = 0$, the divisibility forces $M = 0$, and the claim is that $0 \in \mathrm{raises}(1, 1, 1)$. So the case is trivially true and the hypothesis on $d_0F$ is not used.
