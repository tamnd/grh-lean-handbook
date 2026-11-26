---
title: Periods of false lifts
lean:
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
  - New/OneLift/ComparisonOperator/GluedLattices.lean
decls:
  - New.Rows.lift_polyVector_blockDatum_eq_zero
  - New.Rows.descentsVanish_hyperbolicSum
  - New.Rows.exists_projOn_eq_pairTheta_ne_zero
  - New.Rows.integral_conj_pairTheta_mul_algFormCoeff_eq_zero
  - New.Rows.stdClassSum_gramForm_eq_zero
  - New.Rows.kernelVector
  - New.Rows.stdClassSum_gramForm_kernelVector_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Periods of false lifts

This section assembles the tower. We start from the three conditions of [Section 1](/chapter/false-lifts/#what-the-chapter-proves). The bottom of the tower (Sections 2 to 4) and the plane step (Section 6) give the vanishing of all descents to $W \oplus \mathbb{H}^N$. A theta kernel of $W$ then absorbs the summand $W$, and the theorem of [descents and block periods](/chapter/bessel-periods/#descents-and-block-periods) turns the result into vanishing periods. The last step replaces the integral over $[U(I_l)]$ by a class sum.

### Notation

All results of this section are in the namespace `New.Rows` of the file `New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean`. Fix a descent pair $O$ with $W$ of rank $r \geq 1$, and a form $\Xi$ in `O.FormV`. For a vector $\zeta$ of the Weyl module of $\Xi$ we write

$$c_\zeta(h) = \langle \zeta, \Xi\rangle(h) = \text{`algFormCoeff 1 (gramForm ζ) Ξ'}(h), \qquad y_\zeta = \overline{c_\zeta},$$

for the matrix coefficient of $\Xi$ at $\zeta$, a function on $U(I_n)(\mathbb{A})$, and its conjugate. Both are automorphic (`isAutomorphic_star_algFormCoeff`). If $g = (g_\infty, g_f)$, then $c_\zeta(g) = \langle \rho(g_\infty)^{-1}\zeta, \Xi(g_f)\rangle$ up to the conventions of [algebraic forms](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups), so right translation by a real point $x$ replaces $\zeta$ by its image under the Weyl representation. Let $\zeta_0 = $ `highestVector O.columnCount O.paramV` be the highest weight vector. We write $T = \Sigma^c$ for the set of finite places off $O.\mathrm{places}$ and their conjugates, so "vacuum above $T$" means "the vacuum off $\Sigma$".

We use four facts from earlier volumes.

- Descents and block periods ([Bessel periods](/chapter/bessel-periods/#descents-and-block-periods)): if $Y$ on $U(I_n)$ is continuous, left invariant under the rational points, of level $K_0 \cap (\text{supported on } \Sigma)$, and its descents to $\mathbb{H}^{N}$ twisted by $\upsilon_1^{\#N}$ vanish above $T$, then $\int_{[U(I_l)]} Y(\mathrm{diag}(h_1, h_2))\,dh_2 = 0$ for all $h_1$ (`New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish`).
- Right translation ([the same section](/chapter/bessel-periods/#descents-and-block-periods)): vanishing descents are preserved by right translation by an element that is $1$ at the places of $T$ (`New.SiegelWeil.DescentsVanish.comp_mul_right`).
- Edges and real convolution ([edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows)): at an edge, the lift by the datum $v_P \otimes f$ is a real convolution $\alpha * F$ of the lift $F$ by the harmonic datum $\otimes f$ (`lift_isForm_and_eq_realConv`).
- Class sums ([finite volume and classes](/chapter/reduction-theory/#finite-volume-and-the-finiteness-of-classes)): for $F$ continuous and left invariant on a definite group, with average $f(g_f)$ over the real points and $f$ fixed by a level $K$, $\int_{[U]} F = [K_0 : K]^{-1}\,\mathrm{classSum}_K f$ (`New.Space.integral_quotMeasure_eq_classSum`).

### The block datum

**Lemma (The block datum is killed).** Let $O$ fit $l_0$ and let $\theta^*\Xi = 0$. Then for every polynomial $P$ the descent of $y_{\zeta_0}$ to $U(W)$ by the datum $v_P \otimes \Psi_{\mathrm{bl}}$, with the kernel twisted by $\nu_W = $ `O.charW` and the trivial character, is zero.

Lean: `New.Rows.lift_polyVector_blockDatum_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* The normalized descent $\theta^*\Xi$ is a nonzero scalar times the conjugate of the descent $F$ of $y = \overline{\Xi^\flat}$ by the harmonic datum $\zeta_0 \otimes \Psi_{\mathrm{bl}}$ (`normalizedDescent_eq_smul_star_lift_swap`). So $F = 0$. The pair fits $l_0$, so it is an edge in the sense of Volume 6. By the edge lemma there is a test function $\alpha$ on the real points of $U(W)$ with descent by $v_P \otimes \Psi_{\mathrm{bl}}$ equal to $\alpha * F = 0$. This is for the kernel twisted by the pair $(\nu_W, \nu_V)$, with $\nu_V = $ `O.charV`. The twist $\nu_V(\det h)$ on $I_n$ and the twist $1$ differ by a character of $\det g$ on the side of $W$, which comes out of the integral as a factor. So the descent with the trivial character on $I_n$ is also $0$. Finally $y$ is the conjugate matrix coefficient $y_{\zeta_0}$. $\square$

This lemma is the hypothesis of the theorem of the bottom of the tower in [Section 4](/chapter/false-lifts/#the-bottom-of-the-tower).

### All descents to the hyperbolic sum

**Theorem (Descents to $W \oplus \mathbb{H}^N$).** Let $O$ fit $l_0$, let $\psi_w \neq 1$ for $w \in Q$, and let $\Xi$ satisfy the three conditions at a split place $w$ off $\Sigma$. If $2r + 2\#N + 3 < n$, then for every $\zeta$ the descents of $y_\zeta$ to $W \oplus \mathbb{H}^N$, twisted by $\nu_W\,\upsilon_1^{\#N}$, vanish above $T$.

Lean: `New.Rows.descentsVanish_hyperbolicSum` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* *Step 1: the bottom.* By the lemma on the block datum and the theorem of the bottom of the tower (Section 4), the descents of $y_{\zeta_0}$ to $W$, twisted by $\nu_W$, vanish above $T$. The places of $O$ are split and distinct from their conjugates, so $O.\mathrm{places}$ is disjoint from its conjugate.

*Step 2: sphericity.* Let $k$ be in the maximal level and supported at $w$. Since $w \notin \Sigma$, $k$ lies in the level of $O$, so it fixes $\Xi$. Hence $y_{\zeta_0}$ is spherical at $w$.

*Step 3: the Hecke root.* By the definition of $x_w$ and $|\alpha_w| = \sqrt q^{\,r}$,

$$|\overline{x_w}| = \big(\sqrt q^{\,r}\, q^{\,n - r - 1}\big)^{-1}.$$

*Step 4: the Hecke equation.* The map $\Xi' \mapsto \overline{c_{\zeta_0}(\Xi')}$ is conjugate linear and commutes with right translation by $U(I_n)(\mathbb{A}_f)$ (`algFormCoeff_algFormRep`). So it carries the Hecke operator on forms to the Hecke operator on functions, with the root replaced by its conjugate (`map_heckePolyOp`). By condition 3, $H_w(\overline{x_w})\,y_{\zeta_0} = 0$.

*Step 5: the tower.* The space $W \oplus \mathbb{H}^N$ has the adapted splitting `removePlanes N O.W` into $W$ and $\#N$ planes. The character $\nu_W$ has a weight, so its base change is unramified at $\bar w$ (`HasWeight.charUnramifiedAt`). Steps 1 to 4 and the rank condition are the hypotheses of the theorem of the tower of [Section 6](/chapter/false-lifts/#the-hyperbolic-plane-step). So the descents of $y_{\zeta_0}$ to $W \oplus \mathbb{H}^N$, twisted by $\nu_W\upsilon_1^{\#N}$, vanish above $T$.

*Step 6: all $\zeta$.* Fix a datum $\phi$ that is the vacuum above $T$ and a point $g$. The map $\zeta \mapsto (\text{descent of } y_\zeta \text{ by } \phi)(g)$ is linear, since $\zeta \mapsto y_\zeta$ is linear into the rapid functions and the lift is linear. For a real point $x$ of $U(I_n)$, the invariance of the inner product gives $y_{x\zeta_0}(h) = y_{\zeta_0}(h\,(x, 1))$. Right translation by $(x, 1)$ is $1$ at every finite place, so by Step 5 and the right translation fact, the functional vanishes at $x\zeta_0$. The highest weight vector generates the Weyl module, since its weight is regular for the parameter (`eq_zero_of_forall_map_translate_highestVector_eq_zero`, with `O.isHCParam_paramV.injective`). So the functional is $0$. $\square$

### A nonzero theta kernel

**Lemma (A datum with a nonzero kernel).** Let $W$ and $V$ be hermitian spaces, $a$ and $b$ characters of $U(1)$, $T$ a set of finite places and $p = (g, h)$ a point of $U(W)(\mathbb{A}) \times U(V)(\mathbb{A})$. There is a datum $\phi$ on $\mathrm{Hom}(W, V)$ with $\mathrm{projOn}\ T\ \phi = \phi$ and $\theta_\phi(p) \neq 0$, for the kernel twisted by $a$ and $b$.

Lean: `New.Rows.exists_projOn_eq_pairTheta_ne_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* In the model of [the Weil representation](/chapter/weil-representation/), a datum $\phi$ has "values" $\phi(z) = \theta(\rho(z)\phi)$ at adelic vectors $z$, and $\theta(\rho(z)\phi) = \phi(z)$ (`theta_rho`).

Let $\phi_0 = \omega(p)\,\mathrm{vac}$. The Weil operator is unitary and the vacuum has norm $1$, so $\phi_0 \neq 0$. A datum that vanishes at all vectors with finite part $0$ is zero (`eq_zero_of_apply_realVec_eq_zero`). So there is a vector $z_\infty$ with finite part $0$ and $\phi_0(z_\infty) \neq 0$.

Put $z' = h^{-1} z_\infty\, g$, as a matrix in $\mathrm{Hom}(W, V)$. Its finite part is also $0$. Let $\phi = \rho(z')\,\mathrm{vac}$. The mean $\mathrm{projOn}\ T$ commutes with Heisenberg operators of vectors that are $0$ at the places of $T$, and it fixes the vacuum. So $\mathrm{projOn}\ T\ \phi = \phi$. The Weil operator moves the Heisenberg operator: $\omega(p)\rho(z') = \rho(z_\infty)\omega(p)$. Hence

$$\theta_\phi(p) = \theta(\omega(p)\rho(z')\mathrm{vac}) = \theta(\rho(z_\infty)\phi_0) = \phi_0(z_\infty) \neq 0. \qquad \square$$

### The period integral

**Theorem (Theta periods of false lifts).** Let $O$ fit $l_0$, let $\psi_w \neq 1$ for $w \in Q$, let $\Xi$ satisfy the three conditions at $w$, and let $2r + 2\#N + 3 < n$. Let $\varepsilon : N \sqcup l \simeq n$, $\zeta$ a vector, $b$ a character of $U(1)$, $g \in U(W)(\mathbb{A})$, $h_1 \in U(I_N)(\mathbb{A})$ and $\gamma \in U(I_n)(\mathbb{A}_f)$ supported on $O.\mathrm{places}$. Let $\phi$ be a datum on $\mathrm{Hom}(W, I_l)$ that is the vacuum above $T$. Then

$$\int_{[U(I_l)]} \overline{\theta_\phi(g, h_2)}\; c_\zeta\big(\mathrm{diag}(h_1, h_2)\,(1, \gamma)\big)\, dh_2 = 0,$$

with the kernel of $(W, I_l)$ twisted by $\nu_W$ and $b$.

Lean: `New.Rows.integral_conj_pairTheta_mul_algFormCoeff_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* We show that the conjugate of the integral is $0$. Write $\mathrm{diag}$ for the block embedding of $\varepsilon$.

*Step 1.* Let $y_1(h) = y_\zeta(h(1, \gamma))$. It is automorphic. The element $(1, \gamma)$ is $1$ at the places of $T$, since $\gamma$ is supported on $O.\mathrm{places}$. By the theorem on descents to $W \oplus \mathbb{H}^N$ and right translation, the descents of $y_1$ to $W \oplus \mathbb{H}^N$ vanish above $T$.

*Step 2.* By the lemma on a nonzero kernel, there is a datum $\phi''$ on $\mathrm{Hom}(W, I_N)$, the vacuum above $T$, with $\theta_{\phi''}(g, h_1) \neq 0$ for the twist $(\nu_W, b^{-1})$.

*Step 3.* Let $\Phi = \phi'' \boxtimes \phi$ be the box product, a datum on $\mathrm{Hom}(W, I_n) = \mathrm{Hom}(W, I_N) \oplus \mathrm{Hom}(W, I_l)$. It is the vacuum above $T$ (`boxProd_projOn`). Let $\vartheta(h) = \theta_\Phi(g, h)$ for the pair $(W, I_n)$ with twist $(\nu_W, 1)$, and $y_2 = \vartheta\, y_1$.

*Step 4.* The function $y_2$ is continuous and left invariant under the rational points of $U(I_n)$, as both factors are. It has the level $K_0 \cap (\text{supported on } T)$: such a $k$ is trivial on $O.\mathrm{places}$, so it lies in the level of $\Xi$, it commutes with $(1, \gamma)$, and the Weil operator of $k$ fixes $\Phi$.

*Step 5.* Let $\phi'$ be a datum on $\mathrm{Hom}(\mathbb{H}^N, I_n)$, the vacuum above $T$, and $g'$ a point of $U(\mathbb{H}^N)$. The box product $\Phi' = \phi' \boxtimes \Phi$ is a datum on $\mathrm{Hom}(\mathbb{H}^N \oplus W, I_n)$, the vacuum above $T$. Theta kernels multiply in an orthogonal sum of the source:

$$\theta^{\mathbb{H}^N \oplus W}_{\Phi'}\big((g', g), h\big) = \theta^{\mathbb{H}^N}_{\phi'}(g', h)\;\vartheta(h),$$

with the twists $\upsilon_1^{\#N}\nu_W$, $\upsilon_1^{\#N}$ and $\nu_W$. Integrate against $y_1$. The left side gives the descent of $y_1$ to $W \oplus \mathbb{H}^N$ at $(g', g)$, which is $0$ by Step 1. The right side gives the descent of $y_2$ to $\mathbb{H}^N$ at $g'$. So the descents of $y_2$ to $\mathbb{H}^N$, twisted by $\upsilon_1^{\#N}$, vanish above $T$.

*Step 6.* By Steps 4 and 5 and the theorem on descents and block periods,

$$\int_{[U(I_l)]} y_2(\mathrm{diag}(h_1, h_2))\, dh_2 = 0.$$

*Step 7.* The matrix of $\mathrm{diag}(h_1, h_2)$ is block diagonal. The kernel of a box product at a block diagonal point is the product of the kernels:

$$\vartheta(\mathrm{diag}(h_1, h_2)) = \theta_{\phi''}(g, h_1)\;\theta_\phi(g, h_2),$$

with the twist $b^{-1}$ on $I_N$ and $b$ on $I_l$ (the identity `h_factor` in the proof: the matrix of $\mathrm{diag}(h_1,h_2)$ is `fromBlocks h₁ 0 0 h₂`, and the Weil operators of the two blocks act on the two factors of $\Phi$). So Step 6 says $\theta_{\phi''}(g, h_1)\int \theta_\phi(g, h_2)\, y_1(\mathrm{diag}(h_1, h_2))\, dh_2 = 0$. Divide by the nonzero constant of Step 2, and conjugate. $\square$

### The class sum

**Theorem (Periods of false lifts vanish).** This is the main theorem of [Section 1](/chapter/false-lifts/#what-the-chapter-proves). Let $\vartheta$, $C$, $h_1 \in U(I_N)(\mathbb{A}_f)$, $x$ and $f$ be as there.

Lean: `New.Rows.stdClassSum_gramForm_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* For each basis index $j$ of the Weyl module of weight $\kappa$, the hypothesis gives $c_j \in \mathbb{C}$, $g_j \in U(W)(\mathbb{A})$, a character $b_j$ and a datum $\phi_j$, the vacuum above $T$, with

$$\big(\rho(u)^{-1}\vartheta(h)\big)_j = c_j\,\overline{\theta_{\phi_j}(g_j, (u, h))}$$

for all real points $u$ and finite points $h$ of $U(I_l)$. Let $e_j$ be the basis vectors. Put $y_j = c_{C(e_j)}$ and, for $h_2 \in U(I_l)(\mathbb{A})$,

$$F_j(h_2) = \overline{\theta_{\phi_j}(g_j, h_2)}\; y_j\big(\mathrm{diag}((1, h_1), h_2)\,(1, x)\big).$$

*Step 1: properties of $F_j$.* It is continuous. It is left invariant under the rational points $\delta$ of $U(I_l)$: the kernel is invariant, and $\mathrm{diag}((1,h_1), \delta h_2) = \mathrm{diag}(1, \delta)\,\mathrm{diag}((1, h_1), h_2)$ with $\mathrm{diag}(1, \delta)$ rational. The group $U(I_l)$ is definite, so the quotient is compact, $F_j$ is rapid and integrable.

*Step 2: the sum is $f$.* Let $u$ be real and $h$ finite. Let $k$ be the real part of $\mathrm{diag}((1, h_1), (u, h))^{-1}$. The form $\Xi$ is an algebraic form, so moving the real point $k$ into the value multiplies the value by the Weyl representation. The map $C$ is equivariant for the real points of the block $I_l$, and the inner product is invariant. So

$$f(h) = \big\langle C\big(\rho(u)^{-1}\vartheta(h)\big),\ \rho(k)\,\Xi(\mathrm{diag}(h_1, h)\,x)\big\rangle.$$

Expand $\rho(u)^{-1}\vartheta(h) = \sum_j v_j e_j$. The map $C$ is conjugate linear and the inner product is conjugate linear in its first argument, so the sum comes out with the coefficients $v_j = c_j\overline{\theta_{\phi_j}(\cdots)}$. This gives $\sum_j c_j F_j(u, h) = f(h)$.

*Step 3: left invariance of $f$.* Let $\delta = (\delta_\infty, \delta_f)$ be rational. By Step 2 with $u = \delta_\infty$ and by Step 1, $f(\delta_f h) = \sum_j c_jF_j(\delta(1, h)) = \sum_j c_jF_j(1, h) = f(h)$.

*Step 4: the integral.* Let $K$ fix $f$. The average of $\sum_j c_j F_j$ over the real points at $h$ is $f(h)$ by Step 2, since the real points have volume $1$. By the fact on class sums,

$$\int_{[U(I_l)]} \sum_j c_j F_j = [K_0 : K]^{-1}\, \mathrm{classSum}_K f.$$

*Step 5.* Each $\int F_j = 0$ by the theorem on theta periods, with $\zeta = C(e_j)$, $b = b_j$, $g = g_j$, the point $(1, h_1)$ and $\gamma = x$. So the class sum is $0$. $\square$

**Remark (Formalization).** The data $c_j, g_j, b_j, \phi_j$ are extracted from the existential hypothesis `h_kernels` by `choose`, so they have no explicit form. Only their stated property is used. The point $h_1$ is a finite point in the statement, and $(1, h_1)$ is its adelic point with real part $1$. The level is any $K$ with `K ≤ rightStabilizer f`, so the class sum is the sum over the double cosets weighted by the inverse orders of the stabilizers.

### The kernel vector

The later chapters use one choice of $\vartheta$.

**Definition (Kernel vector).** Let $\mathfrak m$ be a modulus, $\Psi$ a function on the $l \times r$ matrices over $\mathcal O/\mathfrak m$, $\kappa$ a weight and $g \in U(W)(\mathbb{A})$. The kernel vector at $h \in U(I_l)(\mathbb{A}_f)$ has coordinate $j$ equal to the conjugate theta kernel of $(W, I_l)$ at $(g, h)$, twisted by $\nu_W$ and $b$, with the datum $\Psi$ modulo $\mathfrak m$ at the finite places and the Fock vector of the basis polynomial $j$ of weight $\kappa$ at infinity.

Lean: `New.Rows.kernelVector` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Corollary (Periods against kernel vectors).** Let the hypotheses on $O$, $\Xi$, $\varepsilon$ and the rank be as in the main theorem, and let $C$ be conjugate linear and equivariant. Let the places of $\mathfrak m$ lie in $O.\mathrm{places}$, and let $x$ be supported on $O.\mathrm{places}$. Let $K$ be a level such that every $k \in K$ is in $K_0$, fixes $\Psi$ (that is, $\Psi(\bar k^{-1}T) = \Psi(T)$ for all $T$), and has $x^{-1}(1, k)x$ in the level of $\Xi$. Then

$$\mathrm{classSum}_K\Big(h \mapsto \big\langle C(\text{kernelVector}(g, h)),\ \Xi(\mathrm{diag}(h_1, h)\, x)\big\rangle\Big) = 0.$$

Lean: `New.Rows.stdClassSum_gramForm_kernelVector_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

*Proof.* Let $\phi_j$ be the datum of coordinate $j$. Its finite part is the datum `modDatum` of $\Psi$, which is the vacuum at the places outside the conjugate closure of the places of $\mathfrak m$. These lie in $\Sigma$, so $\phi_j$ is the vacuum above $T$. The real points of $U(I_l)$ act on the Fock vectors of the basis polynomials by the Weyl representation of weight $\kappa$ (`realPairWeil_fockLetters`). So $(\rho(u)^{-1}\text{kernelVector}(g, h))_j = \overline{\theta_{\phi_j}(g, (u, h))}$, and the hypothesis of the main theorem holds with $c_j = 1$ and $g_j = g$.

It remains to see that $K$ fixes the function. For $k \in K$, the kernel vector at $hk$ equals the one at $h$, since the Weil operator of $k$ acts on the datum by $\Psi \mapsto \Psi(\bar k^{-1}\,\cdot)$, which fixes $\Psi$. And $\Xi(\mathrm{diag}(h_1, hk)x) = \Xi(\mathrm{diag}(h_1, h)x \cdot x^{-1}(1, k)x) = \Xi(\mathrm{diag}(h_1, h)x)$. Apply the main theorem. $\square$
