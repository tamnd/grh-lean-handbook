---
title: The p-adic gauge
lean:
  - Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
  - Lib/Adelic/Unitary/CongruenceLevels.lean
decls:
  - New.PadicPlace
  - New.weightEmbedding
  - New.adeleExtension
  - New.weylGauge
  - New.integralAbove
  - New.exists_mul_mem_integralAbove
  - New.weylGauge_embFin
  - New.weylGauge_mul_of_mem_integralAbove
  - New.weylGauge_smul
  - New.weylGauge_le_one_iff
  - New.weylGauge_sum_le
  - New.Rows.weylGauge_add_le_max
  - New.GaugeLe
  - New.embValRing
  - New.integralFormsAt
  - New.weylGauge_le_one_of_integralAbove
  - New.StdClasses
  - New.exists_reps_integralAbove
  - New.Rows.weylGauge_deltaForm_le
  - New.Rows.weylGauge_classSum_le_one
  - New.LevelPlaces
  - New.levelOf
  - New.stdClassSum
  - New.LevelPlaces.LevelForm
  - New.LevelPlaces.LevelForm.innerAt
  - New.LevelPlaces.LevelForm.innerAt_eq_stdClassSum
  - New.LevelPlaces.LevelForm.inner_eq_stdClassSum
  - New.gramForm_mem_embValRing
  - New.LevelPlaces.LevelForm.integralForms
  - New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The $p$-adic gauge

Theorem A needs some algebraic forms to be divisible by large powers of a prime $p$. The values are complex vectors, so the source fixes a ring map $\iota : \mathbb{C} \to \mathbb{C}_p$. The size of $\varphi(g)$ must not change under the rational points. The *gauge* moves the vector back by $g^{-1}$ through the $p$-adic components of $g$ and takes the largest $p$-adic absolute value of a coordinate. Class sums and inner products of integral forms are then integral up to stabilizer orders.

### The classical model

A modular form $\sum a_n q^n$ is $p$-integral if all $|a_n|_p \le 1$. An algebraic modular form with values in $W$ is integral when its values at points integral at $p$ lie in a lattice of $W$ stable at $p$. The source uses this second notion, with the coordinate lattice of $\mathbb{C}^I$.

### The gauge

**Definition ($p$-adic place).** A *$p$-adic place* of $\mathbb{C}$ is a ring map $\iota : \mathbb{C} \to \mathbb{C}_p$.

Lean: `New.PadicPlace` (Lib/General/Algebra/AdicCompletion.lean).

Such a map exists by choice, as $\mathbb{C} \cong \mathbb{C}_p$ as abstract fields. It is not continuous.

For an infinite place $\tau$ of $E$ with complex embedding $\Phi_\tau$, $\sigma_\tau(x) = \iota(\Phi_\tau(\bar x))$ embeds $E$ in $\mathbb{C}_p$, induces a place $w_\tau$ above $p$, and extends to $\hat\sigma_\tau : \mathbb{A}_{E,f} \to \mathbb{C}_p$ through the component at $w_\tau$.

Lean: `New.weightEmbedding`, `New.adeleExtension` (Lib/ClassField/Places/ValuationSubrings.lean).

**Definition (Gauge).** For a weight $(\kappa, e)$ with representation $\rho_\kappa$ on $\mathbb{C}^I$ ([Weyl modules](/chapter/weyl-modules/)), $g \in G_f$ and $\xi \in \mathbb{C}^I$, the *gauge* is
$$\|\xi\|_g = \bigl\|\rho_\kappa\bigl((\hat\sigma_\tau(g^{-1}))_\tau\bigr)\, \iota(\xi)\bigr\|_\infty,$$
the largest $p$-adic absolute value of a coordinate in $\mathbb{C}_p^I$.

Lean: `New.weylGauge` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Remark (Formalization).** The gauge is defined in the file of algebraic forms and takes $\iota$ as an instance argument. Results that use the two places $j$ and $j \circ \overline{\,\cdot\,}$ at once, such as the Gram lemma below, name the place explicitly.

Let $\mathcal{K}_p \supseteq K_0$ be the subgroup of $G_f$ of elements with integral invertible components at all places above $p$.

Lean: `New.integralAbove` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Proposition (Properties of the gauge).** Let $g \in G_f$ and $\xi, \eta \in \mathbb{C}^I$.

(a) For a rational point $\gamma$ of the standard space, $\|\rho(\gamma)\xi\|_{\gamma g} = \|\xi\|_g$.

(b) For $k \in \mathcal{K}_p$, $\|\xi\|_{gk} = \|\xi\|_g$.

(c) For $c \in \mathbb{C}$, $\|c\xi\|_g = |\iota(c)|_p\, \|\xi\|_g$.

(d) For $k \in \mathcal{K}_p$, $\|\xi\|_k \le 1$ if and only if $|\iota(\xi_i)|_p \le 1$ for every $i$.

(e) $\|\xi + \eta\|_g \le \max(\|\xi\|_g, \|\eta\|_g)$, so a finite sum of terms of gauge at most $C \ge 0$ has gauge at most $C$.

Lean: `New.weylGauge_embFin`, `New.weylGauge_mul_of_mem_integralAbove`, `New.weylGauge_smul`, `New.weylGauge_le_one_iff`, `New.weylGauge_sum_le`, `New.Rows.weylGauge_add_le_max` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* (a) On $E$, $\hat\sigma_\tau = \sigma_\tau$, and after $\iota$ the action of $\gamma$ is $\rho_\kappa(\sigma(\gamma))$, which cancels against $\rho(\hat\sigma((\gamma g)^{-1}))$. (b) For $a \in \mathcal{K}_p$, each $\hat\sigma_\tau(a)$ is integral, and $\rho_\kappa$ has integral polynomial entries ([Weyl modules](/chapter/weyl-modules/)), so it does not increase the sup norm. Apply this to $k$ and $k^{-1}$. (c) and (e) hold as $\iota$ is a ring map and the sup norm is ultrametric. (d) By (b), $\|\xi\|_k = \|\xi\|_1$. $\square$

So $g \mapsto \|\varphi(g)\|_g$ is a function on a finite set of double cosets.

### Weak approximation and integral forms

**Lemma (Weak approximation above $p$).** Let $V$ be a space with all signs $1$, by default the standard space. For $g, d \in G_f$ there is a rational point $\gamma$ with $\gamma g \in \mathcal{K}_p$ and $d(\gamma g)d^{-1} \in \mathcal{K}_p$.

Lean: `New.exists_mul_mem_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The set of $x$ with $xg \in K_0$ and $dxgd^{-1} \in K_0$ is open and contains $g^{-1}$. By weak approximation ([adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/)) it contains $\gamma h$ with $\gamma$ rational and $h$ trivial above $p$. Above $p$, $\gamma g$ and $\gamma h g$ agree. $\square$

**Definition (Integral forms).** Let $O_\iota$ be the valuation ring of $c \in \mathbb{C}$ with $|\iota(c)|_p \le 1$. An algebraic form $\varphi$ is *bounded by $c \in \mathbb{R}$ at $d \in G_f$* if $\|\varphi(g)\|_{gd} \le c$ for every $g$. The forms of a subspace $S$ bounded by $1$ at $d$ form an $O_\iota$-module by (c) and (e), the *integral forms of $S$ at $d$*.

Lean: `New.embValRing`, `New.GaugeLe`, `New.integralFormsAt` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Proposition.** Let $\varphi$ be an algebraic form on the standard space with $|\iota(\varphi(g)_i)|_p \le 1$ for all $g \in \mathcal{K}_p$ and all $i$. Then $\|\varphi(g)\|_g \le 1$ for every $g \in G_f$.

Lean: `New.weylGauge_le_one_of_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Choose $\gamma$ with $\gamma g \in \mathcal{K}_p$. By (a), $\|\varphi(g)\|_g = \|\varphi(\gamma g)\|_{\gamma g}$, which is at most $1$ by (d). $\square$

### Delta forms and class sums

For a subgroup $K$ of $G_f$, write $\mathrm{Cl}(K) = \Gamma \backslash G_f / K$ for the standard space.

Lean: `New.StdClasses` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Lemma.** For every prime $p$, $\mathrm{Cl}(K)$ has a system of representatives in $\mathcal{K}_p$.

Lean: `New.exists_reps_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Move each representative by a rational point, by weak approximation. $\square$

**Remark (Formalization).** The representatives are chosen by `choose`, one per class. The statement is existential, so nothing later depends on the choice.

**Proposition (Gauge of a delta form).** Let $K$ be a level of finite type, $\chi$ a character of $K$ trivial near $1$ with values of finite order, $x \in G_f$ and $v \in \mathbb{C}^I$. For every $g$, the delta form $\delta_{x,v}$ of Section 6 satisfies $\|\delta_{x,v}(g)\|_g \le \|v\|_x$.

Lean: `New.Rows.weylGauge_deltaForm_le` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* $\delta_{x,v}(g)$ is a finite sum of terms $\chi(k)\rho(\gamma^{-1})v$ with $k = x^{-1}\gamma g \in K$. By (e) bound each term. $|\iota(\chi(k))|_p = 1$, and as $K \subseteq \mathcal{K}_p$, (b) and (a) give $\|\rho(\gamma^{-1})v\|_g = \|\rho(\gamma^{-1})v\|_{\gamma^{-1}x} = \|v\|_x$. $\square$

**Theorem (Integrality of class sums).** Let $(\Gamma, K)$ be of finite type in a group $G$, $f$ a function on $G$ with values in $\mathbb{C}^I$, $g \in G_f$, $c \in \mathbb{C}$, and $A \in \mathbb{N}$ divisible by the order of every stabilizer $\Gamma \cap xKx^{-1}$. If $\|c f(x)\|_g \le 1$ for every $x$, then $\|A c \cdot \Sigma_{\Gamma, K}(f)\|_g \le 1$.

Lean: `New.Rows.weylGauge_classSum_le_one` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The $\xi$ with $\|c\xi\|_g \le 1$ form an additive monoid by (e), and $A \cdot \Sigma_{\Gamma,K}(f)$ is a sum of natural multiples $(A/\#\Gamma_{x_i}) f(x_i)$. $\square$

### Forms of a level and their inner products

**Definition (Level places).** A *set of level places* is two finite families of finite places of $E$, the chosen places and the places of the twist, such that no place of either family equals another place of the two families or the conjugate of one. So all are split.

Lean: `New.LevelPlaces` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Definition (Level cut out by $H$).** For places $(w_i)$ and a subgroup $H$ of $\prod_i \mathrm{GL}_n(k_{w_i})$, $K(H)$ is the group of $k \in K_0$ whose reductions modulo the $w_i$ lie in $H$.

Lean: `New.levelOf` (Lib/Adelic/Unitary/CongruenceLevels.lean).

**Definition (Forms of a level).** For a set of level places $S$, a subgroup $H$ over the places of $S$ and a character $\chi$ of $H$, the *forms of level $(H, \chi)$* are the algebraic forms $\varphi$ of weight $(\kappa, e)$ on the standard space with $\varphi(gk) = \chi(\bar k)\varphi(g)$ for $k \in K(H)$.

Lean: `New.LevelPlaces.LevelForm`, `New.stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Proposition (Inner product).** For an automorphism $\sigma$ of $\mathbb{C}$, the pairing
$$\langle \varphi, \varphi' \rangle_\sigma = \sigma^{-1}\Bigl(\Sigma_{\Gamma, K(H)}\bigl(g \mapsto \langle \sigma\varphi(g), \sigma\varphi'(g)\rangle\bigr)\Bigr)$$
is sesquilinear for $\sigma^{-1} \circ \overline{\,\cdot\,} \circ \sigma$, with $\langle\cdot,\cdot\rangle$ the Gram form. For $\sigma = 1$ it is an inner product, and the forms of level $(H, \chi)$ are a finite-dimensional inner product space with $\langle \varphi, \varphi' \rangle = \Sigma_{\Gamma, K(H)}(g \mapsto \langle \varphi(g), \varphi'(g)\rangle)$.

Lean: `New.LevelPlaces.LevelForm.innerAt`, `New.LevelPlaces.LevelForm.innerAt_eq_stdClassSum`, `New.LevelPlaces.LevelForm.inner_eq_stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The source defines $\langle\cdot,\cdot\rangle_\sigma$ as $[K_0 : K(H)]$ times the pairing of Section 6. The integrand is right invariant under $K(H)$, as $\chi(\bar k)$ is a root of unity. So the class integral at $K_0$ is $[K_0 : K(H)]^{-1}$ times the class sum at $K(H)$ (Section 3). Positivity for $\sigma = 1$ is that of class sums. $\square$

**Remark (Formalization).** The pairing is marked irreducible, so later files use it only through the class sum formula.

**Remark.** For $\sigma = 1$ and $l$ twice the Harish-Chandra parameter, the Petersson theorem of Section 7 gives $\langle \varphi, \varphi' \rangle = [K_0 : K(H)] \cdot d \cdot \langle \varphi^\natural, \varphi'^\natural \rangle_{\mathrm{Pet}}$.

**Lemma.** Let $j : \mathbb{C} \to \mathbb{C}_l$ be an $l$-adic place and $u, v \in \mathbb{C}^I$. If $\|u\|_g \le 1$ for the place $j \circ \overline{\,\cdot\,}$ and $\|v\|_g \le 1$ for $j$, then $\langle u, v\rangle \in O_j$.

Lean: `New.gramForm_mem_embValRing` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Let $a$ be the image of $g$ for $j$. As $g$ is unitary, for $j \circ \overline{\,\cdot\,}$ the matrix of $g^{-1}$ is $a^T$. The vectors $x = \rho(a^{T}) j(\bar u)$ and $y = \rho(a^{-1}) j(v)$ are integral, the Gram matrix $G$ is integral and invariant, so $j(\langle u, v\rangle) = x^T G y$ is integral. $\square$

**Definition (Integral forms of a level).** For an $l$-adic place $j$, the *integral forms* at $j$ are the forms $\varphi$ of level $(H, \chi)$ with $\|\varphi(g)\|_g \le 1$ for all $g$, for the gauge of $j$. They form an $O_j$-module.

Lean: `New.LevelPlaces.LevelForm.integralForms` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Theorem (Integrality of inner products).** Let $A \in \mathbb{N}$ be divisible by the order of every stabilizer $\Gamma \cap gK(H)g^{-1}$. If $\varphi$ is integral at $j \circ \overline{\,\cdot\,}$ and $\varphi'$ is integral at $j$, then $|j(A\langle \varphi, \varphi'\rangle)|_l \le 1$.

Lean: `New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The inner product is a class sum of values in $O_j$ by the lemma, and $A$ clears its denominators. $\square$

### Where the argument uses the gauge

The gauge and bounded forms are used in [divisibility](/chapter/divisibility/), [archimedean size](/chapter/archimedean-size/), [theta kernels and gauges](/chapter/theta-kernels-gauges/), [deep level Poincaré series](/chapter/deep-level-poincare/), [lift volume and height](/chapter/lift-volume-height/) and [Hecke values](/chapter/hecke-values/). Weak approximation is also used in [the comparison operator, second part](/chapter/comparison-operator-2/), with integrality of class sums, and the delta form bound in [the comparison operator, first part](/chapter/comparison-operator-1/). Integrality of inner products is used in [the denominator bound](/chapter/denominator-bound/), [integral target forms](/chapter/integral-target-forms/), Hecke values and lift volume and height.
