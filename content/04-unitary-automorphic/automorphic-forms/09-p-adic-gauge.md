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

Theorem A needs to know that some algebraic forms are divisible by large powers of a prime $p$. An algebraic form has complex values, so the source first fixes a ring map $\iota : \mathbb{C} \to \mathbb{C}_p$ and measures the values through $\iota$. A value $\varphi(g)$ is a vector in $\mathbb{C}^I$, and the group acts on it. So the size of $\varphi(g)$ must be measured in a way that the action of the rational points does not change. The *gauge* does this: it moves the vector back by $g^{-1}$, acting through the $p$-adic components of $g$, and then takes the largest $p$-adic absolute value of a coordinate. This section defines the gauge, proves its invariance, and shows that class sums and inner products of integral forms are integral after one multiplies by the orders of the stabilizers.

### The classical model

For a modular form $f = \sum a_n q^n$ with algebraic coefficients, one says that $f$ is $p$-integral for an embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_p$ if all $a_n$ have absolute value at most $1$ there. For an algebraic modular form $\varphi$ on a definite group, the values $\varphi(g)$ lie in the representation $W$. If $W$ has a lattice $W_{\mathbb{Z}_p}$ stable under the compact open subgroup at $p$, one can call $\varphi$ integral when its values at the points integral at $p$ lie in that lattice. The source uses a notion of the second kind with the coordinate lattice of $\mathbb{C}^I$, through the gauge.

### The gauge

**Definition ($p$-adic place).** A *$p$-adic place* of $\mathbb{C}$, for a prime $p$, is a ring map $\iota : \mathbb{C} \to \mathbb{C}_p$.

Lean: `New.PadicPlace` (Lib/General/Algebra/AdicCompletion.lean).

Such a map exists, by the axiom of choice, since $\mathbb{C}$ and $\mathbb{C}_p$ are isomorphic as abstract fields. It is not continuous. The results of this section hold for every such map.

For an infinite place $\tau$ of $E$, with its chosen complex embedding $\Phi_\tau$, the map $\sigma_\tau(x) = \iota(\Phi_\tau(\bar x))$ is an embedding of $E$ in $\mathbb{C}_p$. It induces a place $w_\tau$ of $E$ above $p$, and it extends to a ring map $\hat\sigma_\tau : \mathbb{A}_{E,f} \to \mathbb{C}_p$: take the component at $w_\tau$ and apply the continuous extension of $\sigma_\tau$ to $E_{w_\tau}$.

Lean: `New.weightEmbedding`, `New.adeleExtension` (Lib/ClassField/Places/ValuationSubrings.lean).

**Definition (Gauge).** Let $(\kappa, e)$ be a weight, with representation $\rho_{\kappa}$ of $\prod_\tau \mathrm{GL}_n$ on coordinate vectors indexed by $I$ ([Weyl modules](/chapter/weyl-modules/)). For $g \in G_f$ and $\xi \in \mathbb{C}^I$, the *gauge* of $\xi$ at $g$ is
$$\|\xi\|_g = \bigl\|\rho_\kappa\bigl((\hat\sigma_\tau(g^{-1}))_\tau\bigr)\, \iota(\xi)\bigr\|_\infty,$$
the largest $p$-adic absolute value of a coordinate of the vector $\rho_\kappa(\hat\sigma(g^{-1}))\,\iota(\xi)$ in $\mathbb{C}_p^I$.

Lean: `New.weylGauge` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Remark (Formalization).** The gauge is defined in the file of algebraic forms, not in the file of this section. It depends on $\iota$ through an instance argument. Some results, such as the lemma on Gram pairings below, use two places $j$ and $j \circ \overline{\,\cdot\,}$ at once, and then the source names the place explicitly.

Let $\mathcal{K}_p$ be the subgroup of $G_f$ of elements whose components at all places above $p$ are integral invertible matrices. It contains $K_0$.

Lean: `New.integralAbove` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Proposition (Properties of the gauge).** Let $g \in G_f$ and $\xi, \eta \in \mathbb{C}^I$.

(a) For a rational point $\gamma$ of the standard space, $\|\rho(\gamma)\xi\|_{\gamma g} = \|\xi\|_g$.

(b) For $k \in \mathcal{K}_p$, $\|\xi\|_{gk} = \|\xi\|_g$.

(c) For $c \in \mathbb{C}$, $\|c\xi\|_g = |\iota(c)|_p\, \|\xi\|_g$.

(d) For $k \in \mathcal{K}_p$, $\|\xi\|_k \le 1$ if and only if $|\iota(\xi_i)|_p \le 1$ for every coordinate $i$.

(e) $\|\xi + \eta\|_g \le \max(\|\xi\|_g, \|\eta\|_g)$. So if every term of a finite sum has gauge at most $C \ge 0$, the sum has gauge at most $C$.

Lean: `New.weylGauge_embFin`, `New.weylGauge_mul_of_mem_integralAbove`, `New.weylGauge_smul`, `New.weylGauge_le_one_iff`, `New.weylGauge_sum_le`, `New.Rows.weylGauge_add_le_max` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* (a) On $E$, the map $\hat\sigma_\tau$ is $\sigma_\tau$. After $\iota$, the action of $\gamma$ on $\mathbb{C}^I$ is $\rho_\kappa$ of the matrices $\sigma_\tau(\gamma)$. So $\rho(\hat\sigma((\gamma g)^{-1}))\,\iota(\rho(\gamma)\xi) = \rho(\hat\sigma(g^{-1}))\rho(\sigma(\gamma))^{-1}\rho(\sigma(\gamma))\iota(\xi)$.

(b) For $a \in \mathcal{K}_p$, each $\hat\sigma_\tau(a)$ is an integral matrix, since $w_\tau$ lies above $p$. The entries of $\rho_\kappa$ of an integral matrix are integral polynomials in its entries ([Weyl modules](/chapter/weyl-modules/)), so they have absolute value at most $1$. A matrix with such entries does not increase the sup norm, by the ultrametric inequality. Apply this to $k$ and to $k^{-1}$.

(c) and (e) hold because $\iota$ is a ring map and the sup norm on $\mathbb{C}_p^I$ is ultrametric.

(d) By (b), $\|\xi\|_k = \|\xi\|_1$, and $\|\xi\|_1$ is the sup norm of $\iota(\xi)$. $\square$

So for an algebraic form $\varphi$ the function $g \mapsto \|\varphi(g)\|_g$ is invariant on the left under the rational points, by (a), and on the right under $\mathcal{K}_p \cap \operatorname{Stab}(\varphi)$, by (b). This is why the gauge is the right measure of size: it is a function on a finite set of double cosets.

### Weak approximation and integral forms

**Lemma (Weak approximation above $p$).** Let $V$ be a space with all signs $1$, by default the standard space. For $g, d \in G_f$ there is a rational point $\gamma$ of $V$ such that $\gamma g \in \mathcal{K}_p$ and $d(\gamma g)d^{-1} \in \mathcal{K}_p$.

Lean: `New.exists_mul_mem_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The set of $x$ with $xg \in K_0$ and $dxgd^{-1} \in K_0$ is open and nonempty, since it contains $g^{-1}$. The rational points times the elements trivial above $p$ are dense in $G_\infty \times G_f$ (the weak approximation theorem of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/)). So the open set contains $\gamma h$ with $\gamma$ rational and $h$ trivial above $p$. At places above $p$ the components of $\gamma g$ and of $\gamma h g$ agree, so they are integral. $\square$

**Definition (Integral forms).** Let $O_\iota$ be the valuation ring of the $c \in \mathbb{C}$ with $|\iota(c)|_p \le 1$. For $c \in \mathbb{R}$ and $d \in G_f$, an algebraic form $\varphi$ of weight $(\kappa, e)$ is *bounded by $c$ at $d$* if $\|\varphi(g)\|_{gd} \le c$ for every $g$. For a subspace $S$ of algebraic forms, the forms in $S$ that are bounded by $1$ at $d$ form an $O_\iota$-module, the *integral forms of $S$ at $d$*.

Lean: `New.embValRing`, `New.GaugeLe`, `New.integralFormsAt` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

They form an $O_\iota$-module by (c) and (e) of the proposition.

**Proposition.** Let $\varphi$ be an algebraic form on the standard space such that $|\iota(\varphi(g)_i)|_p \le 1$ for all $g \in \mathcal{K}_p$ and all coordinates $i$. Then $\|\varphi(g)\|_g \le 1$ for every $g \in G_f$.

Lean: `New.weylGauge_le_one_of_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* By weak approximation choose $\gamma$ with $\gamma g \in \mathcal{K}_p$. By (a), $\|\varphi(g)\|_g = \|\rho(\gamma)\varphi(g)\|_{\gamma g} = \|\varphi(\gamma g)\|_{\gamma g}$. This is at most $1$ by (d) and the hypothesis. $\square$

### Delta forms and class sums

For a subgroup $K$ of $G_f$, the set $\Gamma \backslash G_f / K$ of classes of the standard space is written $\mathrm{Cl}(K)$.

Lean: `New.StdClasses` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Lemma.** For every prime $p$ there is a system of representatives of $\mathrm{Cl}(K)$ that lie in $\mathcal{K}_p$.

Lean: `New.exists_reps_integralAbove` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Move a representative of each class by a rational point, by weak approximation. $\square$

**Remark (Formalization).** The representatives are chosen by `choose` from the weak approximation lemma, one per class. The statement is an existence statement, so no later result depends on the choice.

**Proposition (Gauge of a delta form).** Let $K$ be a level of finite type, $\chi$ a character of $K$ that is trivial near $1$ and whose values have finite order, $x \in G_f$ and $v \in \mathbb{C}^I$. For every $g \in G_f$, the delta form $\delta_{x,v}$ of Section 6 satisfies $\|\delta_{x,v}(g)\|_g \le \|v\|_x$.

Lean: `New.Rows.weylGauge_deltaForm_le` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The value $\delta_{x,v}(g)$ is a finite sum over the transporter of terms $\chi(k)\rho(\gamma^{-1})v$, with $k = x^{-1}\gamma g \in K$. By (e) it is enough to bound each term. As $\chi(k)$ is a root of unity, $|\iota(\chi(k))|_p = 1$. As $k \in K \subseteq K_0 \subseteq \mathcal{K}_p$, (b) gives $\|\rho(\gamma^{-1})v\|_g = \|\rho(\gamma^{-1})v\|_{\gamma^{-1}x}$, and (a) gives that this is $\|v\|_x$. $\square$

**Theorem (Integrality of class sums).** Let $(\Gamma, K)$ be of finite type in a group $G$, $f$ a function on $G$ with values in $\mathbb{C}^I$, $g \in G_f$, $c \in \mathbb{C}$, and $A \in \mathbb{N}$ divisible by the order of every stabilizer $\Gamma \cap xKx^{-1}$. If $\|c f(x)\|_g \le 1$ for every $x$, then
$$\|A c \cdot \Sigma_{\Gamma, K}(f)\|_g \le 1.$$

Lean: `New.Rows.weylGauge_classSum_le_one` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The vectors $\xi$ with $\|c\xi\|_g \le 1$ form an additive monoid, by (e). The class sum is a sum of the terms $f(x_i)/\#\Gamma_{x_i}$, and $A/\#\Gamma_{x_i}$ is a natural number. So $A \cdot \Sigma_{\Gamma,K}(f)$ is a sum of natural multiples of the $f(x_i)$, and it lies in the monoid. $\square$

The factor $A$ is necessary. With trivial weight and $f = 1$, the class sum is the mass $\sum_i 1/\#\Gamma_{x_i}$, which can have $p$ in its denominator when $p$ divides some $\#\Gamma_{x_i}$.

### Forms of a level and their inner products

The forms that the argument counts have a level cut out at finitely many split places.

**Definition (Level places).** A *set of level places* consists of two finite families of finite places of $E$, the chosen places and the places of the twist, such that no place of either family equals another place of the two families or the conjugate of one.

Lean: `New.LevelPlaces` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

In particular no place in the families is fixed by conjugation, so all are split.

**Definition (Level cut out by $H$).** For a family $(w_i)$ of places and a subgroup $H$ of $\prod_i \mathrm{GL}_n(k_{w_i})$, with $k_{w_i}$ the residue fields, the level $K(H)$ is the group of $k \in K_0$ whose reductions modulo the $w_i$ form an element of $H$.

Lean: `New.levelOf` (Lib/Adelic/Unitary/CongruenceLevels.lean).

**Definition (Forms of a level).** Let $S$ be a set of level places, $H$ a subgroup of $\prod_i \mathrm{GL}_n(k_{w_i})$ over all places $w_i$ of $S$, and $\chi$ a character of $H$. The *forms of level $(H, \chi)$* are the algebraic forms $\varphi$ of weight $(\kappa, e)$ on the standard space with $\varphi(gk) = \chi(\bar k)\varphi(g)$ for $k \in K(H)$, where $\bar k$ is the reduction of $k$.

Lean: `New.LevelPlaces.LevelForm`, `New.stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Proposition (Inner product).** For an automorphism $\sigma$ of $\mathbb{C}$, the pairing
$$\langle \varphi, \varphi' \rangle_\sigma = \sigma^{-1}\Bigl(\Sigma_{\Gamma, K(H)}\bigl(g \mapsto \langle \sigma\varphi(g), \sigma\varphi'(g)\rangle\bigr)\Bigr)$$
is sesquilinear for the ring map $\sigma^{-1} \circ \overline{\,\cdot\,} \circ \sigma$, where $\sigma\varphi(g)$ means $\sigma$ applied to each coordinate and $\langle\cdot,\cdot\rangle$ is the Gram form. For $\sigma = 1$ it is an inner product, and the forms of level $(H, \chi)$ are a finite-dimensional inner product space with
$$\langle \varphi, \varphi' \rangle = \Sigma_{\Gamma, K(H)}\bigl(g \mapsto \langle \varphi(g), \varphi'(g)\rangle\bigr).$$

Lean: `New.LevelPlaces.LevelForm.innerAt`, `New.LevelPlaces.LevelForm.innerAt_eq_stdClassSum`, `New.LevelPlaces.LevelForm.inner_eq_stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* The source defines $\langle\cdot,\cdot\rangle_\sigma$ as $[K_0 : K(H)]$ times the pairing of Section 6 for the Gram form twisted by $\sigma$. The function $g \mapsto \sigma^{-1}\langle\sigma\varphi(g), \sigma\varphi'(g)\rangle$ is left invariant under the rational points, since the Gram form is invariant under the twisted action. It is right invariant under $K(H)$, since each $k$ multiplies both values by $\chi(\bar k)$, a root of unity as $H$ is finite, and $\sigma$ preserves its absolute value $1$. So the class integral at $K_0$ is $[K_0 : K(H)]^{-1}$ times the class sum at $K(H)$ (Section 3). Positivity for $\sigma = 1$ is the positivity of class sums. $\square$

**Remark (Formalization).** The pairing $\langle\cdot,\cdot\rangle_\sigma$ is marked irreducible, so later files use it only through the formula with the class sum.

**Remark.** Let $\sigma = 1$ and let $l$ be twice the Harish-Chandra parameter of $(\kappa, e)$. The values of $\chi$ are roots of unity, so the theorem of Section 7 on Petersson products applies, and this inner product is $[K_0 : K(H)] \cdot d$ times the Petersson product of $\varphi^\natural$ and $\varphi'^\natural$.

**Lemma.** Let $j : \mathbb{C} \to \mathbb{C}_l$ be an $l$-adic place, and $u, v \in \mathbb{C}^I$. If $\|u\|_g \le 1$ for the place $j \circ \overline{\,\cdot\,}$ and $\|v\|_g \le 1$ for the place $j$, then the Gram pairing $\langle u, v\rangle$ lies in $O_j$.

Lean: `New.gramForm_mem_embValRing` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* Let $a_\tau$ be the image of $g$ at $\tau$ for $j$. For the place $j \circ \overline{\,\cdot\,}$, the matrix of $g^{-1}$ is the transpose of $a_\tau$, since $g$ is unitary. Let $x = \rho(a^{T}) j(\bar u)$ and $y = \rho(a^{-1}) j(v)$. Their coordinates are integral by hypothesis. The Gram matrix $G$ has integer entries and $\rho(a^{T})^{T} G \rho(a^{-1})$ is $G$ by the invariance of the Gram form. So $j(\langle u, v\rangle) = x^T G y$, which is integral. $\square$

**Definition (Integral forms of a level).** For an $l$-adic place $j$, the *integral forms* at $j$ are the forms $\varphi$ of level $(H, \chi)$ with $\|\varphi(g)\|_g \le 1$ for every $g$, for the gauge of $j$. They form an $O_j$-module.

Lean: `New.LevelPlaces.LevelForm.integralForms` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

**Theorem (Integrality of inner products).** Let $A \in \mathbb{N}$ be divisible by the order of every stabilizer $\Gamma \cap gK(H)g^{-1}$. If $\varphi$ is integral at $j \circ \overline{\,\cdot\,}$ and $\varphi'$ is integral at $j$, then $|j(A\langle \varphi, \varphi'\rangle)|_l \le 1$.

Lean: `New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

*Proof.* By the proposition the inner product is the class sum of $g \mapsto \langle\varphi(g), \varphi'(g)\rangle$. Each value lies in $O_j$ by the lemma, and $A$ clears the denominators of the class sum, as in the theorem on class sums. $\square$

### Where the argument uses these objects

The gauge, its invariance and the bounded forms are used throughout [divisibility](/chapter/divisibility/) and [archimedean size](/chapter/archimedean-size/), in [theta kernels and gauges](/chapter/theta-kernels-gauges/), in [deep level Poincaré series](/chapter/deep-level-poincare/), in [lift volume and height](/chapter/lift-volume-height/) and in [Hecke values](/chapter/hecke-values/). Weak approximation above $p$ and the integral representatives are used in [divisibility](/chapter/divisibility/), [lift volume and height](/chapter/lift-volume-height/), [Hecke values](/chapter/hecke-values/) and the [second chapter on the comparison operator](/chapter/comparison-operator-2/). The bound for delta forms is used in [archimedean size](/chapter/archimedean-size/), [deep level Poincaré series](/chapter/deep-level-poincare/), [Hecke values](/chapter/hecke-values/) and the [first chapter on the comparison operator](/chapter/comparison-operator-1/). The integrality of class sums is used in the second chapter on the comparison operator. The forms of a level and their inner products appear in most chapters of the upper bound, of the determinant and of the congruences, and the integrality of inner products is used in [the denominator bound](/chapter/denominator-bound/), [integral target forms](/chapter/integral-target-forms/), [Hecke values](/chapter/hecke-values/) and [lift volume and height](/chapter/lift-volume-height/).
