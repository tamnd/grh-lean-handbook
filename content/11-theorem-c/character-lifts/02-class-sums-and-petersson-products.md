---
title: Class sums and Petersson products
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
  - New/OneLift/TestedForms.lean
  - Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
decls:
  - New.LevelPlaces.LevelForm.inner_eq_petersson
  - New.Rows.inner_eq_stdClassSum_gramForm
  - New.Rows.classForm
  - New.Rows.inner_classForm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Class sums and Petersson products

A form on a definite unitary group has two faces. As an algebraic form it is a vector valued function on the finite points $G_f$, and its inner product is a finite class sum. As an automorphic form it is a scalar function on the adelic group $G = G_\infty \times G_f$, and its inner product is the Petersson integral over $\Gamma \backslash G$. The Rallis inner product formula of Volume 6 speaks about the second product. The heights and the denominators of Volumes 11 and 12 speak about the first. This section proves the exact relation between the two. The constant is the index of the level times the dimension of the weight.

### The two products

Let $V$ be a standard definite space of rank $N$ over $E$: all signs are $+1$ and the point is the identity (`Space.IsStd`). Let $(\kappa, e)$ be a weight and $l$ twice its Harish-Chandra parameter (`IsHCParam κ e l`). Let $\rho = $ `conjWeylRep κ e` be the representation of the compact group $G_\infty$ on $\mathbb{C}^{d_\kappa}$, where $d_\kappa = \#$`WeylIndex n κ` is the dimension of the weight, and let $v^+ = $ `highestVector κ l` be the highest unit vector. To an algebraic form $\Xi$ of weight $(\kappa, e)$ attach the function

$$\Xi^\natural(x, g) = \langle v^+, \rho(x^{-1})\,\Xi(g)\rangle_{\mathrm{Gram}}, \qquad x \in G_\infty,\ g \in G_f.$$

This is `ofAlgForm l s Ξ`. It is an automorphic form on $G$: continuous, left invariant under the rational points, and right invariant under an open subgroup of $G_f$. The Petersson product of two functions on $G$ is

$$\langle F, F'\rangle_{\mathrm{Pet}} = \int_{\Gamma\backslash G} \overline{F(g)}\, F'(g)\, dg,$$

for the measure `quotMeasure` of [reduction theory for definite unitary groups](/chapter/reduction-theory/). The measure on $G_\infty$ is the probability Haar measure, and the measure on $G_f$ gives $K_0$ the volume $1$.

Fix level places $S$ (a family of chosen places and a family of twist places), a subgroup $H$ of the product of the groups $\mathrm{GL}_N(k_w)$ over the places $w$ of $S$, and a character $\chi$ of $H$. The level $K = $ `levelOf S.placeAt H` is the group of $k \in K_0$ whose reductions at the places of $S$ form an element of $H$. The space `S.LevelForm H χ κ e` consists of the algebraic forms of weight $(\kappa, e)$ with $\Xi(gk) = \chi(\bar k)\,\Xi(g)$ for $k \in K$, where $\bar k$ is the reduction of $k$. Its inner product is the class sum of Section 1.

**Lemma (Gram class sum).** For two forms $\varphi$, $\varphi'$ of the level $K$,

$$\langle\varphi, \varphi'\rangle = \sum_{[g] \in \Gamma\backslash G_f/K} \frac{1}{\#(\Gamma \cap gKg^{-1})}\, \langle\varphi(g), \varphi'(g)\rangle_{\mathrm{Gram}}.$$

Lean: `New.LevelPlaces.LevelForm.innerAt_eq_stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean), `New.Rows.inner_eq_stdClassSum_gramForm` (New/OneLift/TestedForms.lean).

The Lean lemma is stated for the conjugate pairing `innerAt σ` and any automorphism $\sigma$ of $\mathbb{C}$. The inner product of the space is `innerAt 1`. The second name is the same statement for the forms `O.FormV` of a descent pair $O$, whose level is `O.levelGroup`.

*Proof.* By definition, `innerAt σ` is $[K_0 : K]$ times the class integral at $K_0$ of the function $f(g) = \sigma^{-1}\langle\sigma\varphi(g), \sigma\varphi'(g)\rangle_{\mathrm{Gram}}$. The Gram form is invariant under the rational points, so $f$ is left invariant under $\Gamma$. For $k \in K$ both values are multiplied by $\chi(\bar k)$. This is a root of unity, since $H$ is finite, so $|\sigma\chi(\bar k)| = 1$ and $f(gk) = f(g)$. The class integral of a function that is right invariant under $K \leq K_0$ is $[K_0 : K]^{-1}$ times its class sum at $K$ (`classIntegral_eq_inv_smul_classSum`). The two indices cancel. $\square$

### Schur orthogonality in one formula

The comparison rests on one integral over the compact group $G_\infty$. For a function $y$ on $G$ put

$$y^\flat(g) = d_\kappa \int_{G_\infty} y(x, g)\, \rho(x) v^+\, dx.$$

This is `toAlgFormFun κ e l y`. If $l$ matches the weight, then $(\Xi^\natural)^\flat = \Xi$ for every algebraic form $\Xi$ (`toAlgFormFun_ofAlgForm`). This is the Schur orthogonality relation $d_\kappa \int_{G_\infty} \langle v^+, \rho(x)^{-1} u\rangle\, \rho(x) v^+\, dx = u$ for the irreducible representation $\rho$, applied to $u = \Xi(g)$. The background is in [Weyl modules and highest weight vectors](/chapter/weyl-modules/) of Volume 5.

**Proposition (Petersson comparison).** Let $V$ be standard, let $l$ be twice the Harish-Chandra parameter of $(\kappa, e)$, let $K$ be a level and let $\chi$ be a character of $K$ whose values have finite order. For algebraic forms $\varphi$, $\varphi'$ on which $K$ acts by $\chi$,

$$\sum_{[g] \in \Gamma\backslash G_f/K} \frac{\langle\varphi(g), \varphi'(g)\rangle_{\mathrm{Gram}}}{\#(\Gamma \cap gKg^{-1})} = [K_0 : K]\cdot d_\kappa \cdot \langle\varphi^\natural, \varphi'^\natural\rangle_{\mathrm{Pet}}.$$

Lean: `New.Space.classSum_gramForm_eq_mul_petersson` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* There are four steps.

Step 1. The conjugate of $\varphi^\natural$ is $\overline{\varphi^\natural(x, g)} = \langle\varphi(g), \rho(x) v^+\rangle_{\mathrm{Gram}}$ (`star_ofAlgForm`). Indeed $\rho(x)$ is unitary for the Gram form, so $\langle v^+, \rho(x^{-1}) u\rangle = \langle\rho(x) v^+, u\rangle$, and the Gram form is hermitian. So $\Phi = \overline{\varphi^\natural}$ has the form $\Phi(x, g) = L_g(\rho(x) v^+)$ with the linear functional $L_g = \langle\varphi(g), \cdot\rangle_{\mathrm{Gram}}$.

Step 2. For an automorphic function $F$ on $G$ and a level $K$, the integral over $\Gamma\backslash G$ is $[K_0:K]^{-1}$ times the class integral at $K$ of $g \mapsto \int_{G_\infty} F(x, g)\,dx$ (`integral_eq_classIntegral_of_isLevel`). Apply this to $F = d_\kappa \Phi\, \varphi'^\natural$. The inner integral is

$$d_\kappa \int_{G_\infty} L_g(\rho(x) v^+)\, \varphi'^\natural(x, g)\, dx = L_g\Big(d_\kappa \int_{G_\infty} \varphi'^\natural(x, g)\, \rho(x) v^+\, dx\Big) = L_g\big((\varphi'^\natural)^\flat(g)\big) = L_g(\varphi'(g)),$$

since a linear map commutes with the integral, and by Schur orthogonality. So

$$\langle\varphi^\natural, \varphi'^\natural\rangle_{\mathrm{Pet}} = \big(d_\kappa\,[K_0:K]\big)^{-1}\, \mathrm{CI}_K\big(g \mapsto \langle\varphi(g), \varphi'(g)\rangle_{\mathrm{Gram}}\big),$$

with $\mathrm{CI}_K$ the class integral at $K$ (`integral_mul_eq_classIntegral`).

Step 3. The function $g \mapsto \langle\varphi(g), \varphi'(g)\rangle_{\mathrm{Gram}}$ is right invariant under $K$. For $k \in K$ it is multiplied by $\overline{\chi(k)}\chi(k) = |\chi(k)|^2 = 1$, because $\chi(k)$ has finite order.

Step 4. For a function that is right invariant under $K$, the class integral at $K$ is the class sum at $K$ (`classIntegral_eq_classSum`). The numbers $d_\kappa$ and $[K_0 : K]$ are not zero, since the Weyl module is not zero and $K$ is open in the compact group $K_0$. Multiply by them. $\square$

### The lemma that the previous chapter uses

**Lemma (Inner product and Petersson product).** Let $V$ be a standard space with signs $s$, let $l$ be twice the Harish-Chandra parameter of $(\kappa, e)$, and let $S$, $H$, $\chi$ be as above. For two forms $\varphi$, $\varphi'$ in `S.LevelForm H χ κ e`,

$$\langle\varphi, \varphi'\rangle = [K_0 : K]\cdot d_\kappa\cdot \langle\varphi^\natural, \varphi'^\natural\rangle_{\mathrm{Pet}}, \qquad K = \text{`levelOf S.placeAt H`}.$$

Lean: `New.LevelPlaces.LevelForm.inner_eq_petersson` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* By the Gram class sum lemma at $\sigma = 1$, the left side is the class sum at $K$ of the Gram pairings of the values. The level acts on the forms by the character $k \mapsto \chi(\bar k)$, the composite of $\chi$ with the reduction map $K \to H$. The group $H$ is a subgroup of a finite group, so every value of $\chi$ has finite order (`isMulTorsion_of_finite`). Now the Petersson comparison applies to this character and gives the right side. $\square$

**Remark (Formalization).** The index $[K_0 : K]$ is written `(levelOf S.placeAt H).relIndex (stdLevel E n)`, which is $[K_0 : K \cap K_0]$, and it equals `stdLevelIndex K` because $K \leq K_0$. The inner product of Mathlib is conjugate linear in the first variable, and so is the Petersson product `Space.petersson`, so the two sides have the same linearity. The constant depends on the normalization of `quotMeasure`: probability measure on $G_\infty$ and volume $1$ for $K_0$. A different normalization changes the constant, and the later norm formula then changes by the same factor. The lemma needs no hypothesis that $\varphi$ is a Hecke eigenform or that the weight is regular.

**Example.** Let the weight be trivial, $\kappa = 0$ and $e = 0$. Then $d_\kappa = 1$, the Gram form is the product of two complex numbers, and $\varphi^\natural(x, g) = \varphi(g)$. The class sum $\sum_{[g]} |\varphi(g)|^2 / \#\mathrm{Aut}(g)$ is a sum of point masses. The Petersson integral over $\Gamma\backslash G$ is, by Step 2 of the proof above, the same sum with each class weighted by $\mathrm{vol}(K)/\#\mathrm{Aut}(g) = [K_0:K]^{-1}/\#\mathrm{Aut}(g)$. This is the lemma in the scalar case. In this case Schur orthogonality is the statement that the probability measure on $G_\infty$ has mass $1$.

### Forms on one class

The class sum makes it easy to describe the forms that are dual to evaluation at a point. Let $O$ be a descent pair, $h \in G_f$ and $v$ a vector of the weight. The form $\delta_h(v)$ is supported on the class $\Gamma h K$. Its value at $y$ is

$$\delta_h(v)(y) = \sum_{\gamma \in \Gamma,\ h^{-1}\gamma y \in K} \chi_O(h^{-1}\gamma y)\, \rho(\gamma)^{-1} v,$$

where $K$ is the level of $O$, $\chi_O$ is its level character and $\rho$ is the action of the rational points on the weight. The sum is finite, because $\Gamma \cap yKy^{-1}$ is finite.

**Definition (Class form).** The class form at $h$ is the linear map $v \mapsto \delta_h(v)$ from the vectors of the weight to `O.FormV`.

Lean: `New.Rows.classForm` (New/OneLift/TestedForms.lean).

**Lemma (Inner product with a class form).** For $h \in G_f$, a form $\varphi$ in `O.FormV` and a vector $v$ of the weight,

$$\langle\delta_h(v), \varphi\rangle = \langle v, \varphi(h)\rangle_{\mathrm{Gram}}.$$

Lean: `New.Rows.inner_classForm` (New/OneLift/TestedForms.lean).

*Proof.* By the Gram class sum lemma, the left side is the class sum of $g \mapsto L_g(\delta_h(v)(g))$, with $L_g = \langle\cdot, \varphi(g)\rangle_{\mathrm{Gram}}$. The functionals satisfy $L_{\gamma h k}(\chi_O(k)\rho(\gamma) u) = L_h(u)$ for $\gamma \in \Gamma$ and $k \in K$, by the equivariance of $\varphi$, the invariance of the Gram form and $|\chi_O(k)| = 1$. Only the class of $h$ contributes. At $g = h$ the sum defining $\delta_h(v)(h)$ runs over the $\#(\Gamma \cap hKh^{-1})$ elements of the stabilizer, and each term pairs with $\varphi(h)$ to $\langle v, \varphi(h)\rangle_{\mathrm{Gram}}$. The number of terms cancels the weight $1/\#(\Gamma \cap hKh^{-1})$ of the class (`classSum_deltaForm`). $\square$

So the class forms span `O.FormV`, and evaluation at a point is an inner product. Section 8 uses class forms at well chosen points to build the point forms, whose descents have an explicit finite datum.
