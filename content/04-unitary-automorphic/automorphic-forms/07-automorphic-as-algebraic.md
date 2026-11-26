---
title: Automorphic forms as algebraic forms
lean:
  - Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean
  - Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean
  - Lib/Weil/Unramified/SplitHecke.lean
decls:
  - New.Space.IsStd
  - New.isStd_signedSpace
  - New.IsHCParam
  - New.highestVector
  - New.algFormCoeff
  - New.ofAlgForm
  - New.Space.isAutomorphic_algFormCoeff
  - New.Space.toAlgFormFun
  - New.Space.toAlgFormFun_mem_algForm
  - New.Space.realConv_typeKernel
  - New.Space.toAlgFormFun_ofAlgForm
  - New.schur_orthogonality
  - New.Space.isForm_ofAlgForm
  - New.Space.toAlgForm
  - New.Space.ofAlgForm_toAlgForm
  - New.Space.toAlgForm_eq_toAlgFormFun
  - New.Space.toAlgForm_formRep
  - New.Space.algFormEquiv
  - New.heckePolyOp
  - New.HasHeckePolynomial
  - New.hasHeckePolynomial_toAlgForm_iff
  - New.IsLevel
  - New.stdLevelIndex
  - New.stdRatPoints
  - New.Space.integral_eq_classIntegral_of_isLevel
  - New.Space.integral_mul_eq_classIntegral_toAlgFormFun
  - New.Space.integral_mul_eq_classIntegral
  - New.Space.classSum_gramForm_eq_mul_petersson
  - New.maxCompactAt
  - New.sphericalAt
  - New.heckeSplit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Automorphic forms as algebraic forms

Section 4 defines forms of type $e_\lambda$ on any hermitian space, as functions on $G = G_\infty \times G_f$. Section 6 defines algebraic forms on a definite space, as vector valued functions on $G_f$ alone. This section shows that on the standard definite space the two spaces are the same, by an isomorphism that commutes with $G_f$. So the levels, the Hecke operators and the Petersson products of Section 4 can be computed as finite sums over double cosets. The section also shows that the isomorphism preserves Hecke polynomials. Section 8 treats eigenforms.

### The classical statement

Let $\mathbf{G}$ be a reductive group over a totally real field $F$ with $\mathbf{G}(F \otimes \mathbb{R})$ compact. Let $(\rho, W)$ be an irreducible representation of the compact group $G_\infty = \mathbf{G}(F \otimes \mathbb{R})$. Assume that $\rho$ is unitary for an inner product $\langle \cdot, \cdot \rangle$, let $d = \dim W$, and fix a unit vector $v$. The function $e_v(z) = d\,\langle v, \rho(z) v\rangle$ on $G_\infty$ is an idempotent for convolution. The classical statement is this. The map that sends a function $\varphi : \mathbf{G}(\mathbb{A}_f) \to W$ with $\varphi(\gamma g) = \rho(\gamma)\varphi(g)$ for $\gamma \in \mathbf{G}(F)$ and an open stabilizer to the function $(x, g) \mapsto \langle v, \rho(x)^{-1}\varphi(g)\rangle$ on $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A})$ is a linear isomorphism onto the automorphic forms fixed by right convolution with $e_v$, and it commutes with $\mathbf{G}(\mathbb{A}_f)$. This is the link between the algebraic modular forms of Gross (Section 2) and automorphic forms in the sense of Borel and Jacquet. The proof is the Schur orthogonality relations for the compact group $G_\infty$, as in Bröcker and tom Dieck, *Representations of Compact Lie Groups* (1985), Chapter II, Section 4.

The source proves this statement for the standard definite space and for the representations $\rho_\kappa$ of Section 6. Its idempotent is the kernel $e_\lambda$ of Section 4, with $v$ the highest vector.

### The standard space and the parameter

**Definition (Standard space).** A space $V = (J, x)$ with signs $s$ is *standard* if all signs are $+1$ and the point $x$ is the identity matrix. The standard space $I_n$ of chapter 1 is standard, and the signed space of signs $s$ is standard when $s = 1$, if $E$ has a primitive root of unity of order $5040$.

Lean: `New.Space.IsStd` (Lib/Weil/Construction/ThetaJets.lean), `New.isStd_signedSpace` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

A standard space is the space $I_n$ of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/), with its group of rational points $\Gamma_{I_n,f} = U_n(E)$ inside $G_f$. The source writes this group as the standard rational points.

Lean: `New.stdRatPoints` (Lib/Adelic/Unitary/Defs.lean).

**Definition (Harish-Chandra parameter).** Let $\kappa = (\kappa, e)$ be a weight in the sense of Section 6, and let $l$ be a family $l_w : \{1, \dots, n\} \to \mathbb{Z}$ over the infinite places $w$. Write $N = n$ and, for $0 \le p < N$, let
$$h_w(p) = 2\Bigl(e_w + \sum_{p < h < N} \kappa_w(h)\Bigr) + N - 1 - 2p.$$
Then $l$ is *twice the Harish-Chandra parameter* of $(\kappa, e)$ if at each $w$ the map $l_w$ is injective and each value $l_w(i)$ is $h_w(p)$ for some $p < N$.

Lean: `New.IsHCParam` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

As $h_w$ is strictly decreasing, $l_w$ lists the numbers $h_w(0) > \dots > h_w(N-1)$ in some order. The vector $v^+$ in $\mathbb{C}^I$ attached to $l$ is the *highest vector*. When each $l_w$ is injective it is a unit vector for the Gram form $\langle \cdot, \cdot \rangle$ of the Weyl module.

Lean: `New.highestVector` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

So $\lambda = l/2$ is the parameter of the discrete series kernel $e_\lambda$ of Section 4, and the weight $(\kappa, e)$ is the representation of $G_\infty$ with this parameter. The condition ties the two halves of this section: on a compact group, the kernel $e_\lambda$ is a matrix coefficient of $\rho_\kappa$.

### The two maps

Fix a standard space $V$, a weight $(\kappa, e)$ with representation $\rho = \rho_\kappa$ on $\mathbb{C}^I$, and $l$ twice its Harish-Chandra parameter. Let $d = \#I$ be the dimension of $\rho$.

**Definition (The map $\varphi \mapsto \varphi^\natural$).** For a linear form $L$ on $\mathbb{C}^I$ and an algebraic form $\varphi$ of weight $(\kappa, e)$, let $\varphi_L(x, g) = L(\rho(x^{-1})\varphi(g))$ on $G$. For $L = \langle v^+, \cdot \rangle$ write $\varphi^\natural = \varphi_L$:
$$\varphi^\natural(x, g) = \langle v^+, \rho(x^{-1})\varphi(g)\rangle.$$

Lean: `New.algFormCoeff`, `New.ofAlgForm` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Lemma.** For every $L$, the function $\varphi_L$ is automorphic on $V$.

Lean: `New.Space.isAutomorphic_algFormCoeff` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* It is continuous, since $\rho$ is continuous on $G_\infty$ and $\varphi$ is locally constant on $G_f$. It is invariant on the right under the open stabilizer of $\varphi$. For a rational point $\gamma$, with image $(\gamma_\infty, \gamma_f)$ in $G$, we have $\varphi(\gamma_f g) = \rho(\gamma)\varphi(g)$, and $\rho(\gamma)$ is $\rho(\gamma_\infty)$. So $\varphi_L(\gamma_\infty x, \gamma_f g) = L(\rho(x^{-1})\rho(\gamma_\infty)^{-1}\rho(\gamma_\infty)\varphi(g)) = \varphi_L(x, g)$. $\square$

**Definition (The map $y \mapsto y^\flat$).** For a function $y$ on the group of the standard space, let
$$y^\flat(g) = d \int_{G_\infty} y(x, g)\, \rho(x) v^+ \, dx,$$
for the Haar probability measure on $G_\infty$.

Lean: `New.Space.toAlgFormFun` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

**Lemma.** If $y$ is automorphic on the standard space, then $y^\flat$ is an algebraic form of weight $(\kappa, e)$.

Lean: `New.Space.toAlgFormFun_mem_algForm` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* An open subgroup that fixes $y$ fixes $y^\flat$, so the stabilizer of $y^\flat$ is open. For a rational point $\gamma$, translate the integral by $\gamma_\infty$, which preserves Haar measure, and use $y(\gamma_\infty x, \gamma_f g) = y(x, g)$. This gives $y^\flat(\gamma_f g) = \rho(\gamma) y^\flat(g)$. $\square$

The integral is over a compact group of a continuous function, so it converges. No junk value occurs.

**Lemma (Schur orthogonality).** For vectors $a, b, c$ in $\mathbb{C}^I$ and a linear form $f$,
$$\int_{G_\infty} f(\rho(x)c)\,\langle a, \rho(x^{-1}) b\rangle \, dx = d^{-1}\langle a, c\rangle\, f(b).$$

Lean: `New.schur_orthogonality` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

This is the Schur orthogonality relation for the irreducible unitary representation $\rho$ (Bröcker and tom Dieck, Chapter II, Section 4). The source proves it by Schur's lemma: the average of the rank one map $v \mapsto \langle a, v\rangle c$ commutes with $\rho$, so it is a scalar, and its trace fixes the scalar.

**Proposition.** Let $l$ be twice the Harish-Chandra parameter of $(\kappa, e)$.

(a) For $y$ continuous, $R(e_\lambda) y(x, g) = \langle v^+, \rho(x^{-1}) y^\flat(g)\rangle$.

(b) For every algebraic form $\psi$, $(\psi^\natural)^\flat = \psi$.

Lean: `New.Space.realConv_typeKernel`, `New.Space.toAlgFormFun_ofAlgForm` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* (a) On the compact group, the kernel is $e_\lambda(z) = d\,\langle v^+, \rho(z) v^+\rangle$. This uses the value of the formal degree and the match of the discrete series coefficient with the matrix coefficient of $\rho$, which hold under the parameter condition ([discrete series](/chapter/discrete-series/), [Weyl modules](/chapter/weyl-modules/)). Then
$$R(e_\lambda)y(x, g) = \int e_\lambda(z)\, y(xz, g)\, dz = \int d\, y(xz, g)\,\langle v^+, \rho(z)v^+\rangle \, dz.$$
Substitute $z \mapsto x^{-1}z$. The integral becomes $\langle v^+, \rho(x^{-1}) \int d\, y(z, g)\rho(z) v^+ dz\rangle = \langle v^+, \rho(x^{-1}) y^\flat(g)\rangle$.

(b) Fix $g$ and a coordinate $a$ of $\mathbb{C}^I$. The coordinate $a$ of $(\psi^\natural)^\flat(g)$ is $d \int (\rho(x) v^+)_a \langle v^+, \rho(x^{-1})\psi(g)\rangle \, dx$. Schur orthogonality with $f$ the coordinate $a$, $a = c = v^+$ and $b = \psi(g)$ gives $d \cdot d^{-1}\langle v^+, v^+\rangle\, \psi(g)_a = \psi(g)_a$, since $v^+$ is a unit vector. $\square$

### The isomorphism

**Theorem.** Let $V$ be standard and $l$ twice the Harish-Chandra parameter of $(\kappa, e)$, with $s$ the signs of $V$.

(a) For every algebraic form $\psi$ of weight $(\kappa, e)$, the function $\psi^\natural$ is a form of type $e_\lambda$ on $V$.

(b) The map $\psi \mapsto \psi^\natural$ is a linear isomorphism from algebraic forms of weight $(\kappa, e)$ to forms of type $e_\lambda$. Its inverse sends $y$ to $y^\flat$, and $(y^\flat)^\natural = y$.

(c) The isomorphism commutes with right translation by $G_f$.

(d) For every subgroup $K$ of $G_f$, it restricts to an isomorphism between the $K$-fixed algebraic forms and the $K$-fixed forms of type $e_\lambda$.

Lean: `New.Space.isForm_ofAlgForm`, `New.Space.toAlgForm`, `New.Space.ofAlgForm_toAlgForm`, `New.Space.toAlgForm_eq_toAlgFormFun`, `New.Space.toAlgForm_formRep`, `New.Space.algFormEquiv` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* Since $V$ is standard, $s = 1$ and $V = I_n$.

(a) The function $\psi^\natural$ is automorphic by the lemma. It is bounded: the source deduces this from its lemma that automorphic functions are of rapid decay when all signs are equal (Section 5). By part (a) of the proposition and part (b), $R(e_\lambda)\psi^\natural(x, g) = \langle v^+, \rho(x^{-1})\psi(g)\rangle = \psi^\natural(x, g)$.

(b) The map is injective, since $(\psi^\natural)^\flat = \psi$. Let $y$ be a form of type $e_\lambda$. Then $y^\flat$ is an algebraic form by the lemma, and $(y^\flat)^\natural = R(e_\lambda) y$ by part (a) of the proposition. As $y$ is a form of type $e_\lambda$ and $e_\lambda$ is integrable on the compact group, $R(e_\lambda) y = y$. So the map is onto, and the inverse is $y \mapsto y^\flat$.

(c) Right translation by $(1, a)$ on $G$ and right translation by $a$ on $G_f$ match under $\psi \mapsto \psi^\natural$, since $\psi^\natural(g(1, a)) = (a \cdot \psi)^\natural(g)$. The inverse of an equivariant bijection is equivariant.

(d) This follows from (c). $\square$

**Remark (Formalization).** The isomorphism is defined as the inverse of the bijection $\psi \mapsto \psi^\natural$, so its values come from the axiom of choice. The theorem `New.Space.toAlgForm_eq_toAlgFormFun` shows that on the standard space it is the explicit map $y \mapsto y^\flat$, and the argument uses this to compute with it. Part (d) has no hypothesis on $K$: it holds for every subgroup, open or not, because it only restricts an equivariant isomorphism.

**Remark.** The theorem is stated only for standard spaces. The source applies it to $I_n$ and to the space of homomorphisms between two standard spaces, which it also declares standard.

### Hecke eigenvalues under the isomorphism

At a split place $w$, the source has Hecke operators $T_{w,j}$ for $0 \le j \le n$, the Hecke operators (in the sense of Section 3) of the double coset of $\operatorname{diag}(\varpi 1_j, 1)$ in $\mathrm{GL}_n(E_w)$, through the embedding of $\mathrm{GL}_n(E_w)$ in $G_f$ ([Iwahori exponents and Satake](/chapter/iwahori-satake/)). Let $K_w$ be the subgroup of $K_0$ of elements whose components away from $w$ and $\bar w$ are $1$. A vector is *spherical at $w$* if $K_w$ fixes it.

Lean: `New.maxCompactAt`, `New.sphericalAt`, `New.heckeSplit` (Lib/Weil/Unramified/SplitHecke.lean).

**Definition (Hecke polynomial as operators).** Let $q$ be the order of the residue field at $w$. The *Hecke polynomial operator* at $w$ is the function
$$X \mapsto \sum_{i=0}^{n} (-X)^i q^{\binom{i}{2}} T_{w,i}.$$
A vector $y$ *has Hecke polynomial $p$ at $w$*, for a function $p : \mathbb{C} \to \mathbb{C}$, if $y$ is spherical at $w$ and the operator at $X$ acts on $y$ by $p(X)$ for every $X \in \mathbb{C}$.

Lean: `New.heckePolyOp`, `New.HasHeckePolynomial` (Lib/Weil/Unramified/SplitHecke.lean).

**Proposition.** Let $V$ be standard, $l$ twice the Harish-Chandra parameter of $(\kappa, e)$, and $w$ a split place. A form $y$ of type $e_\lambda$ has Hecke polynomial $p$ at $w$ if and only if its algebraic form $y^\flat$, as a function on $G_f$ with right translation, has Hecke polynomial $p$ at $w$.

Lean: `New.hasHeckePolynomial_toAlgForm_iff` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* The map that sends $y$ to the function $y^\flat$ on $G_f$ is linear, injective and equivariant for $G_f$. An equivariant linear map commutes with every Hecke operator, and an injective one preserves the equations $Ty = cy$ and the property of being fixed by $K_w$. $\square$

**Remark (Formalization).** The statement assumes `WeilData E`, which the source describes as the auxiliary element, idele and splitting character fixed on $E$. The proof uses only the equivariance of the isomorphism.

### Integrals as class sums

A *level* is an open subgroup $K$ of $K_0$. Its index is $[K_0 : K]$.

Lean: `New.IsLevel`, `New.stdLevelIndex` (Lib/Adelic/Unitary/Defs.lean).

**Theorem.** Let $V$ be standard, $F$ automorphic on $V$, and $K$ a level. Then
$$\int_{\Gamma \backslash G} F = [K_0 : K]^{-1}\, I_{\Gamma, K}\Bigl(g \mapsto \int_{G_\infty} F(x, g)\, dx\Bigr),$$
for the measure on the quotient of Section 4 and the class integral of Section 3, with $\Gamma$ the standard rational points.

Lean: `New.Space.integral_eq_classIntegral_of_isLevel` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* Let $f(g) = \int_{G_\infty} F(x, g)\,dx$ and $S = \operatorname{Stab}(f) \cap K$. The stabilizer of $f$ contains an open subgroup that fixes $F$, so $S$ is a level. [Reduction theory](/chapter/reduction-theory/) proves that $\int_{\Gamma \backslash G} F = [K_0 : S]^{-1}\, \Sigma_{\Gamma, S}(f)$ for the quotient measure, with $\operatorname{vol}(G_\infty) = \operatorname{vol}(K_0) = 1$. Now $[K_0 : S] = [K : S]\,[K_0 : K]$, and $I_{\Gamma,K}(f) = [K : S]^{-1}\Sigma_{\Gamma,S}(f)$ by the definition of the class integral (Section 3). $\square$

This is the theorem that Section 3 announced: on the standard definite space, the class integral is the integral over the quotient up to the factor $[K_0 : K]$.

**Theorem.** Let $V$ be standard, $l$ twice the Harish-Chandra parameter of $(\kappa, e)$, $\varphi$ an algebraic form, $K$ a level, and $\Phi$ automorphic on $V$ with $\Phi(x, g) = L_g(\rho(x) v^+)$ for linear forms $L_g$. Then
$$\int_{\Gamma \backslash G} \Phi \cdot \varphi^\natural = (d\,[K_0 : K])^{-1}\, I_{\Gamma, K}\bigl(g \mapsto L_g(\varphi(g))\bigr).$$

Lean: `New.Space.integral_mul_eq_classIntegral_toAlgFormFun`, `New.Space.integral_mul_eq_classIntegral` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* For fixed $g$, $\int_{G_\infty} d\,\Phi(x, g) y(x, g)\, dx = L_g(y^\flat(g))$ by linearity of $L_g$ and the definition of $y^\flat$. Apply the last theorem to $d\,\Phi\, y$, and then take $y = \varphi^\natural$, with $(\varphi^\natural)^\flat = \varphi$. $\square$

**Theorem (Petersson product as a class sum).** Let $V$ be standard, $l$ twice the Harish-Chandra parameter of $(\kappa, e)$, $K$ a level, and $\chi$ a character of $K$ whose values have finite order. For algebraic forms $\varphi$, $\varphi'$ on which $K$ acts by $\chi$,
$$\Sigma_{\Gamma, K}\bigl(g \mapsto \langle \varphi(g), \varphi'(g)\rangle\bigr) = [K_0 : K]\cdot d \cdot \langle \varphi^\natural, \varphi'^\natural \rangle_{\mathrm{Pet}}.$$

Lean: `New.Space.classSum_gramForm_eq_mul_petersson` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* The conjugate of $\varphi^\natural(x, g)$ is $\langle \varphi(g), \rho(x)v^+\rangle$. So the last theorem applies with $\Phi = \overline{\varphi^\natural}$ and $L_g = \langle \varphi(g), \cdot\rangle$, and gives the Petersson product as $(d[K_0 : K])^{-1}$ times the class integral of $f(g) = \langle \varphi(g), \varphi'(g)\rangle$. The values of $\chi$ have finite order, so they have absolute value $1$, and $f(gk) = \overline{\chi(k)}\chi(k) f(g) = f(g)$. So $K$ fixes $f$, and the class integral at $K$ is the class sum at $K$ (Section 3). The index and $d$ are nonzero. $\square$

**Example.** Let $d = 1$, $K = K_0$, $\chi = 1$ and $\varphi' = \varphi$ fixed by $K_0$. Then the index is $1$ and the theorem reads $\sum_{c} \langle\varphi(g_c), \varphi(g_c)\rangle/\#\Gamma_c = \langle \varphi^\natural, \varphi^\natural\rangle_{\mathrm{Pet}}$. The sum is over the classes $c$ of $\Gamma \backslash G_f / K_0$, with representatives $g_c$ and stabilizers $\Gamma_c = \Gamma \cap g_c K_0 g_c^{-1}$. For $\varphi = 1$ with trivial weight, the left side is the mass $\sum_c 1/\#\Gamma_c$ of the genus of $I_n$.

### Where the argument uses these objects

The map $y \mapsto y^\flat$ is used in [the seesaw identity](/chapter/seesaw-identity-2/), in [the objects of the upper bound](/chapter/upper-bound-objects/), in [grids, paths and turns](/chapter/grids-paths-turns/), in [single theta lifts](/chapter/single-theta-lifts/) and in [the main summands](/chapter/main-summands/). Its compatibility with $G_f$ is used in the last three of these and in the rows of the upper bound. The isomorphism at a fixed level is used in [deep level Poincaré series](/chapter/deep-level-poincare/) and [the proof of Theorem B](/chapter/proof-of-theorem-b/). The equivalence of Hecke polynomials is used in [single theta lifts](/chapter/single-theta-lifts/). The integral formula against $\varphi^\natural$ is used in the seesaw identity, in deep level Poincaré series and for the auxiliary pair of the upper bound. The fact that $\psi^\natural$ is a form is used in [false lifts](/chapter/false-lifts/), [Hecke values](/chapter/hecke-values/) and [single theta lifts](/chapter/single-theta-lifts/). The Petersson product as a class sum is used in [Hecke values](/chapter/hecke-values/).
