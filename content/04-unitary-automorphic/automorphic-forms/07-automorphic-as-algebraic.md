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

Section 4 defines forms of type $e_\lambda$ as functions on $G = G_\infty \times G_f$. Section 6 defines algebraic forms on a definite space as vector valued functions on $G_f$ alone. This section shows that on the standard definite space the two spaces are isomorphic, compatibly with $G_f$ and with Hecke polynomials. So levels, Hecke operators and Petersson products of Section 4 become finite sums over double cosets.

### The classical statement

Let $\mathbf{G}$ be reductive over a totally real field $F$ with $G_\infty = \mathbf{G}(F \otimes \mathbb{R})$ compact, and let $(\rho, W)$ be an irreducible unitary representation of $G_\infty$ of dimension $d$, with a unit vector $v$. Then $e_v(z) = d\,\langle v, \rho(z) v\rangle$ is a convolution idempotent. The map that sends $\varphi : \mathbf{G}(\mathbb{A}_f) \to W$ with $\varphi(\gamma g) = \rho(\gamma)\varphi(g)$ and an open stabilizer to $(x, g) \mapsto \langle v, \rho(x)^{-1}\varphi(g)\rangle$ is an isomorphism onto the automorphic forms fixed by $e_v$, and it commutes with $\mathbf{G}(\mathbb{A}_f)$. This links the algebraic modular forms of Gross (Section 2) with automorphic forms in the sense of Borel and Jacquet. The proof is Schur orthogonality, as in Bröcker and tom Dieck, *Representations of Compact Lie Groups* (1985), Chapter II, Section 4. The source proves it for the standard space and the representations $\rho_\kappa$ of Section 6, with $e_\lambda$ of Section 4 as idempotent and $v$ the highest vector.

### The standard space and the parameter

**Definition (Standard space).** A space $V = (J, x)$ with signs $s$ is *standard* if all signs are $+1$ and $x$ is the identity matrix. The space $I_n$ of chapter 1 is standard, and the signed space of signs $s$ is standard when $s = 1$, if $E$ has a primitive root of unity of order $5040$.

Lean: `New.Space.IsStd` (Lib/Weil/Construction/ThetaJets.lean), `New.isStd_signedSpace` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

A standard space is $I_n$ of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/), with rational points $\Gamma = U_n(E)$ in $G_f$, the standard rational points.

Lean: `New.stdRatPoints` (Lib/Adelic/Unitary/Defs.lean).

**Definition (Harish-Chandra parameter).** Let $(\kappa, e)$ be a weight (Section 6) and $l$ a family $l_w : \{1, \dots, n\} \to \mathbb{Z}$ over the infinite places $w$. With $N = n$ and $0 \le p < N$, let
$$h_w(p) = 2\Bigl(e_w + \sum_{p < h < N} \kappa_w(h)\Bigr) + N - 1 - 2p.$$
Then $l$ is *twice the Harish-Chandra parameter* of $(\kappa, e)$ if each $l_w$ is injective and each value $l_w(i)$ is $h_w(p)$ for some $p < N$.

Lean: `New.IsHCParam` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

As $h_w$ is strictly decreasing, $l_w$ lists $h_w(0) > \dots > h_w(N-1)$ in some order. The *highest vector* $v^+ \in \mathbb{C}^I$ attached to $l$ is a unit vector for the Gram form when each $l_w$ is injective.

Lean: `New.highestVector` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

So $\lambda = l/2$ is the parameter of the kernel $e_\lambda$, and on the compact group $e_\lambda$ is a matrix coefficient of $\rho_\kappa$.

### The two maps

Fix a standard space $V$, a weight $(\kappa, e)$ with $\rho = \rho_\kappa$ on $\mathbb{C}^I$, $l$ twice its Harish-Chandra parameter, and $d = \#I$.

**Definition (The map $\varphi \mapsto \varphi^\natural$).** For a linear form $L$ and an algebraic form $\varphi$, let $\varphi_L(x, g) = L(\rho(x^{-1})\varphi(g))$. For $L = \langle v^+, \cdot \rangle$ write $\varphi^\natural(x, g) = \langle v^+, \rho(x^{-1})\varphi(g)\rangle$.

Lean: `New.algFormCoeff`, `New.ofAlgForm` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Lemma.** For every $L$, the function $\varphi_L$ is automorphic on $V$.

Lean: `New.Space.isAutomorphic_algFormCoeff` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* It is continuous and right invariant under the stabilizer of $\varphi$. For rational $\gamma$, $\varphi(\gamma_f g) = \rho(\gamma_\infty)\varphi(g)$, so $\varphi_L(\gamma_\infty x, \gamma_f g) = \varphi_L(x, g)$. $\square$

**Definition (The map $y \mapsto y^\flat$).** For a function $y$ on $G$, let $y^\flat(g) = d \int_{G_\infty} y(x, g)\, \rho(x) v^+ \, dx$ for the Haar probability measure.

Lean: `New.Space.toAlgFormFun` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

**Lemma.** If $y$ is automorphic on the standard space, then $y^\flat$ is an algebraic form of weight $(\kappa, e)$.

Lean: `New.Space.toAlgFormFun_mem_algForm` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* A subgroup that fixes $y$ fixes $y^\flat$. For rational $\gamma$, translate the integral by $\gamma_\infty$ to get $y^\flat(\gamma_f g) = \rho(\gamma) y^\flat(g)$. $\square$

The integrand is continuous on a compact group, so no junk value occurs.

**Lemma (Schur orthogonality).** For $a, b, c \in \mathbb{C}^I$ and a linear form $f$,
$$\int_{G_\infty} f(\rho(x)c)\,\langle a, \rho(x^{-1}) b\rangle \, dx = d^{-1}\langle a, c\rangle\, f(b).$$

Lean: `New.schur_orthogonality` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

This is the relation of Bröcker and tom Dieck, Chapter II, Section 4. The source proves it by Schur's lemma: the average of $v \mapsto \langle a, v\rangle c$ commutes with $\rho$, so it is a scalar, fixed by its trace.

**Proposition.** (a) For $y$ continuous, $R(e_\lambda) y(x, g) = \langle v^+, \rho(x^{-1}) y^\flat(g)\rangle$. (b) For every algebraic form $\psi$, $(\psi^\natural)^\flat = \psi$.

Lean: `New.Space.realConv_typeKernel`, `New.Space.toAlgFormFun_ofAlgForm` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* (a) Under the parameter condition, $e_\lambda(z) = d\,\langle v^+, \rho(z) v^+\rangle$ on the compact group, by the formal degree and the match of coefficients ([discrete series](/chapter/discrete-series/), [Weyl modules](/chapter/weyl-modules/)). Then $R(e_\lambda)y(x, g) = \int d\, y(xz, g)\langle v^+, \rho(z)v^+\rangle dz$, and the substitution $z \mapsto x^{-1}z$ gives $\langle v^+, \rho(x^{-1}) y^\flat(g)\rangle$.

(b) The coordinate $a$ of $(\psi^\natural)^\flat(g)$ is $d \int (\rho(x) v^+)_a \langle v^+, \rho(x^{-1})\psi(g)\rangle dx$. Schur orthogonality with $a = c = v^+$ and $b = \psi(g)$ gives $\psi(g)_a$, as $v^+$ is a unit vector. $\square$

### The isomorphism

**Theorem.** Let $V$ be standard and $l$ twice the Harish-Chandra parameter of $(\kappa, e)$.

(a) For every algebraic form $\psi$ of weight $(\kappa, e)$, $\psi^\natural$ is a form of type $e_\lambda$ on $V$.

(b) The map $\psi \mapsto \psi^\natural$ is a linear isomorphism onto the forms of type $e_\lambda$, with inverse $y \mapsto y^\flat$, and $(y^\flat)^\natural = y$.

(c) The isomorphism commutes with right translation by $G_f$.

(d) For every subgroup $K$ of $G_f$, it restricts to an isomorphism between the $K$-fixed spaces.

Lean: `New.Space.isForm_ofAlgForm`, `New.Space.toAlgForm`, `New.Space.ofAlgForm_toAlgForm`, `New.Space.toAlgForm_eq_toAlgFormFun`, `New.Space.toAlgForm_formRep`, `New.Space.algFormEquiv` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* Here $V = I_n$ with all signs $1$. (a) $\psi^\natural$ is automorphic by the lemma, and bounded by the rapid decay of automorphic functions when all signs are equal (Section 5). By the proposition, $R(e_\lambda)\psi^\natural = \psi^\natural$.

(b) Injectivity follows from $(\psi^\natural)^\flat = \psi$. For $y$ of type $e_\lambda$, $y^\flat$ is algebraic and $(y^\flat)^\natural = R(e_\lambda) y = y$.

(c) $\psi^\natural(g(1, a)) = (a \cdot \psi)^\natural(g)$, and the inverse of an equivariant bijection is equivariant. (d) follows from (c). $\square$

**Remark (Formalization).** The isomorphism is defined as the inverse of the bijection $\psi \mapsto \psi^\natural$, so its values come from choice. `New.Space.toAlgForm_eq_toAlgFormFun` shows that it is the explicit map $y \mapsto y^\flat$, and the argument computes with this. Part (d) has no hypothesis on $K$, open or not, since it only restricts an equivariant isomorphism.

**Remark.** The source applies the theorem to $I_n$ and to the space of homomorphisms between two standard spaces, which it also declares standard.

### Hecke eigenvalues under the isomorphism

At a split place $w$, the source has Hecke operators $T_{w,j}$, $0 \le j \le n$, of the double cosets of $\operatorname{diag}(\varpi 1_j, 1)$ in $\mathrm{GL}_n(E_w)$, embedded in $G_f$ ([Iwahori exponents and Satake](/chapter/iwahori-satake/)). Let $K_w$ be the subgroup of $K_0$ of elements with components $1$ away from $w$ and $\bar w$. A vector is *spherical at $w$* if $K_w$ fixes it.

Lean: `New.maxCompactAt`, `New.sphericalAt`, `New.heckeSplit` (Lib/Weil/Unramified/SplitHecke.lean).

**Definition (Hecke polynomial as operators).** With $q$ the residue field order at $w$, the *Hecke polynomial operator* is $X \mapsto \sum_{i=0}^{n} (-X)^i q^{\binom{i}{2}} T_{w,i}$. A vector $y$ *has Hecke polynomial $p : \mathbb{C} \to \mathbb{C}$ at $w$* if $y$ is spherical at $w$ and the operator at $X$ acts on $y$ by $p(X)$ for every $X$.

Lean: `New.heckePolyOp`, `New.HasHeckePolynomial` (Lib/Weil/Unramified/SplitHecke.lean).

**Proposition.** Let $V$ be standard, $l$ twice the Harish-Chandra parameter of $(\kappa, e)$, and $w$ split. A form $y$ of type $e_\lambda$ has Hecke polynomial $p$ at $w$ if and only if $y^\flat$, as a function on $G_f$ with right translation, has Hecke polynomial $p$ at $w$.

Lean: `New.hasHeckePolynomial_toAlgForm_iff` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* The map $y \mapsto y^\flat$ is linear, injective and $G_f$-equivariant, so it commutes with Hecke operators and preserves the equations $Ty = cy$ and $K_w$-invariance. $\square$

**Remark (Formalization).** The statement assumes `WeilData E`, the auxiliary element, idele and splitting character fixed on $E$. The proof uses only equivariance.

### Integrals as class sums

A *level* is an open subgroup $K$ of $K_0$, with index $[K_0 : K]$.

Lean: `New.IsLevel`, `New.stdLevelIndex` (Lib/Adelic/Unitary/Defs.lean).

**Theorem.** Let $V$ be standard, $F$ automorphic on $V$, and $K$ a level. Then
$$\int_{\Gamma \backslash G} F = [K_0 : K]^{-1}\, I_{\Gamma, K}\Bigl(g \mapsto \int_{G_\infty} F(x, g)\, dx\Bigr),$$
for the quotient measure of Section 4 and the class integral of Section 3.

Lean: `New.Space.integral_eq_classIntegral_of_isLevel` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* Let $f(g) = \int_{G_\infty} F(x, g)\,dx$ and $S = \operatorname{Stab}(f) \cap K$, a level. [Reduction theory](/chapter/reduction-theory/) gives $\int_{\Gamma \backslash G} F = [K_0 : S]^{-1}\, \Sigma_{\Gamma, S}(f)$, with $\operatorname{vol}(G_\infty) = \operatorname{vol}(K_0) = 1$. Now $[K_0 : S] = [K : S][K_0 : K]$ and $I_{\Gamma,K}(f) = [K : S]^{-1}\Sigma_{\Gamma,S}(f)$ (Section 3). $\square$

This is the comparison that Section 3 announced.

**Theorem.** Let $V$, $l$ be as above, $\varphi$ an algebraic form, $K$ a level, and $\Phi$ automorphic with $\Phi(x, g) = L_g(\rho(x) v^+)$ for linear forms $L_g$. Then
$$\int_{\Gamma \backslash G} \Phi \cdot \varphi^\natural = (d\,[K_0 : K])^{-1}\, I_{\Gamma, K}\bigl(g \mapsto L_g(\varphi(g))\bigr).$$

Lean: `New.Space.integral_mul_eq_classIntegral_toAlgFormFun`, `New.Space.integral_mul_eq_classIntegral` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* For fixed $g$, $\int d\,\Phi(x, g) y(x, g)\, dx = L_g(y^\flat(g))$. Apply the last theorem to $d\,\Phi\, y$ with $y = \varphi^\natural$ and $(\varphi^\natural)^\flat = \varphi$. $\square$

**Theorem (Petersson product as a class sum).** Let $V$, $l$ be as above, $K$ a level, and $\chi$ a character of $K$ with values of finite order. For algebraic forms $\varphi$, $\varphi'$ on which $K$ acts by $\chi$,
$$\Sigma_{\Gamma, K}\bigl(g \mapsto \langle \varphi(g), \varphi'(g)\rangle\bigr) = [K_0 : K]\cdot d \cdot \langle \varphi^\natural, \varphi'^\natural \rangle_{\mathrm{Pet}}.$$

Lean: `New.Space.classSum_gramForm_eq_mul_petersson` (Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean).

*Proof.* Apply the last theorem with $\Phi = \overline{\varphi^\natural}$, $\Phi(x,g) = \langle \varphi(g), \rho(x)v^+\rangle$. The values of $\chi$ have absolute value $1$, so $K$ fixes $f(g) = \langle \varphi(g), \varphi'(g)\rangle$, and the class integral at $K$ is the class sum (Section 3). The index and $d$ are nonzero. $\square$

### Where the argument uses these objects

The map $y \mapsto y^\flat$ and its compatibility with $G_f$ are used in [the seesaw identity](/chapter/seesaw-identity-2/), [the objects of the upper bound](/chapter/upper-bound-objects/), [grids, paths and turns](/chapter/grids-paths-turns/), [single theta lifts](/chapter/single-theta-lifts/) and [the main summands](/chapter/main-summands/). The isomorphism at a fixed level is used in [deep level Poincaré series](/chapter/deep-level-poincare/) and [the proof of Theorem B](/chapter/proof-of-theorem-b/), and the Hecke equivalence in single theta lifts. The integral formula is used in the seesaw identity and deep level Poincaré series. That $\psi^\natural$ is a form is used in [false lifts](/chapter/false-lifts/) and [Hecke values](/chapter/hecke-values/), and the Petersson formula in Hecke values.
