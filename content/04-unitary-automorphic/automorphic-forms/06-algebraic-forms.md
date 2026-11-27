---
title: Algebraic forms on definite groups
lean:
  - Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean
  - Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean
  - Lib/GLn/SchurModule/SchurOrthogonality.lean
  - Lib/GaloisRep/Main/Defs.lean
decls:
  - New.SmoothForm
  - New.smoothFormRep
  - New.Weight
  - New.conjWeylRep
  - New.Space.weightRep
  - New.Space.forms
  - New.Space.formTranslation
  - New.AlgForm
  - New.algFormRep
  - New.levelSpace_smoothFormRep_apply
  - New.levelSpace_ext_doubleCosets
  - New.evalClassReps
  - New.evalClassReps_injective
  - New.finite_levelSpace_smoothFormRep
  - New.Space.finite_formTranslation_levelSpace
  - New.transporter
  - New.mem_transporter
  - New.card_transporter
  - New.deltaForm
  - New.deltaForm_apply
  - New.classSum_deltaForm
  - New.freeLevelEquiv
  - New.finrank_levelSpace_smoothFormRep
  - New.smoothPairing
  - New.smoothPairing_formTranslation
  - New.Space.exists_isUnitary_formTranslation
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Algebraic forms on definite groups

On a definite space $G_\infty$ is compact, and an automorphic form is a vector valued function on the finite set $\Gamma_{V,f} \backslash G_f / K$: an algebraic modular form of Gross (Section 2). All proofs here are finite sums.

Throughout, $V = (J, x)$ has all signs $+1$, and $\Gamma_{V,f}$ is the image of $U(J)(E)$ in $G_f$ under the injective map $\gamma \mapsto (x^{-1}\gamma x)_f$. The standard definite space is $I_n$, with $J = 1$ and $x = 1$, as in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

### Smooth forms

**Definition (Smooth form).** Let $G$ be a topological group, $\Gamma$ a group, $e : \Gamma \to G$ a homomorphism, and $\rho$ a representation of $\Gamma$ on a complex vector space $W$. A *smooth form* for $(e, \rho)$ is a function $\varphi : G \to W$ such that $\varphi(e(\gamma)\, g) = \rho(\gamma)\, \varphi(g)$ for all $\gamma \in \Gamma$ and $g \in G$, and such that the subgroup of $k \in G$ with $\varphi(gk) = \varphi(g)$ for all $g$ is open. $G$ acts by right translation.

Lean: `New.SmoothForm`, `New.smoothFormRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

The level space of $(K, \chi)$ (Section 3) is the space of smooth forms with $\varphi(gk) = \chi(k)\varphi(g)$ for $k \in K$. Gross's space $M(\rho, K)$ is the level space of $(K, 1)$.

### Weights and algebraic forms

The coefficients are irreducible algebraic representations of $\mathrm{GL}_n$, one at each infinite place, built in [Weyl modules](/chapter/weyl-modules/).

**Definition (Weight).** A *weight* for $E$ is a pair $\kappa = (\kappa_1, \kappa_2)$. For each infinite place $\tau$ and $h \ge 1$, $\kappa_1(\tau, h)$ is the number of columns of height $h$ of a Young diagram, and $\kappa_2(\tau) \in \mathbb{Z}$ is a power of the determinant.

Lean: `New.Weight` (Lib/GaloisRep/Main/Defs.lean).

Let $I$ be the product over $\tau$ of the sets of standard fillings of $\kappa_1(\tau, \cdot)$ with entries in $n$. Then $\mathbb{C}^I$ carries the Weyl module at each place, twisted by $\det^{\kappa_2(\tau)}$. Letting each component of $\prod_\tau U(\operatorname{diag} s)$ act through its entrywise complex conjugate gives the *conjugate Weyl representation* $\rho_\kappa$.

Lean: `New.conjWeylRep` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

**Definition (Weight representation).** For a space $V$, the *weight representation* $\rho_{V,\kappa}$ of $U(J)(E)$ on $\mathbb{C}^I$ sends $\gamma$ to $\rho_\kappa$ of the infinite part of $x^{-1}\gamma x$.

Lean: `New.Space.weightRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Definition (Algebraic form).** Let $V$ be a definite space and $\kappa$ a weight. An *algebraic form of weight $\kappa$* on $V$ is a smooth form on $G_f$ for $U(J)(E) \to G_f$ and $\rho_{V,\kappa}$: a function $\varphi : G_f \to \mathbb{C}^I$ with an open right stabilizer and
$$\varphi(\gamma g) = \rho_{V,\kappa}(\gamma)\, \varphi(g) \qquad \text{for } \gamma \in \Gamma_{V,f},\ g \in G_f.$$
$G_f$ acts by right translation. On $I_n$ the source writes the space with the two parts of the weight as separate arguments.

Lean: `New.Space.forms`, `New.Space.formTranslation`, `New.AlgForm`, `New.algFormRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

This is Gross's definition (Section 2) with $\mathbf{G} = U(J)$ over $F$ and $W$ an algebraic representation of $\prod_\tau \mathrm{GL}_n(\mathbb{C})$. Gross fixes the level; the source takes all open levels and recovers his space as a level space.

**Remark.** For unitary $u$, the entrywise conjugate is $(u^{T})^{-1}$. So $\rho_\kappa$ is the contragredient of the Weyl module of $\kappa$, restricted to the compact group. Texts that use the Weyl module itself have the dual weight.

### Values on representatives

**Lemma.** Let $\varphi$ be a smooth form in the level space of $(K, \chi)$. Then $\varphi(e(\gamma)\, g\, k) = \chi(k)\, \rho(\gamma)\, \varphi(g)$ for $\gamma \in \Gamma$, $g \in G$ and $k \in K$. For representatives $r$ of $e(\Gamma) \backslash G / K$, the map $\varphi \mapsto (\varphi(r(c)))_c$ is injective.

Lean: `New.levelSpace_smoothFormRep_apply`, `New.levelSpace_ext_doubleCosets`, `New.evalClassReps`, `New.evalClassReps_injective` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* Every $y \in G$ is $e(\gamma)\, r(c)\, k$, so the first identity gives the value at $y$ from the value at $r(c)$. $\square$

**Theorem (Finite dimension).** Let $(e(\Gamma), K)$ have finite type (Section 3), let $\chi$ be a character of $K$, and let $W$ have finite dimension. Then the level space of $(K, \chi)$ has finite dimension. The same holds for algebraic forms of weight $\kappa$ on a definite $V$, for every open subgroup $K$ of $G_f$ and character $\chi$ of $K$.

Lean: `New.finite_levelSpace_smoothFormRep` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean); `New.Space.finite_formTranslation_levelSpace` (same file).

*Proof.* By the lemma, the level space embeds in $W^{\Gamma \backslash G / K}$. For the second part, $(\Gamma_{V,f}, K \cap K_0)$ has finite type ([reduction theory](/chapter/reduction-theory/)), and the level space of $(K, \chi)$ lies in that of $K \cap K_0$ with the restricted character. $\square$

On an indefinite group this fails: finitely many values do not fix a form, hence Section 5.

### Forms supported on one class

Let $e$ be injective and $(e(\Gamma), K)$ of finite type, and let $\chi$ be trivial near $1$.

**Definition (Transporter).** For $x, y \in G$, the *transporter* $T(x, y)$ is the set of $\gamma \in \Gamma$ with $x^{-1} e(\gamma) y \in K$. It is finite, with $\#(e(\Gamma) \cap xKx^{-1})$ elements if $x$, $y$ lie in one double coset and $0$ otherwise.

Lean: `New.transporter`, `New.mem_transporter`, `New.card_transporter` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

**Remark (Formalization).** The finite set `New.transporter` is defined by `choose` from the transporter lemma of Section 3. `New.mem_transporter` gives its elements, so the choice does not affect any value.

**Definition (Delta form).** For $x \in G$ and $v \in W$, the *delta form* $\delta_{x,v}$ is
$$\delta_{x,v}(y) = \sum_{\gamma \in T(x, y)} \chi(x^{-1} e(\gamma) y)\; \rho(\gamma^{-1})\, v.$$
It lies in the level space of $(K, \chi)$, vanishes off $e(\Gamma)\, x\, K$, and is linear in $v$.

Lean: `New.deltaForm`, `New.deltaForm_apply` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* Since $T(x, e(\gamma') y) = T(x, y)\, \gamma'^{-1}$, a reindexing gives $\delta_{x,v}(e(\gamma') y) = \rho(\gamma')\, \delta_{x,v}(y)$. Right translation by $k \in K$ maps $T(x, y)$ to $T(x, yk)$ and multiplies each term by $\chi(k)$; as $\chi$ is trivial near $1$, the stabilizer is open. Off $e(\Gamma) x K$ the set $T(x, y)$ is empty. $\square$

For $\chi = 1$, the delta forms at $x$ realize the summand $W^{\Gamma_x}$ of Gross's decomposition (Section 2).

**Proposition (Class sum of a delta form).** For each $g \in G$ let $L_g : W \to \mathbb{C}$ be additive, with $L_{e(\gamma) x k}(\chi(k) \rho(\gamma) v) = L_x(v)$ for all $\gamma \in \Gamma$, $k \in K$, $v \in W$ and $x \in G$. Then
$$\Sigma_{\Gamma, K}\bigl(g \mapsto L_g(\delta_{x,v}(g))\bigr) = L_x(v).$$

Lean: `New.classSum_deltaForm` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The hypothesis on $L$ gives $L_y(\delta_{x,v}(y)) = \#T(x, y)\, L_x(v)$. Only the class of $x$ has $T(x, y)$ nonempty, and there $\#T(x, y) = \#(e(\Gamma) \cap yKy^{-1})$ cancels the weight of the class. $\square$

### Free levels and dimension

A level $K$ is *free* for $e(\Gamma)$ if every stabilizer $e(\Gamma) \cap gKg^{-1}$ is trivial.

**Theorem (Forms at a free level).** Let $K$ be free for $e(\Gamma)$ and let $r$ be a system of representatives of $e(\Gamma) \backslash G / K$. Then the map $\varphi \mapsto (\varphi(r(c)))_c$ is a linear isomorphism from the level space of $(K, \chi)$ onto the space of functions $e(\Gamma) \backslash G / K \to W$. Its inverse sends $f$ to $\sum_c \delta_{r(c), f(c)}$. If $W$ has finite dimension, then
$$\dim \bigl(\text{level space of } (K, \chi)\bigr) = \#\bigl(e(\Gamma) \backslash G / K\bigr) \cdot \dim W.$$

Lean: `New.freeLevelEquiv`, `New.finrank_levelSpace_smoothFormRep` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* At a free level $T(r(c), r(d))$ is $\{1\}$ if $c = d$ and empty otherwise, so the sum takes the value $f(d)$ at $r(d)$. Apply the lemma. $\square$

So at a free level, which the argument shows case by case, the forms are exactly the $W$-valued functions on the class set.

**Example.** For $K$ free of class number $h$ and $W = \mathbb{C}$, the dimension is $h$, the delta forms $\delta_{r(c), 1}$ are the indicators of the classes, and each has class sum $1$.

### The invariant inner product

**Definition (Pairing of forms).** Let $B$ be a form on $\mathbb{C}^I$, sesquilinear for a ring map $\sigma$ in the first variable, with $B(\rho_{V,\kappa}(\gamma) v, \rho_{V,\kappa}(\gamma) v') = B(v, v')$ for all $\gamma \in U(J)(E)$. For algebraic forms $\varphi$, $\varphi'$ of weight $\kappa$ on $V$, the *pairing* is the class integral at $(\Gamma_{V,f}, K_0)$ of the invariant function $g \mapsto B(\varphi(g), \varphi'(g))$:
$$\langle \varphi, \varphi' \rangle_B = I_{\Gamma_{V,f}, K_0}\bigl(g \mapsto B(\varphi(g), \varphi'(g))\bigr).$$
It is invariant under right translation by every $a \in G_f$.

Lean: `New.smoothPairing`, `New.smoothPairing_formTranslation` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

The class integral is the integral over $\Gamma_{V,f} \backslash G_f$ with $\operatorname{vol}(K_0) = 1$ (Section 3).

**Theorem (Unitarity).** For a definite space $V$ and a weight $\kappa$, the algebraic forms of weight $\kappa$ on $V$ carry a positive definite hermitian form that is invariant under right translation by $G_f$.

Lean: `New.Space.exists_isUnitary_formTranslation` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* Take the pairing with the Gram form for which $\rho_\kappa$ is unitary ([Weyl modules](/chapter/weyl-modules/)). For $\varphi \neq 0$, $B(\varphi(g), \varphi(g))$ is $\ge 0$ and somewhere positive, so its class integral is positive by the positivity lemma of Section 3. $\square$

**Remark (Formalization).** The theorem states only that some invariant positive definite form exists; it does not record that it is the pairing with the Gram form. The spectral theorem of Section 8 needs only the existence.

### Where the argument uses algebraic forms

Delta forms are used in [character lifts and tested forms](/chapter/character-lifts/), [Hecke values](/chapter/hecke-values/), [deep level Poincaré series](/chapter/deep-level-poincare/) and [short columns and the gain](/chapter/short-columns-gain/). Free levels are used in [divisibility](/chapter/divisibility/), [archimedean size](/chapter/archimedean-size/), [Poincaré series](/chapter/poincare-series/) and [the proof of Theorem B](/chapter/proof-of-theorem-b/). Pairings are used in [character lifts and tested forms](/chapter/character-lifts/) and [Hecke values](/chapter/hecke-values/). Unitarity is used in [the denominator bound](/chapter/denominator-bound/) and in Section 8.
