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

This section treats the forms that the argument counts. On a definite space the group $G_\infty$ is compact, and an automorphic form is a vector valued function on the finite set $\Gamma_{V,f} \backslash G_f / K$. These are the algebraic modular forms of Gross (Section 2). The source defines them, builds the forms supported on one double coset, computes the dimension at a free level, and puts an invariant inner product on them. All proofs are finite sums.

Throughout, $V = (J, x)$ is a space with all signs $+1$, so $V$ is definite at every infinite place, and $\Gamma_{V,f}$ is the image of $U(J)(E)$ in $G_f$ under $\gamma \mapsto (x^{-1}\gamma x)_f$. This map is injective. The standard definite space is $I_n$, with $J = 1$ and $x = 1$, as in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

### Smooth forms

The source first works with any topological group.

**Definition (Smooth form).** Let $G$ be a topological group, $\Gamma$ a group, $e : \Gamma \to G$ a homomorphism, and $\rho$ a representation of $\Gamma$ on a complex vector space $W$. A *smooth form* for $(e, \rho)$ is a function $\varphi : G \to W$ such that $\varphi(e(\gamma)\, g) = \rho(\gamma)\, \varphi(g)$ for all $\gamma \in \Gamma$ and $g \in G$, and such that the subgroup of $k \in G$ with $\varphi(gk) = \varphi(g)$ for all $g$ is open. The smooth forms make up a complex vector space, and $G$ acts on it by right translation.

Lean: `New.SmoothForm`, `New.smoothFormRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

For a subgroup $K$ of $G$ and a character $\chi$ of $K$, the level space of $(K, \chi)$ (Section 3) is the space of smooth forms with $\varphi(gk) = \chi(k)\varphi(g)$ for $k \in K$. Gross's space $M(\rho, K)$ is the level space of $(K, 1)$.

### Weights and algebraic forms

The coefficients of the source's forms are the irreducible algebraic representations of $\mathrm{GL}_n$, one at each infinite place, in an explicit basis. [Weyl modules](/chapter/weyl-modules/) constructs them.

**Definition (Weight).** A *weight* for $E$ is a pair $\kappa = (\kappa_1, \kappa_2)$. For each infinite place $\tau$ of $E$ and each $h \ge 1$, $\kappa_1(\tau, h)$ is the number of columns of height $h$ of a Young diagram, and $\kappa_2(\tau)$ is an integer, the power of the determinant.

Lean: `New.Weight` (Lib/GaloisRep/Main/Defs.lean).

For a weight, the coordinate vectors $\mathbb{C}^{I}$, with $I$ the product over $\tau$ of the sets of standard fillings of the diagram $\kappa_1(\tau, \cdot)$ with entries in $n$, carry the Weyl module of $\mathrm{GL}_n$ at each place, twisted by $\det^{\kappa_2(\tau)}$. The group $\prod_\tau U(\operatorname{diag} s)$ acts on $\mathbb{C}^I$ by letting each component act through its entrywise complex conjugate. For signs all $+1$, the conjugate of a unitary matrix is its inverse transpose. This is the *conjugate Weyl representation* $\rho_\kappa$.

Lean: `New.conjWeylRep` (Lib/GLn/SchurModule/SchurOrthogonality.lean).

**Definition (Weight representation).** For a space $V$, the *weight representation* $\rho_{V,\kappa}$ of $U(J)(E)$ on $\mathbb{C}^I$ sends $\gamma$ to $\rho_\kappa$ of the infinite part of $x^{-1}\gamma x$.

Lean: `New.Space.weightRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

**Definition (Algebraic form).** Let $V$ be a definite space and $\kappa$ a weight. An *algebraic form of weight $\kappa$* on $V$ is a smooth form on $G_f$ for the embedding of $U(J)(E)$ in $G_f$ and the representation $\rho_{V,\kappa}$. So it is a function $\varphi : G_f \to \mathbb{C}^I$ with an open right stabilizer and
$$\varphi(\gamma g) = \rho_{V,\kappa}(\gamma)\, \varphi(g) \qquad \text{for } \gamma \in \Gamma_{V,f},\ g \in G_f.$$
The group $G_f$ acts on these forms by right translation. On the standard space $I_n$, the source writes the same space with the two parts of the weight as separate arguments.

Lean: `New.Space.forms`, `New.Space.formTranslation`, `New.AlgForm`, `New.algFormRep` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

This is Gross's definition (Section 2) with $\mathbf{G} = U(J)$ over $F$, with $\mathbf{G}(F_\infty)$ compact, and $W$ the restriction of an algebraic representation of $\mathbf{G}(F \otimes \mathbb{C}) = \prod_\tau \mathrm{GL}_n(\mathbb{C})$. Gross fixes the level in the definition. The source takes all forms with some open level and recovers Gross's space as a level space.

**Remark.** For a unitary matrix $u$, the entrywise conjugate is $(u^{T})^{-1}$. So $\rho_\kappa$ is the contragredient of the Weyl module of $\kappa$, restricted to the compact group. Gross allows any algebraic representation $W$, so this is a case of his definition. A reader who compares formulas with a text that uses the Weyl module itself must replace each weight by its dual.

### Values on representatives

**Lemma.** Let $\varphi$ be a smooth form in the level space of $(K, \chi)$. Then $\varphi(e(\gamma)\, g\, k) = \chi(k)\, \rho(\gamma)\, \varphi(g)$ for $\gamma \in \Gamma$, $g \in G$ and $k \in K$. Let $r$ be a system of representatives of $e(\Gamma) \backslash G / K$. Two forms in the level space that agree at every $r(c)$ are equal. So the map $\varphi \mapsto (\varphi(r(c)))_c$ is injective.

Lean: `New.levelSpace_smoothFormRep_apply`, `New.levelSpace_ext_doubleCosets`, `New.evalClassReps`, `New.evalClassReps_injective` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The first identity combines the two transformation rules. Every $y \in G$ is $e(\gamma)\, r(c)\, k$ for some class $c$, some $\gamma$ and some $k$. By the first identity, the value at $y$ is fixed by the value at $r(c)$. $\square$

**Theorem (Finite dimension).** Let $(e(\Gamma), K)$ have finite type (Section 3), let $\chi$ be a character of $K$, and let $W$ have finite dimension. Then the level space of $(K, \chi)$ has finite dimension. For a definite space $V$, a weight $\kappa$, an open subgroup $K$ of $G_f$ and a character $\chi$ of $K$, the level space of $(K, \chi)$ in the algebraic forms of weight $\kappa$ on $V$ has finite dimension.

Lean: `New.finite_levelSpace_smoothFormRep` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean); `New.Space.finite_formTranslation_levelSpace` (same file).

*Proof.* By the lemma, the level space embeds in $W^{\Gamma \backslash G / K}$, a finite sum of copies of $W$. For the second part, $K \cap K_0$ is a level, so $(\Gamma_{V,f}, K \cap K_0)$ has finite type ([reduction theory](/chapter/reduction-theory/)). Let $\chi'$ be the restriction of $\chi$ to $K \cap K_0$. The level space of $(K, \chi)$ lies in the level space of $(K \cap K_0, \chi')$, which has finite dimension by the first part. $\square$

The proof does not give the theorem of Section 5. On an indefinite group the set $\Gamma_V \backslash G / (G_\infty K)$ is still finite, but a form is not fixed by its values at finitely many points, since $G_\infty$ is not compact.

### Forms supported on one class

Let $e$ be injective and $(e(\Gamma), K)$ of finite type, and let $\chi$ be trivial near $1$.

**Definition (Transporter).** For $x, y \in G$, the *transporter* $T(x, y)$ is the set of $\gamma \in \Gamma$ with $x^{-1} e(\gamma) y \in K$. It is finite. Its number of elements is $\#(e(\Gamma) \cap xKx^{-1})$ if $x$ and $y$ lie in the same double coset, and $0$ otherwise.

Lean: `New.transporter`, `New.mem_transporter`, `New.card_transporter` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

**Remark (Formalization).** The finite set `New.transporter` is defined by `choose` from the transporter lemma of Section 3. A finite set is fixed by its elements, and `New.mem_transporter` gives them. So the choice does not affect any value.

**Definition (Delta form).** For $x \in G$ and $v \in W$, the *delta form* $\delta_{x,v}$ is
$$\delta_{x,v}(y) = \sum_{\gamma \in T(x, y)} \chi(x^{-1} e(\gamma) y)\; \rho(\gamma^{-1})\, v.$$
It lies in the level space of $(K, \chi)$, it is $0$ outside the double coset $e(\Gamma)\, x\, K$, and it depends linearly on $v$.

Lean: `New.deltaForm`, `New.deltaForm_apply` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The set $T(x, e(\gamma') y)$ is $T(x, y)\, \gamma'^{-1}$. Reindex the sum by $\gamma = \gamma'' \gamma'^{-1}$: the term becomes $\chi(x^{-1} e(\gamma'') y)\, \rho(\gamma')\rho(\gamma''^{-1}) v$. So $\delta_{x,v}(e(\gamma') y) = \rho(\gamma')\, \delta_{x,v}(y)$. Right translation by $k \in K$ maps $T(x, y)$ to $T(x, yk)$ and multiplies each term by $\chi(k)$. A function on which $K$ acts by a character that is trivial near $1$ has an open stabilizer, since $K$ is open. If $y$ is not in $e(\Gamma) x K$, then $T(x, y)$ is empty. $\square$

At $y = x$ the value is $\sum_{\gamma \in \Gamma_x} \chi(x^{-1} e(\gamma) x)\, \rho(\gamma^{-1}) v$, where $\Gamma_x$ is the stabilizer of $x$. For $\chi = 1$ this is $\#\Gamma_x$ times the projection of $v$ to the $\Gamma_x$-fixed vectors. So the delta forms at $x$ realize the summand $W^{\Gamma_x}$ of Gross's decomposition (Section 2).

**Proposition (Class sum of a delta form).** For each $g \in G$ let $L_g : W \to \mathbb{C}$ be additive, with $L_{e(\gamma) x k}(\chi(k) \rho(\gamma) v) = L_x(v)$ for all $\gamma \in \Gamma$, $k \in K$, $v \in W$ and $x \in G$. Then
$$\Sigma_{\Gamma, K}\bigl(g \mapsto L_g(\delta_{x,v}(g))\bigr) = L_x(v).$$

Lean: `New.classSum_deltaForm` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* Write the class sum over $e(\Gamma)\backslash G/K$ with a representative $y$ of each class. The hypothesis on $L$, applied with $e(\gamma)^{-1}$ and $k = x^{-1} e(\gamma) y$, gives $L_y(\chi(k) \rho(\gamma^{-1}) v) = L_x(v)$ for each $\gamma \in T(x, y)$. So $L_y(\delta_{x,v}(y)) = \#T(x, y)\, L_x(v)$. Only the class of $x$ has $T(x, y)$ nonempty, and there $\#T(x, y) = \#(e(\Gamma) \cap yKy^{-1})$, which cancels the weight of the class. $\square$

This is the way the argument evaluates a linear functional on a form. A functional given by a pairing that is invariant in the sense of the hypothesis takes the value $L_x(v)$ on the delta form at $x$ made from $v$.

### Free levels and dimension

A level $K$ is *free* for $e(\Gamma)$ if every stabilizer $e(\Gamma) \cap gKg^{-1}$ is trivial.

**Theorem (Forms at a free level).** Let $K$ be free for $e(\Gamma)$ and let $r$ be a system of representatives of $e(\Gamma) \backslash G / K$. Then the map $\varphi \mapsto (\varphi(r(c)))_c$ is a linear isomorphism from the level space of $(K, \chi)$ onto the space of functions $e(\Gamma) \backslash G / K \to W$. Its inverse sends $f$ to $\sum_c \delta_{r(c), f(c)}$. If $W$ has finite dimension, then
$$\dim \bigl(\text{level space of } (K, \chi)\bigr) = \#\bigl(e(\Gamma) \backslash G / K\bigr) \cdot \dim W.$$

Lean: `New.freeLevelEquiv`, `New.finrank_levelSpace_smoothFormRep` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* At a free level $T(r(c), r(d))$ is $\{1\}$ if $c = d$ and empty otherwise. So $\sum_c \delta_{r(c), f(c)}$ takes the value $f(d)$ at $r(d)$. The two maps are inverse to each other by the lemma on values at representatives. $\square$

So at a free level the source's space of algebraic forms is exactly the space of $W$-valued functions on the finite set $\Gamma_{V,f} \backslash G_f / K$, and its dimension is the class number of $K$ times $\dim W$. With $\chi = 1$ and $W = \mathbb{C}$, it is the space of functions on the class set. In Gross's decomposition every $\Gamma_i$ is trivial and every $W^{\Gamma_i}$ is $W$.

**Example.** Let $K$ be free and of class number $h$, and let the weight be trivial, so $W = \mathbb{C}$. Then the level space has dimension $h$, and the delta forms $\delta_{r(c), 1}$ are the indicator functions of the classes. The proposition on class sums, with $L_g$ the identity, gives $\Sigma_{\Gamma,K}(\delta_{r(c),1}) = 1$, and the class sum of the constant function $1$ is $h$, as in the lemma of Section 3 on free levels.

The theorem does not say which levels are free. The argument applies it at levels that it shows to be free, and the dimension count enters the size estimates of Theorem A and the count of forms in Theorem B.

### The invariant inner product

**Definition (Pairing of forms).** Let $B$ be a form on $\mathbb{C}^I$, sesquilinear for a ring map $\sigma$ in the first variable, with $B(\rho_{V,\kappa}(\gamma) v, \rho_{V,\kappa}(\gamma) v') = B(v, v')$ for all $\gamma \in U(J)(E)$. For algebraic forms $\varphi$, $\varphi'$ of weight $\kappa$ on $V$, the function $g \mapsto B(\varphi(g), \varphi'(g))$ is left $\Gamma_{V,f}$-invariant and has an open stabilizer. The *pairing* is its class integral at $(\Gamma_{V,f}, K_0)$:
$$\langle \varphi, \varphi' \rangle_B = I_{\Gamma_{V,f}, K_0}\bigl(g \mapsto B(\varphi(g), \varphi'(g))\bigr).$$
It is invariant under right translation by every $a \in G_f$.

Lean: `New.smoothPairing`, `New.smoothPairing_formTranslation` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

The class integral is the integral over $\Gamma_{V,f} \backslash G_f$ for the measure with $\operatorname{vol}(K_0) = 1$ (Section 3). Its invariance under right translation is the invariance of that measure.

**Theorem (Unitarity).** For a definite space $V$ and a weight $\kappa$, the algebraic forms of weight $\kappa$ on $V$ carry a positive definite hermitian form that is invariant under right translation by $G_f$.

Lean: `New.Space.exists_isUnitary_formTranslation` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* Take $B$ the Gram form of $\mathbb{C}^I$ for which $\rho_\kappa$ is unitary ([Weyl modules](/chapter/weyl-modules/)), and the pairing above. It is invariant. For $\varphi \neq 0$, the function $f(g) = B(\varphi(g), \varphi(g))$ is $\ge 0$ and positive at some $g$. Its class integral is a positive multiple of its class sum at the level $K_0 \cap \operatorname{Stab}(\varphi)$, which is positive by the positivity lemma of Section 3. $\square$

**Remark (Formalization).** The theorem states only that some invariant positive definite form exists. The form is the pairing with the Gram form, but the statement does not record this. The argument uses the theorem to apply the spectral theorem to commuting normal operators (Section 8), and for this only the existence matters.

### Where the argument uses these objects

The delta forms and their class sums appear in [false lifts](/chapter/false-lifts/), in [deep level Poincaré series](/chapter/deep-level-poincare/) and in [archimedean size](/chapter/archimedean-size/). The isomorphism at a free level and the dimension formula are used in [divisibility](/chapter/divisibility/), in [archimedean size](/chapter/archimedean-size/), in [Poincaré series](/chapter/poincare-series/) and in [the proof of Theorem B](/chapter/proof-of-theorem-b/). The pairings of forms appear in [false lifts](/chapter/false-lifts/) and [Hecke values](/chapter/hecke-values/). The unitarity theorem is used in [the denominator bound](/chapter/denominator-bound/) and, through the spectral theorem, in Section 8.
