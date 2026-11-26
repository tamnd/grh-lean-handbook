---
title: The bound for denominators
lean:
  - New/Congruences/FirstOrder/DenominatorBound.lean
decls:
  - New.Selmer.diagOp_toSmoothForm_typeProjection
  - New.Selmer.diagOp_typeProjection_eq_zero_of_mem_span
  - New.Selmer.exists_linearMap_eq_smul_mem_integralForms
  - New.Selmer.PreservesHeckeEigenspaces
  - New.Selmer.preservesHeckeEigenspaces_toLin_diagonal
  - New.Selmer.exists_operator_ellVal_le_liftValuationBound
  - New.Selmer.exp_le_norm_det_smul_of_ellVal_le
  - New.Selmer.exists_operator_det_clearingBound
  - New.Selmer.denominatorLe_clearingBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The bound for denominators

This section joins the operator at one base system to the forms. The operator $\mathrm{diagOp}(s)$ of [the operator at one base system](/chapter/denominator-bound/#the-operator-at-one-base-system) acts on algebraic forms of level $L$. Composed with $\mathrm{typeProjection}(c)$, it gives an operator $G$ on the forms of $O$ that has each lift generator as an eigenvector. One $G$ exists for each basis vector of $Z$, and an integral combination of them serves all basis vectors at once. Its determinant then gives the bound `DenominatorLe` that [the theorem and its plan](/chapter/theorem-and-plan/) uses.

### The operator for one lift generator

**Lemma.** Let $v$ be in the range of $\mathrm{typeProjection}(c)$ and nonzero in the system $x$ of level $L$. Then $\mathrm{diagOp}(s')\,(\mathrm{typeProjection}(c)\, v)^{\mathrm{alg}} = \iota_\ell^{-1}(s'(x))\, v^{\mathrm{alg}}$, with $v^{\mathrm{alg}}$ the algebraic form of $v$.

Lean: `New.Selmer.diagOp_toSmoothForm_typeProjection` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* $\mathrm{typeProjection}(c)$ fixes its range, and $\mathrm{diagOp}(s')$ scales the forms of $x$ by $\iota_\ell^{-1}(s'(x))$. $\square$

**Lemma.** Let the forms of type $c$ have base level, and let $s$ vanish at every system that contains a nonzero lift generator of $Z$. Then $\mathrm{diagOp}(s)\,(\mathrm{typeProjection}(c)\, z)^{\mathrm{alg}} = 0$ for every $z$ in the span of the lift generators.

Lean: `New.Selmer.diagOp_typeProjection_eq_zero_of_mem_span` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* The map is linear, so it is enough to take a lift generator $v$. By [the dichotomy](/decl/New.Selmer.IsLiftGenerator.typeProjection_eq_zero_or_mem_range/), either $\mathrm{typeProjection}(c)\, v = 0$, or $v$ is in the range and nonzero in a system $x$, which has level $L$ since the base level is contained in each level. In the second case the previous lemma gives $\iota_\ell^{-1}(s(x))\, v^{\mathrm{alg}} = 0$. $\square$

**Theorem (The operator for one lift generator).** Let $\vartheta$ be an auxiliary twist of cost $\mathrm{ram}$, let $\mathrm{sel} \neq \infty$, let $Z$ lie in the span of its lift generators for $\infty$, and let $v_0 \neq 0$ be a lift generator for $\mathrm{sel}$. Then there is a linear map $G$ from the forms of $O$ to algebraic forms such that:

- (a) every lift generator $v$ for $\infty$ has $G v = \mu\, v^{\mathrm{alg}}$ for some $\mu \in \mathbb{C}$;
- (b) if $G v_0 = \mu\, v_0^{\mathrm{alg}}$, then $\mathrm{ellVal}(\iota_\ell \mu) \leq \mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel})$;
- (c) if $y$ is integral at $\iota_\ell$ and orthogonal to the false lifts for $E$ and $Z^\perp$, then every form $w$ with $w^{\mathrm{alg}} = G(P_Z y)$ is integral at $\iota_\ell$.

Lean: `New.Selmer.exists_linearMap_eq_smul_mem_integralForms` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $A$ be the set of lift generators for $\infty$; then $Z = \operatorname{span} A$. Let $\mathcal{X}$ be the set of systems in which some $v \in A$ is nonzero. Take a lift setting $c$ of $v_0$. Since $\mathrm{typeProjection}(c)\, v_0 = v_0 \neq 0$, the dichotomy gives a system $x_0$ in which $v_0$ is nonzero. [The base level](/decl/New.Selmer.exists_baseLevel/) gives base data $B$ such that the forms of type $c$ have base level, $N\, \mathrm{typeProjection}(c)$ keeps integral forms, and the systems at every good level are of type $c$ with the quadratic relation. So $x_0 \in \mathcal{X}$ and $x_0$ is a system of base level.

Every system in $\mathcal{X}$ lifts with a twisted lattice for $x_0$ and $\mathrm{sel}$, by [lifts with twisted lattices](/decl/New.Selmer.IsLiftGenerator.exists_isMainSummandLike_hasTwistedLattice/). [The operator at one base system](/decl/New.Selmer.exists_ellVal_le_and_diagOp_mem_ellIntegralForms/) gives $L$ and $s$. Put
$$G = N^2\, \mathrm{diagOp}(s) \circ (\cdot)^{\mathrm{alg}} \circ \mathrm{typeProjection}(c).$$

(a) By the dichotomy, $G v = 0$ or $G v = N^2 \iota_\ell^{-1}(s(x))\, v^{\mathrm{alg}}$ by the first lemma.

(b) At $v_0$ the eigenvalue is $\mu = N^2 \iota_\ell^{-1}(s(x_0))$, since $v_0^{\mathrm{alg}} \neq 0$. So $\iota_\ell \mu = N^2 s(x_0)$, and part (a) of the operator at one base system bounds its valuation.

(c) Apply part (b) of the operator at one base system with $l = \mathrm{typeProjection}(c)\, y$ and the form $\mathrm{typeProjection}(c)(P_Z y)$. The form $N l$ is integral by the choice of $B$ and [integral forms](/decl/New.Selmer.mem_integralForms_ofIso_iff/). The form $P_Z y$ lies in the span of $A$, so the second lemma gives the support condition on $\mathcal{X}$. For the agreement, let $s'$ vanish at the base systems that are not weak lifts, and let $M = \ker(\mathrm{diagOp}(s') \circ (\cdot)^{\mathrm{alg}})$. A form of type $c$, nonzero in $x$ and not in $M$, has $s'(x) \neq 0$, so $x$ is a weak lift. [Agreement off the weak lifts](/decl/New.Selmer.typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts/) gives $\mathrm{typeProjection}(c)(y - P_Z y) \in M$, which is the agreement. Here $Z$ is stable under the Hecke operators and $\mathrm{typeProjection}(c)$ since it is the span of $A$. So $N \cdot N \cdot \mathrm{diagOp}(s)\,(\mathrm{typeProjection}(c) P_Z y)^{\mathrm{alg}} = G(P_Z y)$ is integral. $\square$

### The operator on $Z$

**Definition.** An operator $\Lambda$ on $Z$ *preserves the Hecke eigenspaces* if, for every split place $w$ off the places of $O$ and their conjugates and all $\xi, a \in \mathbb{C}$, $\mathrm{heckePolyOnForms}_w(\xi)\, z = a z$ implies $\mathrm{heckePolyOnForms}_w(\xi)\, \Lambda z = a\, \Lambda z$.

Lean: `New.Selmer.PreservesHeckeEigenspaces` (New/Congruences/FirstOrder/DenominatorBound.lean).

**Lemma.** Let $b$ be a basis of $Z$ of forms with lift Hecke polynomials. An operator diagonal in $b$ preserves the Hecke eigenspaces.

Lean: `New.Selmer.preservesHeckeEigenspaces_toLin_diagonal` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Each $b_k$ is an eigenvector of each Hecke operator, so on $Z$ the Hecke operator $T$ is diagonal in $b$. Two diagonal operators commute. If $Tz = az$, then $T \Lambda z = \Lambda T z = a \Lambda z$. $\square$

**Theorem (Bound for denominators).** Let $\vartheta$ be an auxiliary twist of cost $\mathrm{ram}$, let $\mathrm{sel} \neq \infty$, and let $Z$ lie in the span of its lift generators for $\mathrm{sel}$. Then there is an operator $\Lambda$ on $Z$ such that:

- (a) $\Lambda$ preserves the Hecke eigenspaces;
- (b) every eigenvalue $\mu$ of $\Lambda$ has $\mathrm{ellVal}(\iota_\ell \mu) \leq \mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel})$;
- (c) for every $y$ integral at $\iota_\ell$ and orthogonal to the false lifts for $E$ and $Z^\perp$, the form $\Lambda(P_Z y)$ is integral at $\iota_\ell$.

Lean: `New.Selmer.exists_operator_ellVal_le_liftValuationBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Choose lift generators $\omega_k$, $k < \dim Z$, that form a basis $b$ of $Z$. A lift generator for $\mathrm{sel}$ is one for $\infty$, so the previous theorem applies to each $\omega_k$. It gives $G_k$ with $G_k \omega_p = \mathrm{eig}(k, p)\, \omega_p^{\mathrm{alg}}$ for all $p$, and $\mathrm{ellVal}(\iota_\ell\, \mathrm{eig}(k,k)) \leq \mathrm{liftValuationBound}$.

Call an operator on $Z$ *good* if it has property (c). The operator $D_k$, diagonal in $b$ with entries $\mathrm{eig}(k, \cdot)$, has $(D_k z)^{\mathrm{alg}} = G_k z$ on the basis, so on all of $Z$. So $D_k$ is good by part (c) of the previous theorem. A combination $\sum_p \iota_\ell^{-1}(d_p)\, G'_p$ of good operators with $\|d_p\| \leq 1$ is good, since integral forms form a module over the integral elements.

[The diagonal lemma](/decl/New.Selmer.exists_diagonal_mem_norm_ge/) gives a good operator $\Lambda$, diagonal in $b$ with entries $\mu_k$, such that $\|\iota_\ell \mu_k\| \geq \|\iota_\ell\, \mathrm{eig}(k, k)\|$ for every $k$. It takes an integral point $d$ at which each linear form $\sum_p \mathrm{eig}(p, k) X_p$ has norm at least that of each coefficient. Then (a) is the previous lemma. For (b), an eigenvalue of $\Lambda$ is some $\mu_k$, and $\mathrm{ellVal}(\iota_\ell \mu_k) \leq \mathrm{ellVal}(\iota_\ell\, \mathrm{eig}(k,k)) \leq \mathrm{liftValuationBound}$. $\square$

**Lemma.** Let $Z$ be finite dimensional, $N \in \mathbb{N}$ and $B \geq 0$. If $\mathrm{ellVal}(N \iota_\ell \mu) \leq B$ for every eigenvalue $\mu$ of $\Lambda$, then
$$\exp(-\dim Z \cdot B \log \ell) \leq \|\iota_\ell \det(N \Lambda)\|.$$

Lean: `New.Selmer.exp_le_norm_det_smul_of_ellVal_le` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* $\det(N\Lambda) = N^{\dim Z} \det \Lambda$, and $\det \Lambda$ is the product of the eigenvalues with multiplicity, over $\mathbb{C}$. Each factor $N \iota_\ell \mu$ has norm at least $\ell^{-B} = \exp(-B \log \ell)$. $\square$

**Theorem (The determinant with the clearing bound).** Let $\vartheta$ be an auxiliary twist of cost $e'_\ell = \mathrm{twistError}(\ell, D)$, and let $Z$ lie in the span of its lift generators for $e'_\ell$. Then there is an operator $\Lambda$ on $Z$ such that:

- (a) $\exp(-\dim Z \cdot \#r \cdot \beta_\ell \log \ell) \leq \|\iota_\ell \det \Lambda\|$, with $\beta_\ell = \mathrm{clearingBound}(D, \ell)$;
- (b) for every $y'$ integral at $\iota_\ell$ and orthogonal to the false lifts, $\Lambda(P_Z y')$ is integral at $\iota_\ell$;
- (c) for such $y'$ and every $y$ integral at all $\ell$-adic places, $\|\iota_\ell \langle y, \Lambda(P_Z y') \rangle\| \leq 1$.

Lean: `New.Selmer.exists_operator_det_clearingBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* If every lift generator is $0$, then $Z = 0$ and $\Lambda = 1$ serves: its determinant is $1$ and $P_Z y' = 0$. Otherwise take a nonzero lift generator and its lift setting $c$. The lift setting gives $1 \leq \#r \leq r$ and $t' \leq t$. So [the budget](/decl/New.Selmer.add_denominatorError_le_mul_clearingBound/) gives
$$\mathrm{liftValuationBound}(\ell, O, e'_\ell, e'_\ell) + v \leq \#r \cdot \beta_\ell.$$
Let $\Lambda_0$ come from the bound for denominators, with $\mathrm{ram} = \mathrm{sel} = e'_\ell$, which is finite, and put $\Lambda = N \Lambda_0$.

(a) For an eigenvalue $\mu$ of $\Lambda_0$, $\mathrm{ellVal}(N \iota_\ell \mu) \leq v + \mathrm{liftValuationBound} \leq \#r \beta_\ell$. Apply the previous lemma with $B = \#r \beta_\ell$.

(b) An integer multiple of an integral form is integral.

(c) The class stabilisers of the standard lattice have orders dividing $N$, since the rank $\#n$ is at most $2 n(m)$ by the lift setting (`New.Data.card_classAut_dvd_chosenGroupOrder`, [chains and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels)). So $N$ times the inner product of two integral forms is integral (`New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one`, [the $p$-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). Apply this to $y$ and $\Lambda_0(P_Z y')$. $\square$

**Remark (Formalization).** In case $Z = 0$ the operator is the identity of the zero space and the bound (a) reads $1 \leq 1$.

**Theorem (Denominators for a good twist).** Let $\iota$ be an isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, $\vartheta$ an auxiliary twist of cost $e'_\ell$ for the avatar at $\iota$, and $Z$ in the span of its lift generators for $e'_\ell$. Then `DenominatorLe` holds for $\iota$, $O$, $E$, $Z$ and the exponent $\beta_\ell \log \ell$: some operator $\Lambda$ on $Z$ has $\exp(-\dim Z \cdot \#r \cdot \beta_\ell \log \ell) \leq \|\iota \det \Lambda\|$, and it takes $P_Z y$, for $y$ integral at $\iota$ and orthogonal to the false lifts, to a form integral at $\iota$ whose pairings with the forms integral at all $\ell$-adic places are integral.

Lean: `New.Selmer.denominatorLe_clearingBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* This is the previous theorem, with the order of the two forms in (c) as in the definition of `New.Selmer.DenominatorLe` ([tested forms](/chapter/character-lifts/#point-forms-and-tested-forms)). $\square$
