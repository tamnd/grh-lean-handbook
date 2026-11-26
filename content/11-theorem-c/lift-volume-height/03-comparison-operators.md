---
title: Comparison operators
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.IsComparisonOperator
  - New.Data.comparisonOp
  - New.Data.heckeValueProd_div_eq
  - New.Data.adjoint_glue_goodLift
  - New.Data.inner_goodLift_comparisonOp
  - New.Data.isOrthogonalToFalseLifts_comparisonOp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Comparison operators

This section defines a comparison operator and the operator $U_\vartheta$ of the source. It then proves three facts about $U_\vartheta$ on the lifts: a formula for the ratio of Hecke values, a formula for the inner products $\langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle$, and the orthogonality of $U_\vartheta z$ to the false lifts for every lift $z$. These are three of the five properties. Sections 4 and 5 prove the other two.

### Notation

Fix the data $D$ and $1 \leq j \leq m$ (`j : D.LiftIndex`). For a twist $\vartheta$ let $\mathcal{F}_\vartheta$ be the space of forms on $V_j$ of the lift datum at $\vartheta$ (`(D.descentPair ϑ j).FormV`), and let $\Theta_\vartheta = $ `D.goodLift ϑ j` be the good lift from the good forms on $W_j$ to $\mathcal{F}_\vartheta$. The good forms on $W_j$ are the range of the central idempotent $e_0$ (`D.goodForms (D.spaceW j)`). The *lifts* are the range $L_\vartheta$ of $\Theta_\vartheta$, and $L_\vartheta^\perp$ is its orthogonal complement.

*Hecke values.* The product of Hecke values of the lift is

$$\mathrm{HV}_j(\vartheta) = \prod_{i}\,\mathrm{lValueProd}\big(S\cup Q(\vartheta),\,(\nu_i\,\vartheta^{s_i})^{-1},\,z_i\big),$$

over the three pairs $(\nu_i, z_i)$ of the exchange pair of $j$, with exponent $s_i = 1$ for the first pair and $s_i = \pm 1$, the sign, for the other two. The product is real, and Lean casts it to $\mathbb{C}$. Lean: `New.Data.heckeValueProd` (New/OneLift/ComparisonOperator/ThreeExchanges.lean), from [the comparison operator, part 2](/chapter/comparison-operator-2/). Each factor is a product of norms of places and squared absolute values of partial Hecke $L$-values at integers. The *ratio* is

$$\rho_j(\vartheta) = \mathrm{HV}_j(\vartheta)/\mathrm{HV}_j(1).$$

*False lifts.* A form $y \in \mathcal{F}_\vartheta$ is *orthogonal to the false lifts* if $y \perp \mathrm{FL}_w(e_0, L_\vartheta^\perp)$ for every split place $w$ off the places of the datum and their conjugates. Here $\mathrm{FL}_w(e_0, Z) = \mathrm{range}(e_0)\cap\ker H_w(x_w)\cap Z$, with the Hecke polynomial $H_w$ and its root $x_w$ ([character lifts](/chapter/character-lifts/#point-forms-and-tested-forms)). Lean: `New.DescentPair.IsOrthogonalToFalseLifts` (New/OneLift/TestedForms.lean).

*Integral forms and squared norms.* For an $\ell$-adic place $\iota$ the integral forms at $\iota$ and the squared norm $\|\varphi\|_\sigma^2$ at $\sigma \in \mathrm{Aut}(\mathbb{C})$ are those of Section 2.

*Sizes.* Put $A = f m b\log^2 b$, where $f$ is the number of infinite places, $m$ the number of lifts and $b$ the weight scale ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)).

### The definition

**Definition (Comparison operator).** A family $U = (U_\vartheta)$ of operators $U_\vartheta$ on $\mathcal{F}_\vartheta$, one for each twist $\vartheta$, is a *comparison operator* for $j$ if it has five properties.

1. (`ratio_ne_zero`) $\rho_j(\vartheta) \neq 0$ for every twist $\vartheta$.
2. (`exists_inner_eq`) There is an operator $U^\circ$ on the good forms on $W_j$ with $\langle y, U^\circ y\rangle > 0$ for every $y \neq 0$, such that for every twist $\vartheta$ and all good forms $y'$, $y$,
$$\langle\Theta_\vartheta y', U_\vartheta\,\Theta_\vartheta y\rangle = \rho_j(\vartheta)\,\langle y', U^\circ y\rangle .$$
3. (`isOrthogonalToFalseLifts`) For every twist $\vartheta$ and every $z \in L_\vartheta$, the form $U_\vartheta z$ is orthogonal to the false lifts for $e_0$ and $L_\vartheta^\perp$.
4. (`mem_integralForms`) For every twist $\vartheta$, every prime $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$ and every $\ell$-adic place $\iota$, $U_\vartheta$ maps the integral forms at $\iota$ into the integral forms at $\iota$.
5. (`normSqAt_le`) For every $\varphi \in \mathcal{F}_1$ and every $\sigma$, $\|U_1\varphi\|_\sigma^2 \leq \exp(3A)^2\,\|\varphi\|_\sigma^2$.

Lean: `New.Data.IsComparisonOperator` (New/OneLift/LiftVolumeHeight.lean).

The ratio in property 2 is the number $\rho_j(\vartheta)$ itself, not an arbitrary scalar. This is how the Hecke values enter the height bound. Property 2 at $\vartheta = 1$ reads $\langle\Theta_1 y', U_1\Theta_1 y\rangle = \rho_j(1)\langle y', U^\circ y\rangle$.

**Remark (Formalization).** In Lean $x/0 = 0$. So if $\mathrm{HV}_j(1) = 0$, then $\rho_j(\vartheta) = 0$ for every $\vartheta$, and property 2 would only say that $\langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle = 0$. Property 1 excludes this junk case: $\rho_j(1) \neq 0$ forces $\mathrm{HV}_j(1) \neq 0$, and then $\rho_j(1) = 1$. This is row F-072 of [the register of findings](/chapter/register-of-findings/). The source proves property 1 for its operator in Section 5, from the nonvanishing of the twist factor below.

### The operator of the source

The construction uses the gluing maps of [the comparison operator, part 2](/chapter/comparison-operator-2/). We state the facts we use, each in one line.

- There is a space $\mathcal{T}_j$ of *tuples* of forms on the definite space $V^\circ$ (`New.Data.FormTuples j`): one value in the Weyl module of the diagram $\mu^-$ for each pair $b = (i, c)$ of a choice $i$ and a class $c$ of $V^\circ$, with the inner product $\langle\zeta, \zeta'\rangle = \sum_b\langle\zeta_b, \zeta'_b\rangle_{\mathrm{Gram}}$.
- For each twist there is a linear *gluing map* $\mathrm{glue}_\vartheta \colon \mathcal{T}_j \to \mathcal{F}_\vartheta$ (`New.Rows.glue`).
- The *twist factor* $c'_\vartheta \in \mathbb{C}$ (`New.Rows.twistFactor`) is chosen so that the seesaw identity $c'_\vartheta\,\mathrm{glue}_\vartheta^*\,\Theta_\vartheta = \Theta^\circ$ holds, with a map $\Theta^\circ$ from the good forms to $\mathcal{T}_j$ that does not depend on $\vartheta$ (`New.Rows.twistFactor_smul_adjoint_glue_comp`). The map $\Theta^\circ$ is `New.Rows.periodLift`, defined as $c'_1\,\mathrm{glue}_1^*\,\Theta_1$.
- There is a constant $C_0 \in \mathbb{C}$, possibly $0$, with $|c'_\vartheta|^2 = C_0/\mathrm{HV}_j(\vartheta)$ for every $\vartheta$ (`New.Rows.exists_norm_twistFactor_sq_eq`).
- $c'_\vartheta \neq 0$ for every $\vartheta$ (`New.Rows.twistFactor_ne_zero`), and $\Theta^\circ$ is injective (`New.Rows.periodLift_injective`).
- For every good form $y$, the form $\mathrm{glue}_\vartheta(\Theta^\circ y)$ is orthogonal to the false lifts for $e_0$ and $L_\vartheta^\perp$ (`New.Rows.isOrthogonalToFalseLifts_glue_periodLift`).

Let $h_j$ be the hook number of the diagram $\mu^-$, the weight of the forms on $V^\circ$ (`New.Rows.hookNumberMinus`), a positive integer ([Weyl modules](/chapter/weyl-modules/)). Let $n_{\mathrm{Aut}}$ be the chosen group order, a positive integer divisible by the order of every stabilizer of a class ([chains of lifts and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels)).

**Definition (The comparison operator of the source).**

$$U_\vartheta = n_{\mathrm{Aut}}\,h_j^2\;\mathrm{glue}_\vartheta\circ\mathrm{glue}_\vartheta^* .$$

Lean: `New.Data.comparisonOp` (New/OneLift/LiftVolumeHeight.lean).

The operator $\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*$ is positive semidefinite on $\mathcal{F}_\vartheta$. The factor $n_{\mathrm{Aut}}h_j^2$ is there for integrality (Section 4). It clears the denominators of the inner products and the hook number of the frame.

**Remark (Formalization).** The twist factor is defined by `choose` from an existence statement of the second part. Nothing in this chapter depends on the choice. The proofs use only the seesaw identity, the formula for $|c'_\vartheta|^2$ and $c'_\vartheta \neq 0$. The constant $C_0$ of the formula may be $0$ as stated. It is not $0$, as the next proof shows.

### The ratio of Hecke values

**Lemma (The ratio as a ratio of twist factors).** For every twist $\vartheta$,

$$\rho_j(\vartheta) = \frac{|c'_1|^2}{|c'_\vartheta|^2}.$$

Lean: `New.Data.heckeValueProd_div_eq` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Take $C_0$ with $|c'_\vartheta|^2 = C_0/\mathrm{HV}_j(\vartheta)$ for every $\vartheta$. First $C_0 \neq 0$: if $C_0 = 0$, then $|c'_1|^2 = 0/\mathrm{HV}_j(1) = 0$, so $c'_1 = 0$, which contradicts $c'_1 \neq 0$. Then

$$\frac{|c'_1|^2}{|c'_\vartheta|^2} = \frac{C_0/\mathrm{HV}_j(1)}{C_0/\mathrm{HV}_j(\vartheta)} = \frac{\mathrm{HV}_j(\vartheta)}{\mathrm{HV}_j(1)} .$$

The last step is the identity $(C_0/a)/(C_0/b) = b/a$ for $C_0 \neq 0$. In Lean it holds for all $a$ and $b$, also when one of them is $0$, by the convention $x/0 = 0$. $\square$

**Remark (Formalization).** The proof also shows $\mathrm{HV}_j(\vartheta) \neq 0$ for every $\vartheta$. If $\mathrm{HV}_j(\vartheta) = 0$, then $|c'_\vartheta|^2 = C_0/0 = 0$, so $c'_\vartheta = 0$. The source does not state this separately. It enters through property 1.

### The adjoint on the lifts

**Lemma (The adjoint of the gluing map on the lifts).** For every twist $\vartheta$ and every good form $y$ on $W_j$,

$$\mathrm{glue}_\vartheta^*\big(\Theta_\vartheta y\big) = (c'_\vartheta)^{-1}\,\Theta^\circ y .$$

Lean: `New.Data.adjoint_glue_goodLift` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Since $c'_\vartheta \neq 0$, the claim is equivalent to $c'_\vartheta\,\mathrm{glue}_\vartheta^*(\Theta_\vartheta y) = \Theta^\circ y$. This is the seesaw identity applied to $y$. $\square$

**Lemma (Inner products on the lifts).** For every twist $\vartheta$ and all good forms $y'$, $y$ on $W_j$,

$$\langle\Theta_\vartheta y', U_\vartheta\,\Theta_\vartheta y\rangle = \frac{n_{\mathrm{Aut}}\,h_j^2}{|c'_\vartheta|^2}\,\langle\Theta^\circ y', \Theta^\circ y\rangle .$$

Lean: `New.Data.inner_goodLift_comparisonOp` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The scalar $n_{\mathrm{Aut}}h_j^2$ is real, and the inner product is linear in the second variable. Move $\mathrm{glue}_\vartheta$ to the left by the adjoint:

$$\langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle = n_{\mathrm{Aut}}h_j^2\,\big\langle\mathrm{glue}_\vartheta^*\Theta_\vartheta y', \mathrm{glue}_\vartheta^*\Theta_\vartheta y\big\rangle .$$

By the previous lemma both vectors are $(c'_\vartheta)^{-1}\Theta^\circ y'$ and $(c'_\vartheta)^{-1}\Theta^\circ y$. The inner product is conjugate linear in the first variable, so the two scalars give $\overline{(c'_\vartheta)^{-1}}\,(c'_\vartheta)^{-1} = |c'_\vartheta|^{-2}$. $\square$

Combine the two lemmas. The factor $n_{\mathrm{Aut}}h_j^2/|c'_\vartheta|^2$ is $\rho_j(\vartheta)$ times $n_{\mathrm{Aut}}h_j^2/|c'_1|^2$, and the second factor does not depend on $\vartheta$. This is property 2, with $U^\circ$ a positive multiple of $(\Theta^\circ)^*\Theta^\circ$. Section 5 writes this out.

### Orthogonality to the false lifts

**Lemma (Lifts go to forms orthogonal to the false lifts).** For every twist $\vartheta$ and every lift $z \in L_\vartheta$, the form $U_\vartheta z$ is orthogonal to the false lifts for $e_0$ and $L_\vartheta^\perp$.

Lean: `New.Data.isOrthogonalToFalseLifts_comparisonOp` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Write $z = \Theta_\vartheta y$ with a good form $y$. By the lemma on the adjoint,

$$U_\vartheta z = n_{\mathrm{Aut}}h_j^2\,\mathrm{glue}_\vartheta\big((c'_\vartheta)^{-1}\Theta^\circ y\big) = \big(n_{\mathrm{Aut}}h_j^2\,(c'_\vartheta)^{-1}\big)\,\mathrm{glue}_\vartheta(\Theta^\circ y) .$$

Let $w$ be a split place off the places of the datum and their conjugates. The form $\mathrm{glue}_\vartheta(\Theta^\circ y)$ is orthogonal to $\mathrm{FL}_w(e_0, L_\vartheta^\perp)$ by the result of the second part. The orthogonal complement of a subspace is a subspace, so it contains every scalar multiple. $\square$

The content of the lemma is in the second part. There the source proves that the theta kernel pairing of $\mathrm{glue}_\vartheta^*\varphi$ vanishes for every false lift $\varphi$, so that $\langle\mathrm{glue}_\vartheta\Theta^\circ y, \varphi\rangle = \langle\Theta^\circ y, \mathrm{glue}_\vartheta^*\varphi\rangle = 0$. The periods of false lifts are the subject of [false lifts](/chapter/false-lifts/).
