---
title: Point forms and tested forms
lean:
  - New/OneLift/TestedForms.lean
decls:
  - New.Rows.IsPointLift
  - New.Rows.exists_isPointLift
  - New.Rows.normalizedDescent_classForm
  - New.Rows.pointLift
  - New.Rows.isPointLift_pointLift
  - New.Rows.pointForm
  - New.Rows.inner_pointForm
  - New.Rows.pointFormDatum
  - New.Rows.residueBlockDatum_inv_pointLift_mul
  - New.Rows.normalizedDescent_pointForm
  - New.DescentPair.exists_invariant_pairing_eq_innerAt
  - New.LevelPlaces.LevelForm.innerAt_heckePolyOnForms
  - New.DescentPair.groupAlgAction
  - New.DescentPair.falseLiftsAt
  - New.DescentPair.IsOrthogonalToFalseLifts
  - New.DescentPair.IsTestForm
  - New.PadicPlace.ofIso
  - New.PadicPlace.ιₚ_ofIso
  - New.Selmer.DenominatorLe
  - New.DescentPair.isOfFinOrder_prod_tamePart_det
  - New.DescentPair.innerAt_formAction
  - New.DescentPair.range_groupAlgAction_mem_invtSubmodule
  - New.DescentPair.heckePolyOnForms_comm
  - New.DescentPair.innerAt_groupAlgAction
  - New.DescentPair.exists_adjoint_heckePolyOnForms_comm
  - New.DescentPair.innerAt_heckePolyOnForms_eq_zero
  - New.DescentPair.orthogonal_range_heckePolyOnForms_le_ker
  - New.DescentPair.normSqAt_eq_re_innerAt
  - New.DescentPair.normSqAt_le_add_of_innerAt_eq_zero
  - New.DescentPair.mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts
  - New.DescentPair.normSqAt_starProjection_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Point forms and tested forms

The file `New/OneLift/TestedForms.lean` works with any descent pair $O$ from a space $W$ of rank $r$ to $V$ of rank $N$. It has two parts. The first part builds point forms: forms supported on one class whose descent has an explicit finite datum. The second part is about the pairings $\langle\cdot,\cdot\rangle_\sigma = $ `innerAt σ` for $\sigma \in \mathrm{Aut}(\mathbb{C})$: the adjoint of the Hecke polynomial, the false lifts, and the bound $\|\mathrm{pr}_Z\, y\|_\sigma \leq \|y\|_\sigma$ for forms $y$ orthogonal to the false lifts.

### Point forms

The class forms $\delta_h(v)$ of Section 2 have a descent that is a conjugate theta kernel.

**Lemma (Descent of a class form).** For $h \in G_f$, a vector $v$ of the weight and $g \in U(W)(\mathbb{A})$,

$$\theta^*\big(\delta_h(v)\big)(g) = \overline{\mathrm{modKernel}\big(W, V, \nu_W, \nu_V, \mathfrak{m}, \Psi_0, \mathrm{fockPoly}(\bar v)\big)(g, h)},$$

with $\mathfrak{m} = $ `O.levelModulus 2` and $\Psi_0(T)$ the function `residueBlockDatum` of the reductions of $T$ at the places of $O$.

Lean: `New.Rows.normalizedDescent_classForm` (New/OneLift/TestedForms.lean).

*Proof.* The descent of a form $\varphi$ is the class sum over $x$ of `O.conjKernel g x` applied to $\varphi(x)$. The kernel is equivariant under $G(E)$ on the left and under the level on the right (`conjKernel_equivariant`). So for $\delta_h(v)$ the sum reduces to the single term `O.conjKernel g h v` (`classSum_deltaForm`). By definition this term is the conjugate of the scalar kernel on the right. $\square$

To change the finite datum, move the point $h$ by an integral element with prescribed reductions.

**Definition (Point lift).** Let $Y_i$ be $N \times r$ matrices over $k_{w_i}$ at the chosen places, and $e : r \hookrightarrow n$ an injection. An element $k$ of $K_0$ is a point lift for $(Y, e)$ (`IsPointLift Y e k`) if:

- $k$ is $1$ outside the places of $O$ and their conjugates;
- at each chosen place, the columns of the reduction of $k$ at the indices of `O.incl` form $Y_i$;
- at each twist place, the rows $e$ of the reduction of $k$ are the unit vectors at the indices of `O.incl`.

Lean: `New.Rows.IsPointLift` (New/OneLift/TestedForms.lean).

**Lemma (Point lifts exist).** If each $Y_i$ has full column rank, then for every $e$ there is a point lift $k$ for $(Y, e)$.

Lean: `New.Rows.exists_isPointLift` (New/OneLift/TestedForms.lean).

*Proof.* A matrix of full column rank extends to an invertible matrix $A_i$ with $A_i\, \iota = Y_i$, where $\iota$ is the inclusion matrix of `O.incl` (`exists_GL_mul_inclMatrix`). At a twist place take $B_i$ invertible with $B_i\, \iota_e = \iota$. The reduction map from $K_0$ to the product of the groups $\mathrm{GL}_n(k_w)$ over the places of $O$ is onto, with a preimage supported on these places (`exists_reduceFamily_eq`). Take $k$ with reductions $A_i$ and $B_i^{\mathsf T}$. $\square$

**Definition (Chosen point lift).** `pointLift hY e` is a point lift for $(Y, e)$, and `isPointLift_pointLift` states that it is one.

Lean: `New.Rows.pointLift` (New/OneLift/TestedForms.lean), `New.Rows.isPointLift_pointLift` (New/OneLift/TestedForms.lean).

**Remark (Formalization).** `pointLift` is defined by `Classical.choose` from the existence lemma, so it is not explicit. All later statements use only the three properties of `IsPointLift`.

**Definition (Point form).** The point form at $h$ is $v \mapsto \delta_{hA}(v)$, with $A = $ `pointLift hY e`.

Lean: `New.Rows.pointForm` (New/OneLift/TestedForms.lean).

**Lemma (Inner product with a point form).** $\langle\mathrm{pointForm}(h)(v), \varphi\rangle = \langle v, \varphi(hA)\rangle_{\mathrm{Gram}}$.

Lean: `New.Rows.inner_pointForm` (New/OneLift/TestedForms.lean).

*Proof.* This is the lemma on inner products with a class form at the point $hA$. $\square$

**Definition (Datum of a point form).** For a family $X$ of $N \times r$ matrices over the residue fields at the places of $O$, `pointFormDatum Y e X` is $\prod_{w\in Q}\psi_w(\det X_{w,e})$ if $X_i = Y_i$ at every chosen place, and $0$ otherwise. Here $X_{w,e}$ is the $r\times r$ matrix of the rows $e$ of $X_w$.

Lean: `New.Rows.pointFormDatum` (New/OneLift/TestedForms.lean).

**Lemma (Moving the datum).** For every family $X$, `residueBlockDatum` of the family $\bar A^{-1} X$ is `pointFormDatum Y e X`.

Lean: `New.Rows.residueBlockDatum_inv_pointLift_mul` (New/OneLift/TestedForms.lean).

*Proof.* At a chosen place, $\bar A^{-1}X_i = \iota$ holds exactly when $X_i = \bar A\iota = Y_i$. At a twist place, the rows `O.incl` of $\bar A^{-1}X$ are the rows $e$ of $X$, because the rows $e$ of $\bar A$ are the unit vectors at `O.incl`. Rows are selected by transposed inclusion matrices, and the two selections differ by $\bar A$, which cancels against $\bar A^{-1}$. $\square$

**Theorem (Descent of a point form).** For $h$, $v$ and $g$,

$$\theta^*\big(\mathrm{pointForm}(h)(v)\big)(g) = \overline{\mathrm{modKernel}\big(W, V, \nu_W, \nu_V, \mathfrak{m}, \Psi_{Y,e}, \mathrm{fockPoly}(\bar v)\big)(g, h)},$$

with $\Psi_{Y,e}(T) = $ `pointFormDatum Y e` of the reductions of $T$.

Lean: `New.Rows.normalizedDescent_pointForm` (New/OneLift/TestedForms.lean).

*Proof.* Apply the descent of a class form at $hA$. In the kernel, the right factor $A$ of the point $hA$ acts on the datum by translation $T \mapsto A^{-1}T$ at the finite places, times $\nu_W(\det A)$, which is $1$ (`modKernel_mul_stdLevel_right`). So the datum becomes `residueBlockDatum` of the reductions of $A^{-1}T$, and by the previous lemma this is $\Psi_{Y,e}$. $\square$

The chapter [false lifts](/chapter/false-lifts/) uses point forms to compute the periods of false lifts.

### The adjoint of the Hecke polynomial

**Lemma (Invariant pairing).** For every $\sigma$ there is a pairing $B$ on all smooth forms of the weight, semilinear for $\sigma^{-1}\circ\mathrm{conj}\circ\sigma$ in the first variable, that restricts to $\langle\cdot,\cdot\rangle_\sigma$ on `O.FormV` and is invariant under right translation by $G_f$.

Lean: `New.DescentPair.exists_invariant_pairing_eq_innerAt` (New/OneLift/TestedForms.lean).

*Proof.* Let $G$ be the Gram matrix, viewed as a pairing that is semilinear for $\sigma^{-1}\circ\mathrm{conj}\circ\sigma$. It is invariant under the weight representation of $U(J)$: after $\sigma$ this is the invariance of the Gram form on $\sigma$-conjugates (`gramForm_map_weightRep`). Take $B$ to be the index of the level times the smooth pairing `smoothPairing` of $G$. It is invariant under translation (`smoothPairing_formTranslation`), and its restriction to `O.FormV` is `innerAt σ` by definition. $\square$

**Theorem (Adjoint of the Hecke polynomial).** Let $w \neq \bar w$ with $w$ and $\bar w$ off the places of $O$ and their conjugates. For all $\varphi$, $\varphi'$ and $T \in \mathbb{C}$,

$$\langle H_w(T)\varphi, \varphi'\rangle_\sigma = \langle\varphi, H_{\bar w}(T')\varphi'\rangle_\sigma, \qquad T' = \sigma^{-1}\big(\overline{\sigma(T)}\big).$$

Lean: `New.LevelPlaces.LevelForm.innerAt_heckePolyOnForms` (New/OneLift/TestedForms.lean).

*Proof.* Write $\langle\cdot,\cdot\rangle_\sigma$ with the invariant pairing $B$. Forms of the level are spherical at $w$. For an invariant pairing of spherical vectors, the adjoint of $T_{w,i}$ is $T_{\bar w, i}$, and so the adjoint of $H_w(T)$ is $H_{\bar w}(T')$ (`heckePolyOp_adjoint`, in [Iwahori-Hecke algebras and the Satake transform](/chapter/iwahori-satake/)). The scalar $T$ becomes $T'$ because $B$ is semilinear for $\sigma^{-1}\circ\mathrm{conj}\circ\sigma$. $\square$

**Lemma (Commuting Hecke polynomials).** For split places $w$, $u$ off the level and all $T$, $T'$, $H_w(T)H_u(T') = H_u(T')H_w(T)$ on `O.FormV`.

Lean: `New.DescentPair.heckePolyOnForms_comm` (New/OneLift/TestedForms.lean).

*Proof.* Both sides are double sums of products of Hecke operators at $w$ and at $u$. On spherical vectors these operators commute. $\square$

**Lemma (Normality).** $H_w(T)$ has an adjoint $A'$ for $\langle\cdot,\cdot\rangle_\sigma$ that commutes with it.

Lean: `New.DescentPair.exists_adjoint_heckePolyOnForms_comm` (New/OneLift/TestedForms.lean).

*Proof.* Take $A' = H_{\bar w}(T')$. It is an adjoint by the theorem, and it commutes with $H_w(T)$ by the previous lemma. $\square$

**Lemma (Range and kernel).** If $H_w(T)z = 0$, then $\langle H_w(T)v, z\rangle_\sigma = 0$ for every $v$. For $\sigma = 1$, the orthogonal complement of the range of $H_w(T)$ is contained in its kernel.

Lean: `New.DescentPair.innerAt_heckePolyOnForms_eq_zero` (New/OneLift/TestedForms.lean), `New.DescentPair.orthogonal_range_heckePolyOnForms_le_ker` (New/OneLift/TestedForms.lean).

*Proof.* For the first claim, $\langle A'z, A'z\rangle_\sigma = \langle z, H_w(T)A'z\rangle_\sigma = \langle z, A'H_w(T)z\rangle_\sigma = 0$. The pairing is definite (`eq_zero_of_innerAt_self`), so $A'z = 0$ and $\langle H_w(T)v, z\rangle_\sigma = \langle v, A'z\rangle_\sigma = 0$. For the second claim, let $u$ be orthogonal to the range of $H = H_w(T)$, and take $A'$ for $\sigma = 1$. Then $\langle u, HA'u\rangle = 0$. By normality and the adjoint property, $\langle Hu, Hu\rangle = \langle u, A'Hu\rangle = \langle u, HA'u\rangle = 0$, so $Hu = 0$. $\square$

### The group algebra at the chosen places

Let $G_M = \prod_{w\in M}\mathrm{GL}_r(k_w)$. The pair has an action `O.formAction` of $G_M$ on `O.FormV`: $g$ acts as $\prod_w\psi_w(\det g_w)$ times right translation by an integral element whose reduction at $w \in M$ is $g_w$ on the indices of `O.incl` and $1$ on the others.

**Definition (Group algebra action).** For $e_0$ in the group algebra $\mathbb{C}[G_M]$, `O.groupAlgAction e₀` is the operator by which $e_0$ acts through `formAction`.

Lean: `New.DescentPair.groupAlgAction` (New/OneLift/TestedForms.lean).

**Lemma (Roots of unity).** For $g \in G_M$, $\prod_w\psi_w(\det g_w)$ has finite order.

Lean: `New.DescentPair.isOfFinOrder_prod_tamePart_det` (New/OneLift/TestedForms.lean).

*Proof.* Each $\psi_w$ is a character of the finite group $k_w^\times$. $\square$

**Lemma (Invariance).** For every $\sigma$, $\langle gx, gy\rangle_\sigma = \langle x, y\rangle_\sigma$.

Lean: `New.DescentPair.innerAt_formAction` (New/OneLift/TestedForms.lean).

*Proof.* $g$ is a root of unity $c$ times a translation. The translation preserves the pairing by the invariant pairing lemma, and $\sigma(\bar c)\sigma(c) = 1$ since $\sigma$ maps roots of unity to roots of unity of absolute value $1$. $\square$

**Lemma (Invariant images).** An operator that commutes with `formAction` preserves the image of every $e_0$.

Lean: `New.DescentPair.range_groupAlgAction_mem_invtSubmodule` (New/OneLift/TestedForms.lean).

*Proof.* The image is spanned by the vectors $e_0 y$, and $f(e_0 y) = e_0 f(y)$ since $e_0$ is a combination of the operators $g$. $\square$

**Lemma (Self-adjoint idempotent).** If $e_0$ is a central idempotent (`IsCentralProj`: idempotent with coefficients a class function), then $\langle e_0x, y\rangle_\sigma = \langle x, e_0y\rangle_\sigma$.

Lean: `New.DescentPair.innerAt_groupAlgAction` (New/OneLift/TestedForms.lean).

*Proof.* This is the general lemma `IsCentralProj.self_adjoint` of [congruence subgroups](/chapter/congruence-subgroups/) of Volume 4, for the representation `formAction` and the pairing $\langle\cdot,\cdot\rangle_\sigma$, which is invariant under $G_M$ by the previous lemma. $\square$

### False lifts and tested forms

From here on orthogonal complements and projections are taken for $\sigma = 1$.

**Definition (False lifts).** For a split place $w$ off the level, $e_0 \in \mathbb{C}[G_M]$ and a subspace $Z$,

$$\mathrm{FL}_w(e_0, Z) = \mathrm{range}(e_0)\cap\ker H_w(x_w)\cap Z, \qquad x_w = \text{`O.liftHeckeRoot w`}.$$

A form $y$ is orthogonal to the false lifts if $y \perp \mathrm{FL}_w(e_0, Z)$ for every such $w$.

Lean: `New.DescentPair.falseLiftsAt` (New/OneLift/TestedForms.lean), `New.DescentPair.IsOrthogonalToFalseLifts` (New/OneLift/TestedForms.lean).

By the root lemma of Section 5, every theta lift lies in $\ker H_w(x_w)$. So a false lift is a form that looks like a lift to the Hecke polynomial at $w$ and lies in $Z$.

**Definition (Test form).** A form $\Xi$ is a test form above a prime $\ell$ if it is integral at every embedding $\mathbb{C} \to \mathbb{C}_\ell$ (all its values have gauge at most $1$) and orthogonal to the false lifts for $e_0 = $ `tupleIdem r (X − 1)` and $Z = \ker\theta^*$.

Lean: `New.DescentPair.IsTestForm` (New/OneLift/TestedForms.lean).

The idempotent `tupleIdem` at $X - 1$ is the tensor product over $w \in M$ of the label idempotents of $\mathrm{GL}_r(k_w)$ for the polynomial $X - 1$, from [finite general linear groups](/chapter/finite-gln/) of Volume 5. For $r = 1$ it is the mean over $G_M$.

**Definition (l-adic place of an isomorphism).** For $\iota : \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, `PadicPlace.ofIso ι` is $\iota$ followed by $\overline{\mathbb{Q}}_\ell \subseteq \mathbb{C}_\ell$, and `ιₚ_ofIso` states this.

Lean: `New.PadicPlace.ofIso` (New/OneLift/TestedForms.lean), `New.PadicPlace.ιₚ_ofIso` (New/OneLift/TestedForms.lean).

**Definition (Denominator bound).** `DenominatorLe ι O e₀ Z β` holds if there is an operator $\Lambda$ on $Z$ with

$$\exp\big(-\dim Z\cdot\#r\cdot\beta\big) \leq |\iota(\det\Lambda)|,$$

such that for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts for $e_0$ and $Z^\perp$, the form $\Lambda(\mathrm{pr}_Z\,y)$ is integral at $\iota$, and $|\iota\langle y', \Lambda\,\mathrm{pr}_Z\,y\rangle| \leq 1$ for every $y'$ integral at every embedding.

Lean: `New.Selmer.DenominatorLe` (New/OneLift/TestedForms.lean).

So $\Lambda$ clears the denominators of the projection, and its determinant is not too small. The chapter [Hecke values of character lifts](/chapter/hecke-values/) and Volume 12 prove and use such bounds.

### The projection bound

**Lemma (Norms and pairings).** $\|v\|^2_\sigma = $ `normSqAt v σ` is $\mathrm{Re}\,\sigma(\langle v, v\rangle_\sigma)$, and if $\langle x, z\rangle_\sigma = 0$ then $\|z\|^2_\sigma \leq \|z + x\|^2_\sigma$.

Lean: `New.DescentPair.normSqAt_eq_re_innerAt` (New/OneLift/TestedForms.lean), `New.DescentPair.normSqAt_le_add_of_innerAt_eq_zero` (New/OneLift/TestedForms.lean).

*Proof.* $\sigma(\langle v, v\rangle_\sigma)$ is the class sum of the Gram norms of the vectors $\sigma(v(g))$, which is real (Section 2 at $\sigma$). For the second claim, $\|z + x\|^2_\sigma = \|z\|^2_\sigma + \|x\|^2_\sigma + 2\,\mathrm{Re}\,\sigma\langle x, z\rangle_\sigma \geq \|z\|^2_\sigma$. $\square$

**Lemma (Decomposition).** Let $e_0$ be a central idempotent, $w$ split off the level, and $y$ orthogonal to the false lifts for $e_0$ and $Z^\perp$. Then $y \in Z + \ker e_0 + \mathrm{range}\,H_w(x_w)$.

Lean: `New.DescentPair.mem_sup_ker_sup_range_of_isOrthogonalToFalseLifts` (New/OneLift/TestedForms.lean).

*Proof.* Let $u$ be orthogonal to $Z + \ker e_0 + \mathrm{range}\,A$, $A = H_w(x_w)$. Then $u \in Z^\perp$. Since $e_0$ is self-adjoint, $(\ker e_0)^\perp = \mathrm{range}\,e_0$, so $u \in \mathrm{range}\,e_0$. By the lemma on range and kernel, $u \in \ker A$. So $u$ is a false lift for $e_0$ and $Z^\perp$, and $y \perp u$. Hence $y$ lies in the double orthogonal of $Z + \ker e_0 + \mathrm{range}\,A$, which is this space, since the space of forms is finite dimensional. $\square$

**Theorem (Projection bound).** Let $e_0$ be a central idempotent, $w$ split off the level, and $Z \subseteq \mathrm{range}(e_0)\cap\ker H_w(x_w)$. If $y$ is orthogonal to the false lifts for $e_0$ and $Z^\perp$, then for every $\sigma$,

$$\|\mathrm{pr}_Z\,y\|^2_\sigma \leq \|y\|^2_\sigma.$$

Lean: `New.DescentPair.normSqAt_starProjection_le` (New/OneLift/TestedForms.lean).

*Proof.* By the decomposition, $y = z + x$ with $z \in Z$ and $x \in \ker e_0 + \mathrm{range}\,A$. Every vector of $\ker e_0$ is orthogonal to $\mathrm{range}\,e_0 \supseteq Z$ at every $\sigma$, by self-adjointness. Every vector of $\mathrm{range}\,A$ is orthogonal to $\ker A \supseteq Z$ at every $\sigma$, by the lemma on range and kernel. So $\langle x, z'\rangle_\sigma = 0$ for all $z' \in Z$ and all $\sigma$. At $\sigma = 1$ this says $\mathrm{pr}_Z\,y = z$. At $\sigma$ it says $\langle x, z\rangle_\sigma = 0$, and the Pythagoras inequality gives $\|z\|^2_\sigma \leq \|y\|^2_\sigma$. $\square$

The point of the theorem is that the projection is defined by the complex inner product, but the bound holds at every conjugate pairing. The chapter [the height of one lift determinant](/chapter/lift-volume-height/) uses this to bound the heights of projections of integral forms.
