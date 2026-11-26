---
title: Heisenberg groups of the floors
lean:
  - Lib/DiscreteSeries/Bruhat/FloorMeasures.lean
decls:
  - New.Floors.TraceOne.heisenbergElem
  - New.Floors.FloorGroups.heisenbergElem_mul
  - New.Floors.FloorGroups.mul_heisenbergElem
  - New.Floors.FloorGroups.exists_eq_heisenbergElem_of_mem
  - New.Floors.FloorGroups.bijOn_mulVec_eStar
  - New.Floors.FloorGroups.existsUnique_prod_of_mem_besselU
  - New.mem_besselS
  - New.Floors.FloorGroups.simpleRootSum_conj_heisenbergElem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Heisenberg groups of the floors

This section describes the group $\mathcal N_a$ of floor $a$ by explicit Eichler transformations, and proves that $\mathsf U$ is the product $\mathcal N_0 \mathcal N_1 \cdots \mathcal N_{\varrho - 1}$ with unique factors. Two consequences follow: the Bessel subgroup is $S = \mathsf U H$, and the character $\sigma$ of a conjugate of a Heisenberg element is a value of the form. The big cell of the next section uses the Heisenberg elements to clear one floor at a time. The measures on the floors in Section 7 are convolutions along the same factorisation.

Throughout this section $A$ has a fixed element $\tau$ with $\tau + \bar\tau = 1$, and $J_T$ is hermitian and invertible. Over a field of characteristic zero the source takes $\tau = 1/2$. An element $\beta$ is *skew* if $\bar\beta = -\beta$. For $x \in A$ put $\operatorname{sk}(x) = x - \bar x$, a skew element.

### Eichler transformations

Let $V$ be a hermitian space, $e \in V$ isotropic, $v \in V$ orthogonal to $e$ and $c \in A$. The Eichler transformation $E(e, v, c)$ is $w \mapsto w + h(v, w) e - h(e, w)(v + c e)$. It is an isometry when $c + \bar c = h(v, v)$, and these maps form the unipotent radical of the stabiliser of the line $Ae$. In the floor $a$ the isotropic vector is $e_a$, and the source uses $-v$ in place of $v$ and the parameter $c = \tau h(v, v) - \beta$. The condition $c + \bar c = h(v, v)$ holds because $\tau + \bar\tau = 1$ and $\beta$ is skew.

**Definition.** Let $a < \varrho$, let $v$ be a vector supported on the basis vectors of floor at least $a + 1$, and let $\beta$ be skew. The *Heisenberg element* $\nu_a(v, \beta)$ is the isometry
$$\nu_a(v, \beta)\, w = w + w_{e^*_a} v + \big( (\beta - \tau h(v, v))\, w_{e^*_a} - h(v, w) \big) e_a,$$
where $w_{e^*_a}$ is the coefficient of $e^*_a$ in $w$. In particular $\nu_a(v, \beta) e^*_a = e^*_a + v + (\beta - \tau h(v, v)) e_a$.

Lean: `New.Floors.TraceOne.heisenbergElem` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

The formula is `New.Floors.FloorGroups.heisenbergElem_mulVec`. The element fixes every basis vector of floor below $a$, it fixes $e_a$, and it is unitriangular for the levels of $\mathcal N_{<a+1}$. So $\nu_a(v, \beta) \in \mathcal N_a$ (Lean: `New.Floors.FloorGroups.heisenbergElem_mem_floorUnipotent`).

**Example.** Let $\varrho = 1$, $\kappa = \{1\}$ and $T = \operatorname{diag}(1, -1)$ over $\mathbb C$, so the basis is $e_0, x, z, e^*_0$. Take $v = \alpha x + \zeta z$ and $\tau = 1/2$. Then $h(v, v) = |\alpha|^2 - |\zeta|^2$, and in the basis $(e_0, x, z, e^*_0)$
$$\nu_0(v, \beta) = \begin{pmatrix} 1 & -\bar\alpha & \bar\zeta & \beta - \tfrac12(|\alpha|^2 - |\zeta|^2) \\ 0 & 1 & 0 & \alpha \\ 0 & 0 & 1 & \zeta \\ 0 & 0 & 0 & 1 \end{pmatrix}.$$
The second and third columns come from $-h(v, x) = -\bar\alpha$ and $-h(v, z) = \bar\zeta$. The real dimension of the group is $2 \cdot 2 + 1 = 5$: it is the Heisenberg group of $\mathbb C^2$.

### The group law

**Proposition.** For $a < \varrho$, vectors $v, v'$ of the floors at least $a + 1$ and skew $\beta, \beta'$,
$$\nu_a(v, \beta)\, \nu_a(v', \beta') = \nu_a\big(v + v', \ \beta + \beta' + \operatorname{sk}(\tau h(v', v))\big).$$

Lean: `New.Floors.FloorGroups.heisenbergElem_mul` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* Let $w$ be a vector and $c = w_{e^*_a}$. The vectors $v'$ and $e_a$ have no $e^*_a$ coefficient, so $c$ is also the $e^*_a$ coefficient of $w' = \nu_a(v', \beta') w$. We have $h(v, e_a) = 0$, so $h(v, w') = h(v, w) + c\, h(v, v')$. Apply $\nu_a(v, \beta)$ to $w'$. The result is $w + c(v + v') + C e_a$ with
$$C = (\beta + \beta' - \tau h(v, v) - \tau h(v', v'))c - h(v, w) - h(v', w) - c\, h(v, v').$$
The right side gives the coefficient $(\beta + \beta' + x - \bar x - \tau h(v + v', v + v'))c - h(v + v', w)$, with $x = \tau h(v', v)$ and $\bar x = \bar\tau h(v, v')$. Expand $h(v + v', v + v')$. The difference of the two coefficients is $c$ times
$$x - \bar x - \tau h(v, v') - \tau h(v', v) + h(v, v') = (1 - \tau - \bar\tau)\, h(v, v') = 0. \qquad \square$$

So the parameters $(v, \beta)$ form a Heisenberg group with the cocycle $\operatorname{sk}(\tau h(v', v))$. The inverse is $\nu_a(-v, \operatorname{sk}(\tau h(v, v)) - \beta)$ (Lean: `New.Floors.FloorGroups.heisenbergElem_inv`).

**Lemma.** Let $s \in H_{a+1}$. Then $s\, \nu_a(v, \beta) = \nu_a(s v, \beta)\, s$, where $s v$ is the block of $s$ on the floors at least $a + 1$ applied to $v$.

Lean: `New.Floors.FloorGroups.mul_heisenbergElem` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* The element $s$ fixes $e_a$ and $e^*_a$, it preserves the span of the floors at least $a + 1$, and it preserves the form. So $(sw)_{e^*_a} = w_{e^*_a}$ and $h(sv, sw) = h(v, w)$. Apply both sides to $w$ and compare with the formula of the definition. $\square$

### Every element of $\mathcal N_a$ is a Heisenberg element

**Proposition.** For $a < \varrho$, every $g \in \mathcal N_a$ equals $\nu_a(v, \beta)$ for some vector $v$ of the floors at least $a + 1$ and some skew $\beta$.

Lean: `New.Floors.FloorGroups.exists_eq_heisenbergElem_of_mem` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* Put $w = g e^*_a$. It vanishes on the floors below $a$, its $e^*_a$ coefficient is $1$, and it is isotropic. Write $w = e^*_a + v + d e_a$ with $v$ on the floors at least $a + 1$. Isotropy gives $d + \bar d = -h(v, v)$. Put $\beta = \operatorname{sk}(\bar\tau d)$. Then $\beta - \tau h(v, v) = \bar\tau d - \tau \bar d + \tau(d + \bar d) = d$, so $\nu_a(v, \beta) e^*_a = w$. Now $g^{-1} \nu_a(v, \beta)$ fixes $e^*_a$ and lies in $Q_{a+1} \cap H_a$, so it lies in $H_{a+1}$. It also lies in $\mathcal N_{<a+1}$. An element of $H_{a+1} \cap \mathcal N_{<a+1}$ agrees with $1$ on the floors up to $a$, and on the other floors it is unitriangular for a constant level, so it is $1$ (Lean: `New.Floors.FloorGroups.eq_one_of_mem_floorGroup_inf`). $\square$

**Remark (Formalization).** The proposition gives existence of the parameters only. The source says so in the docstring: it is a weaker form of the standard parametrisation of the unipotent radical by Eichler transformations, for one floor and without uniqueness. The parameters are in fact unique, since $g e^*_a$ determines $v$ and $d$, and $d$ determines $\beta = \operatorname{sk}(\bar\tau d)$ (Exercise 2). The source gets the uniqueness that it needs from the next proposition, which is stated on the vectors $u e^*_a$.

**Proposition.** For $a < \varrho$, the map $u \mapsto u e^*_a$ is a bijection from $\mathcal N_a$ onto the set of vectors $y$ that vanish on the floors below $a$, are isotropic, and satisfy $h(e_a, y) = 1$.

Lean: `New.Floors.FloorGroups.bijOn_mulVec_eStar` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* The image lies in the set, since $u$ is an isometry that fixes the floors below $a$ and is unitriangular. If $u e^*_a = u' e^*_a$, then $u^{-1} u'$ fixes $e^*_a$, so it lies in $H_{a+1} \cap \mathcal N_{<a+1} = \{1\}$. A vector $y$ of the set is $\nu_a(v, \beta) e^*_a$ by the computation in the last proof. $\square$

### The factorisation of $\mathsf U$

**Theorem.** Every $u \in \mathsf U$ is a product $u = x_0 x_1 \cdots x_{\varrho - 1}$ with $x_l \in \mathcal N_l$, and the factors $x_l$ are unique.

Lean: `New.Floors.FloorGroups.existsUnique_prod_of_mem_besselU` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* Since $\mathsf U = \mathcal N_{<\varrho}$, it is enough to prove the statement for $\mathcal N_{<j}$ and all $j$, by induction on $j$. For $j = 0$ the group $\mathcal N_{<0}$ is trivial, since all floors get the same level.

The first step is a splitting. Every $s \in Q_j$ is a product $s = \gamma \nu$ with $\gamma \in H_j$ and $\nu \in \mathcal N_{<j}$ (Lean: `New.Floors.FloorGroups.exists_floorGroup_mul_unipotentBelow`). This follows by induction from the case of one floor: an element $s \in Q_{l+1} \cap H_l$ is $g \nu$ with $g \in H_{l+1}$ and $\nu \in \mathcal N_l$. For that case, $s^{-1} e^*_l$ is an isotropic vector of the form in the last proposition, so $s^{-1} \nu_l(v, \beta) \in H_{l+1}$ for some Heisenberg element.

For the induction step let $u \in \mathcal N_{<j+1}$. Split $u^{-1} = \gamma \nu$ with $\gamma \in H_j$ and $\nu \in \mathcal N_{<j}$. Then $u = \nu^{-1} \gamma^{-1}$, and $\gamma^{-1} = \nu u$ lies in $H_j \cap \mathcal N_{<j+1} = \mathcal N_j$. By induction $\nu^{-1} = x_0 \cdots x_{j-1}$, and we put $x_j = \gamma^{-1}$. For uniqueness let $u = x'_0 \cdots x'_j$ be a second product, and put $\nu' = x'_0 \cdots x'_{j-1} \in \mathcal N_{<j}$. Then $\nu \nu' = \gamma^{-1} (x'_j)^{-1}$ lies in $\mathcal N_{<j} \cap H_j = \{1\}$. So $x'_j = \gamma^{-1}$ and $\nu' = \nu^{-1}$, and the induction hypothesis gives $x'_l = x_l$ for $l < j$. $\square$

**Lemma.** An element $s \in G_T$ lies in the Bessel subgroup $S$ if and only if $s = u h$ with $u \in \mathsf U$ and $h \in H$.

Lean: `New.mem_besselS` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* Let $s \in S = Q_{\varrho + 1}$. The splitting gives $s = h \nu$ with $h \in H_{\varrho + 1} = H$ and $\nu \in \mathcal N_{<\varrho + 1} = \mathsf U$. Then $s = (h \nu h^{-1}) h$, and $h \nu h^{-1} \in \mathsf U$ since $H_{\varrho+1}$ normalises $\mathcal N_{<\varrho+1}$ (Lean: `New.Floors.FloorGroups.conj_mem_unipotentBelow`). Conversely $\mathsf U \subset S$ and $H \subset S$. $\square$

The group $S$ also normalises $\mathsf U^0$, the part of $\mathsf U$ that fixes the frame (Lean: `New.Floors.FloorGroups.besselS_le_normalizer_besselU0`).

### The character on conjugates

The Poincaré series of Theorem B need the character $\sigma$ on conjugates $s \nu s^{-1}$. For a Heisenberg element the answer is one value of the form.

**Proposition.** Let $a < \varrho$, $s \in H_{a+1}$, $v$ a vector of the floors at least $a + 1$ and $\beta$ skew. Then
$$\sigma\big(s\, \nu_a(v, \beta)\, s^{-1}\big) = -h(v, s^{-1} f_{a+1}).$$

Lean: `New.Floors.FloorGroups.simpleRootSum_conj_heisenbergElem` (Lib/DiscreteSeries/Bruhat/FloorMeasures.lean).

*Proof.* By the lemma on $H_{a+1}$, $s \nu_a(v, \beta) s^{-1} = \nu_a(sv, \beta)$. On the frame, $\nu_a(v', \beta')$ differs from $1$ only in the row $f_a = e_a$, where its entry at $f_c$ is $-h(v', f_c)$ (Lean: `New.Floors.FloorGroups.frameMatrix_heisenbergElem`). So the only nonzero simple root entry is at $(f_a, f_{a+1})$, and it equals $-h(sv, f_{a+1}) = -h(v, s^{-1} f_{a+1})$. $\square$

In the model case $\varrho = 1$ and $s = 1$, this is the value $-h(v, z) = \bar\zeta$ that the example reads in the entry $(e_0, z)$.
