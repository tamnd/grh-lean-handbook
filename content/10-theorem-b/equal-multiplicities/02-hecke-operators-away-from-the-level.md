---
title: Hecke operators away from the level
lean:
  - New/Spanning/Multiplicities/HeckeEigensystems.lean
decls:
  - New.mem_levelSpace_iff_forall_apply_eq
  - New.commute_asAlgebraHom_mapDomain_trivialOn
  - New.mapDomain_mem_universalLevelAlgebra
  - New.Data.IsSplitOffLevel
  - New.Data.IsSplitOffLevel.star
  - New.Data.offLevelGroup
  - New.Data.IsSplitOffLevel.ofSplitPlace_mem
  - New.Data.principalForms_le_sphericalAt
  - New.Data.heckeSplit_mem_principalForms
  - New.Data.principalHeckeSplit
  - New.Data.sphericalAlgebra
  - New.Data.mem_sphericalAlgebra_of_mem_universalLevelAlgebra
  - New.Data.heckeAlgebra
  - New.Data.mem_heckeAlgebra
  - New.Data.exists_heckeAlgebra_eq_asAlgebraHom
  - New.Data.exists_asAlgebraHom_eq_heckeSplit
  - New.Data.principalHeckeSplit_mem_heckeAlgebra
  - New.Data.heckeOperator
  - New.Data.coe_heckeOperator_apply
  - New.Data.liftGroupAlgebra
  - New.Data.liftResidue_apply_mem_levelSpace
  - New.Data.liftGroupAlgebra_mem_universalLevelAlgebra
  - New.Data.commute_heckeAlgebra_principalRep
  - New.Data.heckeOnGood
  - New.Data.coe_heckeOnGood_apply
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke operators away from the level

The comparison of traces needs one operator on two spaces. On $Y_0$ and on $W_j$ the forms live on different groups at the real places, but the finite adelic group $G_f$ is the same. So an element of the group algebra of $G_f$ acts on the forms of both spaces. This section builds the algebra $\mathcal{H}$ of such elements that keep the principal level, proves that it contains the Hecke operators $T_{w,i}$ at the split places away from the level, and proves that it commutes with $\bar G$. The last fact lets $\mathcal{H}$ act on the good forms.

Throughout, $V$ runs over the hermitian spaces of rank $r$ over $E$, with any signs $s$. The representation of $G_f$ on the forms of type $e_{l,s}$ on $V$ is $\rho_V$, the action by right translation (`V.formRep` in Lean). For a subgroup $K$ of a group $G$ and a representation $\rho$ of $G$, $\rho^K$ is the space of $K$-fixed vectors.

**Lemma (Fixed vectors).** A vector $y$ lies in $\rho^K$ if and only if $\rho(k)y = y$ for every $k \in K$.

Lean: `New.mem_levelSpace_iff_forall_apply_eq` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

This is the definition of the level space with the trivial character, and Lean proves it by simplification.

### Places and groups away from the level

**Definition (Split places away from the level).** A finite place $w$ of $E$ is *split away from the level* if $w \neq \bar w$, where $\bar w$ is the complex conjugate place, and neither $w$ nor $\bar w$ is a chosen place.

Lean: `New.Data.IsSplitOffLevel`, `New.Data.IsSplitOffLevel.star` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

The condition is symmetric under conjugation: if $w$ is split away from the level, so is $\bar w$. This is the second Lean name.

**Definition (The group away from the level).** $G^M$ is the subgroup of $G_f$ of the elements $g$ with $g_x = 1$ at every chosen place $x$.

Lean: `New.Data.offLevelGroup` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

Here $g_x$ is the component of $g$ at the place underlying $x$. In Lean $G^M$ is `trivialOn RowIndex (range chosenPlace)`. The letter $M$ is the level, the product of the two level primes.

At a split place $w$ the unitary group is a general linear group: the map `ofSplitPlace` embeds $\mathrm{GL}_r(E_w)$ into $G_f$, with the component $g$ at $w$, the conjugate inverse transpose at $\bar w$, and $1$ elsewhere. [Iwahori and Satake](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials) gives the details.

**Lemma (Split places map into $G^M$).** If $w$ is split away from the level, then the image of $\mathrm{GL}_r(E_w)$ under `ofSplitPlace` lies in $G^M$.

Lean: `New.Data.IsSplitOffLevel.ofSplitPlace_mem` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The image has component $1$ at every place other than $w$ and $\bar w$. No chosen place is $w$ or $\bar w$. $\square$

### The Hecke operators at one place

Recall from [Iwahori and Satake](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials) that for a split place $w$ and $0 \leq i$ the operator $T_{w,i}$ is the Hecke operator of the double coset of $\mathrm{diag}(\varpi_w 1_i, 1_{r-i})$ for $\mathrm{GL}_r(\mathcal{O}_w)$, acting on the vectors fixed by the maximal compact subgroup at $w$ and $\bar w$ (the vectors *spherical at $w$*). In Lean it is `New.heckeSplit`.

**Lemma (Principal forms are spherical away from the level).** Let $w$ be split away from the level. Every form of principal level on $V$ is spherical at $w$, and $T_{w,i}$ maps $\mathcal{A}_M(V)$ into itself.

Lean: `New.Data.principalForms_le_sphericalAt`, `New.Data.heckeSplit_mem_principalForms`, `New.Data.principalHeckeSplit` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The principal level $J_M$ is maximal at every place that is not chosen and not conjugate to a chosen place. So $J_M$ contains the maximal compact subgroup at $w$ and $\bar w$, and a form fixed by $J_M$ is spherical at $w$. The operator $T_{w,i}$ is a sum of translates by elements supported at $w$ and $\bar w$. Such elements commute with the components of $J_M$ at the other places, and $T_{w,i}$ keeps the spherical vectors at $w$. So it keeps the vectors fixed by $J_M$. The general statement is `New.heckeSplit_mem_levelSpace` of [Iwahori and Satake](/chapter/iwahori-satake/). $\square$

The restriction of $T_{w,i}$ to $\mathcal{A}_M(V)$ is the third Lean name.

### The spherical algebra and the Hecke algebra

For a subgroup $K$ of a group $G$, the *universal level algebra* of $K$ is the set of $a \in \mathbb{C}[G]$ such that, for every representation $\rho$ of $G$ on a complex vector space, $\rho(a)$ maps $\rho^K$ into $\rho^K$. It is a subalgebra; see [the comparison of traces](/chapter/trace-formula/#the-comparison-of-traces). The next two lemmas are general facts about $G_f$ and a set $S$ of finite places, with $H = \{g \in G_f : g_v = 1 \text{ for } v \in S\}$.

**Lemma (Commuting with elements at $S$).** Let $\rho$ be a representation of $G_f$, let $k \in G_f$ be supported at the places of $S$ and their conjugates, and let $a \in \mathbb{C}[H]$. Then $\rho(k)$ commutes with $\rho(a)$.

Lean: `New.commute_asAlgebraHom_mapDomain_trivialOn` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The group $G_f$ is a restricted product over the places. An element supported at $S$ and an element that is $1$ at $S$ commute, since they commute at each place. So $\rho(k)$ commutes with $\rho(g)$ for each $g \in H$, and by linearity with $\rho(a)$. $\square$

**Lemma (From $H$ to $G_f$).** Let $J \leq K_0$ be a subgroup with $K_0 \cap H \leq J$. Let $a \in \mathbb{C}[H]$ keep the vectors fixed by $K_0 \cap H$ in every representation of $H$. Then the image of $a$ in $\mathbb{C}[G_f]$ lies in the universal level algebra of $J$.

Lean: `New.mapDomain_mem_universalLevelAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Let $\rho$ be a representation of $G_f$, let $y \in \rho^J$, and put $T = \rho(a)$. Let $k \in J$. Write $k = uv$ with $u$ supported at $S$ and its conjugates and $v \in H$. Since $k \in K_0$, the factor $v$ is integral, so $v \in K_0 \cap H \leq J$, and then $u = kv^{-1} \in J$. The vector $y$ is fixed by $K_0 \cap H$, so by the hypothesis on $a$, applied to the restriction of $\rho$ to $H$, the vector $Ty$ is fixed by $K_0 \cap H$. So $\rho(v)Ty = Ty$. By the previous lemma $\rho(u)$ commutes with $T$, and $\rho(u)y = y$ since $u \in J$. Hence

$$\rho(k)Ty = \rho(u)\rho(v)Ty = \rho(u)Ty = T\rho(u)y = Ty. \qquad \square$$

**Definition (Spherical algebra).** $\mathcal{S}$ is the set of $a \in \mathbb{C}[G^M]$ whose image in $\mathbb{C}[G_f]$ lies in the universal level algebra of $J_M$.

Lean: `New.Data.sphericalAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

**Lemma (A test for sphericity).** If $a \in \mathbb{C}[G^M]$ keeps the vectors fixed by $K_0 \cap G^M$ in every representation of $G^M$, then $a \in \mathcal{S}$.

Lean: `New.Data.mem_sphericalAlgebra_of_mem_universalLevelAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Apply the previous lemma with $S$ the set of chosen places, so that $H = G^M$, and with $J = J_M$. One has $J_M \leq K_0$, and an element of $K_0$ that is $1$ at every chosen place has reduction $1$ there, so $K_0 \cap G^M \leq J_M$. $\square$

**Definition (Hecke algebra away from the level).** $\mathcal{H}$ is the set of families $T = (T_V)_V$, with $T_V$ an endomorphism of $\mathcal{A}_M(V)$ for every hermitian space $V$ of rank $r$, for which there is one $a \in \mathcal{S}$ with

$$T_V y = \rho_V(a)\, y \qquad \text{for every } V \text{ and every } y \in \mathcal{A}_M(V).$$

It is a subalgebra of the product of the endomorphism algebras.

Lean: `New.Data.heckeAlgebra`, `New.Data.mem_heckeAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

The sum and product of families given by $a$ and $b$ are given by $a + b$ and $ab$, and the scalar $c$ is given by $c \cdot 1$. So $\mathcal{H}$ is a subalgebra.

**Lemma (Elements of $\mathcal{S}$ give elements of $\mathcal{H}$).** For every $a \in \mathcal{S}$ there is $T \in \mathcal{H}$ with $T_V y = \rho_V(a)y$ for all $V$ and $y \in \mathcal{A}_M(V)$.

Lean: `New.Data.exists_heckeAlgebra_eq_asAlgebraHom` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Since $a \in \mathcal{S}$, the operator $\rho_V(a)$ keeps $\mathcal{A}_M(V) = \rho_V^{J_M}$. Let $T_V$ be its restriction. $\square$

**Remark (Formalization).** An element of $\mathcal{H}$ is the family $T$. The element $a$ of the group algebra is only asserted to exist, and different $a$ may give the same family. All statements of this chapter are about the operators $T_V$, so the choice of $a$ never matters. The universal level algebra quantifies over representations on complex vector spaces in the lowest universe `Type`. The forms of all spaces lie there, so this is enough for every use in the chapter.

### The operators $T_{w,i}$ in $\mathcal{H}$

**Lemma (One element gives $T_{w,i}$).** Let $w$ be split away from the level and $i \geq 0$. There is $a \in \mathbb{C}[G^M]$ such that $\rho(a) = T_{w,i}$ in every representation $\rho$ of $G_f$. The family of the restrictions of $T_{w,i}$ to $\mathcal{A}_M(V)$ lies in $\mathcal{H}$.

Lean: `New.Data.exists_asAlgebraHom_eq_heckeSplit`, `New.Data.principalHeckeSplit_mem_heckeAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Let $\iota : \mathrm{GL}_r(E_w) \to G^M$ be `ofSplitPlace`, which lands in $G^M$ by the lemma above. The operator $T_{w,i}$ is the sum of $\rho(\iota(g))$ over representatives $g$ of the cosets $g\,\mathrm{GL}_r(\mathcal{O}_w)$ in the double coset. Let $a$ be the sum of the corresponding group elements $\iota(g)$ in $\mathbb{C}[G^M]$; in Lean it is the Hecke operator of the regular representation of $G^M$ applied to $1$. Then $\rho(a) = T_{w,i}$ for every $\rho$. For the second statement, $a$ lies in $\mathcal{S}$: in a representation $\rho$ of $G_f$, a vector fixed by $J_M$ is spherical at $w$, and then $T_{w,i}$ keeps it fixed by $J_M$, as in the proof of the lemma on spherical forms. $\square$

**Definition (The operators $T_x$).** For a pair $x = (w, i)$ of a finite place and a natural number, $T_x \in \mathcal{H}$ is the family of the restrictions of $T_{w,i}$ if $w$ is split away from the level, and $T_x = 0$ otherwise.

Lean: `New.Data.heckeOperator`, `New.Data.coe_heckeOperator_apply` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

**Remark (Formalization).** The value $T_x = 0$ at the other places is a junk value. It matters for eigensystems. An eigensystem in Lean is a function $q$ on all pairs $(w, i)$. At a pair where $T_x = 0$, a nonzero form can lie in the $q$-part only if $q(x) = 0$. So these pairs add no information and no condition beyond $q(x) = 0$.

### Commuting with $\bar G$

The group $\bar G$ acts on $\mathcal{A}_M(V)$ through integral lifts. For $g \in \bar G$, the lift $\tilde g \in K_0$ has component $1$ at every place that is neither chosen nor conjugate to a chosen place, and its reduction at each chosen place $x$ is $g_x$. In Lean the lift is `liftResidue g`, and $g$ acts as $\rho_V(\tilde g)$.

**Definition (Lift of the group algebra).** For $\xi = \sum_g \xi(g)\, g \in \mathbb{C}[\bar G]$, its lift is $\tilde \xi = \sum_g \xi(g)\, \tilde g \in \mathbb{C}[G_f]$.

Lean: `New.Data.liftGroupAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

**Lemma (Lifts keep the principal level).** For $g \in \bar G$ and a representation $\rho$ of $G_f$, $\rho(\tilde g)$ maps $\rho^{J_M}$ into itself. So the lift of every element of $\mathbb{C}[\bar G]$ lies in the universal level algebra of $J_M$.

Lean: `New.Data.liftResidue_apply_mem_levelSpace`, `New.Data.liftGroupAlgebra_mem_universalLevelAlgebra` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The lift $\tilde g$ lies in $K_0$ and normalises $J_M$, the subgroup of $K_0$ cut out by a condition on the reductions at the chosen places. So $\tilde g$ maps $J_M$-fixed vectors to $J_M$-fixed vectors. In Lean this is the representation `levelRep` of $\bar G$ on $\rho^{J_M}$. The second statement follows by linearity. $\square$

**Lemma (Hecke operators commute with $\bar G$).** For $T \in \mathcal{H}$ and $\xi \in \mathbb{C}[\bar G]$, the operators $T_V$ and $\xi$ commute on $\mathcal{A}_M(V)$.

Lean: `New.Data.commute_heckeAlgebra_principalRep` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* It suffices to take $\xi = g \in \bar G$. Let $a \in \mathcal{S}$ give $T$. The lift $\tilde g$ is supported at the chosen places and their conjugates, and $a \in \mathbb{C}[G^M]$ with $G^M$ the elements that are $1$ there. By the lemma on commuting elements, $\rho_V(\tilde g)$ commutes with $\rho_V(a)$. On $\mathcal{A}_M(V)$ these operators are $g$ and $T_V$. $\square$

**Definition (Hecke operators on good forms).** For $T \in \mathcal{H}$, $T_V$ maps $\mathcal{G}(V) = e_0\mathcal{A}_M(V)$ into itself, since $T_V e_0 y = e_0 T_V y$. The restriction is $T|_{\mathcal{G}(V)}$, and $T \mapsto T|_{\mathcal{G}(V)}$ is a homomorphism of monoids from $\mathcal{H}$ to the endomorphisms of $\mathcal{G}(V)$.

Lean: `New.Data.heckeOnGood`, `New.Data.coe_heckeOnGood_apply` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

The map is also linear in $T$, as restriction is linear, but Lean records only the multiplicative structure, which is what the proofs use.

### An example

Let $r = 2$ and let $V$ be definite. The forms of principal level are then vectors of functions on the finite set $\Gamma \backslash G_f / J_M$, where $\Gamma$ is the group of rational points; see [automorphic forms](/chapter/automorphic-forms/). Let $w$ be split away from the level, with residue field of $q$ elements. The double coset of $\mathrm{diag}(\varpi_w, 1)$ is the union of the $q + 1$ cosets $g_j\,\mathrm{GL}_2(\mathcal{O}_w)$ with

$$g_\infty = \begin{pmatrix} 1 & 0 \\ 0 & \varpi_w\end{pmatrix}, \qquad g_t = \begin{pmatrix}\varpi_w & t \\ 0 & 1\end{pmatrix}, \quad t \in \mathcal{O}_w/\varpi_w.$$

So $T_{w,1}\phi(x) = \sum_j \phi(x\,\iota(g_j))$. The element $a = \sum_j \iota(g_j)$ of $\mathbb{C}[G^M]$ does not depend on $V$. On an indefinite space $V'$ of the same rank the same $a$ acts on the forms of $V'$, by the same formula. This is the sense in which $T_{w,1}$ is one element of $\mathcal{H}$ that acts on all spaces. It is the unitary form of the fact that the Brandt matrices and the classical $T_\ell$ come from the same element of the Hecke algebra of $\mathrm{GL}_2(\mathbb{Q}_\ell)$.
