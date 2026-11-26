---
title: The Hecke tower and the model
lean:
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Shimura/IntegralModel/TowerExistence.lean
  - Lib/Shimura/IntegralModel/UniversalFamily.lean
  - Lib/Shimura/ArcExtension.lean
  - Lib/General/Geometry/GaloisCovers.lean
  - Lib/Cohomology/Etale/Basic.lean
decls:
  - New.Variety.Model
  - New.Variety.IsNeat
  - New.Variety.IsSignedFrameFor.eq_one_of_congr_large_norm
  - New.Variety.eventually_isNeat
  - New.Variety.UniversalFamily.GraphClosure
  - New.Variety.UniversalFamily.smooth_and_isDenseFamily_and_exists_comp_eq_act
  - New.Variety.exists_level_conj_mem
  - New.Variety.IsGaloisCovering
  - New.Variety.isGaloisCovering_of_complex_points
  - New.Variety.cancels_moebius_of_factorsThrough_sup
  - New.Variety.UniversalFamily.GraphClosure.congruenceRelation
  - New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Hecke tower and the model

Section 6 gives one scheme over $R$. A Shimura variety comes with a tower of levels and Hecke correspondences. In the textbook, the tower comes from the action of the adelic group on level structures (Kottwitz 1992, §5). In the source, each cover is again a closure of tuples of points, and every map is a lift of a translation of complex points. This section proves the existence theorem of Section 1.

### The structure of a model

Fix $E$, a finite type $n$, $d_0$, a level $\mathfrak{N} \in \mathcal{O}_E$, a number $\nu$ of marked points, and $R$. A level index $i$ is a finite set of pairs $(\mathfrak{a}, g)$, with $\mathfrak{a}$ a nonzero integer of $E$ and $g \in GU^+$. Here $GU^+$ is the set of similitudes $g$ whose inverse is integral (`New.Variety.GUPlus`), and $K(\mathfrak{a})$ is the group of integral similitudes congruent to $1$ modulo $\mathfrak{a}$ (`New.Variety.levelGU`).

**Definition (Model).** A model `Model n d₀ 𝔑 ν R` consists of the following data over $\operatorname{Spec} R$.

1. A base $Z$, schemes $W_i$, sets $s_i \subseteq GL_n(\mathbb{A}_f)$ with $1 \in s_i$, and legs $p_g : W_i \to Z$, one for each coset $g K(\mathfrak{N})$. Write $\pi = p_1$.
2. For $g \in GU^+$ and a level $j$, all large levels $i$ have $g \in s_i$ and a map $f : W_i \to W_j$ with $p_q \circ f = p_{gq}$ for all $q \in s_j$.
3. Finite groups $\Delta_i$ that act on $W_i$. For each $\delta$ there is $\kappa \in K(\mathfrak{N})$ with $p_q \circ \delta = p_{\kappa q}$ for all $q \in s_i$.
4. Maps $m_\alpha : Z \to Z$ for $\alpha : \mathrm{Fin}\,\nu \to \mathcal{O}_E$.
5. Complex points $[a]_i$ of $W_i$ for every moduli point $a$. Every complex point is of this form. $\pi[a]_i = \pi[b]_i$ if and only if some $z \in GL_n(E)$ is an isomorphism from $a$ to $b$ at level $K(\mathfrak{N})$. For $g \in s_i$, $m_\alpha p_g [a]_i = \pi [a \cdot (g, \alpha)]_i$.
6. $Z$ is smooth of a relative dimension $\dim$ and proper. Each $W_i$ is reduced and has a projective embedding. $\pi$ is a Galois covering with group $\Delta_i$.
7. The fields `tangent` and `congruence`, stated below.

Lean: `New.Variety.Model` (Lib/Shimura/HeckeTower/Model.lean).

The field `tangent` says: if $g \in s_i$ and $z$ is an isomorphism from $a \cdot (g, \alpha)$ to $a$ at level $K(\mathfrak{N})$ as in the tangent theorem below, then at $[a]_i$ the polynomial `New.Variety.localTerm α χ μ` is a constant times $\det(1 - X A)$, where $d(m_\alpha p_g) = d\pi \circ A$ on a tangent space of dimension $\dim$ (`New.Variety.IsTangentPoly`). The field `congruence` says: Let $w$ be a split place that is safe for $\mathfrak{N}$, with residue field of order $q = p^f$. Let $\mathfrak{p} \subseteq R$ contain the image of $w$. Let the Hecke elements $g_A$ (`New.Variety.invHeckeIsogeny`), for the subspaces $A$ of $k_w^n$, lie in $s_i$. Then for every field $k$ of characteristic $p$ and every point $x$ of $W_i$ over $k$ that kills $\mathfrak{p}$,
$$\sum_A (-1)^{r_A} q^{\binom{r_A}{2}} \,[\, p_{g_A}(x) \circ F^{(n - r_A) f} \,] = 0, \qquad r_A = \dim A,$$
as a formal sum of points of $Z$ (`New.Variety.CongruenceRelation`). [Chapter 3](/chapter/congruence-relation/) turns this into the Eichler-Shimura relation.

**Definition (Galois covering).** A map $c : W \to Z$ is a Galois covering with group $\Delta$ if every $\delta$ acts over $Z$, $c$ is surjective, and for every field $k$ of characteristic $0$, two $k$-points of $W$ with the same image differ by a unique $\delta$.

Lean: `New.Variety.IsGaloisCovering` (Lib/Cohomology/Etale/Basic.lean).

**Remark (Formalization).** The textbook covering $\mathrm{Sh}_{K'} \to \mathrm{Sh}_K$ for $K'$ normal in a neat $K$ is finite étale with group $K/K'$ (Milne, *Introduction to Shimura varieties*, §5). The source does not ask $c$ to be finite or étale, and asks the torsor condition only in characteristic $0$.

### Neat levels

**Definition (Neat level).** $\mathfrak{N}$ is neat if $\mathfrak{N} \neq 0$ and the following holds. Let $x$ be a signed frame for some $\ell$, and let $y \in GL_n(E)$ have $x^{-1} y x \in K(\mathfrak{N})$ and fix $\ell$. Then $y = 1$.

Lean: `New.Variety.IsNeat` (Lib/Shimura/HeckeTower/HeckeData.lean).

**Lemma (Large congruence kills automorphisms).** Let $(x, \ell, \beta)$ be a signed frame. Let $y$ fix $\ell$, and let $(x^{-1} y x)^{-1}$ be a frame for the identity form. Let $x^{-1} y x$ be congruent to $1$ modulo an ideal $J$ of $\hat{\mathcal{O}}_E$, and let $J \cap \mathcal{O}_E \subseteq I$ with $(2\,|n|)^{[E:\mathbb{Q}]} < N(I)$. Then $y = 1$.

Lean: `New.Variety.IsSignedFrameFor.eq_one_of_congr_large_norm` (Lib/Shimura/HeckeTower/HeckeData.lean).

*Proof.* The frame conditions say that $y$ preserves $\beta$ and has eigenvalues of modulus $1$ at every infinite place. So every conjugate of $\operatorname{tr} y - n$ has modulus at most $2n$, and $|N(\operatorname{tr} y - n)| \le (2n)^{[E:\mathbb{Q}]}$. The congruence puts $\operatorname{tr} y - n$ in $I$. A nonzero element of $I$ has norm divisible by $N(I)$. So $\operatorname{tr} y = n$. At a place $w \neq v_0$ the form $\beta$ is positive definite, and $y$ is an isometry of it. So $y$ is diagonalizable with eigenvalues of modulus $1$ and sum $n$. All of them are $1$, and $y = 1$. $\square$

**Theorem (Neat levels exist).** Let $E$ have a base place and let $n$ be nonempty. For all but finitely many finite places $w$, every nonzero $\mathfrak{N} \in w$ is neat.

Lean: `New.Variety.eventually_isNeat` (Lib/Shimura/HeckeTower/HeckeData.lean).

*Proof.* Only finitely many places have $q_w \le (2n)^{[E:\mathbb{Q}]}$. For the others take $I = w$; if $\mathfrak{N} \in w$, the lemma applies. $\square$

*Example.* Take $n = 1$. Then $y \in E^\times$ has $|y|_v = 1$ at every infinite place, so $y$ is a root of unity. If $y \equiv 1$ modulo a prime $w$ with $q_w > 2^{[E:\mathbb{Q}]}$, then $|N(y - 1)| \le 2^{[E:\mathbb{Q}]} < q_w$ forces $y = 1$.

### Extension over an arc

The source extends isogenies of complex tori over an *arc*, a valuation ring $O$ of $\mathbb{C}$, with theta coordinates and properness only. Its main result, `New.Variety.exists_hom_of_hasThetaCoords` (Lib/Shimura/ArcExtension.lean), extends a homomorphism of complex tori to an additive morphism of the schemes over $O$. The proof uses the commutator pairing of the theta group (Mumford, *Abelian Varieties*, §23), in the form `New.Variety.lift_commutator_iff_weil_pairing`. The textbook extension theorems instead need a noetherian normal base (Faltings and Chai, *Degeneration of Abelian Varieties* (1990), Chapter I, 2.7). The source applies the result in `New.ThetaObject.TorusModel.exists_isIsogenyOfMatrix`, and through it in `New.Variety.UniversalFamily.datumPoint_eq_iff` and [Chapter 3](/chapter/congruence-relation/).

### The covers and the base

**Definition (Graph closure).** Let $\gamma : J \to \mathcal{O}_E^{\neq 0} \times GU^+$ be a finite family of pairs $(\mathfrak{m}_j, g_j)$. The graph closure is the reduced closure, in a product of fibre powers of the theta family, of the tuples $(\mathrm{datumPoint}_{\mathfrak{m}_j}(a \cdot g_j))_j$ for all moduli points $a$.

Lean: `New.Variety.UniversalFamily.GraphClosure` (Lib/Shimura/IntegralModel/UniversalFamily.lean).

**Theorem (The base).** Let $\nu \neq 0$. The fibre power of the theta family at level $1$ over $\mathrm{NonzeroTorsion}\,1 \oplus \mathrm{Fin}\,\nu$ is smooth over $R$ of relative dimension $|n| - 1 + \nu \cdot \mathrm{abelianDim}$. Its complex points $\mathrm{datumPoint}_1(a)$ are dense. For each $\alpha$ there is a map $m_\alpha$ with $m_\alpha(\mathrm{datumPoint}_1(a)) = \mathrm{datumPoint}_1(a \cdot \alpha)$.

Lean: `New.Variety.UniversalFamily.smooth_and_isDenseFamily_and_exists_comp_eq_act` (Lib/Shimura/IntegralModel/UniversalFamily.lean).

**Lemma (Choice of the auxiliary level).** Let $\mathfrak{N} \neq 0$ and let $s$ be a finite set of pairs. There is $m$ such that $g^{-1} K(m) g \subseteq K(\mathfrak{N}) \cap K(\mathfrak{a})$ for all $(\mathfrak{a}, g)$ in $s \cup \{(1, 1), (m, 1)\}$.

Lean: `New.Variety.exists_level_conj_mem` (Lib/Shimura/HeckeTower/Model.lean).

*Proof.* Each condition on $k$ is open and holds at $k = 1$. Finitely many open conditions hold on a congruence subgroup $K(m)$. The pair $(m, 1)$ asks only for $K(m) \subseteq K(\mathfrak{N})$, which is the case of the pair $(1, 1)$. $\square$

**Theorem (Galois coverings from complex points).** Let $R$ be a countable domain with a map to $\mathbb{C}$ such that all maps from $R$ to fields of characteristic $0$ are injective. Let $c : W \to Z$ be surjective, with $W$ proper and $Z$ separated, and let $\Delta$ act on $W$ over $Z$ and simply transitively on the fibres of $c$ on complex points. Then $c$ is a Galois covering.

Lean: `New.Variety.isGaloisCovering_of_complex_points` (Lib/General/Geometry/GaloisCovers.lean).

### The two local fields

**Lemma (Möbius cancellation).** Let $W \neq 0$ be a subspace of $k_w^n$, and let $v$ be a map on subspaces with $v(A) = v'(A + W)$ for some $v'$. Then $\sum_A (-1)^{r_A} q^{\binom{r_A}{2}} [v(A)] = 0$.

Lean: `New.Variety.cancels_moebius_of_factorsThrough_sup` (Lib/Shimura/IntegralModel/TowerExistence.lean).

*Proof.* Write $\mu(A) = (-1)^{r_A} q^{\binom{r_A}{2}}$ and $F(B) = \sum_{A + W = B} \mu(A)$. The sum is $\sum_B F(B) [v'(B)]$, so it suffices that $F = 0$. For each $B$, $\sum_{B' \le B} F(B') = \sum_{A + W \le B} \mu(A)$. If $W \not\le B$ this is empty. Otherwise it is $\sum_{A \le B} \mu(A) = \prod_{j=0}^{m-1} (1 - q^j)$ with $m = \dim B \ge 1$, by the $q$-binomial theorem (`New.q_binomial_submodule`). The factor $j = 0$ is $0$. So all partial sums vanish, and Möbius inversion on the lattice of subspaces gives $F = 0$. $\square$

**Theorem (Congruence relation on a closure).** Let $D.\beta$ be the image of $(1 + \sqrt{-d_0})/2$ and let $C$ be a graph closure. Let $c$ send the point of $a$ to $\mathrm{datumPoint}_1(a)$. Let $w$ be split and safe for $D.\mathrm{level}$, let $D$ be good at $w$, let $q = l^f$, and let $\mathfrak{p}$ contain the image of $w$. Let the maps $u_A$ send the point of $a$ to $\mathrm{datumPoint}_1(a \cdot g_A)$. Then the $u_A$ satisfy the congruence relation modulo $\mathfrak{p}$ with coefficients $(-1)^{r_A} q^{\binom{r_A}{2}}$ and exponents $(|n| - r_A) f$.

Lean: `New.Variety.UniversalFamily.GraphClosure.congruenceRelation` (Lib/Shimura/IntegralModel/TowerExistence.lean).

*Proof.* A point $x$ in characteristic $l$ comes from a point $z$ with countable residue field, and $z$ is the centre of an arc (`New.Variety.UniversalFamily.GraphClosure.exists_arc`). On the arc, the Frobenius twists of the reduced Hecke neighbours depend only on $A + W$ for some $W \neq 0$. This geometric step is `New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup`, proved in [Chapter 3](/chapter/congruence-relation/). The Möbius lemma gives the cancellation on the residue field of the arc. It descends to $z$ and goes up to $k$, because Frobenius commutes with field maps. $\square$

**Theorem (Tangent map at a fixed point).** With $C$ and $c$ as above, let $v$ send the point of $a$ to $\mathrm{datumPoint}_1(a \cdot (g, \alpha))$. Let $z$ be an isomorphism from $a \cdot (g, \alpha)$ to $a$ at level $D.\mathrm{level}$ with separable characteristic polynomial, and let the reflection of $a$ be `markedReflection z μ`. Then `localTerm α z.charpoly μ` is a tangent polynomial for $(c, v)$ at the point of $a$, in dimension $|n| - 1 + \nu \cdot \mathrm{abelianDim}$.

Lean: `New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate` (Lib/Shimura/IntegralModel/TowerExistence.lean).

*Proof.* A ball family through $a$ gives a holomorphic family of points, and $z$ acts on its parameters near $0$ by a linear map $K$ with the determinant formula `localTerm`. The jet of the family embeds the parameters as a tangent space, injectively after $c$ since the family is immersed in the base, and $dv = dc \circ K$ by the chain rule. $\square$

### Proof of the existence theorem

*Proof of `New.Variety.exists_model`.* Choose $M(i)$ for each level $i$ by the lemma on the auxiliary level. Take the base $Z$ and the maps $m_\alpha$ from the theorem on the base. Let $W_i$ be the graph closure of the pairs $(\mathfrak{m}, \kappa g)$, with $\kappa$ in the finite quotient $\Delta_i$ of $K(\mathfrak{N})$ by the normal core of $K(M(i))$, and $(\mathfrak{m}, g)$ in $i \cup \{(1,1), (M(i), 1)\}$. The legs $p_g$ are the maps that translate points by $g$ (`New.Variety.UniversalFamily.GraphClosure.exists_forall_eq_apply_mk_of_translate`), and $s_i$ is the set of $g$ for which such a leg exists. Identities between legs follow from identities on the dense complex points. Properness comes from instances. For `covering`, the Galois criterion applies with $R$ as in `New.Variety.injective_of_subalgebra_of_charZero`. Freeness on complex points uses neatness: two deck maps that agree at a point differ by an automorphism of level $\mathfrak{N}$, which is trivial. The fields `tangent` and `congruence` are the two theorems above, with the hypothesis that $D$ is good at every safe place. $\square$

**Remark (Formalization).** $M(i)$ and the legs are chosen with `choose`, so the deck groups are not canonical. The later chapters use only the fields of the model.
