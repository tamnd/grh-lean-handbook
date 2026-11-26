---
title: The spaces and groups of the source
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Unitary/Defs.lean
  - Lib/Adelic/Unitary/GramMatrix.lean
  - Lib/Adelic/Unitary/ComponentsAndBlockSums.lean
  - Lib/Adelic/Unitary/WeakApproximation.lean
  - Lib/Adelic/Adeles/StrongApproximation.lean
decls:
  - New.HasPrimitiveRoot5040
  - New.HasPrimitiveRoot5040.exists_isUnit_sub_star
  - New.FinPlace.IsSplit
  - New.stdForm
  - New.Gf
  - New.G
  - New.G.toUnitary
  - New.stdLevel
  - New.mem_stdLevel
  - New.IsLevel
  - New.volume_stdLevel
  - New.ofSplitPlace
  - New.Space
  - New.Space.isHermitian_J
  - New.Space.ratEmbed
  - New.stdSpace
  - New.signedSpace
  - New.Space.discreteTopology_Gamma
  - New.Space.weak_approximation
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The spaces and groups of the source

This section gives the definitions of the source: the standing condition on roots of unity, the standard form, the adelic unitary group $G = G_\infty \times G_f$, the standard level $K_0$, and the hermitian spaces with a point. It ends with the discreteness of the rational points and with weak approximation. Each difference from Section 3 gets a remark.

Throughout, $E$ is a CM field with a CM type in the sense of Section 2, $F = E^+$, and $n$ is a finite index set. A family of signs is a map $s$ from $n$ to $\{\pm 1\}$.

### The standing condition

**Definition (Roots of unity of order 5040).** The CM field $E$ satisfies the *standing condition* if it contains a primitive root of unity of order $5040 = 7!$.

Lean: `New.HasPrimitiveRoot5040` (Lib/Adelic/Adeles/Basic.lean).

**Proposition.** Let $E$ satisfy the standing condition. Then $\mathcal{O}_E$ contains an element $i$ with $i^2 = -1$ and $\bar\imath = -i$, and an element $\omega$ with $\omega + \bar\omega = 1$ and $\omega\bar\omega = 2$. The element $y = i\omega$ has $y - \bar y = i$, which is a unit of $\mathcal{O}_E$.

Lean: `New.HasPrimitiveRoot5040.exists_mul_self_eq_neg_one`, `New.HasPrimitiveRoot5040.exists_add_star_eq_one_mul_star_eq_two`, `New.HasPrimitiveRoot5040.exists_isUnit_sub_star` (Lib/Adelic/Adeles/Basic.lean).

*Proof.* Since $4$ and $7$ divide $5040$, $\mathcal{O}_E$ contains a primitive fourth root of unity $i$ and a primitive seventh root of unity $\eta$. Complex conjugation inverts every root of unity of a CM field, so $\bar\imath = i^{-1} = -i$ and $\bar\eta = \eta^6$. Put $\omega = -(\eta + \eta^2 + \eta^4)$. Then $\bar\omega = -(\eta^3 + \eta^5 + \eta^6)$, and $\omega + \bar\omega = 1$ by $1 + \eta + \dots + \eta^6 = 0$. A direct computation with the same relation gives $\omega\bar\omega = 2$. Finally $y - \bar y = i\omega + i\bar\omega = i$, and $i \cdot (-i) = 1$. $\square$

The element $\omega$ is a root of $X^2 - X + 2$, of discriminant $-7$, so $\omega = (1 \pm \sqrt{-7})/2$. The source records the next consequence in a comment only. Its proof is classical.

**Remark.** Under the standing condition, $E$ is unramified over $F$ at every finite place. Indeed $E = F(i)$, since $i \notin F$, and $F(i)/F$ is unramified at every place not above $2$, since $X^2 + 1$ has discriminant $-4$. Also $E = F(\omega)$, and $F(\omega)/F$ is unramified at every place not above $7$, since $X^2 - X + 2$ has discriminant $-7$. A place lies above $2$ or above $7$, not both. The comments of the source call such a field *stably unramified*. A place above $2$ divides exactly one of $\omega$ and $\bar\omega$, since $\omega\bar\omega = 2$ and $\omega + \bar\omega = 1$. So no place above $2$ is fixed by conjugation.

**Remark (Formalization).** The plan of the book records that the constant $5040$ has no source in the documents of the source (F-058). The proofs of this chapter use only the divisors $4$ and $7$: the element $i$, the element $\omega$, and through them a $y$ with $y - \bar y$ a unit.

**Remark.** The standing condition forces $[F : \mathbb{Q}]$ to be even, that is, $E$ has an even number of infinite places. Let $\chi = \prod_v \chi_v$ be the quadratic character of the ideles of $F$ attached to $E/F$ by class field theory. It is trivial on $F^\times$. At a real place $\chi_v(-1) = -1$, since $E \otimes_F F_v = \mathbb{C}$. At a finite place $\chi_v$ is unramified by the remark above, so $\chi_v(-1) = 1$, since $-1$ is a unit. So $1 = \chi(-1) = (-1)^{[F:\mathbb{Q}]}$. The comparison of traces `New.trace_comparison` (Lib/Adelic/TraceFormula/TraceComparison.lean) takes the evenness as a separate hypothesis `hE`, next to the standing condition. By this remark the hypothesis follows from the standing condition. The source does not prove this implication.

### Finite places and conjugation

Complex conjugation acts on the finite places of $E$: $\bar w$ is the prime ideal of the conjugates of the elements of $w$. A finite place $w$ is *split* if $\bar w \neq w$. Then $w$ and $\bar w$ lie over one place of $F$, which splits in $E$.

Lean: `New.FinPlace.IsSplit` (Lib/Adelic/Adeles/Basic.lean).

### The standard form and the adelic group

**Definition (Standard form).** For signs $s$, the *standard form* $\varepsilon_s$ is the diagonal matrix over $\mathbb{A}_E$ that is $\mathrm{diag}(s)$ at every infinite place and the identity matrix at the finite places.

Lean: `New.stdForm` (Lib/Adelic/Unitary/Defs.lean).

**Definition (Adelic unitary group).** The *finite adelic unitary group* $G_f$ is the group of matrices $g \in \mathrm{GL}_n(\mathbb{A}_{E,f})$ with $g^* g = 1$. The *archimedean group* $G_\infty$ is the product over the infinite places of $E$ of copies of $U(\mathrm{diag}(s))$ over $\mathbb{C}$. The *adelic unitary group* is $G = G_\infty \times G_f$. The map $(g_\infty, g_f) \mapsto$ (the adelic matrix with components $g_w$ and finite part $g_f$) is an isomorphism of $G$ onto $U(\varepsilon_s)$, the unitary group of the standard form over $\mathbb{A}_E$.

Lean: `New.Gf`, `New.GInf`, `New.G`, `New.G.toUnitary` (Lib/Adelic/Unitary/Defs.lean).

The involution on $\mathbb{A}_{E,f}$ is conjugation, and it moves the component at $w$ to the place $\bar w$. So a matrix $g \in G_f$ has $g_{\bar w} = \overline{(g_w^*)^{-1}}$ at each finite place, after the identification of $E_{\bar w}$ with $E_w$ by conjugation. At a nonsplit place this says that $g_w$ is in the unitary group of the identity form over $E_w / F_v$. At a split pair it says that $g_{\bar w}$ is determined by $g_w$.

**Definition (Embedding at a split place).** Let $w$ be a split place. The homomorphism $\mathrm{GL}_n(E_w) \to G_f$ sends $g$ to the element with component $g$ at $w$, component $(g^*)^{-1}$ at $\bar w$ after conjugation, and $1$ at all other places. Its component at $w$ is $g$.

Lean: `New.ofSplitPlace`, `New.atPlace_ofSplitPlace` (Lib/Adelic/Unitary/Defs.lean).

**Remark (Formalization).** The classical group $U(V)(\mathbb{A}_F)$ is a group over the adeles of $F$. The source has no adeles of $F$ here. It uses $\mathbb{A}_{E,f}$ with its involution, and the group of fixed points of the involution plays the part of $\mathbb{A}_{F,f}$. Since $E \otimes_F \mathbb{A}_{F,f} = \mathbb{A}_{E,f}$, the group $G_f$ is $U_n(\mathbb{A}_{F,f})$ for the identity form, and the split places give the factors $\mathrm{GL}_n(F_v)$ of Section 3. The archimedean group has one factor for each infinite place of $E$, which is one for each real place of $F$, since $E$ is CM. All factors have the same signs $s$.

**Definition (Standard level).** The *standard level* $K_0$ is the subgroup $G_f \cap \mathrm{GL}_n(\hat{\mathcal{O}}_E)$ of $G_f$, the stabilizer of the lattice $\hat{\mathcal{O}}_E^n$. An element $g \in G_f$ lies in $K_0$ if and only if all entries of $g$ lie in $\hat{\mathcal{O}}_E$. The group $K_0$ is compact and open in $G_f$.

Lean: `New.stdLevel`, `New.mem_stdLevel`, `New.isCompact_stdLevel`, `New.isOpen_stdLevel` (Lib/Adelic/Unitary/Defs.lean).

The criterion of membership holds since $g^{-1} = g^*$ for $g \in G_f$: if the entries of $g$ are integral, so are those of $g^{-1}$.

**Definition (Level).** A subgroup $K$ of $G_f$ is a *level* if it is open and contained in $K_0$. A level is compact. The *index* of a subgroup $K$ of $G_f$ is $[K_0 : K \cap K_0]$.

Lean: `New.IsLevel`, `New.IsLevel.isCompact`, `New.stdLevelIndex` (Lib/Adelic/Unitary/Defs.lean).

**Remark (Formalization).** The index is the relative index of Mathlib. It is $0$ when the index is infinite. For a level the index is finite, since $K$ is open and $K_0$ is compact. A statement about the index of a subgroup that is not a level can have the value $0$ as a junk value.

**Theorem (Haar measure on $G_f$).** The source puts on $G_f$ the Haar measure with $\operatorname{vol}(K_0) = 1$.

Lean: `New.volume_stdLevel` (Lib/Adelic/Unitary/Defs.lean).

So the volume of a level $K$ is $1/[K_0 : K]$. Classical treatments often use the Tamagawa measure instead. The two differ by a constant that depends on $n$ and $E$. The measures of quotients in [quotients and reduction theory](/chapter/reduction-theory/) use the normalization of the source.

### Hermitian spaces with a point

**Definition (Hermitian space with a point).** A *space* with signs $s$ is a pair $V = (J, x)$ of a matrix $J \in M_n(E)$ and an adelic matrix $x \in \mathrm{GL}_n(\mathbb{A}_E)$ with
$$x^* J x = \varepsilon_s,$$
where $J$ is read in $M_n(\mathbb{A}_E)$ by the diagonal embedding. So the columns of $x$ are an orthonormal basis for $J$ at every finite place, and a basis with Gram matrix $\mathrm{diag}(s)$ at every infinite place.

Lean: `New.Space`, `New.Space.gram_point` (Lib/Adelic/Unitary/Defs.lean).

**Proposition.** The matrix $J$ of a space is hermitian and invertible.

Lean: `New.Space.isHermitian_J`, `New.Space.isUnit_J`, `New.Space.map_J` (Lib/Adelic/Unitary/GramMatrix.lean).

*Proof.* The image of $J$ in $M_n(\mathbb{A}_E)$ is $(x^{-1})^* \varepsilon_s x^{-1}$, which is hermitian and invertible. The diagonal embedding is injective and commutes with conjugation, and a matrix over $E$ is invertible if its image is. $\square$

**Remark (Formalization).** The structure of a space has three fields: $J$, $x$ and the identity $x^* J x = \varepsilon_s$. It does not ask that $J$ is hermitian. This follows from the third field, by the proposition. The background notes of the plan describe a space as a hermitian matrix with a point. That is true of every space, but it is a theorem, not a field.

**Remark (Formalization).** The definition restricts the spaces in two ways. First, a space is the identity form at every finite place. By Section 3, its discriminant is a local norm at every finite place, and the space has a unimodular lattice at every finite place: the lattice $E^n \cap x_f \hat{\mathcal{O}}_E^n$, which the source calls the base lattice. Second, the signature is the same at all infinite places. The classical theory allows any discriminant and a different signature at each real place of $F$. The argument uses only spaces of this restricted kind. A space also carries a chosen point $x$, which the classical notion does not. Two points of the same $J$ differ by an element of $G$ on the right, by the definition of $G$ as $U(\varepsilon_s)$.

**Definition (Rational points).** Let $V = (J, x)$ be a space. The map $\gamma \mapsto x^{-1}\gamma x$ sends the rational unitary group $U(J)(E)$ into $G$. Its image is the group $\Gamma_V$ of rational points of $V$. Its finite part $\Gamma_{V,f}$ is the image of $\gamma \mapsto (x^{-1}\gamma x)_f$ in $G_f$. The *base lattice* of $V$ is $E^n \cap x_f \hat{\mathcal{O}}_E^n$, the set of $y \in E^n$ such that $x^{-1} y$ has integral finite part.

Lean: `New.Space.ratEmbed`, `New.Space.toRatCoords`, `New.Space.Γ`, `New.Space.Γf`, `New.Space.baseLattice` (Lib/Adelic/Unitary/Defs.lean).

The point $x$ thus moves the rational group into the standard coordinates. In these coordinates every space with signs $s$ has the same adelic group $G$, and only the discrete subgroup $\Gamma_V$ depends on $V$.

**Definition (Standard spaces).** The *definite standard space* $I_n$ is $(1, 1)$, with all signs $+1$. Under the standing condition, the *signed space* with signs $s$ is $(\mathrm{diag}(s), x_s)$, where $x_s$ is diagonal, with entry $1$ where $s_i = 1$, and entry $(1, \epsilon)$ where $s_i = -1$. Here $\epsilon$ is a chosen unit of $\hat{\mathcal{O}}_E$ with $\bar\epsilon\epsilon = -1$.

Lean: `New.stdSpace`, `New.signedSpace`, `New.Weil.normNegOne`, `New.normNegOneIdele` (Lib/Adelic/Unitary/Defs.lean, Lib/Adelic/Unitary/ComponentsAndBlockSums.lean).

The unit $\epsilon$ exists by the local theory: $-1$ is fixed by conjugation and is a unit at every place, so it is a norm of a unit of $\hat{\mathcal{O}}_E$ (`New.exists_unit_star_mul_self_eq`, Section 5). The unit is chosen by `choose`. A different choice gives a different point, and the two points differ by an element of $K_0$ on the right. The space $I_n$ needs no condition on $E$.

The source also forms the orthogonal sum $V \perp W$ of two spaces, with block diagonal matrix and point; the negative $-V = (-J, \epsilon x)$, which needs the standing condition; and the moved space $(J, xg)$ for $g \in G$.

Lean: `New.Space.sum`, `New.Space.neg`, `New.Space.move` (Lib/Adelic/Unitary/ComponentsAndBlockSums.lean).

### Discreteness and weak approximation

**Proposition.** For every space $V$, the group $\Gamma_V$ is discrete in $G$.

Lean: `New.Space.discreteTopology_Gamma` (Lib/Adelic/Adeles/StrongApproximation.lean).

*Proof.* The map $g \mapsto x g x^{-1}$ is continuous and injective, and it sends $\Gamma_V$ into the matrices over $E$, read in $M_n(\mathbb{A}_E)$. These form a discrete subgroup, by the lattice theorem of Section 2 applied to each entry. $\square$

**Theorem (Weak approximation).** Let $V$ be a space and let $S$ be a finite set of finite places of $E$. Let $G_f^S$ be the subgroup of $G_f$ of elements with component $1$ at every place of $S$. Then the products $\gamma \cdot (1, h)$, with $\gamma \in \Gamma_V$ and $h \in G_f^S$, are dense in $G$.

Lean: `New.Space.weak_approximation`, `New.Gf.trivialOn` (Lib/Adelic/Unitary/WeakApproximation.lean).

So $\Gamma_V$ is dense in the product of $G_\infty$ with the components at the places of $S$. The proof uses the Cayley transform. For a rational skew matrix $u$ with $1 + u$ invertible, $(1 - u)(1 + u)^{-1}$ is in the unitary group of $J$. By strong approximation for matrices, rational matrices approach any given adelic matrix at the infinite places and at the places of $S$ and $\bar S$. For all but finitely many values of an auxiliary unitary scalar $c$, the rescaled Cayley transforms of the corresponding skew matrices tend to the given element at these places. An element of $G_f^S$ corrects the other components. $\square$

**Remark (Formalization).** The classical weak approximation for $U(V)$ is a statement about the places of $F$. The source states it for a set $S$ of places of $E$. Since an element of $G_f$ with component $1$ at $w$ also has component $1$ at $\bar w$, the theorem controls the places of $S$ and of $\bar S$ together. The finite parts of the rational points of a definite space form a discrete subgroup of $G_f$, since $G_\infty$ is then compact. The source proves this as an instance for spaces whose signs are all $1$, in Lib/Adelic/Unitary/WeakApproximation.lean.
