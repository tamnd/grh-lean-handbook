---
title: The flat closure and the theta family
lean:
  - Lib/Shimura/ThetaModuli/FlatClosure.lean
  - Lib/Shimura/ThetaModuli/FamilyFromPoints.lean
  - Lib/Shimura/ThetaModuli/ThetaFamilyRigidity.lean
decls:
  - New.Variety.ThetaNull.IsCutDegree
  - New.Variety.ThetaNull.eventually_isCutDegree
  - New.Variety.ThetaNull.thetaRanks
  - New.Variety.ThetaNull.IsCutOutAt
  - New.Variety.ThetaNull.eq_map_and_flat_of_isCutOut
  - New.Variety.ThetaNull.IsFlatClosure
  - New.Variety.ThetaNull.exists_isFlatClosure
  - New.IsAbelianScheme
  - New.ThetaFamily
  - New.ThetaFamily.IsModelledOn
  - New.Variety.ThetaNull.IsNonvanishingIndex
  - New.Variety.exists_maps_of_riemann_relation
  - New.Variety.exists_thetaFamily_of_points
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The flat closure and the theta family

Section 4 controls the ideal of the reduced theta points at each point over a good place. This section turns that pointwise statement into a flat family, and puts a group law on it with Riemann's relation. The result is a *theta family*: an abelian scheme with an action of $\mathcal{O}_E$, a projective embedding by theta coordinates, and level points.

### The model case: a flat closure in one variable

Let $O$ be a discrete valuation ring with fraction field $K$, and let $Z_K \subset \mathbb{P}^m_K$ be a closed subscheme. The schematic closure $Z$ of $Z_K$ in $\mathbb{P}^m_O$ is flat over $O$, because its local rings are torsion free (Hartshorne, *Algebraic Geometry*, III.9.8). Its special fibre has the same Hilbert polynomial as $Z_K$ (Hartshorne, III.9.9). Over a base of higher dimension the closure need not be flat. The criterion of the source: if at every point the ideal of the fibre has the expected Hilbert function and is cut out by points that lift, the closure is flat.

### A degree bound for monomial ideals

**Definition (Degree bound).** Let $J$ be a finite set, $r \in \mathbb{N}$, and $\sigma : \mathbb{N} \to \mathbb{N}$. A number $d$ is a *degree bound* for $(J, r, \sigma)$ when every monomial ideal $M$ in the variables $J$ that leaves out at most $\sigma(i)$ monomials of degree $r^i$ for all $i \leq d$ does so for all $i$.

Lean: `New.Variety.ThetaNull.IsCutDegree` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

**Lemma (Degree bounds exist).** For finite $J$, every large enough $d$ is a degree bound for $(J, r, \sigma)$.

Lean: `New.Variety.ThetaNull.eventually_isCutDegree` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

*Proof.* The monomial ideals of $\mathbb{N}^J$ satisfy the ascending chain condition (Dickson's lemma). The source runs a Noetherian induction: an ideal that leaves too many monomials in a degree $r^i$ is enlarged by a monomial of that degree, and the chain must stop. $\square$

The datum $D$ carries one such bound, `D.exponentBound`, for the ranks below.

**Definition (Theta ranks).** For a subgroup $T$ of an additive group $G$, put $\sigma_T(j) = \lfloor \sqrt{\#\{y \in G : r^j y \in T\}} \rfloor$.

Lean: `New.Variety.ThetaNull.thetaRanks` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

With $G$ the adelic torsion and $T = D.\mathrm{dualTorsion}$, the set $\{y : r^j y \in T\}$ is the group $r^{-j}T$. So $\sigma_T(j)$ is the dimension of the space of theta functions of degree $r^j$ (Birkenhake and Lange, *Complex Abelian Varieties*, Chapter 3).

**Remark (Formalization).** The group $G$ is an arbitrary additive group, and `Nat.card` is $0$ on infinite types. In the use here the set is finite, since $T$ is finite and $r^j$ has finite kernel.

### Ideals cut out at a point

**Definition (Cut out at a point).** Let $S$ be a scheme, $(P_a)_{a \in I}$ maps from $S$ to $\mathbb{P}^{J}$ given as linear systems, $t$ a point of $S$ with values in a field $k$, and $Z \subseteq k^J$ a set. Then $P$ *cuts out $Z$ at $t$*, with ranks $\sigma$ and bound $i$, when the following holds for all choices $l$ of charts of the $P_a$ at $t$ and every $c \in J$. The vanishing ideal of the points $v / v_c$, $v \in Z$ with $v_c \neq 0$, is cut out in the chart $c$ by the affine coordinates of the $P_a(t)$ in the charts $l_a$, with ranks $\sigma$ and bound $i$.

Lean: `New.Variety.ThetaNull.IsCutOutAt` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

**Lemma (Flatness from cut-out ideals).** Let $A$ be a ring, $\varphi : A \to k$ a local homomorphism to a field, and $\psi_n : A \to K$, $n \in \kappa$, ring maps to a field such that only $0$ lies in the kernel of all $\psi_n$. Let $1 < r$, and let $i$ be a degree bound for $(J, r, \sigma)$. Let $P_a \in A^J$ be points. Assume that the ideal $I_0$ over $k$ is cut out in the chart $c$ by the points $\varphi(P_a)$, and each ideal $I_n$ over $K$ by the points $\psi_n(P_a)$, all with ranks $\sigma$ and bound $i$. Let $T$ be the ideal of polynomials $f$ over $A$ with $\psi_n(f) \in I_n$ for all $n$. Then $I_0 = \varphi(T)$, and $A[X_J]/T$ is flat over $A$.

Lean: `New.Variety.ThetaNull.eq_map_and_flat_of_isCutOut` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

*Proof.* Fix a monomial order. Call a monomial *standard* if it is not the leading monomial of the reduction of a form in $T$. The standard monomials form the complement of a monomial ideal. In each degree $r^j$ with $j \leq i$ there are at most $\sigma(j)$ standard monomials: the source builds forms with the needed leading monomials from determinants of the values at the points $P_a$, which have unit leading coefficient since $\varphi$ is local. Since $i$ is a degree bound, the same count holds in every degree $r^j$. Division shows that they span the quotient by $T$ in each degree, and the ranks $\sigma(j)$ show that they are independent modulo $I_0$ and each $I_n$. So the quotient is free in each degree, and $\varphi(T) = I_0$. $\square$

### The flat closure

**Definition (Flat closure).** Let $S$ be a scheme with complex points $\eta_n$, $n \in \kappa$, and let $\theta_n(z) \in \mathbb{C}^J$ be vectors for $z \in W$. A scheme $A$ over $S$ with a linear system $N$ and points $e_n(z)$ of $A$ over $\eta_n$ is a *flat closure* of the $\theta_n(z)$ when:

1. $N$ embeds $A$ in projective space over $S$, and $A$ is proper over $S$;
2. $A$ is flat over $S$;
3. $e_n(z)$ has homogeneous coordinates $\theta_n(z)$;
4. the fibre of $A$ over each $\eta_n$ is reduced, and the points $e_n(z)$ are dense in it;
5. every point of $S$ specializes to a geometric point over which the fibre is reduced;
6. $A$ is reduced, and all the points $e_n(z)$ together are dense in it.

Lean: `New.Variety.ThetaNull.IsFlatClosure` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

**Theorem (Existence of the flat closure).** Let $S$ be a reduced scheme with complex points $\eta_n$, $n \in \kappa$, and let $j : \iota \to \kappa$ with $\iota$ finite be such that the $\eta_{j(a)}$ are dense. Let $(P_a)_{a \in I}$ be linear systems on $S$ with values in $\mathbb{P}^J$, $J$ finite. Let $1 < r$ and let $i$ be a degree bound for $(J, r, \sigma)$. Let $\theta_n(v) \in \mathbb{C}^J$ be nonzero vectors such that $P$ cuts out $\{\theta_n(v)\}_v$ at $\eta_n$ for each $n$. Assume that every point of $S$ specializes to a geometric point $t$ at which $P$ cuts out some set. Then a flat closure of the $\theta_n(v)$ exists.

Lean: `New.Variety.ThetaNull.exists_isFlatClosure` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

*Proof.* Let $A$ be the reduced closure in $\mathbb{P}^J \times S$ of the points with coordinates $\theta_{j(a)}(v)$ over $\eta_{j(a)}$. The lemma `exists_reduced_projective_closure` gives $A$ with its embedding and dense points. Fix a geometric point $t$ at which some set $Z$ is cut out. In the local ring at $t$, the complex points give the maps $\psi_n$, with no common kernel since $S$ is reduced, and $t$ gives $\varphi$. The flatness lemma applies in each chart of $N$ at $t$. It shows that $A$ is flat near $t$ and that the fibre over $t$ has the vanishing ideal of $Z$, which is reduced. Every point specializes to such a $t$, so $A$ is flat everywhere. $\square$

### Theta families

**Definition (Abelian scheme).** A commutative group scheme $A$ over $S$ is an *abelian scheme* when it is smooth and proper over $S$ and multiplication by every $m \neq 0$ is surjective.

Lean: `New.IsAbelianScheme` (Lib/Shimura/AbelianScheme/Basic.lean).

**Remark (Formalization).** The textbook definition asks also that the fibres be geometrically connected (Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, Definition 6.1). The source does not state this (finding F-062 and question Q-63 of the plan). The source definition implies it, by an argument that is not in the source. On a geometric fibre $A_{\bar s}$, multiplication by $m$ is surjective, since surjectivity is stable under base change. The component group $F$ of $A_{\bar s}$ is finite, and multiplication by $m$ is onto $F$. Take $m = |F|$: then $F = mF = 0$.

**Definition (Theta family).** Let $D$ be a PEL datum of the source and $S$ a scheme over $\mathcal{O}_E$. A *theta family* for $D$ over $S$ consists of:

1. an abelian scheme $A$ over $S$ with an action of $\mathcal{O}_E$;
2. a linear system $N$ on $A$ with coordinates indexed by $T = D.\mathrm{dualTorsion}$ that embeds $A$ in projective space over $S$;
3. an $\mathcal{O}_E$-linear map from the level torsion $D.\mathrm{levelTorsion}$ to the sections of $A$, the *level points*;
4. the *theta law*: after any base change to a local ring, the coordinates of $N$ are theta coordinates for the Lagrangian of $D$ with respect to the level points;
5. the class laws of the datum for the class of $N$;
6. the *signature condition*: over a local ring, the action of $\bar\beta - b$ and $\beta - b$ on the Lie algebra satisfies the rank one condition of Section 2;
7. smoothness of $A$ over $S$ of relative dimension `abelianDim` $= n[E : \mathbb{Q}]/2$;
8. a *rigidity* condition: two points of $S$ over $\mathcal{O}_E$ with affine source are equal when the coordinates of their level points agree.

Lean: `New.ThetaFamily` (Lib/Shimura/ThetaModuli/ThetaFamilyRigidity.lean).

The docstring says "No universal property is asked for". Condition 8 is the only trace of a moduli property. It is the theta-null embedding of Mumford, *On the equations defining abelian varieties I*, §4.

**Definition (Modelled on a torus).** The fibre of a theta family $X$ at a complex point $t$ is *modelled on* the theta torus $x$ when it has a torus model for the period map of $x$ whose theta coordinates are the theta functions $\theta_k$ of $x$.

Lean: `New.ThetaFamily.IsModelledOn` (Lib/Shimura/ThetaModuli/FamilyFromPoints.lean).

### A theta family from points

**Definition (Nonvanishing index).** Let $c$ be a family of line bundles on $S$ indexed by the level torsion, with charts indexed by $T$. An index $a \in T$ is *nonvanishing* at a point $t$ of $S$ when $t$ lies in the chart $k$ of $c(l)$ for all $l, k \in T$ with $l + k = a$.

Lean: `New.Variety.ThetaNull.IsNonvanishingIndex` (Lib/Shimura/ThetaModuli/FamilyFromPoints.lean).

**Theorem (Theta family from points).** Let $S$ be a reduced, locally noetherian scheme over $\operatorname{Spec} R$, with a ring map $\varphi : \mathcal{O}_E \to R$ such that $\operatorname{Spec} R \to \operatorname{Spec} \mathcal{O}_E$ is a monomorphism. Let $\eta_k$, $k \in \kappa$, be complex points of $S$ over the base place $v_0$, with a finite dense subfamily $\eta_{j(i)}$. Let $x_k$ be theta tori for $D$, and let $c_\omega$, $\omega$ in the level torsion, be linear systems on $S$ whose product embeds $S$ in projective space over $R$. Assume:

1. at $\eta_k$, the linear system $c_\omega$ has the homogeneous coordinates $(\theta_s(\text{lift of } \omega))_{s \in T}$ of $x_k$;
2. $\varphi(\bar\beta - \beta)$ and $|T|$ are units of $R$;
3. every point of $S$ specializes to a geometric point at which the $c_\omega$ cut out some set, with ranks `thetaRanks T r` and bound $D.\mathrm{exponentBound}$;
4. for every point $t$ of $S$ and every $s \in T$ there is $a \in T$ such that $a$, $-a$ and $s - a$ are nonvanishing at $t$.

Then there is a theta family $X$ for $D$ over $S$ whose fibre at each $\eta_k$ is modelled on $x_k$.

Lean: `New.Variety.exists_thetaFamily_of_points` (Lib/Shimura/ThetaModuli/FamilyFromPoints.lean).

*Proof.* The flat closure theorem gives $A$, $N$ and the points $e_k(z)$, with the theta coordinates $\theta_s(z)$ of $x_k$; its hypotheses come from condition 3 and from Section 4 at the complex points. The group law comes from Riemann's relation in the following form.

**Lemma (Extension along Riemann's relation).** Let $p$ and $q$ be Riemann tuples whose first two pairs are $(1, 0)$, and let $|T|$ be a unit of $R$. Assume condition 4. If for each pair $(a, b)$ of the doubled tuple of $(q, p)$ the map $(z, y) \mapsto az + by$ of the tori extends to a morphism $A \times_S A \to A$, then the same holds for the doubled tuple of $(p, q)$, and the pull-backs of $N$ along the two families of maps have products of the same class.

Lean: `New.Variety.exists_maps_of_riemann_relation` (Lib/Shimura/ThetaModuli/FamilyFromPoints.lean).

The proof of the lemma writes the coordinates of $az + by$ near a point $t$ by Riemann's relation. Near $t$ the theta-null values for nonvanishing indices are units, and $|T|^{-1}$ is regular. So the new map is given locally by regular functions that agree with $az + by$ at the dense points.

Apply the lemma to two padding tuples of Section 4: the tuple for $c = -1$ with a padding $a$ of $1$ whose entries $a_l$ span $\mathcal{O}_E$ (the datum gives one, `D.hasPadding_one`), and the tuple for $c = 0$ with all entries $1$. The lemma gives morphisms for the pairs $(1, 1)$, $(-1, 1)$ and $(a_l, 0)$ of the first tuple, that is, the addition, the subtraction and the action of each $a_l$ (the lemma `New.Variety.exists_add_and_intAction`). The $d \in \mathcal{O}_E$ whose action extends form a subgroup that contains the $a_l$, so it is $\mathcal{O}_E$. The axioms hold at the dense points, so they hold on $A$ (`New.exists_isAbelianScheme`). Smoothness and the signature condition reduce to the action on $V$ at the dense points. Rigidity comes from the embedding of $S$ by the $c_\omega$. $\square$

**Remark (Formalization).** Condition 4 is stated at every point of $S$, including the special fibres. Section 6 checks it with the theta-null lemma of Section 4, for a valuation of $\mathbb{C}$ that extends the place.
