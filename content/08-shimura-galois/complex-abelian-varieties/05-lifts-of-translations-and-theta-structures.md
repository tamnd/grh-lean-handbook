---
title: Lifts of translations and theta structures
lean:
  - Lib/Shimura/ThetaGroup.lean
decls:
  - New.Variety.IsSectionLift
  - New.Variety.IsTranslationLift
  - New.Variety.coordSection
  - New.Variety.IsSectionLift.picClass_eq
  - New.Variety.exists_isSectionLift
  - New.Variety.IsSectionLift.exists_eq_smul
  - New.Variety.IsTranslationLift.mul
  - New.Variety.IsTranslationLift.pow
  - New.Variety.exists_isTranslationLift_iff
  - New.Variety.IsThetaStructure
  - New.Variety.IsThetaStructure.pull_eq_of_intertwines
  - New.Variety.IsThetaStructure.pull_eq_of_picClass_eq
  - New.Variety.IsThetaStructure.card_nsmul_eq_zero_of_isTranslationLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lifts of translations and theta structures

In [Section 3](/chapter/complex-abelian-varieties/) the twisted translations $\Theta_z$ acted on the space of theta functions, and for $z$ in the dual lattice they sent the space to itself. The operators did not commute. They formed a Heisenberg group, and its irreducibility gave the dimension formula. This section does the same over any base ring, with the algebraic tools of [Section 4](/chapter/complex-abelian-varieties/). A translation of an abelian scheme acts on the sections of a line bundle $L$ only after the choice of an isomorphism $t_z^* L \cong L$. Such an isomorphism exists exactly for $z$ in the kernel $K(L)$ of the pairing. A *theta structure* is a choice of coordinates in which these actions take a standard form. Its main use is rigidity: a homomorphism that respects the theta structures and the classes of the bundles respects the coordinates.

The textbook objects are the theta group $\mathcal{G}(L)$ of pairs $(z, \varphi)$ with $\varphi \colon \mathcal{L} \xrightarrow{\sim} t_z^*\mathcal{L}$, the group $K(L)$ of points $z$ with $t_z^* \mathcal{L} \cong \mathcal{L}$, and the exact sequence $1 \to \mathbb{G}_m \to \mathcal{G}(L) \to K(L) \to 0$ (Mumford, *Abelian Varieties*, Section 23). A theta structure in the textbook sense is an isomorphism of $\mathcal{G}(L)$ with a standard Heisenberg group (Mumford, "On the equations defining abelian varieties I", Invent. Math. 1 (1966), Section 1). The source does not form the group $\mathcal{G}(L)$. It works with the maps on global sections that its elements induce.

### Lifts of morphisms to sections

Let $f \colon X' \to X$ be a morphism of schemes, $L$ a line bundle on $X$ and $L'$ a line bundle on $X'$. Line bundles are cocycles on a cover, and $H^0(L)$ is the module of global sections, as in [Schemes through their points](/chapter/schemes-through-points/).

**Definition (Section lift).** A map $\Phi \colon H^0(L) \to H^0(L')$ is a *lift* of $f$ if there is an isomorphism $u \colon f^* L \cong L'$, given as a frame of $L' \otimes (f^*L)^{-1}$, such that $\Phi(s) = u \cdot f^* s$ in local coordinates for every global section $s$.

Lean: `New.Variety.IsSectionLift` (Lib/Shimura/ThetaGroup.lean).

**Definition (Translation lift).** Let $A$ be a commutative group object over $\operatorname{Spec} R$ and $z$ a section of $A$ over $R$. An $R$-linear endomorphism $\Phi$ of $H^0(L)$ is a *lift of the translation* by $z$ if it is a lift of $t_z \colon y \mapsto y + z$ from $L$ to $L$.

Lean: `New.Variety.IsTranslationLift` (Lib/Shimura/ThetaGroup.lean).

**Definition (Coordinate section).** Let $L$ be a linear system with index set $\iota$, that is, $L$ is given by sections $X_j$, $j \in \iota$, without common zero, and its transition functions are $g_{ij} = X_j / X_i$ on $U_i = \{X_i \neq 0\}$. The *coordinate section* $X_j \in H^0(L)$ is the section with local components $g_{ij}$.

Lean: `New.Variety.coordSection` (Lib/Shimura/ThetaGroup.lean).

In the complex model case, $L$ is the bundle of theta functions of type $(B, \chi)$, the coordinate sections are a basis $\theta_j$ of the space of theta functions, and $\Theta_z$ is a translation lift for $z$ in the dual lattice.

**Proposition.** If $\Phi$ is a lift of $f$ from $L$ to $L'$, then $[L'] = f^*[L]$ in $\operatorname{Pic}(X')$. Conversely, let $F \colon Y \to X$ be a morphism over $\operatorname{Spec} R$ and $N$ a line bundle on $Y$ with $[N] = F^*[L]$. Then there is an $R$-linear lift $\Phi \colon H^0(L) \to H^0(N)$ of $F$.

Lean: `New.Variety.IsSectionLift.picClass_eq` and `New.Variety.exists_isSectionLift` (Lib/Shimura/ThetaGroup.lean).

*Proof.* Two line bundles have the same class exactly when there is a frame of $L' \otimes (f^* L)^{-1}$. The first claim reads the frame off the lift. For the second, take a frame $u$ of $N \otimes (F^*L)^{-1}$ and put $\Phi(s) = u \cdot F^* s$. The local formula is additive and $R$-linear in $s$. $\square$

**Proposition.** Let $X'$ be a commutative group object over $\operatorname{Spec} R'$ whose structure map has constant functions in the sense of [Section 4](/chapter/complex-abelian-varieties/). If $\Phi$ and $\Psi$ are lifts of the same morphism $f$ from $L$ to $L'$, then there is $c \in R'$ with $\Phi(s) = c\,\Psi(s)$ for all $s \in H^0(L)$.

Lean: `New.Variety.IsSectionLift.exists_eq_smul` (Lib/Shimura/ThetaGroup.lean).

*Proof.* The two frames differ by a global function $c$ on $X'$. By the hypothesis, $c$ takes at every point the value that it takes at the zero section. So $c$ is the constant given by its value at zero. $\square$

The constant $c$ can be $0$ only if the frames vanish somewhere, which they do not: $c$ is a unit. The statement does not record this, and the proofs below do not need it.

### Lifts of translations and the group $K(L)$

**Proposition.** Let $\Phi$ and $\Psi$ be lifts of the translations by $z$ and by $w$. Then $\Phi \Psi$ is a lift of the translation by $z + w$, and $\Phi^k$ is a lift of the translation by $k z$ for every natural number $k$.

Lean: `New.Variety.IsTranslationLift.mul` and `New.Variety.IsTranslationLift.pow` (Lib/Shimura/ThetaGroup.lean).

**Theorem.** Let $R$ be a local ring, $A$ a commutative group object over $\operatorname{Spec} R$, $L$ a line bundle on $A$ and $z$ a section of $A$ over $R$. Write $\pi \colon A \to \operatorname{Spec} R$ for the structure map. The translation by $z$ has a lift to $L$ if and only if
$$\langle z \circ \pi, 1_A \rangle_{[L]} = 0 \quad \text{in } \operatorname{Pic}(A).$$

Lean: `New.Variety.exists_isTranslationLift_iff` (Lib/Shimura/ThetaGroup.lean).

*Proof.* By the first proposition of this section, a lift exists if and only if $t_z^*[L] = [L]$. By the definition of the pairing, $\langle z \circ \pi, 1_A \rangle = t_z^*[L] - (z\circ\pi)^*[L] - [L] + 0^*[L]$. The two middle terms are pulled back from $\operatorname{Spec} R$, whose Picard group is trivial since $R$ is local. So the pairing is $t_z^*[L] - [L]$. $\square$

So over a local ring the sections $z$ that have lifts are exactly the sections of $K(L)$. On an abelian variety over $\mathbb{C}$ with $L$ of type $(B, \chi)$, $K(L)$ is $L^\perp / L$, where $L^\perp$ is the dual lattice of [Section 2](/chapter/complex-abelian-varieties/), and the lifts are the operators $\Theta_z$ up to scalars (Birkenhake and Lange, *Complex Abelian Varieties*, Chapter 2).

### Theta structures

In [Section 3](/chapter/complex-abelian-varieties/) the canonical multiplier gave operators $\Theta_z$ with a Heisenberg law. In a basis adapted to a Lagrangian decomposition of $L^\perp/L$, these operators permute the basis vectors and multiply them by roots of unity. The definition below takes this form as an axiom on a linear system. It also asks for lifts of the maps $y \mapsto -y + \eta(s)$, which correspond to a symmetric bundle.

**Definition (Theta structure).** Let $R$ be a ring, $A$ a commutative group object over $\operatorname{Spec} R$, $H$ an abelian group, $L_g \subseteq H$ a subgroup, $\eta \colon H \to A(R)$ a homomorphism to the group of sections, and $N$ a linear system on $A$ whose coordinates $X_t$ are indexed by $t \in H$. Let $c \colon H \to \widehat{H}_R$ assign to each $s \in H$ a character $c_s \colon H \to R^\times$. The data form a *theta structure* if the following hold.

1. Symmetry: $c_s(-t) = c_t(s)$ for all $s, t \in H$.
2. The theta law: for every $m \in \{1, -1\}$ and $s \in H$, the map $y \mapsto m y + \eta(s)$ has a lift $\Phi$ from $N$ to $N$ with $\Phi(X_t) = c_s(t)\,X_{m(s + t)}$ for all $t \in H$.
3. $X_s = X_0$ for all $s \in L_g$.
4. The number $|H|$ is a unit in $R$.
5. For every $s \notin L_g$, $\sum_{l \in L_g} c_s(l)^2 = 0$.

Lean: `New.Variety.IsThetaStructure` (Lib/Shimura/ThetaGroup.lean).

**Remark (Formalization).** The number $|H|$ in condition 4 is `Nat.card H`, which is $0$ for an infinite group. Then condition 4 asks that $0$ is a unit, which holds only in the zero ring. The theorems below assume `[Finite H]` in any case. In condition 5 the sum runs over a `Fintype` instance on $L_g$, so it is only meaningful when $L_g$ is finite. The definition does not ask that $\eta$ is injective, that $N$ is symmetric, or that the coordinates are a basis of $H^0(N)$. Where the theorems need spanning, they assume it.

The textbook form is an isomorphism of the theta group of a symmetric bundle with the Heisenberg group of $K(\delta) \times \widehat{K(\delta)}$ that is compatible with the inverse map (Mumford, "On the equations defining abelian varieties I", Section 2). The source does not need the isomorphism. Its proofs use only the action on the coordinates, so the definition records only this action. In the next chapter the theta structures come from the family of theta-null points, where the theta law holds by construction.

In the proofs below, the lifts that the theta law gives are chosen by `choose`. Each is unique only up to a scalar, by the proposition on proportional lifts, and the proofs use only relations that hold for every choice.

### Rigidity

**Lemma.** Let $(N, \eta, c)$ be a theta structure on $A$ with $H$ finite, and assume that the coordinates $X_t$ span $H^0(N)$. Let $(N', \eta', c')$ be a theta structure on $A'$ for the same $H$ and $L_g$, with coordinates $X'_t$. Let $U_s$ be endomorphisms of $H^0(N)$ with $U_s(X_t) = c_s(t)\,X_{s + t}$. Let $T \colon H^0(N') \to H^0(N)$ be a lift of $f \colon A \to A'$ with $T(X'_s) = U_s(T(X'_0))$ for all $s \in H$. Then $f^* N' = N$ as linear systems.

Lean: `New.Variety.IsThetaStructure.pull_eq_of_intertwines` (Lib/Shimura/ThetaGroup.lean).

*Proof.* It is enough to show that $T(X'_0) = a X_0$ for some $a \in R$. Then $T(X'_s) = U_s(a X_0) = a\,c_s(0)\,X_s = a X_s$, and a lift that multiplies every coordinate by the same scalar shows $f^*N' = N$.

First, for $l \in L_g$ and $t \in H$, apply $U_t$ to $X_l = X_0$. This gives $c_t(l)\,X_{t + l} = X_t$, so $X_{t + l} = c_t(-l)\,X_t$. Put $P = \sum_{l \in L_g} U_{-l}$. For $t \in L_g$, $P(X_t) = |L_g| X_0$. For $t \notin L_g$,
$$P(X_t) = \sum_{l \in L_g} c_{-l}(t)\,X_{t - l} = \Big(\sum_{l \in L_g} c_t(l)^2\Big) X_t = 0,$$
by the symmetry of $c$ and condition 5. Since the coordinates span, the image of $P$ lies in $R X_0$.

Second, apply $P$ to $T(X'_0)$. By the hypothesis on $T$ and condition 3 for $N'$, $U_{-l}(T(X'_0)) = T(X'_{-l}) = T(X'_0)$. So $P(T(X'_0)) = |L_g|\,T(X'_0)$. The order $|L_g|$ divides $|H|$, so it is a unit. Hence $T(X'_0) \in R X_0$. $\square$

**Theorem (Rigidity).** Let $(N, \eta, c)$ on $A$ and $(N', \eta', c')$ on $A'$ be theta structures over $R$ for the same finite group $H$ and the same subgroup $L_g$. Assume:

1. the structure map $A \to \operatorname{Spec} R$ has constant functions;
2. the coordinates of $N$ span $H^0(N)$;
3. $|H|$ is odd;
4. $f \colon A \to A'$ is a homomorphism with $f \circ \eta(s) = \eta'(s)$ for all $s \in H$;
5. $[N] = f^*[N']$ in $\operatorname{Pic}(A)$.

Then $f^* N' = N$ as linear systems.

Lean: `New.Variety.IsThetaStructure.pull_eq_of_picClass_eq` (Lib/Shimura/ThetaGroup.lean).

Note that $A$ and $A'$ need only be commutative group objects. The theorem does not ask them to be abelian schemes.

*Proof.* By hypothesis 5 there is a lift $T$ of $f$. Let $U_{m,s}$ and $U'_{m,s}$ be the lifts of the theta law on $A$ and $A'$. Since $f$ is additive and carries $\eta$ to $\eta'$, the maps $T \circ U'_{m,s}$ and $U_{m,s} \circ T$ are lifts of the same morphism $A \to A'$. By hypothesis 1 and the proposition on proportional lifts, $T \circ U'_{m,s} = b_{m,s}\,U_{m,s} \circ T$ for some $b_{m,s} \in R$.

A computation on the coordinates, with the character property and the symmetry of $c$, gives the relation
$$U_{1, 2s}\,U_{-1, 0}\,U_{1, s} = U_{1, s}\,U_{-1, 0}$$
on $H^0(N)$, since both sides send $X_t$ to the same multiple of $X_{s - t}$. The same relation holds on $H^0(N')$. Move $T$ through both sides. The scalars $b_{1,s} b_{-1,0}$ appear on both sides and cancel, and one gets $T(U'_{1,s}U'_{-1,0}v) = U_{1,2s}\,T(U'_{-1,0}U'_{1,s}v)$ for all $v$. At $v = X'_{-s}$ both sides carry the unit $c'_s(s)$, and the result is $T(X'_{2s}) = U_{1, 2s}(T(X'_0))$. Since $|H|$ is odd, every element of $H$ is of the form $2s$. The lemma now applies with $U_s = U_{1,s}$. $\square$

The hypothesis that $|H|$ is odd is used only to write every element as $2s$.

### Torsion in $K(N)$

**Theorem.** Let $(N, \eta, c)$ be a theta structure on $A$ over $R$ with $H$ finite. Assume that the structure map $A \to \operatorname{Spec} R$ has constant functions, that the coordinates of $N$ span $H^0(N)$, and that $N$ embeds $A$ in projective space over $R$. If the translation by a section $y$ has a lift $\Psi$ to $N$, then $|H|\,y = 0$.

Lean: `New.Variety.IsThetaStructure.card_nsmul_eq_zero_of_isTranslationLift` (Lib/Shimura/ThetaGroup.lean).

Over a local ring, the hypothesis on $y$ says that $y \in K(N)$, by the theorem on lifts of translations. So the theorem says that $K(N)$ is killed by $|H|$, under the hypotheses on $N$.

*Proof.* Put $n = |H|$ and let $U_s$ be the lifts of the translations by $\eta(s)$ from the theta law with $m = 1$. The maps $\Psi^n$ and $(\Psi U_s)^n$ are lifts of the translations by $n y$ and $n y + \eta(n s) = n y$. By the proposition on proportional lifts, $\Psi^n = a\,(\Psi U_s)^n$ for some $a \in R$. So $\Psi^n$ commutes with $\Psi U_s$. Apply this to $X_0$ and cancel $\Psi$. This needs $\Psi$ to be injective, which holds because a translation is an isomorphism. The result is $\Psi^n(X_s) = U_s(\Psi^n(X_0))$ for all $s$. The lemma, applied with $A' = A$ and $T = \Psi^n$, gives $t_{ny}^* N = N$. Since $N$ is a projective embedding, two morphisms into $A$ over $R$ that pull $N$ back to the same linear system are equal. So $t_{ny}$ is the identity and $n y = 0$. $\square$

### What the next chapter uses

In [the next chapter](/chapter/integral-model/) these results are applied to the theta objects of a PEL family over local rings, in `Lib/Shimura/ThetaModuli/ThetaFamilyRigidity.lean`. The torsion theorem gives the criterion `New.ThetaObject.HasSpanningCoords.eq_zero_of_pairing_eq_zero` for a point of the kernel of the polarization to vanish in characteristic $l$. The rigidity theorem gives `New.ThetaObject.HasSpanningCoords.eq_and_comp_toFamily_eq_of_hom`, which identifies two objects that a homomorphism respecting the action, the pairing and the level points relates. The constant functions come from [Section 4](/chapter/complex-abelian-varieties/), through `New.Variety.hasConstFunctions_of_isPullback`.
