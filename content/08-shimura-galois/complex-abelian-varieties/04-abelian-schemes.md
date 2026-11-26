---
title: Abelian schemes
lean:
  - Lib/Shimura/AbelianScheme/Basic.lean
  - Lib/Shimura/AbelianScheme/Pairings.lean
  - Lib/Shimura/AbelianScheme/IsogenyFlatness.lean
  - Lib/Shimura/AbelianScheme/TangentCoordinates.lean
decls:
  - New.IsAbelianScheme
  - New.Pic.pairing
  - New.Pic.ParallelogramLaw
  - New.Pic.ParallelogramLaw.pairing_nsmul_left
  - New.Variety.pull_nsmul_eq_sq_smul
  - New.Variety.locallyQuasiFinite_of_pull_picClass
  - New.Variety.exists_finite_kernel_ring
  - New.Variety.isIsogeny_of_locallyQuasiFinite
  - New.Variety.exists_isAdditive_comp_eq_of_isIsogeny
  - New.Variety.eq_zero_of_nsmul_eq_zero_of_comp_eq_zero
  - New.HasConstFunctions
  - New.Variety.hasConstFunctions_of_isPullback
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Abelian schemes

The integral model of [the next chapter](/chapter/integral-model/) is a family of abelian varieties over a base of mixed characteristic. So the source needs abelian schemes over a general base. This section gives the definition of the source, the pairing on the Picard group that replaces the theorem of the cube, and the results on isogenies and torsion that later chapters use. The proofs use the language of [Schemes through their points](/chapter/schemes-through-points/).

### Group objects

Let $S$ be a scheme. A morphism $x \colon T \to A$ over $S$ is a $T$-point of $A$. A *commutative group object* over $S$ is the class abbreviation `New.AddObj`: an additive group object of Mathlib with commutative addition. Every $A(T)$ is then an abelian group, by the global instance `attribute [instance] Hom.addCommGroup` at line 54 of `Lib/Shimura/AbelianScheme/Basic.lean`. An action of a ring $O$ is the class `New.ModuleObj`.

**Remark (Formalization).** The global instance `Hom.addCommGroup` and the reducible instance `ModuleObj.homModule` (line 66) put group and module structures on all sets of morphisms into a group object. None of them is unsound, but they change instance search in every file that imports `Lib/Shimura/AbelianScheme/Basic.lean`. This is finding F-023 of the plan. It does not change the meaning of any statement of this chapter.

### The definition

The textbook definition is the following. An *abelian scheme* over $S$ is a group scheme $A \to S$ that is smooth and proper and has geometrically connected fibres (Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, Definition 6.1). Such a group scheme is commutative. Over a field, an abelian scheme is an abelian variety.

**Definition (Abelian scheme).** A commutative group object $A$ over $S$ is an *abelian scheme* if $A \to S$ is smooth and proper and, for every natural number $m \neq 0$, multiplication by $m$ on $A$ is a surjective morphism of schemes.

Lean: `New.IsAbelianScheme` (Lib/Shimura/AbelianScheme/Basic.lean).

**Remark (Formalization).** The source asks for divisibility where the textbook asks for connected fibres. The docstring of the file says so. The proofs of the source use the condition at one place: in the uniformization of [Section 6](/chapter/complex-abelian-varieties/), the exponential map has an image of finite index $m$ in $A(\mathbb{C})$, and surjectivity of multiplication by $m$ shows that the image is everything. The question whether the two definitions agree is open in the findings of the plan (F-062, question Q-63). The following argument, not checked in Lean, shows that they agree.

Let $A \to S$ be smooth and proper with a commutative group structure. Both conditions can be tested on the geometric fibres, so let $S = \operatorname{Spec} \bar k$ with $\bar k$ algebraically closed. The component group $\pi_0 = A/A^0$ is finite of some order $r$. If multiplication by $r$ is surjective on $A$, it is surjective on $\pi_0$ and also kills it, so $\pi_0 = 0$. Conversely, if $A$ is connected, it is an abelian variety, and multiplication by $m \neq 0$ is an isogeny, hence surjective (Mumford, *Abelian Varieties*, Section 6, Application 2). So `New.IsAbelianScheme` is the textbook notion with a commutative group law.

The source does not fix the relative dimension in the definition. Where a result needs it, it adds the hypothesis `SmoothOfRelativeDimension g A.hom`. Base change preserves abelian schemes (an instance in `Lib/Shimura/AbelianScheme/Pairings.lean`). A *homomorphism* is a morphism that is additive on all groups of points (`New.IsAdditive`). An *isogeny* is a homomorphism that is finite, flat and surjective (`New.IsIsogeny`, a class abbreviation). The *translation* by a section $z$ is $x \mapsto x + z$ (`New.translation`).

### The pairing and the parallelogram law

Write the Picard group $\operatorname{Pic}(X)$ of the source additively. Its elements are classes of line bundles in the sense of [Schemes through their points](/chapter/schemes-through-points/), and $x^* c$ is the pull-back of a class $c$ along a point $x \colon T \to A$ (`New.Pic.atPoint`).

**Definition (Pairing).** Let $A$ be a commutative group object over $S$ and $c \in \operatorname{Pic}(A)$. For $T$-points $x, y$ of $A$, the *pairing* of $c$ is
$$\langle x, y \rangle_c = (x + y)^* c - x^* c - y^* c + 0^* c \in \operatorname{Pic}(T).$$

Lean: `New.Pic.pairing` (Lib/Shimura/AbelianScheme/Basic.lean).

**Definition (Parallelogram law).** A class $c \in \operatorname{Pic}(A)$ *satisfies the parallelogram law* if
$$(x + y)^* c + (x - y)^* c + 2 \cdot 0^* c = 2\,(x^* c + y^* c)$$
in $\operatorname{Pic}(T)$, for every $S$-scheme $T$ and all $T$-points $x, y$ of $A$.

Lean: `New.Pic.ParallelogramLaw` (Lib/Shimura/AbelianScheme/Basic.lean).

For the textbook, the theorem of the cube gives $(f + g + h)^*\mathcal{L} \cong (f + g)^*\mathcal{L} \otimes (f + h)^*\mathcal{L} \otimes (g + h)^*\mathcal{L} \otimes f^*\mathcal{L}^{-1} \otimes g^*\mathcal{L}^{-1} \otimes h^*\mathcal{L}^{-1}$ (Mumford, *Abelian Varieties*, Section 6, Corollary 2). For a symmetric $\mathcal{L}$ it gives the parallelogram law and $[m]^*\mathcal{L} \cong \mathcal{L}^{m^2}$ (Section 6, Corollary 3).

**Remark (Formalization).** The source does not prove the theorem of the cube. It takes the parallelogram law as a hypothesis wherever it is needed. In the PEL families of [the next chapter](/chapter/integral-model/), the law is a field of the data: `New.PEL.HasClassLaws.parallelogramLaw` in `Lib/Shimura/ThetaModuli/PELThetaTori.lean` reads it off the class laws that the family carries. So the source never needs the cube for a general line bundle, and the classes to which it applies the results below are the ones whose law is part of the data.

**Proposition.** Let $c$ satisfy the parallelogram law. For $T$-points $x, y$ of $A$ and every natural number $m$, $\langle m x, y \rangle_c = m\,\langle x, y \rangle_c$.

Lean: `New.Pic.ParallelogramLaw.pairing_nsmul_left` (Lib/Shimura/AbelianScheme/Pairings.lean).

*Proof.* The parallelogram law, written for the pairing, is $\langle x + y, z\rangle + \langle x - y, z\rangle = 2\langle x, z\rangle$ (`New.Pic.ParallelogramLaw.pairing_add_add_pairing_sub`). Put $x \mapsto (m + 1)x$ and $y \mapsto x$. This gives $\langle (m + 2)x, y\rangle = 2\langle (m + 1)x, y\rangle - \langle mx, y\rangle$, and induction on $m$ from $m = 0, 1$ finishes. $\square$

The pairing is symmetric (`New.Variety.pairing_comm`) and is pulled back along homomorphisms (`New.Variety.pairing_comp`).

**Theorem.** Let $R$ be a local ring, $A$ a commutative group object over $\operatorname{Spec} R$, and $c \in \operatorname{Pic}(A)$ a class that satisfies the parallelogram law. Then $[m]^* c = m^2 c$ for every natural number $m$.

Lean: `New.Variety.pull_nsmul_eq_sq_smul` (Lib/Shimura/AbelianScheme/Pairings.lean).

*Proof.* Over a local ring, a class pulled back along a point that factors through a section of $A$ over $R$ is $0$, because the Picard group of $\operatorname{Spec} R$ is trivial (`New.Variety.atPoint_toUnit_comp_eq_zero`). So $0^* c = 0$. The parallelogram law at $x = y = 1_A$ gives $[2]^* c = 4c$. The proposition at $x = y = 1_A$ gives $[m + 1]^* c - [m]^* c - c = m([2]^* c - 2c) = 2mc$. Induction on $m$ gives $[m]^* c = m^2 c$. $\square$

The local ring is needed only to kill the terms $0^* c$. Over a general base the statement would hold up to classes pulled back from the base.

### Finite kernels and isogenies

**Proposition.** Let $A \to \operatorname{Spec} R$ be a scheme with a morphism $f \colon A \to B$ to a separated commutative group scheme $B$ over $\operatorname{Spec} R$, and assume that $f$ is finite. Then the fibre of $f$ over the zero section is $\operatorname{Spec} S$ for a finite $R$-algebra $S$. More precisely, there is a closed immersion $\iota \colon \operatorname{Spec} S \to A$ with $\iota \circ f = 0$, through which every point $y$ of $A$ with $f \circ y = 0$ factors, and $S$ is flat over $R$ if $f$ is flat.

Lean: `New.Variety.exists_finite_kernel_ring` (Lib/Shimura/AbelianScheme/Basic.lean).

*Proof.* The zero section of a separated group scheme is a closed immersion. Its pull-back along the finite morphism $f$ is finite over the affine scheme $\operatorname{Spec} R$, hence affine, and flatness passes to the pull-back. The universal property of the pull-back gives the factorization. $\square$

**Proposition.** Let $A \to S$ be proper, with a linear system $N$ that embeds $A$ in projective space over $S$, and let $B \to S$ be separated. If $f \colon A \to B$ is a morphism over $S$ with $f^* c = m [N]$ for some $c \in \operatorname{Pic}(B)$ and some natural number $m \neq 0$, then $f$ is locally quasi-finite.

Lean: `New.Variety.locallyQuasiFinite_of_pull_picClass` (Lib/Shimura/AbelianScheme/Pairings.lean).

*Proof.* On a fibre $X$ of $f$, the class $m[N]$ is trivial, since it is pulled back from a point. The power $N^m$ is again an embedding, so its sections are global functions on $X$ that embed $X$ in affine space. A proper scheme that is a closed subscheme of affine space is finite over the base. $\square$

**Theorem.** Let $R$ be a local ring and $f \colon A \to B$ a homomorphism of abelian schemes over $\operatorname{Spec} R$. If $f$ is locally quasi-finite and surjective, then $f$ is an isogeny.

Lean: `New.Variety.isIsogeny_of_locallyQuasiFinite` (Lib/Shimura/AbelianScheme/IsogenyFlatness.lean).

The textbook form is that a quasi-finite surjective homomorphism of abelian schemes is finite and flat (Bosch, Lütkebohmert and Raynaud, *Néron Models*, Section 7.3). For flatness the source localizes $B$ at a generic point of its special fibre, applies the local criterion of flatness, and spreads flatness over $B$ by translations.

**Theorem.** Let $k$ be an Artinian ring. Let $A$ be a commutative group scheme and $B$, $C$ abelian schemes over $\operatorname{Spec} k$. Let $f \colon A \to B$ be an isogeny and $g \colon A \to C$ a homomorphism. Assume that for every finite local Noetherian $k$-algebra $S$ and every point $y \colon \operatorname{Spec} S \to A$ with $f \circ y = 0$, one has $g \circ y = 0$. Then there is a homomorphism $j \colon B \to C$ with $j \circ f = g$.

Lean: `New.Variety.exists_isAdditive_comp_eq_of_isIsogeny` (Lib/Shimura/AbelianScheme/IsogenyFlatness.lean).

This is the universal property of the quotient $B = A/\ker f$ (Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter IV, Section 3). Over an Artinian ring the finite kernel is a product of spectra of finite local Noetherian algebras, so the hypothesis says that $g$ kills the kernel.

### Torsion is unramified

**Theorem.** Let $R$ be a local ring, $B$ an abelian scheme over $\operatorname{Spec} R$ that is smooth of relative dimension $g$, and $m$ a natural number that is a unit in $R$. Let $x$ be a section of $B$ over $R$ with $m x = 0$. If $x$ vanishes at one point $\operatorname{Spec} K \to \operatorname{Spec} R$ with $K$ a nonzero ring, then $x = 0$.

Lean: `New.Variety.eq_zero_of_nsmul_eq_zero_of_comp_eq_zero` (Lib/Shimura/AbelianScheme/TangentCoordinates.lean).

*Proof.* Let $I \subseteq R$ be the ideal that cuts out the locus where $x = 0$. The point $\operatorname{Spec} K$ lies in this locus, so $I$ is a proper ideal, contained in the maximal ideal. Over $R/I^2$ the section $x$ vanishes modulo the square-zero ideal $I/I^2$. Sections that vanish modulo a square-zero ideal form a group isomorphic to $g$ copies of $I/I^2$, through the tangent coordinates of `Lib/Shimura/AbelianScheme/TangentCoordinates.lean`. Multiplication by the unit $m$ is injective on this group, so $x = 0$ over $R/I^2$. This gives $I \subseteq I^2$, and Nakayama's lemma gives $I = 0$. $\square$

So over a local ring in which $m$ is a unit, an $m$-torsion section is determined by its value at any one point. This is a form of the classical fact that the $m$-torsion is étale when $m$ is invertible.

### Constant functions

**Definition (Constant functions).** A morphism $s \colon X \to S$ *has constant functions* if every global function $c$ on $X$ takes equal values at any two ring-valued points $x, y \colon \operatorname{Spec} B \to X$ with $s \circ x = s \circ y$.

Lean: `New.HasConstFunctions` (Lib/Shimura/AbelianScheme/Basic.lean).

**Theorem.** Let $k$ be a field and $A$ an abelian scheme over $\operatorname{Spec} k$ whose underlying scheme is integral. Let $X = A \times_k \operatorname{Spec} C$ for a ring $C$, with projection $s \colon X \to \operatorname{Spec} C$. Then $s$ has constant functions.

Lean: `New.Variety.hasConstFunctions_of_isPullback` (Lib/Shimura/AbelianScheme/Basic.lean).

The textbook form is $H^0(X, \mathcal{O}_X) = C$, from $H^0(A, \mathcal{O}_A) = k$ and flat base change. The source states the consequence on points that the theta structures of [Section 5](/chapter/complex-abelian-varieties/) need.
