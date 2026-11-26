---
title: Frobenius and sections of powers
lean:
  - Lib/General/Geometry/SerreTheorem.lean
  - Lib/Shimura/ThetaGroup.lean
  - Lib/Shimura/ThetaNormality/NormalGeneration.lean
decls:
  - New.Variety.natCast_eq_zero_of_over_charP
  - New.Variety.exists_absFrobenius
  - New.Variety.absFrobenius
  - New.Variety.comp_absFrobenius
  - New.Variety.absFrobenius_comm
  - New.Variety.absFrobenius_apply
  - New.Variety.picClass_pull_absFrobenius
  - New.ThetaTori.formSpan
  - New.Variety.coordSection
  - New.Variety.H0_ext
  - New.Variety.mul_mem_formSpan_succ
  - New.Variety.eventually_mem_formSpan_of_mul
  - New.Variety.eventually_mem_formSpan_of_mul_pow
  - New.Variety.pow_transition_apply
  - New.Variety.exists_mul_pow_mem_formSpan_of_isSection
  - New.Variety.eq_zero_of_apply_eq_zero_of_dominant
  - New.Variety.eventually_span_coordSection
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Frobenius and sections of powers

This section treats two results of `Lib/General/Geometry/SerreTheorem.lean`. The first is the absolute Frobenius of a scheme in characteristic $l$ and its action on the Picard group. The second is a case of Serre's theorem: for large $m$, the monomials of degree $m$ in the coordinates of a projective embedding span the sections of the $m$-th power. Both are used in the construction of the integral model and in the congruence relation (Volume 12, [the integral model](/chapter/integral-model/) and [the congruence relation](/chapter/congruence-relation/)).

### The absolute Frobenius

Let $X$ be a scheme over $\mathbb{F}_l$. The absolute Frobenius $F_X \colon X \to X$ is the identity on the topological space and $a \mapsto a^l$ on the structure sheaf. It commutes with all morphisms of schemes over $\mathbb{F}_l$. For an invertible sheaf $\mathcal{L}$, $F_X^* \mathcal{L} \cong \mathcal{L}^{\otimes l}$: the transition functions of $F_X^* \mathcal{L}$ are the $l$-th powers of those of $\mathcal{L}$.

In the source, $k$ is a field of characteristic $l$, with $l$ prime, and $X$ is an object of the category of schemes over $\operatorname{Spec} k$. For a ring $B$ with $l = 0$ in $B$, `New.frobPow` is the ring map $x \mapsto x^{l^f}$ of $B$.

**Theorem.** If $\operatorname{Spec} B$ maps to $\operatorname{Spec} k$, then $l = 0$ in $B$.

Lean: `New.Variety.natCast_eq_zero_of_over_charP` (Lib/General/Geometry/SerreTheorem.lean).

**Theorem.** There is an endomorphism $F$ of the scheme $X$ such that $F \circ t = t \circ \operatorname{Spec}(x \mapsto x^{l^f})$ for every ring $B$ and every point $t \colon \operatorname{Spec} B \to X$.

Lean: `New.Variety.exists_absFrobenius` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* The family $t \mapsto t \circ \operatorname{Spec}(x \mapsto x^{l^f})$ is compatible with base change, because ring maps commute with the map $x \mapsto x^{l^f}$. The descent of morphisms of Section 2 (`New.exists_hom_of_cover`), on the cover of $X$ by the single open $X$, glues it to a morphism. $\square$

**Definition (Absolute Frobenius).** `absFrobenius f X` is the morphism of the last theorem, chosen with `Exists.choose`.

Lean: `New.Variety.absFrobenius` (Lib/General/Geometry/SerreTheorem.lean).

**Theorem.** The absolute Frobenius satisfies the defining property of the last theorem on points. It commutes with every morphism $X \to Y$ of schemes over $\operatorname{Spec} k$, and it is the identity on the underlying space of $X$.

Lean: `New.Variety.comp_absFrobenius`, `New.Variety.absFrobenius_comm`, `New.Variety.absFrobenius_apply` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* The first statement is the specification of the choice. The second holds on points by the first, so it holds by `New.hom_ext_of_points`. For the third, test on the residue field at $x$, whose spectrum has one point. $\square$

The definition uses `choose`, but the first statement determines the morphism, by `New.hom_ext_of_points`. So the choice has no effect on any statement.

**Theorem.** Let $L$ be a linear system on $X$. Then $l^f\, [L] = [F^* L]$ in $\operatorname{Pic} X$, where $F$ is the absolute $l^f$-Frobenius.

Lean: `New.Variety.picClass_pull_absFrobenius` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* By Section 5, $l^f [L] = [L^{\otimes l^f}]$. The bundle $F^* L$ has the same opens as $L$, since $F$ is the identity on the space. Its transition functions are $g_{ab}(A, F \circ t) = g_{ab}(A, t)^{l^f}$, by the property on points and the regularity of $g_{ab}$ on $U_a$. On the constant tuples $(a, \dots, a)$, the bundle $L^{\otimes l^f}$ has the opens $U_a$ and the transition functions $g_{ab}^{l^f}$. The refinement theorem of Section 3, with the map $a \mapsto (a, \dots, a)$, gives the equality of classes. $\square$

**Remark (Formalization).** The theorem needs $L$ to be a linear system. The proof uses that $g_{ab}$ is regular on all of $U_a$, so that the value at $F \circ t$ is computed for every point $t$ of $U_a$, and not only for points of $U_a \cap U_b$. Classically the result holds for every invertible sheaf. For a general line bundle of the source, the same proof would work with the regularity of $g_{ab}$ on $U_a \cap U_b$, and with the refinement theorem applied on the overlaps. The source does not state that general form. The uses are in `Lib/Shimura/CongruenceRelation/HeckeNeighbours.lean` and `Lib/Shimura/Deformation/TangentBound.lean`, and they apply the theorem to the linear system of a projective embedding.

### Forms and coordinates

Let $R$ be a ring, $A$ an $R$-algebra and $x \in A^\iota$. The *forms of degree $m$ at $x$* are the values $P(x)$ of homogeneous polynomials $P \in R[X_i]$ of degree $m$.

**Definition (Span of forms).** The $R$-submodule $\operatorname{formSpan}(R, x, m) = (\operatorname{span}_R \{x_i\})^m$ of $A$.

Lean: `New.ThetaTori.formSpan` (Lib/Shimura/ThetaNormality/NormalGeneration.lean).

The power of a submodule is the span of the products of $m$ elements. So this is the set of forms of degree $m$ at $x$. For $m = 0$ it is the span of $1$.

**Definition (Coordinate section).** Let $L$ be a linear system on a scheme over $\operatorname{Spec} R$. For an index $j$, the element of $H^0(L)$ whose component in the chart $i$ is $g_{ij}$.

Lean: `New.Variety.coordSection` (Lib/Shimura/ThetaGroup.lean).

It is an element of the module $H^0(L)$ of Section 3, because a linear system has $g_{ij} = 0$ off $U_i$.

**Theorem.** Two elements of $H^0(L)$ are equal if they agree at the points of each chart.

Lean: `New.Variety.H0_ext` (Lib/Shimura/ThetaGroup.lean).

**Theorem.** If $f \in \operatorname{formSpan}(R, x, m)$, then $f x_j \in \operatorname{formSpan}(R, x, m+1)$.

Lean: `New.Variety.mul_mem_formSpan_succ` (Lib/General/Geometry/SerreTheorem.lean).

**Theorem (Cancellation).** Let $R$ be noetherian, $\iota$ finite, and $x \in A^\iota$ with $x_r = 1$ for some $r$. For all large $D$: if $f x_j$ is a form of degree $D + 1$ for every $j$, then $f$ is a form of degree $D$.

Lean: `New.Variety.eventually_mem_formSpan_of_mul` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* The source defines an increasing chain of ideals $I_c$ of $R[X_i]$ by conditions on the parts of each degree of a polynomial. Since $R[X_i]$ is noetherian, the chain stops at some $c$. For $D \ge c$, the element $f = f x_r$ is the value of a homogeneous polynomial of degree $D + 1$ in $I_{D+1} = I_c$, and the definition of $I_c$ makes $f$ a form of degree $D$. $\square$

**Theorem (Saturation).** Under the same hypotheses, for all large $D$: if for each $i$ some $f x_i^{N}$ is a form of degree $D + N$, then $f$ is a form of degree $D$.

Lean: `New.Variety.eventually_mem_formSpan_of_mul_pow` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* Induction on the vector of exponents, with the cancellation theorem at each step. The bound on $D$ comes from the cancellation theorem, so it does not depend on the exponents. $\square$

Classically, this is the statement that a graded ring and its saturation agree in large degrees.

### Serre's theorem in the source

Let $X \subseteq \mathbb{P}^n_A$ be a closed subscheme over a noetherian ring $A$, with homogeneous coordinate ring $S = A[x_0, \dots, x_n] / I$. Then the natural map $S_d \to \Gamma(X, \mathcal{O}_X(d))$ is an isomorphism for all large $d$ (Hartshorne, *Algebraic Geometry*, Chapter II, Exercise 5.9, which assumes that $A$ is a finitely generated algebra over a field). The surjective half says that the forms of degree $d$ in the coordinates span the sections of $\mathcal{O}_X(d)$.

**Theorem.** The transition functions of $L^{\otimes m}$ are $g_{cd} = \prod_{a} g_{c_a d_a}$ for $m$-tuples $c$ and $d$. Let $\iota$ be finite, let $L$ embed $X$ over $\operatorname{Spec} R$, let $t$ be a section of $L^{\otimes m}$, and let $\xi$ be a point in the charts $i$ and $j$, with $x_l = g_{il}(B, \xi)$. Then for some $N$, the value of $t$ at $\xi$ in the chart $(i, \dots, i)$ times $x_j^N$ is a form of degree $m + N$ at $x$.

Lean: `New.Variety.pow_transition_apply`, `New.Variety.exists_mul_pow_mem_formSpan_of_isSection` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* By Section 5, the chart $U_j$ is affine and its sections are polynomials $P$ in the $g_{jl}$. So the value of $t$ in the chart $j$ is $P(y)$ with $y_l = g_{jl}(B, \xi)$. The value in the chart $i$ is $x_j^m P(y)$, and $x_l = x_j y_l$. Homogenize $P$ to a form $Q$ of degree $m + \deg P$. Then $Q(x) = t(\xi)\, x_j^{\deg P}$. $\square$

**Theorem.** Let $\xi$ be a point of the chart $i$ of $L$ that is quasi-compact and scheme-theoretically dominant. A global section of $L$ with value $0$ at $\xi$ in the chart $i$ is $0$.

Lean: `New.Variety.eq_zero_of_apply_eq_zero_of_dominant` (Lib/General/Geometry/SerreTheorem.lean).

**Theorem (A case of Serre's theorem).** Let $F$ be a field, $A$ an integral scheme over $F$, and $N$ a projective embedding of $A$ over $\operatorname{Spec} F$ with finite index set. Let $k$ be a noetherian ring with a map $\operatorname{Spec} k \to \operatorname{Spec} F$, and let $p \colon A' \to A$ be the base change, so $A' = A \times_F k$. Then for all large $m$, and for every proof $h$ that $(p^* N)^{\otimes m}$ is a linear system, the coordinate sections of $(p^* N)^{\otimes m}$ span $H^0((p^* N)^{\otimes m})$ over $k$.

Lean: `New.Variety.eventually_span_coordSection` (Lib/General/Geometry/SerreTheorem.lean).

*Proof.* Let $\zeta$ be the generic point of $A$, as a point with values in its residue field. It is dominant, and so scheme-theoretically dominant, since $A$ is integral. Its base change $\xi$ to $A'$ is a point with values in a ring $B$. The source claims, through flat base change, that $\xi$ is scheme-theoretically dominant and quasi-compact. So evaluation at $\xi$ in a chart $i$ that contains $\zeta$ is an injective map $H^0((p^* N)^{\otimes m}) \to B$. The coordinate section for a tuple evaluates to the monomial for that tuple in the affine coordinates $x_l$ of $\xi$, so the image of the span of the coordinates contains $\operatorname{formSpan}(k, x, m)$. It remains to show that the value of a section $t$ at $\xi$ is a form of degree $m$. By saturation, it is enough that for each $j$ some $t(\xi) x_j^N$ is a form of degree $m + N$. If $x_j = 0$ this is clear with $N = 1$. Otherwise $x_j$ is the image of a nonzero element of a field, so it is a unit, and $\xi$ lies in the chart $j$. The theorem before the last one gives the claim. $\square$

**Remark (Formalization).** Three points about the statement.

1. It is a special case of the classical theorem. The scheme $A'$ is a base change of an integral scheme over a field, and not an arbitrary closed subscheme of $\mathbb{P}^n_k$. The proof uses the generic point of $A$ and the flatness of the base change, and both need these hypotheses. The docstring of the source calls it "a case of" Serre's theorem.
2. The quantifier $\forall h$ over proofs that $(p^* N)^{\otimes m}$ is a linear system is not a hypothesis. Such a proof always exists, by `New.LineBundle.IsLinearSystem.pull` and `New.LineBundle.IsLinearSystem.pi`. Since `IsLinearSystem` is a proposition, all proofs $h$ give the same coordinate sections. The quantifier is there because `New.Variety.coordSection` takes the proof as an argument.
3. The coordinate sections are indexed by $m$-tuples, so each monomial appears several times. This does not change the span, as Section 5 says.

The theorem is used in `Lib/Shimura/IntegralModel/UniversalFamily.lean`. There $k$ is replaced by a noetherian local ring $B$, the base field is algebraically closed, and the result is used to show that the geometric fibres of a family are rigid. The section of $[c]^* N \cong N^{\otimes c^2}$ is found for large $c$, and a trace over the $c$-torsion brings it down to $N$. The source does not claim that the bound on $m$ is effective, and the proof gives none: the bound comes from a noetherian chain condition.
