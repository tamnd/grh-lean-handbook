---
title: Line bundles and the Picard group
lean:
  - Lib/General/Geometry/LineBundles.lean
decls:
  - New.LineBundle
  - New.LineBundle.transition_mul_transition
  - New.LineBundle.isUnit_transition
  - New.LineBundle.pull
  - New.LineBundle.one
  - New.LineBundle.inv
  - New.LineBundle.mul
  - New.LineBundle.IsSection
  - New.LineBundle.IsFrame
  - New.LineBundle.IsIsomorphic
  - New.LineBundle.H0
  - New.LineBundle.IsFrame.exists_eq_mul
  - New.LineBundle.exists_isSection_eq_mul
  - New.LineBundle.IsIsomorphic.refl
  - New.LineBundle.IsIsomorphic.symm
  - New.LineBundle.IsIsomorphic.trans
  - New.LineBundle.IsIsomorphic.mul
  - New.Pic
  - New.LineBundle.picClass
  - New.LineBundle.picClass_eq_iff
  - New.LineBundle.picClass_eq_of_le
  - New.LineBundle.picClass_mul
  - New.LineBundle.picClass_one
  - New.LineBundle.exists_isFrame_of_picClass_eq_zero
  - New.Pic.pull
  - New.Pic.pull_comp
  - New.Pic.eq_zero_of_isLocalRing
  - New.LineBundle.exists_isFrame_of_fpqc
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Line bundles and the Picard group

This section gives the line bundles of the source, their sections, the relation of isomorphism and the Picard group. A line bundle is an open cover with a cocycle of regular functions on points. The Picard group is the set of such cocycles modulo isomorphism, with the tensor product as the group law. The section ends with a comparison with the classical Picard group. The source does not state that comparison.

### The classical picture

Let $X$ be a scheme. An invertible sheaf is a sheaf of $\mathcal{O}_X$-modules $\mathcal{L}$ that is locally isomorphic to $\mathcal{O}_X$. The isomorphism classes of invertible sheaves form a group under $\otimes$, the Picard group $\operatorname{Pic} X$, with inverse $\mathcal{L}^\vee = \mathcal{H}om(\mathcal{L}, \mathcal{O}_X)$ (Hartshorne, *Algebraic Geometry*, Chapter II, Section 6). Choose an open cover $(U_i)$ and trivializations $\mathcal{L}|_{U_i} \cong \mathcal{O}_{U_i}$. The two trivializations on $U_i \cap U_j$ differ by a unit $g_{ij} \in \mathcal{O}(U_i \cap U_j)^\times$. These units satisfy $g_{ii} = 1$ and $g_{ij} g_{jk} = g_{ik}$ on triple overlaps. Conversely, such a cocycle defines an invertible sheaf by gluing (Hartshorne, Chapter II, Exercise 5.18, for vector bundles). Two cocycles define isomorphic sheaves if and only if they differ by a coboundary on a common refinement. So
$$\operatorname{Pic} X \cong \check{H}^1(X, \mathcal{O}_X^\times) \cong H^1(X, \mathcal{O}_X^\times)$$
(Hartshorne, Chapter III, Exercises 4.4 and 4.5).

The source takes the cocycle as the definition, with the transition functions read as functions on points.

### Line bundles

**Definition (Line bundle).** A *line bundle* on $X$ with index set $\iota$ consists of opens $U_i \subseteq X$ and functions on points $g_{ij}$, for $i, j \in \iota$, such that

1. the $U_i$ cover $X$;
2. $g_{ij}$ is regular on $U_i \cap U_j$;
3. $g_{ii}(A, t) = 1$ at each point $t$ that lands in $U_i$;
4. $g_{ij}(A, t)\, g_{jk}(A, t) = g_{ik}(A, t)$ at each point $t$ that lands in $U_i$, $U_j$ and $U_k$.

Lean: `New.LineBundle` (Lib/General/Geometry/LineBundles.lean).

The fields are `opens`, `transition`, `cover`, `regular`, `transition_self` and `transition_trans`. The index set $\iota$ is any type in the universe $0$. It need not be finite.

**Theorem.** At a point that lands in $U_i$ and $U_j$, $g_{ij}\, g_{ji} = 1$. So $g_{ij}$ is a unit there.

Lean: `New.LineBundle.transition_mul_transition`, `New.LineBundle.isUnit_transition` (Lib/General/Geometry/LineBundles.lean).

*Proof.* By the cocycle condition with $k = i$, $g_{ij} g_{ji} = g_{ii} = 1$. $\square$

So the structure does not need a separate field for units. The cocycle condition gives them.

**Definition (Operations).** Let $L = (U_i, g_{ij})_{i \in \iota}$ and $M = (V_k, h_{kl})_{k \in \kappa}$ be line bundles on $X$, and let $p \colon Y \to X$.

1. The *pull-back* $p^* L$ has opens $p^{-1}(U_i)$ and transition functions $t \mapsto g_{ij}(A, t \circ p)$.
2. The *trivial bundle* $\mathbf{1}$ has the index set with one element, the open $X$ and the transition function $1$.
3. The *dual* $L^{-1}$ has the opens $U_i$ and the transition functions $g_{ji}$.
4. The *tensor product* $L \otimes M$ has index set $\iota \times \kappa$, opens $U_i \cap V_k$ and transition functions $g_{ij} h_{kl}$.

Lean: `New.LineBundle.pull`, `New.LineBundle.one`, `New.LineBundle.inv`, `New.LineBundle.mul` (Lib/General/Geometry/LineBundles.lean).

The dual uses $g_{ji}$ in place of $g_{ij}^{-1}$. The two agree on $U_i \cap U_j$ by the last theorem, and $g_{ji}$ needs no inverse in the ring of functions on points.

### Sections and frames

**Definition (Section, frame).** A *section* of $L$ is a family $(s_i)_{i \in \iota}$ of functions on points such that $s_i$ is regular on $U_i$ and $s_i(A, t) = g_{ij}(A, t)\, s_j(A, t)$ at each point $t$ that lands in $U_i$ and $U_j$. A *frame* is a section with $s_i(A, t)$ a unit at each point $t$ that lands in $U_i$.

Lean: `New.LineBundle.IsSection`, `New.LineBundle.IsFrame` (Lib/General/Geometry/LineBundles.lean).

A frame is a nowhere vanishing section. Classically, a line bundle has a frame if and only if it is trivial.

**Definition (Isomorphism).** Line bundles $L$ and $M$ are *isomorphic* if $L \otimes M^{-1}$ has a frame.

Lean: `New.LineBundle.IsIsomorphic` (Lib/General/Geometry/LineBundles.lean).

**Definition (Module of sections).** Let $X$ be a scheme over $\operatorname{Spec} R$. The $R$-module $H^0(L)$ is the set of sections $(s_i)$ of $L$ with $s_i(A, t) = 0$ at each point $t$ that does not land in $U_i$.

Lean: `New.LineBundle.H0` (Lib/General/Geometry/LineBundles.lean).

The condition of vanishing off $U_i$ removes the junk values. Without it, two sections that differ only off the opens would be different elements. A scalar $r \in R$ acts at the point $t$ by the image of $r$ in $A$.

**Theorem.** Let $u$ be a frame of $L$ and $s$ a section of $L$. There is a global function $c \in \Gamma(X, \mathcal{O}_X)$ with $s_i(A, t) = \operatorname{ofSection}(c)(A, t)\, u_i(A, t)$ at each point $t$ that lands in $U_i$.

Lean: `New.LineBundle.IsFrame.exists_eq_mul` (Lib/General/Geometry/LineBundles.lean).

*Proof.* The quotients $s_i / u_i$ are regular on $U_i$, and on $U_i \cap U_j$ they agree, because $s_i = g_{ij} s_j$ and $u_i = g_{ij} u_j$. So the functions glue to one section $c$ over $X$, by the descent of functions of Section 2 applied to the identity of $X$ and the cover $(U_i)$. $\square$

So the sections of a trivial bundle are the global functions, as in the classical theory.

### Isomorphism is an equivalence relation

The proofs of the three properties use one descent statement for sections. It is the main technical lemma of the file.

**Theorem (Descent of sections).** Let $\pi \colon Y \to X$ be flat, surjective and quasi-compact. Let $u$ be a section of $\pi^*(M \otimes L^{-1})$ whose value at a point of $Y$ depends only on its image in $X$, and let $s$ be a section of $L$. Then there is a section $r$ of $M$, zero off the opens of $M$, with $r_k(A, t \circ \pi) = u_{(k, i)}(A, t)\, s_i(A, t \circ \pi)$ at each point $t$ of $Y$ with $t \circ \pi$ in $V_k \cap U_i$.

Lean: `New.LineBundle.exists_isSection_eq_mul` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Fix $k$. The products $u_{(k,i)} \cdot \pi^* s_i$ agree at points with the same image in $X$. The proof uses the cocycle relations of $u$ and $s$ and the hypothesis on the fibres of $u$. By the descent of functions they descend to one section $r_k$ over $V_k$. The relation $r_k = h_{kl}\, r_l$ is tested after pull-back along $\pi$, which is scheme-theoretically dominant. $\square$

**Theorem.** Isomorphism of line bundles is reflexive, symmetric and transitive. It is compatible with the tensor product: if $L \cong M$ and $N \cong P$, then $L \otimes N \cong M \otimes P$.

Lean: `New.LineBundle.IsIsomorphic.refl`, `New.LineBundle.IsIsomorphic.symm`, `New.LineBundle.IsIsomorphic.trans`, `New.LineBundle.IsIsomorphic.mul` (Lib/General/Geometry/LineBundles.lean).

*Proof.* For reflexivity, the family $u_{(i,j)} = g_{ij}$ is a frame of $L \otimes L^{-1}$, by the cocycle condition. A first consequence of the descent of sections, along the identity of $X$, is this: if $L \cong M$ and $M$ has a frame, then $L$ has a frame. For transitivity, $L \cong M$ gives $L \otimes N^{-1} \cong M \otimes N^{-1}$, and the latter has a frame if $M \cong N$. For symmetry, invert a frame of $L \otimes M^{-1}$ pointwise. This gives $L^{-1} \cong M^{-1}$. So $M \otimes L^{-1} \cong M \otimes M^{-1}$, and the latter has a frame. For the tensor product, the product of frames of $L \otimes M^{-1}$ and $N \otimes P^{-1}$ is a frame of $(L \otimes N) \otimes (M \otimes P)^{-1}$, after a reordering of the index set. $\square$

### The Picard group

**Definition (Picard group).** The *Picard group* $\operatorname{Pic} X$ is the set of pairs $(\iota, L)$, with $\iota$ a type and $L$ a line bundle on $X$ with index set $\iota$, modulo isomorphism. The class of $L$ is written $[L]$.

Lean: `New.Pic`, `New.LineBundle.picClass` (Lib/General/Geometry/LineBundles.lean).

**Theorem.** $[L] = [M]$ if and only if $L$ and $M$ are isomorphic.

Lean: `New.LineBundle.picClass_eq_iff` (Lib/General/Geometry/LineBundles.lean).

The next result gives isomorphisms without frames. It is used for every group axiom.

**Theorem (Refinement).** Let $e \colon \kappa \to \iota$ be a map with $V_a \subseteq U_{e(a)}$ for all $a$, and suppose that $h_{ab}(A, t) = g_{e(a) e(b)}(A, t)$ at each point $t$ that lands in $V_a$. Then $[L] = [M]$.

Lean: `New.LineBundle.picClass_eq_of_le` (Lib/General/Geometry/LineBundles.lean).

*Proof.* A frame of $L \otimes L^{-1}$, read at the indices $(i, e(a))$, is a frame of $L \otimes M^{-1}$. $\square$

**Theorem.** The operations $[L] + [M] = [L \otimes M]$, $-[L] = [L^{-1}]$ and $0 = [\mathbf{1}]$ make $\operatorname{Pic} X$ an abelian group.

Lean: `New.LineBundle.picClass_mul`, `New.LineBundle.picClass_one` (Lib/General/Geometry/LineBundles.lean).

*Proof.* The operations are well defined by the compatibility of isomorphism with tensor products and duals. Associativity, commutativity and the unit law follow from the refinement theorem: in each case the two bundles have the same cover up to a bijection of index sets, and the same transition functions. For the inverse, a frame of $L \otimes L^{-1}$ is a frame of $(L \otimes L^{-1}) \otimes \mathbf{1}^{-1}$. $\square$

The group is written additively. The instance is `AddCommGroup (New.Pic X)`, and the two lemmas say that the class of a tensor product is the sum of the classes and that the trivial bundle has class $0$.

**Theorem.** If $[L] = 0$, then $L$ has a frame.

Lean: `New.LineBundle.exists_isFrame_of_picClass_eq_zero` (Lib/General/Geometry/LineBundles.lean).

**Definition (Pull-back of classes).** For $p \colon Y \to X$, the homomorphism $p^* \colon \operatorname{Pic} X \to \operatorname{Pic} Y$ with $p^*[L] = [p^* L]$.

Lean: `New.Pic.pull` (Lib/General/Geometry/LineBundles.lean).

**Theorem.** $(p \circ q)^* = q^* \circ p^*$ and $\mathrm{id}^* = \mathrm{id}$.

Lean: `New.Pic.pull_comp` (Lib/General/Geometry/LineBundles.lean).

The identity law is the lemma `New.Pic.pull_id`. Both laws hold by definition on representatives, since pull-back of line bundles is strictly functorial: `New.LineBundle.pull_comp` and `New.LineBundle.pull_id` are proved by `rfl`.

**Theorem.** Let $A$ be a local ring. Then $\operatorname{Pic}(\operatorname{Spec} A) = 0$.

Lean: `New.Pic.eq_zero_of_isLocalRing` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Let $L$ be a line bundle on $\operatorname{Spec} A$. The identity of $\operatorname{Spec} A$ is a point with values in the local ring $A$. Its closed point lies in some $U_i$, so the identity lands in $U_i$, and $U_i$ is all of $\operatorname{Spec} A$. The trivial bundle is then the restriction of $L$ to the single chart $i$, where the transition function is $g_{ii} = 1$. The refinement theorem with the constant map $e = i$ gives $[\mathbf{1}] = [L]$. $\square$

The classical proof says that a finitely generated projective module of rank one over a local ring is free. The proof of the source is shorter, because a line bundle is given by a cover, and a cover of the spectrum of a local ring contains the whole space.

### Descent of frames

**Theorem (fpqc descent of frames).** Let $\pi \colon Y \to X$ be flat, surjective and quasi-compact, and let $u$ be a frame of $\pi^* L$ whose value at a point of $Y$ depends only on the image of the point in $X$. Then $L$ has a frame.

Lean: `New.LineBundle.exists_isFrame_of_fpqc` (Lib/General/Geometry/LineBundles.lean).

*Proof.* Read $u$ as a frame of the pull-back of $L \otimes \mathbf{1}^{-1}$ and apply the descent of sections to it and to the frame $1$ of $\mathbf{1}$. The descended section is a frame, since its pull-back is a product of units and $\pi$ is surjective (`New.LineBundle.IsSection.isFrame_of_eq_mul`). $\square$

The hypothesis on $u$ is the descent datum. Classically a frame of $\pi^* \mathcal{L}$ descends if its two pull-backs to $Y \times_X Y$ agree. The source states the condition on points: $u_i(B, t) = u_i(B, t')$ whenever $t \circ \pi = t' \circ \pi$. A pair of such points is a point of $Y \times_X Y$, so the two conditions agree. The theorem is used for abelian schemes in Volume 8, in `Lib/Shimura/AbelianScheme/Pairings.lean`, together with the triviality of the Picard group of a local ring.

### Comparison with the classical Picard group

**Remark (Formalization).** The source never compares `New.Pic X` with $H^1(X, \mathcal{O}_X^\times)$ or with a Picard group in Mathlib. The findings of the plan record this as the second half of question Q-63: is the hand-built `Pic` equal to that of Mathlib? The following argument shows that `New.Pic X` is isomorphic to $\check{H}^1(X, \mathcal{O}_X^\times)$, and so to the classical Picard group. It is an argument of this book. The source does not contain it, and Lean has not checked it.

Let $L = (U_i, g_{ij})$ be a line bundle. By `New.PointFn.IsRegularOn.exists_ofSection`, each $g_{ij}$ agrees on $U_i \cap U_j$ with the function of a unique section $\gamma_{ij} \in \mathcal{O}(U_i \cap U_j)$. The relations $g_{ii} = 1$ and $g_{ij} g_{jk} = g_{ik}$ hold at the points $\operatorname{Spec} \mathcal{O}_{X,x} \to X$, so they hold for the germs of the $\gamma$, by `New.PointFn.ofSection_fromSpecStalk`, and so for the sections. Hence $(\gamma_{ij})$ is a Čech cocycle of $\mathcal{O}_X^\times$ on the cover $(U_i)$. Conversely, a Čech cocycle on any open cover gives a line bundle by $g_{ij} = \operatorname{ofSection}(\gamma_{ij})$, and the two constructions are inverse up to junk values off the overlaps. A frame of $L \otimes M^{-1}$ is, in the same way, a family of units $\mu_{ik} \in \mathcal{O}(U_i \cap V_k)^\times$ with $\mu_{ik} = \gamma_{ij}\, \mu_{jl}\, \delta_{lk}$ on the overlaps, where $(\delta_{kl})$ is the cocycle of $M$. This says that the two cocycles become cohomologous on the common refinement $(U_i \cap V_k)$. So $L \mapsto [(\gamma_{ij})]$ is a bijection from `New.Pic X` to $\check{H}^1(X, \mathcal{O}_X^\times)$, and it sends tensor products to products. Every open cover of $X$ can be indexed by a type in the universe $0$, for instance by a set of opens of $X$, so no class is lost by the restriction on universes. Finally $\check{H}^1(X, \mathcal{F}) \cong H^1(X, \mathcal{F})$ for every sheaf of abelian groups on every topological space (Hartshorne, Chapter III, Exercise 4.4), and $H^1(X, \mathcal{O}_X^\times) \cong \operatorname{Pic} X$ (Chapter III, Exercise 4.5). The isomorphism is compatible with pull-back.

So the second half of Q-63 has a positive answer, on every scheme, by an argument that the source does not formalize. The argument of the source does not need it. It uses only the theorems on `New.Pic` that the source proves.
