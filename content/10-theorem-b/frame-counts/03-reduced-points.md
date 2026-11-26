---
title: Reduced points
lean:
  - New/Spanning/Unfolding/ReducedPoints.lean
decls:
  - New.Filling.conjTranspose_eichler_mul_mul
  - New.Filling.exists_mem_classUnipotent_eq_one_add_smul
  - New.Filling.exists_eichler_classUnipotent
  - New.Filling.exists_classUnipotent_frameMatrix_eq
  - New.Filling.exists_frameMatrix_classUnipotent_eq_mul
  - New.Filling.tsum_le_of_encard_range_le
  - New.Filling.tsum_le_relIndex_pow_mul
  - New.Filling.submoduleIndex_smul_intVectors
  - New.Filling.submoduleIndex_smul_ne_zero
  - New.Filling.existsUnique_mul_unitriangular_mem
  - New.Filling.ratTriangle_eq_sum
  - New.Filling.IsResidueDomain.exists_mul_mem_reducedPoints_iff_rightCoset
  - New.Filling.IsResidueDomain.isBoxPartitionOfUnity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Reduced points

This section gives explicit elements of $\mathsf U_c(M)$, two colouring bounds for weighted sums, and the reduced points. The main result says that every point has exactly one coset of moves that makes it reduced. The data $S$ (`New.Filling E 𝔰`), the groups $\mathsf U_c(M)$ and $\mathsf U^0_c$, the set $D$ of residues and the reduced points are defined in [the anatomy of a term](/chapter/anatomy-of-a-term/). Throughout, $E$ contains a primitive $5040$-th root of unity (`HasPrimitiveRoot5040 E`).

### Eichler elements

**Lemma (Eichler maps are isometries).** Let $J$ be hermitian. Let the columns of $x$ be isotropic and orthogonal to each other and to the columns of $u$. Let $s^* = -s$, $g = \bar g$ and $\tau + \bar\tau = g$. Then $1 + g(xu^*J - (u + x(\tau u^*Ju - s))x^*J)$ preserves $J$.

Lean: `New.Filling.conjTranspose_eichler_mul_mul` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Put $w = u + x(\tau u^*Ju - s)$ and $T = xu^*J - wx^*J$. The hypotheses give $x^*Jx = 0$ and $x^*Ju = 0$, so $x^*Jw = 0$ and $w^*Jw = u^*Ju$. Expand $(1 + gT)^*J(1 + gT) = J + g(JT + T^*J) + g^2T^*JT$. In $JT + T^*J$ the terms $Jxu^*J$ and $Jux^*J$ cancel, and what remains is $-Jx\bigl((\tau + \bar\tau)u^*Ju - (s + s^*)\bigr)x^*J = -g\,Jxu^*Ju\,x^*J$. In $T^*JT$ only $Jxw^*Jwx^*J = Jxu^*Ju\,x^*J$ survives. So the two corrections cancel. $\square$

**Lemma (A general element).** Let $J$ be the rational Gram matrix. Let $x$ have the columns $e_{p(b)}$. Let the columns of $u$ be integral in the basis of the class $c$, and let $u$ have coordinate $0$ at $e^*_a$ for every $a \leq p(b')$. Let $s$ be integral and skew-hermitian. Then there is $\gamma \in \mathsf U_c(M)$ and $\tau \in E$ with

$$\gamma = 1 + M\bigl(xu^*J - (u + x(\tau u^*Ju - s))x^*J\bigr).$$

If the columns of $u$ are orthogonal to the frame, then $\gamma \in \mathsf U^0_c$.

Lean: `New.Filling.exists_mem_classUnipotent_eq_one_add_smul` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* The root of unity gives an integer $\tau_0$ with $\tau_0 + \bar\tau_0 = 1$. Put $\tau = M\tau_0$ and $g = M$. The vanishing of $u$ at $e^*_a$ for $a \leq p(b')$ gives $x^*Ju = 0$, and $x^*Jx = 0$ holds because the $e_a$ are isotropic and orthogonal. So the element is an isometry by the lemma above. Its matrix is block upper unitriangular, since the $e_{p(b)}$ lie low in the flag and $u$ has no coordinates at the high $e^*_a$. In the class basis, $M^{-1}(\gamma - 1)$ is integral, since $u$, $s$, $\tau_0$ and the class Gram matrix are integral. If $u$ is orthogonal to the frame, then $u^*Jf_b = 0$ and $x^*Jf_b = 0$, because $e_a$ is orthogonal to all frame vectors. So $\gamma f_b = f_b$. $\square$

**Lemma (A prescribed row).** Let $a < \varrho$. Let the row $l$ vanish at $e_b$ and at $e^*_b$ for all $b \leq a$, and let $l$ be integral on the lattice of the class $c$. Let $s$ be an integer of $E$ with $\bar s = -s$. Then some $\gamma \in \mathsf U_c(M)$ has, in $\gamma - 1$ and outside the column $e^*_a$, the row $Ml$ at $e_a$ and zero rows at the other $e_b$. If $l = 0$, the only possibly nonzero entry of these rows is $Ms$ at $(e_a, e^*_a)$.

Lean: `New.Filling.exists_eichler_classUnipotent` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Write $l = u^*J$; this is possible since $J$ is invertible. Apply the general element with the single column $x = e_a$ and with this $u$. The row of $\gamma - 1$ at $e_b$ is $M$ times the row of $xu^*J - (\dots)x^*J$. The first term gives $Ml$ at $e_a$. The second term has its columns only at $e^*_a$, since $x^*J = (e^*_a)^*$. $\square$

The rows $e_a$ with the free entries are those used in [the integral of a cutoff](/chapter/frame-counts/#the-integral-of-a-cutoff). The matrix of $u \in \mathsf U_c(M)$ on the frame is $\Theta(u)$ (`frameMatrix u`). It is unitriangular.

**Lemma.** For $a < b \leq \varrho$ and an integer $x$ of $E$, some $u \in \mathsf U_c(M)$ has $\Theta(u) = 1 + Mx\,E_{ab}$. Conversely, for every $u \in \mathsf U_c(M)$ and $a < b$, the entry $\Theta(u)_{ab}$ is $M$ times an integer of $E$.

Lean: `New.Filling.exists_classUnipotent_frameMatrix_eq`, `New.Filling.exists_frameMatrix_classUnipotent_eq_mul` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* There is an integral form $l$ that is $1$ at $f_b$ and $0$ at the other basis vectors outside $X_0$ (`exists_integral_form_besselFrame`). Apply the lemma on a prescribed row with the row $xl$ at $e_a$. For the converse, $M^{-1}(u - 1)$ is integral in the class basis, and the frame vectors are part of that basis. $\square$

### Colouring

**Lemma (Colouring).** Let a set $A$ have a colouring with at most $N$ colours, such that elements of one colour are $R$-related. Suppose every nonempty subset of $A$ of pairwise $R$-related elements has total weight at most $x$. Then $\sum_{a \in A}w(a) \leq Nx$.

Lean: `New.Filling.tsum_le_of_encard_range_le` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Each colour class is a nonempty set of pairwise related elements, so its weight is at most $x$. Sum over the colours. $\square$

**Lemma (Colouring by residues).** Let $f(a) \in (K')^\iota$ for $a \in A$, and let $K \cap K'$ have finite index in $K'$. Suppose every nonempty subset of $A$ on which $f$ is constant modulo $K$ has weight at most $x$. Then $\sum_{a \in A}w(a) \leq [K' : K \cap K']^{|\iota|}\,x$.

Lean: `New.Filling.tsum_le_relIndex_pow_mul` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Colour $a$ by the classes of the $f(a)_i$ in $K'/(K \cap K')$. There are at most $[K' : K \cap K']^{|\iota|}$ colours. Apply the lemma on colouring. $\square$

**Lemma.** For a unit $c$ of the finite adeles in $\hat{\mathcal O}$, the index of $c\hat{\mathcal O}^\iota$ in $\hat{\mathcal O}^\iota$ is $[\hat{\mathcal O} : c\hat{\mathcal O}]^{|\iota|}$, and it is not zero.

Lean: `New.Filling.submoduleIndex_smul_intVectors`, `New.Filling.submoduleIndex_smul_ne_zero` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* $c\hat{\mathcal O}^\iota$ is the lattice of the columns of the scalar matrix $c\cdot 1$, whose determinant is $c^{|\iota|}$. The index of a column lattice is the index of its determinant (`New.submoduleIndex_colLattice_intVectors`, in [congruence subgroups](/chapter/congruence-subgroups/)). The index $[\hat{\mathcal O} : c\hat{\mathcal O}]$ is positive. $\square$

**Remark (Formalization).** The index is `New.submoduleIndex`, a natural number. For an infinite index Lean gives the value $0$. The second statement excludes this case here, and the colouring lemma asks for `relIndex K K' ≠ 0` for the same reason.

### Unitriangular reduction

**Lemma (Reduction of unitriangular matrices).** Let $L$ be an additive submonoid of a ring $R$, and let every $w \in R$ have exactly one translate $l + w$, $l \in L$, in a set $D$. Let $\Gamma$ be a group of upper unitriangular $n \times n$ matrices whose entries above the diagonal lie in $L$, and which contains $1 + lE_{ab}$ for all $a < b$ and $l \in L$. Then for every unitriangular $x$ there is exactly one $\gamma \in \Gamma$ such that every entry of $x\gamma$ above the diagonal lies in $D$.

Lean: `New.Filling.existsUnique_mul_unitriangular_mem` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Give the position $(a, b)$, $a < b$, the degree $b - a$. If the entries of $\gamma$ of degree less than $b - a$ are those of $1$, then $(g\gamma)_{ab} = \gamma_{ab} + g_{ab}$ for every unitriangular $g$. Indeed, in $\sum_l g_{al}\gamma_{lb}$ only $l = a$ and $l = b$ remain: $g_{al} = 0$ for $l < a$, $\gamma_{lb} = 0$ for $l > b$, and $\gamma_{lb} = 0$ for $a < l < b$ by the hypothesis on the degree. The elementary matrix $1 + lE_{ab}$ changes the entry at $(a, b)$ by $l$ and no other entry of the same or lower degree. Now fix the entries degree by degree. At each position the condition $(x\gamma)_{ab} \in D$ fixes $\gamma_{ab}$ in a unique way, by the hypothesis on $D$. An abstract form of this induction is `existsUnique_mul_mem_box`. $\square$

### The unique coset

For a point $y = (y_v)$ at the infinite places, $T(y)$ (`S.ratTriangle y`) is the triangular Gram-Schmidt matrix of $y$ read in the rational frame, as a matrix of tuples over the infinite places. The point $y$ is *reduced* for $D$ if every entry of $T(y)$ above the diagonal lies in $D$.

**Lemma.** For $u$ in the rational group with $u \in \mathsf U$, $T(y) = T(uy)\,\Phi(\Theta(u))$, where $\Phi$ applies the embeddings at each infinite place.

Lean: `New.Filling.ratTriangle_eq_sum` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* In the normalised frame, the Gram-Schmidt matrix satisfies $\operatorname{GS}(uy)\Theta(u) = \operatorname{GS}(y)$ (`gramSchmidtMatrix_besselS_mul`). Pass to the rational frame. The scales of the summation index cancel. $\square$

**Theorem (One coset).** Let $D$ be a residue domain (`IsResidueDomain`) and $c$ a class. For each point $y$ there is $u_0 \in \mathsf U_c(M)$ such that, for all $u \in \mathsf U_c(M)$,

$$uy \text{ is reduced} \iff uu_0^{-1} \in \mathsf U^0_c.$$

Lean: `New.Filling.IsResidueDomain.exists_mul_mem_reducedPoints_iff_rightCoset` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* Work in the group $G$ of unitriangular matrices over the ring of tuples $\mathbb C^{\text{places}}$. The map $\theta(u) = \Phi(\Theta(u))$ is a homomorphism from $\mathsf U_c(M)$ to $G$. Its kernel is $\mathsf U^0_c$: $u$ fixes the frame exactly when $\Theta(u) = 1$. By the last lemma, $T(uy) = T(y)\theta(u^{-1})$. The image of $\theta$ satisfies the hypotheses of the reduction lemma with $L = M\mathcal O_E$ (the level multiples) and the given $D$, by the lemma on frame matrices. So there is exactly one $\theta(w)$ in the image with $T(y)\theta(w)$ reduced. Put $u_0 = w^{-1}$. Then $uy$ is reduced if and only if $\theta(u^{-1}) = \theta(u_0^{-1})$, that is, if and only if $\theta(uu_0^{-1}) = 1$. $\square$

**Theorem (Reduced points give a partition of unity).** Let $S$ be admissible. For every class $c$, the indicator $\omega$ of the points reduced for $D$ is a partition of unity in boxes (`IsBoxPartitionOfUnity`). That is, $\omega$ is measurable and $\omega \leq 1$; $\omega(y) \neq 0$ implies $y_v \in \operatorname{Box}(b^{27}\ell(y_v))$ at every place $v$; $\omega$ is invariant under the fixer of the frame; and $\sum_{\gamma \in \mathsf U_c(M)}a(\gamma)\,\omega(\gamma y) = 1$ for every weight $a$ whose sum over each right coset of $\mathsf U^0_c$ is $1$.

Lean: `New.Filling.IsResidueDomain.isBoxPartitionOfUnity` (New/Spanning/Unfolding/ReducedPoints.lean).

*Proof.* The set of reduced points is measurable, and an indicator is at most $1$. The box condition is the bound for reduced points, `IsResidueDomain.mem_frameBox`, from [the anatomy of a term](/chapter/anatomy-of-a-term/). The fixer of the frame does not change $T(y)$. For the sum: by the theorem on one coset, the $\gamma$ with $\gamma y$ reduced are exactly the $u u_0$ with $u \in \mathsf U^0_c$. So the sum is $\sum_{u}a(uu_0) = 1$. $\square$

**Remark (Formalization).** The sum is a `tsum` in $[0, \infty]$, so it always exists, and no question of convergence arises. The weights $a$ are arbitrary; the identity holds for every $a$ with sum $1$ on each coset.
