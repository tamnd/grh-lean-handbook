---
title: The evaluation of a pair is admissible
lean:
  - New/UpperBound/Seesaw/AdmissibleEvaluation.lean
decls:
  - New.Seesaw.inv_xFin_mulVec_mem_of_spansLattice
  - New.Seesaw.flipScale
  - New.Seesaw.coe_flipScale
  - New.Seesaw.inv_xFin_flipSum_mulVec_mem_iff
  - New.Grading.gradeZeroRows
  - New.Grading.isIntMatrix_gradeZeroRows
  - New.Grading.conjTranspose_gradeZeroRows
  - New.Seesaw.DoubleLiftData.liftVector
  - New.Seesaw.DoubleLiftData.LiftsNeighbours
  - New.Seesaw.DoubleLiftData.MatchesDenominators
  - New.Seesaw.DoubleLiftData.neighbourLift
  - New.Seesaw.DoubleLiftData.planeCoeff
  - New.Seesaw.DoubleLiftData.isotropicCoeff
  - New.Seesaw.DoubleLiftData.latticeLift
  - New.Seesaw.DoubleLiftData.conjTranspose_latticeLift_mulVec_stackedStringMapFin
  - New.Seesaw.DoubleLiftData.latticeLift_eq_latticeUnitary_add_isotropic
  - New.Seesaw.DoubleLiftData.isIntMatrix_latticeLift
  - New.Seesaw.DoubleLiftData.zeroTermLattice_splitting_eq
  - New.Seesaw.DoubleLiftData.evalAt_liftVector_eq_zero
  - New.Seesaw.DoubleLiftData.evalAt_neighbourLift_eq_zero
  - New.Seesaw.DoubleLiftData.conjTranspose_latticeLift_mulVec_mem
  - New.Seesaw.DoubleLiftData.latticeUnitary_mulVec_conjTranspose_latticeLift_mulVec
  - New.Seesaw.DoubleLiftData.conjTranspose_iFin_mulVec_mem
  - New.Seesaw.DoubleLiftData.exists_finEval_finHeisenbergOp_vacElem
  - New.Seesaw.DoubleLiftData.exists_zeroTermFin_splitting_vacElem_eq_sum
  - New.Seesaw.isAdmissibleEval_finEval
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The evaluation of a pair is admissible

Let $D$ be double lift data for gradings $\mathsf Y$, $\mathsf Y'$, $\mathsf Y''$ of $V$, $V'$, $V''$, as in [part 1](/chapter/seesaw-identity-1/). This section proves that the finite evaluation $\mathrm{ev}_D$ is an admissible evaluation in the sense of Section 3, under conditions on the lifts of neighbour vectors. The key step identifies the zero term lattice $L'_D$ with the neighbour lattice of Section 2.

In this section $X$, $X'$, $X''$ denote the definite parts with their last vectors $e$, $e'$, $e''$ included. So the rows of Section 2 are indexed by $X \sqcup X''$, the basis of $X^- \oplus X''$, and the columns by $X'$. Fix $N$ prime, $P$ split for $N$, $\pi$ split squarefree for $N$ at $P$, and a scaling $\kappa$ at $M$ for $(N, \beta, \delta)$. Let $\gamma$ be the neighbour matrix and $g = (\kappa\gamma) \otimes 1$ the lattice unitary of Section 2.

### Two lattice facts

The space $V^-$ is $V$ with the form negated. Its point is the point of $V$ times a fixed idele.

**Definition (The flip scale).** The flip scale $s$ is the finite part of the conjugate of the flip idele for $\eta$ (`flipIdele normNegOne 1`). It satisfies $s = \bar\eta\,\bar\alpha\alpha^{-1}$, where $\alpha$ is the finite idele of the Weil data.

Lean: `New.Seesaw.flipScale`, `New.Seesaw.coe_flipScale` (New/UpperBound/Seesaw/AdmissibleEvaluation.lean).

**Lemma (The lattice of $V^- \oplus V''$).** A vector $y$ on the basis of $V \oplus V''$ lies in the lattice of $V^- \oplus V''$ if and only if $s^{-1}y_V$ lies in the lattice of $V$ and $y_{V''}$ lies in the lattice of $V''$.

Lean: `New.Seesaw.inv_xFin_flipSum_mulVec_mem_iff`.

*Proof.* The point of $V^- \oplus V''$ is block diagonal, with blocks $s$ times the point of $V$ and the point of $V''$. So its inverse is block diagonal with blocks $s^{-1}$ times the inverse point of $V$ and the inverse point of $V''$ (Lean: `New.Seesaw.inv_xFin_flipSum`). A vector is integral if and only if each block is integral. $\square$

The glued lattice of [standard lattices](/chapter/seesaw-identity-1/) has the basis $B(a, \pi, u)$. For odd $s$ it consists of the vectors of $X \setminus \{e\}$, the glue vector $y' = e/\bar\pi + uz/N$ and $u e_b$ for the string vectors $e_b$. Here $z$ is the middle vector of the string.

**Lemma (Vectors of the glued lattice).** Suppose that the frame of $V$ spans the glued lattice for $(a, \pi, u)$ and that the string has odd length. Let $x$ be a vector on $X$ and $c$ an adele. Let $w$ be the vector with component $x$ on $X$, coordinate $u(\pi^{-1}x_e + c)$ at $z$ and $0$ at the other string vectors. If $c$, $\bar\pi x_e$ and $x_i$ for $i \neq e$ are integral, then $w$ lies in the lattice of $V$.

Lean: `New.Seesaw.inv_xFin_mulVec_mem_of_spansLattice`.

*Proof.* Write $w$ in the basis $B(a, \pi, u)$. The coefficients are $x_i$ at $i \neq e$, $\bar\pi x_e$ at $y'$, $c$ at $uz$ and $0$ elsewhere. Indeed $\bar\pi x_e\,y' = x_e e + u\bar\pi x_e N^{-1} z$, and $\bar\pi N^{-1} = \pi^{-1}$. These coefficients are integral. The point of $V$ is $B(a, \pi, u)k$ with $k \in \mathrm{GL}(\hat{\mathcal O})$. So the coordinates of $w$ in the point are $k^{-1}$ times integral coefficients, and they are integral. $\square$

The map $x \mapsto AxR$ below uses rows of the point of $V'$. Let $R$ be the matrix of the rows of the point of $V'$ at the indices of $X'$.

**Lemma (The grade zero rows).** If the frame of $V'$ spans the glued lattice for $(a, \pi, u)$ and the string of $V'$ has even length, then $R$ is integral. In general $R^*$ is the inverse point of $V'$ followed by the inclusion of $X'$.

Lean: `New.Grading.gradeZeroRows`, `New.Grading.isIntMatrix_gradeZeroRows`, `New.Grading.conjTranspose_gradeZeroRows`.

*Proof.* For even length the glued basis is the identity on $X'$. So the rows of $B(a, \pi, u)k$ at $X'$ are the rows of $k$, which are integral. For the second claim, the inverse of the point is its adjoint times the Gram matrix, and the Gram matrix is $1$ on $X'$. $\square$

### The lift of the neighbour matrix

The grade zero part of $V^- \oplus V''$ is $q$ hyperbolic planes plus $X^- \oplus X''$ (part 1). A vector of the grade zero part is mapped to $V^- \oplus V''$ by the inclusion of $D$.

**Definition (The lift of a neighbour vector).** For an adele $c$ and a vector $x$ on $X \sqcup X''$, the lift $\ell(c, x)$ is the image under the inclusion of the grade zero vector with:

1. coefficient $0$ at the first vector of each plane;
2. coefficient $s u c$ at the second vector of each plane;
3. component $s\kappa_b x_b$ at $b \in X$ and $\kappa_b x_b$ at $b \in X''$.

The lifts *lift the neighbours* for $(\pi, u, \kappa, \delta)$ if $\ell(c, x)$ lies in the lattice of $V^- \oplus V''$ for every neighbour vector $(c, x)$ for $(\pi, \delta)$. The data *match the denominators* for $(\kappa, \beta)$ if $v(\mathrm{selfOrConj}(\beta)_i) = v(\mathrm{selfOrConj}(\beta)_b\,\kappa_b)$ at every finite place whenever the inclusion has a nonzero entry at $(i, b)$.

Lean: `New.Seesaw.DoubleLiftData.liftVector`, `New.Seesaw.DoubleLiftData.LiftsNeighbours`, `New.Seesaw.DoubleLiftData.MatchesDenominators`.

Here $\mathrm{selfOrConj}(\beta)_i$ for an index $i$ of $V \sqcup V''$ means $\beta$ on the indices of $V$ and $\bar\beta$ on those of $V''$.

**Definition (The lattice lift).** Let $A$ be the matrix whose column $j$ is the coordinate vector, in the point of $V^- \oplus V''$, of the lift of column $j$ of $\gamma$ with coefficient $c_j$. Let $\mathrm{pc}$ be the matrix with entry $s u c_j$ at each plane. The isotropic coefficient $\mathrm{ic}$ is $0$ at the maps of positive degree and $\mathrm{pc} \otimes 1$ at the planes. The lattice lift is $B = A \otimes R^{\mathsf T}$, the matrix of $x \mapsto AxR$ from $\mathrm{Hom}(X', X^- \oplus X'')$ to $\mathrm{Hom}(V', V^- \oplus V'')$.

Lean: `New.Seesaw.DoubleLiftData.neighbourLift`, `New.Seesaw.DoubleLiftData.planeCoeff`, `New.Seesaw.DoubleLiftData.isotropicCoeff`, `New.Seesaw.DoubleLiftData.latticeLift`.

Let $\tau$ be the finite coordinates of the stacked shift $(\mathrm{sh}^*, \mathrm{sh}')$, by which $\mathrm{ev}_D$ translates.

**Lemma ($B$ kills the shift).** $B^*\tau = 0$.

Lean: `New.Seesaw.DoubleLiftData.conjTranspose_latticeLift_mulVec_stackedStringMapFin`.

*Proof.* $B^* = A^* \otimes (R^*)^{\mathsf T}$, so $B^*\tau = A^*\,\tau\,R^*$ as a matrix. By the lemma on grade zero rows, $R^*$ is the inverse point of $V'$ followed by the inclusion of $X'$. So $\tau R^*$ is the stacked shift restricted to $X'$. Both shifts only move string vectors, so this restriction is $0$. $\square$

Let $i$ be the finite embedding of $\mathrm{Hom}(X', X^- \oplus X'')$ in $\mathrm{Hom}(V', V^- \oplus V'')$ given by the splitting of $D$, and $k$ the finite isotropic frame.

**Theorem (The lattice lift is a lift of $g$).** $B = i\,g + k\,\mathrm{ic}$.

Lean: `New.Seesaw.DoubleLiftData.latticeLift_eq_latticeUnitary_add_isotropic`.

*Proof.* Let $Z = X^- \oplus X''$ with point $\mathrm{diag}(s, 1)$. Let $S$ be the splitting of $Z$ plus $q$ planes that removes the planes, with embedding $S_i$ and frame $S_k$. Let $A_0$ be the inverse point of $V^- \oplus V''$ times the inclusion of $D$. Column $j$ of $A$ is $A_0$ applied to the grade zero vector of the definition. That vector is $S_i$ applied to $Z$'s point times column $j$ of $\kappa\gamma$, plus $S_k$ applied to column $j$ of $\mathrm{pc}$. So

$$A = A_0\bigl(S_i\,\mathrm{diag}(s, 1)\,\kappa\gamma + S_k\,\mathrm{pc}\bigr).$$

The splitting of $D$ is the composite of the removal of the maps of nonzero degree and the removal of the planes. In coordinates this gives $i = (A_0 S_i\,\mathrm{diag}(s,1)) \otimes R^{\mathsf T}$ and $k\,\mathrm{ic} = (A_0 S_k\,\mathrm{pc}) \otimes R^{\mathsf T}$. Since $g = \kappa\gamma \otimes 1$, the product $i g$ is $(A_0 S_i\,\mathrm{diag}(s,1)\,\kappa\gamma) \otimes R^{\mathsf T}$. The Kronecker product is additive in the first factor, so $ig + k\,\mathrm{ic} = A \otimes R^{\mathsf T} = B$. $\square$

So $Bx$ lies in $I^\perp$ for the isotropic space $I$ of the splitting, and its class in $I^\perp/I$ is $gx$.

**Corollary (Integrality).** If the frame of $V'$ spans the glued lattice for some $(a, \pi, u')$ and the lifts lift the neighbours for $(\pi, u, \kappa, \delta)$, then $B$ is integral.

Lean: `New.Seesaw.DoubleLiftData.isIntMatrix_latticeLift`.

*Proof.* Column $j$ of $\gamma$, with coefficient $c_j$, is a neighbour vector (Section 2). So column $j$ of $A$ is integral by hypothesis. The string of $V'$ has even length (part 1), so $R$ is integral. Each entry of $B$ is a product of an entry of $A$ and an entry of $R$. $\square$

### The zero term lattice is the neighbour lattice

Two facts on the zero term lattice $L'_D$ of part 1 are needed. They hold for every splitting.

**Lemma (Lattices from integral lifts).** Let $g$ be a finite unitary point and $B = ig + kc$ an integral matrix. Then:

1. $g\hat{\mathcal O}^{n_0} \subseteq L'_D$;
2. $L'_D = g\hat{\mathcal O}^{n_0}$.

Lean: `New.Seesaw.map_stdLattice_le_zeroTermLattice`, `New.Seesaw.zeroTermLattice_eq_map_of_le` (New/UpperBound/Seesaw/EdgePairEvaluation.lean).

*Proof.* (1) For integral $x$ the vector $Bx = i(gx) + k(cx)$ is integral. So $gx \in L'_D$ with $b = cx$. (2) Let $w \in L'_D$. By part 1, $L'_D$ is unimodular, so $\psi_{\mathrm f}(x^*w) = 1$ for all $x \in L'_D$, in particular for $x \in g\hat{\mathcal O}^{n_0}$. The lattice $g\hat{\mathcal O}^{n_0}$ is self-dual, as the image of a self-dual lattice under a unitary point. So $w \in g\hat{\mathcal O}^{n_0}$. With (1) the two lattices are equal. $\square$

**Theorem (The zero term lattice of a pair).** Suppose that the frame of $V'$ spans the glued lattice for some $(a, \pi, u')$ and that the lifts lift the neighbours for $(\pi, u, \kappa, \delta)$. Then $L'_D$ is the neighbour lattice $g\hat{\mathcal O}$.

Lean: `New.Seesaw.DoubleLiftData.zeroTermLattice_splitting_eq`.

*Proof.* Apply the lemma to $B = ig + k\,\mathrm{ic}$, which is integral by the corollary. $\square$

**Corollary (The zero term of the vacuum).** Under the same hypotheses there is $c \neq 0$ with

$$\mathrm{ZT}^{\mathrm f}_D(\phi_0) = c\sum_{(y, q)}\rho\bigl(r(y, q)\bigr)\phi_0',$$

where $\phi_0$ and $\phi_0'$ are the vacua of $\mathrm{Hom}(V', V^- \oplus V'')$ and of the pair space, and $r(y, q)$ runs over the coset representatives of Section 2.

Lean: `New.Seesaw.DoubleLiftData.exists_zeroTermFin_splitting_vacElem_eq_sum`.

*Proof.* By the theorem, the representatives $r(y, q)$ lie in $L'_D$ and represent it modulo integral points (Section 2). Apply the [theorem on translates of the vacuum](/decl/New.Seesaw.exists_zeroTermFin_vacElem_eq_sum/). $\square$

### The value at a translate

**Lemma (Translates and the zero term).** Let $B = ig + kc$ be integral with $g$ unitary. For every $y$ there is $\zeta$, equal to $0$ or a root of unity, with $\mathrm{ZT}^{\mathrm f}_D(\rho(y)\phi_0) = \zeta\,\rho(gB^*y)\,\mathrm{ZT}^{\mathrm f}_D(\phi_0)$.

Lean: `New.Seesaw.exists_zeroTermFin_finHeisenbergOp_eq_smul` (New/UpperBound/Seesaw/EdgePairEvaluation.lean).

*Proof.* If the left side is $0$, take $\zeta = 0$. Otherwise part 1 gives $y = iw + kb + l$ with $l$ integral. Then $\mathrm{ZT}^{\mathrm f}_D(\rho(y)\phi_0) = \zeta_1\rho(w)\mathrm{ZT}^{\mathrm f}_D(\phi_0)$ for a root of unity $\zeta_1$ (Lean: `New.Seesaw.exists_zeroTermFin_finHeisenbergOp_add`). The orthogonality of $i$ and $k$ gives $B^*(iw + kb) = g^{-1}w$. So $gB^*y = w + x$ with $x = gB^*l$. Since $B^*l$ is integral, $x \in g\hat{\mathcal O} \subseteq L'_D$. The translations by $L'_D$ fix $\mathrm{ZT}^{\mathrm f}_D(\phi_0)$ (Lean: `New.Seesaw.finHeisenbergOp_zeroTermFin_vacElem`). Let $\tau_0$ be the trace one adele. The composition law $\rho(w)\rho(x) = \psi(\bar\tau_0\,x^*w)\,\rho(w + x)$ (Lean: `New.Space.finHeisenbergOp_finHeisenbergOp`) gives $\rho(w)\mathrm{ZT}^{\mathrm f}_D(\phi_0) = \rho(w)\rho(x)\mathrm{ZT}^{\mathrm f}_D(\phi_0) = \psi(\bar\tau_0\,x^*w)\,\rho(gB^*y)\mathrm{ZT}^{\mathrm f}_D(\phi_0)$. The value of $\psi$ is a root of unity, so $\zeta = \zeta_1\psi(\bar\tau_0\,x^*w)$ works. $\square$

**Lemma (Away from $N$ only $g$ counts).** If $y$ vanishes above $N$, then $gB^*y = i^*y$.

Lean: `New.Seesaw.DoubleLiftData.latticeUnitary_mulVec_conjTranspose_latticeLift_mulVec`.

*Proof.* Let $\epsilon$ be the idempotent of $P \cup \bar P$. Each coefficient $c_j$ has a factor $j$ or $\bar j$, so $\epsilon\,\mathrm{ic} = \mathrm{ic}$. Then $\mathrm{ic}^*k^*y = \mathrm{ic}^*\epsilon k^*y = \mathrm{ic}^*k^*(\epsilon y) = 0$, since $\epsilon$ is self-conjugate and $\epsilon y = 0$. So $B^*y = g^*i^*y = g^{-1}i^*y$, and $gB^*y = i^*y$. $\square$

**Theorem (The value at a translate).** Suppose that $B$ is integral and $y$ vanishes above $N$. Then there is $\zeta$, equal to $0$ or a root of unity, with

$$\mathrm{ev}_D(\rho(y)\phi_0) = \zeta\cdot\mathrm{arrowTensor}^{-1}\Bigl(\rho(i^*y)\,\mathrm{ZT}^{\mathrm f}_D(\phi_0)\Bigr).$$

Lean: `New.Seesaw.DoubleLiftData.exists_finEval_finHeisenbergOp_vacElem`.

*Proof.* By definition $\mathrm{ev}_D(f) = \mathrm{arrowTensor}^{-1}\bigl(\mathrm{ZT}^{\mathrm f}_D(\rho(\tau)f)\bigr)$. The composition law gives $\rho(\tau)\rho(y)\phi_0 = \xi\rho(\tau + y)\phi_0$ with $\xi = \psi(\bar\tau_0\,y^*\tau)$ a root of unity. By the two lemmas, $gB^*(\tau + y) = gB^*y = i^*y$, since $B^*\tau = 0$. The lemma on translates gives $\zeta'$ with $\mathrm{ZT}^{\mathrm f}_D(\rho(\tau + y)\phi_0) = \zeta'\rho(i^*y)\mathrm{ZT}^{\mathrm f}_D(\phi_0)$. Take $\zeta = \xi\zeta'$. The left inverse is linear. $\square$

### Denominators

**Lemma (Zero entries of the lift).** Suppose that the data match the denominators for $(\kappa, \beta)$. If $v(\mathrm{selfOrConj}(\beta)_i) \neq v(\mathrm{selfOrConj}(\beta)_j\,\kappa_j)$ at a place $w$, then the entry $A_{ij}$ vanishes at $\bar w$.

Lean: `New.Seesaw.DoubleLiftData.evalAt_liftVector_eq_zero`, `New.Seesaw.DoubleLiftData.evalAt_neighbourLift_eq_zero`.

*Proof.* Above $N$ both $\mathrm{selfOrConj}(\beta)$ and $\kappa$ are units, so the valuations agree there. Hence $w$ and $\bar w$ are not in $P \cup \bar P$. At $\bar w$ column $j$ of $\gamma$ is the basis vector $j$ and $c_j = 0$. So at $\bar w$ the lift of column $j$ is column $j$ of the inclusion, times a factor. The entry $A_{ij}$ is a sum over $l$ of the inverse point at $(i, l)$ times the lift at $l$. If the inclusion vanishes at $(l, j)$, the term is $0$ at $\bar w$. Otherwise $v(\mathrm{selfOrConj}(\beta)_l) = v(\mathrm{selfOrConj}(\beta)_j\kappa_j) \neq v(\mathrm{selfOrConj}(\beta)_i)$, so $l$ and $i$ lie in different blocks. The inverse point of $V^- \oplus V''$ is block diagonal, so its entry at $(i, l)$ is $0$. $\square$

**Proposition (The projection keeps the denominators).** Suppose that $B$ is integral and the data match the denominators. Let $y$ vanish above $N$, with $\mathrm{selfOrConj}(\beta)\,y$ integral away from $n$. Then $\mathrm{selfOrConj}(\beta)\,i^*y$ is integral away from $n$.

Lean: `New.Seesaw.DoubleLiftData.conjTranspose_latticeLift_mulVec_mem`, `New.Seesaw.DoubleLiftData.conjTranspose_iFin_mulVec_mem`.

*Proof.* First, $\mathrm{selfOrConj}(\beta)_j\kappa_j\,(B^*y)_j$ is integral away from $n$. Indeed $(B^*y)_j = \sum_i \bar B_{ij}y_i$. When the valuations of the weights at $i$ and $j$ agree, $v(\bar B_{ij}) \le 1$ gives the bound. When they differ, $B_{ij}$ vanishes at $\bar w$ by the lemma, so $\bar B_{ij}$ vanishes at $w$ (Lean: `New.Seesaw.conjTranspose_mulVec_mem_weightedTranslations`). Second, $B^*y$ vanishes above $N$, so $g$ acts on it by the rows $\kappa_j$ (Section 2). With the last lemma, $i^*y = gB^*y$ has entries $\kappa_j(B^*y)_j$. $\square$

### The main theorem on evaluation

**Theorem (The evaluation of a pair is admissible).** Suppose that:

1. the frame of $V'$ spans the glued lattice for some $(a, \pi, u')$;
2. the lifts lift the neighbours for $(\pi, u, \kappa, \delta)$;
3. the data match the denominators for $(\kappa, \beta)$.

Then $\mathrm{ev}_D$ is an admissible evaluation for $(N, P, \beta)$ with weights $\mathrm{selfOrConj}(\beta)$.

Lean: `New.Seesaw.isAdmissibleEval_finEval`.

*Proof.* $B$ is integral by the corollary on integrality. Let $c \neq 0$ be the constant of the corollary on the zero term of the vacuum, and $K$ the order of the away quotient $Q$. Take $C = cK$. Let $n$ be prime to $N$ and $y$ with $\mathrm{selfOrConj}(\beta)y$ integral away from $n$.

1. By Section 3, $\rho(y)\phi_0 = \xi\rho(y')\phi_0$ with $\xi$ a root of unity and $y'$ vanishing above $N$, with the same denominators.
2. By the theorem on the value at a translate, $\mathrm{ev}_D(\rho(y')\phi_0) = \zeta\,A^{-1}\bigl(\rho(i^*y')\mathrm{ZT}^{\mathrm f}_D(\phi_0)\bigr)$, where $A$ is $\mathrm{arrowTensor}$.
3. By the proposition on denominators, $i^*y'$ vanishes above $N$ and has the denominators $\mathrm{selfOrConj}(\beta)$ away from $n$.
4. Substitute the corollary: the vector is $\xi\zeta c$ times $\mathrm{arrowTensor}^{-1}$ of $\rho(i^*y')\sum_{(y,q)}\rho(r(y,q))\phi_0'$. By the theorem on the sum over the neighbour lattice (Section 3), that vector is an admissible combination of the vectors $K\,G(t_1, t_2)$. Its image under multiplication by $c$ is an admissible combination of the vectors $cK\,G(t_1, t_2)$.
5. Multiplication by $\zeta$ and by $\xi$, each $0$ or a root of unity, keeps a combination admissible (Lean: `New.Seesaw.IsAdmissibleCombination.smul_of_eq_zero_or_isOfFinOrder`). $\square$

**Remark (Formalization).** The constant of `IsAdmissibleEval` is an existential. The proof gives $C = cK$ with $c \neq 0$ and $K \geq 1$, so here $C \neq 0$. The left inverse of arrowTensor is a choice off the range of arrowTensor. The vectors to which it is applied in the proof lie in the range by the gluing theorem of Section 3, so the value does not depend on the choice there.

Section 5 checks the three hypotheses for the middle pairs and the last pair of the tower.
