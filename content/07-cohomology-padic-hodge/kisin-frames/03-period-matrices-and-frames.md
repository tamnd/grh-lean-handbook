---
title: Period matrices and frames
lean:
  - Lib/PadicHodge/Kisin/Bicommutant.lean
  - Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean
  - Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean
decls:
  - New.Lift.Chart.bicommutant
  - New.Lift.Chart.adjoinEDivPClosure_eq_bicommutant
  - New.Lift.Chart.exists_bicommutant_mul_phi_E_eq_one
  - New.Lift.Chart.IsPeriodMatrix
  - New.Lift.Chart.IsPeriodMatrixOf
  - New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf
  - New.Lift.Chart.IsPeriodBasis
  - New.Lift.Chart.IsPeriodMatrix.exists_basis
  - New.Lift.Chart.exists_det_ne_zero
  - New.Lift.Chart.not_dvd_det_of_frobenius
  - New.Lift.Chart.IsPeriodMatrix.exists_frame
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Period matrices and frames

This section goes from a crystalline lattice to a frame. The steps are these. A crystalline lattice has a matrix $M$ of invariant periods over $B_{\max}$. After multiplication by a power of $E\tau$, this matrix has entries in $B^+$. The result $U$ is a *period matrix*. From $U$ the source builds a matrix $Q$ over $A_{\inf}$ that spans the solutions of $UY = E^h X$, and it shows that $p \nmid \det Q$. Then $Q$ and the matrix $Z$ with $UZ = E^h Q$ form a *frame*. The ring in which $Z$ has its entries is the ring $S_B$, which we define first.

Throughout, $c$ is a chart with ring $S$ and element $E$, as in the previous section. The maps $A_{\inf} \to A_{\max} \to B^+ \to B_{\max}$ are injective. The source writes `ainfToBPlus` for the map $A_{\inf} \to B^+$, and `amaxImage` for the image of $A_{\max}$ in $B^+$.

### The ring $S_B$

Classically, the elements of $\mathfrak{S}[1/p]$ that are "integral enough" for crystalline periods form the ring $\mathcal{O}$ of rigid functions on the open unit disc, or the completion of $\mathfrak{S}[E/p]$. The source uses a ring of the second kind, but it defines it by a commutation property.

**Definition (The ring $S_B$).** The ring $S_B$ of the chart is the set of $y \in B^+$ such that multiplication by $y$ commutes with every $S$-linear map $G : B^+ \to B^+$ that keeps the image of $A_{\max}$.

Lean: `New.Lift.Chart.bicommutant` (Lib/PadicHodge/Kisin/Bicommutant.lean).

The definition is a bicommutant. The set of $S$-linear maps that keep $A_{\max}$ is a monoid, and $S_B$ is the set of elements whose multiplication is in its centralizer. So $S_B$ is an $S$-subalgebra of $B^+$. It contains $S$, and it contains $1/p$, because $p$ is in $S_B$ and is a unit of $B^+$ (`New.Lift.Chart.exists_bicommutant_mul_p_eq_one`). The next theorem gives a concrete form.

**Theorem.** The ring $S_B$ is the closure of $S[E/p]$ in $B^+$ with $p$ inverted. Precisely, $y \in S_B$ if and only if there is $m$ such that for every $n$, $p^m y = s + p^n w$ with $s \in S[E/p]$ and $w$ in the image of $A_{\max}$.

Lean: `New.Lift.Chart.adjoinEDivPClosure_eq_bicommutant` (Lib/PadicHodge/Kisin/Bicommutant.lean).

*Proof.* The source outlines the proof as follows. The coordinate map $\lambda_0 : A_{\inf} \to S$ of the chosen topological basis is $S$-linear and is the identity on $S$. Its extension to $B^+$ keeps the image of $A_{\max}$, and it fixes $S[E/p]$ and $S_B$. Let $y$ be in the closure, with $p^m y = s_n + p^n w_n$ for every $n$. Then $\lambda_0$ moves $p^m y$ by an element of $p^n A_{\max}$ for every $n$, so it does not move it. In the other direction, let $y \in S_B$. Then $\lambda_0$ sends polynomial approximations of $p^m y$ over $A_{\max}$ into $S[E/p]$. $\square$

**Lemma.** The image of $\varphi(E)$ in $B^+$ has an inverse in $S_B$.

Lean: `New.Lift.Chart.exists_bicommutant_mul_phi_E_eq_one` (Lib/PadicHodge/Kisin/Bicommutant.lean).

*Proof.* The element $\varphi(E)$ is associated to $\varphi(\xi)$, and $\varphi(\xi)$ is associated to $p$ in $A_{\max}$. So $\varphi(E)$ is a unit of $B^+$. The ring $S_B$ has this property: if $w \in S_B$ is nonzero and $wu \in S_B$, then $u \in S_B$. Apply it with $w = \varphi(E)$, which is in $S_B$, and $u = \varphi(E)^{-1}$, with $wu = 1$. $\square$

Every $S$-linear map $f : A_{\inf} \to A_{\inf}$ extends to an $S$-linear map of $B^+$ that keeps the image of $A_{\max}$ (`New.Lift.Chart.exists_extendToBPlus`). The source chooses one extension, `New.Lift.Chart.extendToBPlus`. This is the second use of `choose` in the chapter.

### Period matrices

Let $\Gamma$ be a group with a map to $G_p$. Let $T$ be a free $\mathbb{Z}_p$-module of finite rank with an action $\rho$ of $\Gamma$, and fix a basis $e$ of $T$. A matrix $M$ over $B_{\max}$ *has invariant columns* (`New.Period.HasInvariantColumns`) if each column, read in the basis $e$, is an element of $B_{\max} \otimes T$ that is fixed by $\Gamma$. If $\rho$ is crystalline, there is an invertible such $M$ (`New.Period.IsCrystalline.exists_hasInvariantColumns`).

**Definition (Period matrix).** Let $U$ be a square matrix over $B^+$, let $h \geq 0$ and let $v$ be a unit of $A_{\inf}$. Then $U$ is a *period matrix of height $h$ with Frobenius factor $v$* for the chart $c$ if four conditions hold.

1. There is $W$ over $B^+$ with $UW = (E\tau)^h$.
2. There are $F$ and $F'$ over $B^+$ with entries of $F$ in $S_B$, $F'F = 1$ and $\varphi(U) = v\,UF$.
3. For each $g \in G_p$ that fixes the chart, there is $\rho_g$ over $A_{\inf}$ with $\rho_g \cdot g(U) = U$.
4. Let $f : A_{\inf} \to A_{\inf}$ be $S$-linear. If $E^h$ divides $Uy$ for a vector $y$ over $B^+$, then $E^h$ divides $U y'$, where $y'$ is $y$ with the extension of $f$ applied to each coordinate.

Lean: `New.Lift.Chart.IsPeriodMatrix` (Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean).

Here scalars stand for scalar matrices. Condition 1 says that $U$ is invertible after $E\tau$ is inverted. Since $E\tau$ is $\mu$ up to a unit, $U$ is invertible over $B_{\max}$.

**Definition (Period matrix of a lattice).** Let $\rho$, $e$ be as above and $a, b \geq 0$. The triple $(M, U, v)$ is a *period matrix of $\rho$* if $M$ has invariant columns, $E\tau v = \mu$, $U$ is a period matrix of height $a + b$ with Frobenius factor $v^a$, and the image of $U$ in $B_{\max}$ is $(E\tau)^a M$.

Lean: `New.Lift.Chart.IsPeriodMatrixOf` (Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean).

**Theorem (Existence of period matrices).** Let $c$ be a chart of $j : \Gamma \to G_p$. Let $\rho$ be crystalline, let $e$ be a basis of $T$, and let all Hodge-Tate jumps of $\rho$ at the identity embedding lie in $[-a, b]$. Then there are an invertible $M$ over $B_{\max}$, a matrix $U$ over $B^+$ and a unit $v$ of $A_{\inf}$ such that $(M, U, v)$ is a period matrix of $\rho$.

Lean: `New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf` (Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean).

*Proof.* Take $M$ with invariant columns. The jumps in $[-a, b]$ give that $U = (E\tau)^a M$ and $U' = (E\tau)^b M^{-1}$ have entries in $B^+$. Then $UU' = (E\tau)^{a+b}$, which is condition 1. The invariance of the columns of $M$ under $\varphi$ and under $\Gamma$ gives conditions 2 and 3. The elements that fix the chart are in $j(\Gamma)$, because $c$ is a chart of $j$. Condition 4 follows from the description of $S_B$. $\square$

The docstring of the theorem says what it does not do. It supplies a period matrix over $B^+$ for jumps in $[-a, b]$. It does not supply a Frobenius-stable submodule. That is the work of the frame.

**Example (The trivial lattice).** Let $T = \mathbb{Z}_p$ with the trivial action. Then $M = 1$ has invariant columns, and the only jump is $0$. Take $a = b = 0$ and $v = \mu/(E\tau)$. Then $U = 1$ is a period matrix of height $0$: take $W = 1$, $F = F' = 1$, $\rho_g = 1$, and condition 4 is empty. The frame below is $Q = L = Z = Z' = B = 1$.

### The basis of a period matrix

The next step finds a matrix $Q$ over $A_{\inf}$ that spans the solutions of $UY = E^h X$.

**Definition (Period basis).** Let $U$ be square over $B^+$, $Q$ over $A_{\inf}$ and $Z$ over $B^+$. The pair $(Q, Z)$ is a *period basis* of $U$ of height $h$ if five conditions hold.

1. $\det Q \neq 0$.
2. The entries of $Z$ are in $S_B$.
3. $UZ = E^h Q$.
4. Every vector $x$ over $A_{\inf}$ with $Uy = E^h x$ for some $y$ over $S_B$ is $Qs$ for some $s$ over $S$.
5. Let $Uy = E^h x$ with $y$ over $B^+$. Let $\delta \in A_{\inf}$ with $p \nmid \delta$, and let $l$, $g$ be vectors with $lQ = \delta g$. Then $\delta$ divides $l \cdot x$.

Lean: `New.Lift.Chart.IsPeriodBasis` (Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean).

**Proposition.** Every period matrix has a period basis.

Lean: `New.Lift.Chart.IsPeriodMatrix.exists_basis` (Lib/PadicHodge/Kisin/PeriodMatrixBasis.lean).

The proof builds $Q$ and $Z$ from the $S$-module of the solutions $x$ in condition 4 (`exists_spanning_matrix` in the source). It proves condition 5 by approximation modulo powers of $p$ (`dvd_dotProduct_of_spanning`). Condition 4 holds over $S$, not over $A_{\inf}$. Condition 5 is the extra information that the next step needs to pass from $S$ to $A_{\inf}$.

### The key step: $p$ does not divide $\det Q$

Over a field the next result would be trivial. Over $A_{\inf}$ it is the heart of the construction. It uses two lemmas from linear algebra.

**Lemma (A nonzero determinant).** Let $R : S \to D$ be a homomorphism of rings with $D$ nontrivial, and let $X$ be a set of vectors over $S$. Suppose that if $R(t \cdot x) = 0$ for all $x \in X$, then $R(t_i) = 0$ for all $i$. Then some square matrix $N$ with rows in $X$ has $R(\det N) \neq 0$.

Lean: `New.Lift.Chart.exists_det_ne_zero` (Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean).

*Proof.* Among the matrices with $R(\det N) \neq 0$, take one whose set of rows in $X$ is maximal. The identity matrix is a candidate, so such an $N$ exists. Suppose row $k$ is not in $X$. Let $t$ be column $k$ of the adjugate of $N$. For $x \in X$, $t \cdot x$ is the determinant of $N$ with row $k$ replaced by $x$. This matrix has more rows in $X$, so by maximality $R(t \cdot x) = 0$. The hypothesis gives $R(t_i) = 0$ for all $i$, and in particular $R(t_k) = R(\det N) = 0$, a contradiction. $\square$

The second lemma, `New.exists_mulVec_eq_zero_and_forall_comp_eq`, is Artin's argument with vectors of minimal support, over a valuation ring. It lets the source pass from a vector killed by the reduction of $Q$ to a vector fixed by the Galois elements that fix $S$.

**Theorem ($p \nmid \det Q$).** Let $Q$ be a matrix over $A_{\inf}$ such that, for $t$ over $S$, if $p$ divides every entry of $Qt$ then $p$ divides every entry of $t$. Suppose that $QB = \rho\,\varphi(Q)$ for some $\rho$ over $A_{\inf}$ and some $B$ over $S$ with $p \nmid \det B$. Suppose that for each $g \in G_p$ that fixes $S$ pointwise, $Q = \rho_g\,g(Q)$ for some $\rho_g$ over $A_{\inf}$. Then $p$ does not divide $\det Q$.

Lean: `New.Lift.Chart.not_dvd_det_of_frobenius` (Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean).

*Proof.* The source outlines the proof as follows. The hypothesis on $Q$ and $t$ and the first lemma give a matrix $N$ over $S$ with $p \nmid \det N$, whose rows read coordinates of entries of $Qt$ in the chosen basis of $A_{\inf}$ over $S$. Suppose $p \mid \det Q$. Then the reduction of $Q$ modulo $p$, a matrix over $\mathcal{O}_C^\flat$, kills a nonzero vector $a$. Artin's argument and the Galois hypothesis let one take $a$ fixed by the elements that fix $S$. The approximation theorem of the previous section then approximates $a$ from $S$. With the Frobenius relation this forces every component of $\det B \cdot \det N$ to vanish modulo $p$. But $\det B \cdot \det N$ is not $0$ modulo $p$. This is a contradiction. $\square$

The role of $p \nmid \det Q$ is this. Over $A_{\inf}[1/p]$ the matrix $Q$ is invertible after $\tau$ is inverted. With $p \nmid \det Q$, the source shows that $Q$ divides $\tau^h$ over $A_{\inf}$ itself, which is property (a) below.

### The frame

**Theorem (The frame).** Let $U$ be a period matrix of height $h$ with Frobenius factor $v$. Then there are $Q$, $L$ over $A_{\inf}$, $Z$, $Z'$ over $B^+$ and $B$ over $S$ with the following properties.

1. $QL = \tau^h$.
2. The entries of $Z$ are in $S_B$.
3. $UZ = E^h Q$.
4. $Z'Z = E^h$.
5. $\varphi(Q) = v\,QB$.
6. For each $g \in G_p$ that fixes the chart, $g(Z) = ZG$ for some $G$ over $A_{\inf}$.

Lean: `New.Lift.Chart.IsPeriodMatrix.exists_frame` (Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean).

*Proof.* Take the period basis $(Q, Z)$. The Frobenius relation $\varphi(U) = vUF$ and the inverse of $\varphi(E)$ in $S_B$ show that the columns of $v^{-1}\varphi(Q)$ are solutions of $UY = E^h X$ with $Y$ over $S_B$. Condition 4 of a period basis writes them as $QB$ with $B$ over $S$. This is property 5. The relation $UW = (E\tau)^h$ says that the columns of $\tau^h$ are solutions with $Y$ over $B^+$. By the theorem above $p \nmid \det Q$, and condition 5 of a period basis then puts every such solution in the $A_{\inf}$-span of the columns of $Q$. This gives $L$ with $QL = \tau^h$. For property 6, the source writes $U\,g(Z) = E^h Q G = UZG$ and cancels $U$. $\square$

**Remark (Formalization).** The frame is the case of Kisin's theorem that the source uses. The docstring of `New.Lift.Chart.IsPeriodMatrix.exists_frame` says that it "says nothing on finite height". Classically the columns of $Q$ would span a Breuil-Kisin module $\mathfrak{M}$ with $\varphi$-matrix $vB$. Finite $E$-height would say that $vB$ divides $E^h$ over $S$. The source does not state this. Property 5 gives only that $\varphi(Q)$ is in the $S$-span of the columns of $Q$.

**Remark (Formalization).** All the objects of the frame are given by an existence statement. Later results use `choose` or `obtain` on it. No later statement depends on the choice of $Q$: the modules of the next section are defined without it, and the frame only proves facts about them.
