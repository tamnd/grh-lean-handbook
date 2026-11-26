---
title: The last path
lean:
  - New/Determinant/AuxiliaryForms/LastPath.lean
decls:
  - New.Exchange.diagramWeight_eq_add_succ
  - New.Exchange.diagramWeight_eq_zero_of_le_succ
  - New.Exchange.add_diagramWeight_mem_Icc_of_interlace
  - New.Exchange.boxes_le_boxes_of_interlace
  - New.Exchange.exists_add_eq_of_interlace
  - New.Exchange.norm_dotProduct_mulVec_le_of_isDualPairing
  - New.Exchange.IsBranchingPairing
  - New.Exchange.exists_isBranchingPairing
  - New.Exchange.le_div_two_add_of_paramsCorrespond
  - New.Data.LastPathIndex
  - New.Data.exists_isLiftWeight_isHCParam
  - New.Data.lastPathColumns
  - New.Data.lastPathDetExp
  - New.Data.isLiftWeight_lastPathColumns
  - New.Data.gridWeight_eq_lastPathDetExp
  - New.Data.isHCParam_lastPathColumns
  - New.Data.LastPathVector
  - New.Data.LastPathForm
  - New.Data.LastPathFiniteDatum
  - New.Data.lastPathBranching
  - New.Data.isBranchingPairing_lastPathBranching
  - New.Data.lastPathPairing
  - New.Data.exists_lastPathBranching_equivariant
  - New.Data.norm_dotProduct_lastPathBranching_mulVec_le
  - New.Data.exists_integral_eq_lastPathPairing
  - New.Data.isStd_gridSpace_last
  - New.Data.lastPathToAlgForm
  - New.Data.card_lastPathIndex_le
  - New.Data.natAbs_lastPathDetExp_le
  - New.Data.boxes_lastPathColumns_le_natB_mul
  - New.Data.lastPathLevel
  - New.Data.lastPathLevel_le_principalLevel
  - New.Data.gridChar_hasWeight_lastPathDetExp
  - New.Data.lastPathKernel
  - New.Data.lastPathBlockPoint
  - New.Data.FixedByOuterLevels
  - New.Data.lastPathEdgeDatum
  - New.Data.lastPathChain
  - New.Data.lastPathPeriod
  - New.Data.edges_last
  - New.Data.edgeCharProd_last
  - New.Data.lastPathKernel_omega_lastPathEdgeDatum
  - New.Data.IsPathDatum.sum_lastPathPairing_omega_invariant
  - New.Data.lastPathPairing_lastPathChain_mem_smoothInvariants
  - New.Data.IsPathDatum.sum_lastPathPairing_mul_level
  - New.Data.exists_lastPathPeriod_mem_smul_norm_le
  - New.Data.exists_gridPathMap_eq_ofAlgForm_smul_lastPathChain
  - New.Data.isProportional_lastPathPeriod
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The last path

The last path is the row $b = m$ in both grids. Its half $z$ runs through the nodes $(z, j, m)$ for $j \leq m$, that is $Y^j_m$ for $z$ false and $\tilde Y^m_j$ for $z$ true. All of these spaces are positive definite. So the forms are algebraic, the lifts are definite lifts, and the period on $\tilde Y^m_m$ is a definite branching. All results are in [LastPath.lean](lean:New/Determinant/AuxiliaryForms/LastPath.lean).

```text
  half false:  Y_m = Y^0_m -> Y^1_m -> ... -> Y^m_m
  half true:   Ỹ^m_0 -> Ỹ^m_1 -> ... -> Ỹ^m_m
  period:      Y^m_m  inside  Ỹ^m_m = Y^m_m ⊕ E ẽ
```

We use the definite lifts of [definite lifts and the Galois law](/chapter/theta-lifts-seesaw/#definite-lifts-and-the-galois-law), the branching matrices of [branching and duality](/chapter/weyl-modules/#branching-and-duality), and the plain sums over classes of [a chain of lifts as a plain sum](/chapter/chain-valuation/#a-chain-of-lifts-as-a-plain-sum).

### Interlacing and the branching pairing

For column multiplicities $\kappa$ in rank $N$, row $i$ of the diagram is $\lambda_i = \sum_{i < h < N} \kappa(h)$. Columns of height $N$ go into the determinant. So $\lambda_i = \kappa(i+1) + \lambda_{i+1}$ if $i + 1 < N$, and $\lambda_i = 0$ if $N \leq i + 1$.

Lean: `New.Exchange.diagramWeight_eq_add_succ`, `New.Exchange.diagramWeight_eq_zero_of_le_succ` (New/Determinant/AuxiliaryForms/LastPath.lean).

**Lemma (Interlacing).** Let $(\kappa, e)$ be a weight of $\mathrm{GL}_{N+1}$ with doubled parameter $l'$ and $(\kappa_0, e_0)$ a weight of $\mathrm{GL}_N$ with doubled parameter $l$. Suppose that for every place $w$ and every $x \in \mathbb{Z}$ the count $\#\{j : x < l'_{w,j}\} - \#\{i : x < l_{w,i}\}$ is $0$ or $1$. Then for $q < N$ the highest weights interlace: $e(w) + \lambda_{q+1} \leq e_0(w) + \lambda^0_q \leq e(w) + \lambda_q$. Hence $\kappa_0$ has at most as many boxes as $\kappa$, and there are $\gamma, \kappa_1$ with $\gamma + \kappa_1 = \kappa$, $\kappa_0(q) = \kappa_1(q) + \gamma(q+1)$ for $0 < q < N$, and $e_0 = e + \kappa_1(N)$.

Lean: `New.Exchange.add_diagramWeight_mem_Icc_of_interlace`, `New.Exchange.boxes_le_boxes_of_interlace`, `New.Exchange.exists_add_eq_of_interlace` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* Entry $q$ of the highest weight is entry $q$ of $l$, in decreasing order, shifted by the half sum of positive roots of the rank. Take the indices at position $q$ of $l$ and at positions $q$, $q+1$ of $l'$. The count condition at values near entry $q$ of $l$ puts it between the two entries of $l'$, and the shifts of the two ranks differ by one half. Sum the interlacing over $q$ for the boxes. For the strip, put $\gamma(q) = $ the number of columns of height $q$ in $\kappa$ that lose their bottom box; interlacing says exactly that the differences $\lambda_q - \lambda^0_q$ and $\lambda^0_q - \lambda_{q+1}$ are sums of these numbers. The columns of height $N + 1$ that keep their box become columns of height $N$, which are a power of the determinant. $\square$

**Lemma (Cauchy-Schwarz).** If the integer matrix $A$ is a duality pairing between two Weyl modules for the parameter $l$, then $|v'^{T} A v| \leq \|v'\|\,\|v\|$ in the Gram norms.

Lean: `New.Exchange.norm_dotProduct_mulVec_le_of_isDualPairing` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* Pairing with $v$ is the Gram form against a vector $x$ with $\|x\| = \|v\|$. Apply Cauchy-Schwarz for the positive definite Gram matrix. $\square$

**Definition.** An integer matrix $B$ is a *branching pairing* between $(\kappa', e')$ on $\mathrm{GL}_n$ and $(\kappa, e)$ on $\mathrm{GL}_{n+1}$ if three things hold. (1) There are $N(\tau)$ with $|N(\tau)| \leq |\kappa| + |e(\tau)|$ such that moving $v'$ by $g$ and $v$ by $\mathrm{diag}(g, u)$ multiplies $v'^{T} B v$ by $\prod_\tau \det \tau(u)^{N(\tau)}$, over every commutative star ring. (2) If $|\kappa| \leq M$, then $|v'^{T} B v| \leq (M^M)^3 \|v'\|\,\|v\|$. (3) For every real point $g$ there is $c$ such that, for every standard space $V$, algebraic forms $\eta, \varphi$, finite point $u$ of the line and level $K$,
$$\int_{[V]} \eta^\sharp(x)\, \varphi^\sharp(\mathrm{diag}(x, 1, u)\, g)\, dx = \frac{c}{[K_0 : K]} \int_{G_f / G(E)} \eta(h)^{T} B\, \varphi(\mathrm{diag}(h, u))\, dh.$$

Lean: `New.Exchange.IsBranchingPairing` (New/Determinant/AuxiliaryForms/LastPath.lean).

**Theorem (Branching pairing).** If all signs are $1$ and the parameters $l$, $l'$ interlace as above, a branching pairing exists.

Lean: `New.Exchange.exists_isBranchingPairing` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* The gap of $l$ gives a weight $(\kappa_0, e_0)$ with parameter $l$ (`exists_isHCParam_of_hasGap`, Section 2). The interlacing lemma gives the boxes bound and the strip. The strip gives a branching matrix $b$ from $\mathrm{GL}_{n+1}$ to $\mathrm{GL}_n$: it is equivariant for $\mathrm{diag}(g, u)$ up to a power of $u$, of norm at most $(M^M)^3$, and the branching has multiplicity one. A duality matrix $A$ pairs $(\kappa_0, e_0)$ with $(\kappa', e')$. Put $B = Ab$. Then (1) holds with $N(\tau)$ the first row of $\gamma$ plus $e(\tau)$, and this row is at most $|\kappa|$. (2) follows from Cauchy-Schwarz and the norm of $b$. For (3), the real integral is over a compact group; by multiplicity one it is a multiple of the pairing, and the rest is the integral formula for algebraic forms. $\square$

**Lemma.** If the parameters of definite groups of ranks $n < n'$ correspond under a theta lift with exponents $\gamma, \gamma'$, then $\gamma'(w) \leq \lfloor l_{w,i}/2 \rfloor + \lfloor n/2 \rfloor$ for every entry.

Lean: `New.Exchange.le_div_two_add_of_paramsCorrespond` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* Every shifted entry $l_{w,i} - 2\gamma'(w) + n'$ lies outside the block of $n' - n$ numbers centred at $0$, so it exceeds $n' - n$ in absolute value; solve. $\square$

### Weights, levels and kernels

**Theorem (Weights on the last path).** For each half $z$ there are $\kappa$ and $e_i$ such that the weight $(\kappa, e_i)$ lifts from $(z, i, m)$ to $(z, i+1, m)$ along the character of the edge, the character at the lower end has weight $e_{i+1}$, and for $i \leq m$ the weight $(\kappa, e_i)$ has the doubled parameter $-\mathrm{gridParam}_{z,0,i,m}$.

Lean: `New.Data.exists_isLiftWeight_isHCParam` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* Prescribe $\mathrm{gap} - t - z$ columns of each height $|Y^j|$ for $j \geq 1$. The previous lemma gives the hypothesis of `exists_isHCParam_of_le`, which fits $\kappa$ to the parameter at $j = 0$. Put $e_j = \mathrm{gridWeight}_j + \kappa(|Y^j|)$. Across an edge the parameters correspond, and they correspond exactly when the second is the parameter of the lifted weight. Induct on $j$. $\square$

The choices are `lastPathColumns` and `lastPathDetExp`, with their three properties. The value spaces, the forms and the finite data of the edges are `LastPathVector`, `LastPathForm` and `LastPathFiniteDatum`; the node index is `LastPathIndex`. Forms at the outer ends become algebraic by `lastPathToAlgForm`.

Lean: `New.Data.lastPathColumns`, `New.Data.lastPathDetExp`, `New.Data.isLiftWeight_lastPathColumns`, `New.Data.gridWeight_eq_lastPathDetExp`, `New.Data.isHCParam_lastPathColumns`, `New.Data.LastPathVector`, `New.Data.LastPathForm`, `New.Data.LastPathFiniteDatum`, `New.Data.LastPathIndex`, `New.Data.isStd_gridSpace_last`, `New.Data.lastPathToAlgForm` (New/Determinant/AuxiliaryForms/LastPath.lean).

The parameters at $(\mathrm{false}, m, m)$ and $(\mathrm{true}, m, m)$ interlace. This gives `lastPathBranching` and the form `lastPathPairing`.

Lean: `New.Data.lastPathBranching`, `New.Data.isBranchingPairing_lastPathBranching`, `New.Data.lastPathPairing`, `New.Data.exists_lastPathBranching_equivariant`, `New.Data.norm_dotProduct_lastPathBranching_mulVec_le`, `New.Data.exists_integral_eq_lastPathPairing` (New/Determinant/AuxiliaryForms/LastPath.lean).

**Lemma (Bounds).** For $j \leq m$: the rank is at most $2n_m$, $|e_j(\tau)| \leq \lceil 20b \rceil$, and $|\kappa| \leq b_0 r^4$.

Lean: `New.Data.card_lastPathIndex_le`, `New.Data.natAbs_lastPathDetExp_le`, `New.Data.boxes_lastPathColumns_le_natB_mul` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* The entries of the grid parameters are at most $\lceil 20 b\rceil$. Apply the two bounds of Section 2 and compare the constants of the data. $\square$

The level at $(z, j, m)$ is $J(\mathfrak{m})$ on $Y_m$ and $J(\mathfrak{b})$ elsewhere; every one lies in $J(\mathfrak{b})$. The kernel of an edge is the theta kernel of the two characters, with derivatives scaled by `jetScale`. The block point of $h$ is $\mathrm{diag}(h, \epsilon^m)$, with the flip scalar $\epsilon$ of $\mathfrak{m}$. The edge datum is a power of `vacuumScale` times the vacuum at the matrix $S(\text{edge})$. The chain lifts the outer form along $j$ edges. Then
$$\Xi(\Psi; y) = \sum_{S} \Psi(S) \int_{G_f/G(E)} \big\langle \mathrm{chain}_{\mathrm{false}}(y_0)(h),\ \mathrm{chain}_{\mathrm{true}}(y_1)(\mathrm{diag}(h, \epsilon^m)) \big\rangle\, dh,$$
over the tuples $S$ on the edges of the last path, with the integral over the level at $(\mathrm{false}, m, m)$.

Lean: `New.Data.lastPathLevel`, `New.Data.lastPathLevel_le_principalLevel`, `New.Data.gridChar_hasWeight_lastPathDetExp`, `New.Data.lastPathKernel`, `New.Data.lastPathBlockPoint`, `New.Data.FixedByOuterLevels`, `New.Data.lastPathEdgeDatum`, `New.Data.lastPathChain`, `New.Data.lastPathPeriod` (New/Determinant/AuxiliaryForms/LastPath.lean).

### The finite sum and the proportionality

The edges of the last path are the row edges at $b = m$, and the edge character product splits over them. If the integral points $u, u'$ reduce to $g$ at the two ends of an edge, the Weil action takes the datum of the moved tuple to that of $S$ times the edge character. A path datum is invariant under admissible families up to these characters. So the sum $\sum_S \Psi(S) \langle \beta(\cdot), \beta'(\cdot)\rangle$ does not change if all data move by a family $a$ of level elements with $a_{\mathrm{true},m} = \mathrm{diag}(a_{\mathrm{false},m}, 1)$. The integrand of $\Xi$ is smooth and left invariant, and the sum is right invariant under the level at $Y^m_m$.

Lean: `New.Data.edges_last`, `New.Data.edgeCharProd_last`, `New.Data.lastPathKernel_omega_lastPathEdgeDatum`, `New.Data.IsPathDatum.sum_lastPathPairing_omega_invariant`, `New.Data.lastPathPairing_lastPathChain_mem_smoothInvariants`, `New.Data.IsPathDatum.sum_lastPathPairing_mul_level` (New/Determinant/AuxiliaryForms/LastPath.lean).

**Theorem (Shape of $\Xi$).** Let $\Psi$ be a path datum with values sums of at most $N$ roots of unity, and let $y$ have the outer levels. Let $\sigma : \mathbb{C} \to F$ be a ring map to a normed field, and let a property of vectors hold at the outer forms and be kept by the kernels. If $\|\sigma(M a)\| \leq R$ for every pairing $a$ of such vectors at $h$ and $\mathrm{diag}(h, \epsilon^m)$, then $\Xi$ is a sum of $L \prod_{z} \prod_{j} |G_f / K_{z,j}\, G(E)|$ numbers $a$ with $\|\sigma(M a)\| \leq R$, over $j < m + [z = \mathrm{false}]$, for some $L \leq N \cdot \mathrm{edgeMatrixCountBound}^{2m}$.

Lean: `New.Data.exists_lastPathPeriod_mem_smul_norm_le` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* All levels lie in $J(\mathfrak{b})$, which is free, so the class groups have trivial automorphisms. By the invariance, the integral and both chains are plain sums over classes. Each term is a sum over $S$ of $\Psi(S)$ times a pairing of reached vectors. A root of unity has $\|\sigma(\zeta)\| = 1$, and $0$ is in the set since $R \geq 0$. The tuples number at most $\mathrm{edgeMatrixCountBound}^{2m}$. $\square$

**Theorem (Proportionality).** For every family $\Psi$ and real point $g$ there is $\beta$ with $I(\Psi_\vartheta; g)(y, \varphi) = \beta\, \Xi(\Psi_\vartheta; y, \varphi) / |\mathrm{GL}_{n_m}(\mathcal{O}/\mathfrak{m}_0)|$ for all $\vartheta$. Here $n_m$ is the rank of $Y_m$. In the notation of [path data and periods](/chapter/seesaw-squares/#path-data-and-periods): $\Psi \propto \Xi / |\mathrm{GL}|$ on the last path.

Lean: `New.Data.exists_gridPathMap_eq_ofAlgForm_smul_lastPathChain`, `New.Data.isProportional_lastPathPeriod` (New/Determinant/AuxiliaryForms/LastPath.lean).

*Proof.* By induction on $j$, the lift of $F$ along $j$ edges is $c \cdot [K_0 : K_{z,j}]/[K_0 : K_{z,0}]$ times the algebraic chain, read by $\sharp$: each definite lift is a constant over the index at its lower end times the algebraic lift (`exists_lift_ofAlgForm_eq_smul`). Insert both chains into the period at $(m, m)$ and apply property (3). The index at $Y^m_m$ cancels, and the indices in the grid of $\tilde Y$ do not depend on $\vartheta$. The index at $Y_m$ is $\kappa' \cdot |\mathrm{GL}|$ with a constant $\kappa' \neq 0$. $\square$

**Remark (Formalization).** `lastPathColumns`, `lastPathDetExp` and `lastPathBranching` come from `choose`. The constants $c$ of property (3) and $\beta$ of the proportionality come from existence statements and may be $0$; then the theorem says nothing about the period.
