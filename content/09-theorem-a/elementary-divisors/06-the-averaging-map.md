---
title: The averaging map
lean:
  - New/UpperBound/ElementaryDivisors/InvariantAverage.lean
  - New/UpperBound/ElementaryDivisors/AveragingMap.lean
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
decls:
  - New.Average.IsAverage
  - New.Average.exists_isAverage
  - New.FrobeniusCycle.partialAverage
  - New.FrobeniusCycle.partialAverage_empty
  - New.FrobeniusCycle.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies
  - New.FrobeniusCycle.partialAverage_univ_mulVec_mem_defectConditions
  - New.FrobeniusCycle.pow_dvd_pairing_partialAverage_insert_sub
  - New.FrobeniusCycle.exists_average_mem_defectConditions_and_dvd_sub
  - New.FrobeniusCycle.IsEdgeCondition
  - New.FrobeniusCycle.mem_translatesIn_of_pow_smul_mem
  - New.FrobeniusCycle.exists_isEdgeCondition
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The averaging map

Section 5 showed that the forms of the halfway lattices satisfy the defect conditions modulo $w^c$, and that over the residue field few forms satisfy them. The proof of the theorem needs one more object: a map $\mathrm{Av}$ into the defect conditions that is close to multiplication by a fixed power of $p$, when it is paired with the halfway lattices. With it, the image of the Hecke operator can be compared with the whole space. This section builds $\mathrm{Av}$ from an invariant linear form on polynomials in a generic matrix, and packages the result as the edge conditions.

Throughout, $O$ is a valuation domain of characteristic $0$ in which $p$ is not a unit, $N = 2\ell$, $r = a + 1$, $c^* = 3kc$ and $c_0 = k^2fN$ (Section 2).

### An invariant average

Let $L(W) = \mathrm{levi}(W, \tau)$ act on polynomials $\psi$ in the entries of a $k \times k$ matrix $X$ by conjugation, $X \mapsto \iota(a^{-1})X\iota(a)$. Let $\rho \in \mathbb Z^k$ weigh the indices. The row weight of a monomial $\alpha$ in the entries is $\sum_{(i,j)}\alpha(i,j)\rho(i)$. A monomial is bad if its row weight exceeds a threshold $t$.

**Definition (Average).** A linear form $I$ on these polynomials is an average for $(\tau, \iota, \rho, t, c, D)$ if: $I$ is invariant under conjugation by $L(W)$; $I$ vanishes on bad monomials; and for every ideal $J$ and every $\psi$ of total degree at most $D$ such that the bad coefficients of all conjugates of $\psi$ lie in $J$, one has $I(\psi) - c\,\psi(1) \in J$.

Lean: `New.Average.IsAverage` (New/UpperBound/ElementaryDivisors/InvariantAverage.lean).

The evaluation $\psi \mapsto \psi(1)$ is invariant but does not vanish on bad monomials. An average is a correction of $p^{k^2f}$ times the evaluation that removes the bad part and changes nothing modulo $J$ when the bad part is already in $J$.

**Theorem (Averages exist).** Let $W$ be local, $p$ prime and not a unit of $O$, $D < p^f$ and $D + k \le |k_W|$. For all $\rho$ and $t$ there is an average for $(\tau, \iota, \rho, t, p^{k^2f}, D)$.

Lean: `New.Average.exists_isAverage` (New/UpperBound/ElementaryDivisors/InvariantAverage.lean).

*Proof (main steps).* By Section 3 there are weights $\eta(\gamma)$ with $\mathrm{multinomial}(\gamma)\,\eta(\gamma) = p^{k^2f}$ in degree below $p^f$, for which the substitutions by a matrix and by its transpose are adjoint (`New.Average.exists_isAdjointWeight`). With them a polynomial $\psi$ of degree $d$ gives an element $\psi^\sharp$ of the Schur algebra of degree $d$, acting on $U = (O^k)^{\otimes d}$ (`New.Average.dualOperator`). Its trace on $U$ is the scaled value $p^{k^2f}\psi(1)$, and conjugation of $\psi$ becomes conjugation of $\psi^\sharp$. Let $U_+$ be the submodule generated under the Schur algebra by the basis tensors of row weight above $t$ (`New.Average.largeWeightSubmodule`); $\psi^\sharp$ keeps it. When $d + k \le |k_W|$ the points of $L(W)$ span the Schur algebra (`New.Average.eq_top_of_schurMap_eq_leviMonomialValues`), so $U_+$ is spanned by the images of these tensors under the matrices $\iota(a)^{\otimes d}$. Put $I_d(\psi) = \mathrm{tr}_U(\psi^\sharp) - \mathrm{tr}_{U_+}(\psi^\sharp)$, the trace on the quotient, and $I = \sum_{d \le D}I_d$. It is invariant. A bad monomial maps $U$ into $U_+$, so its two traces agree and $I$ vanishes on it. Finally $I(\psi) - p^{k^2f}\psi(1) = -\sum_d\mathrm{tr}_{U_+}(\psi^\sharp)$. By the spanning, this trace is computed from the bad coefficients of the conjugates of $\psi$, so it lies in $J$ when they do (`New.Average.largeWeightTrace_mem`). $\square$

The source cites Green (Polynomial Representations of $\mathrm{GL}_n$, Lecture Notes in Mathematics 830, 1980) for the Schur algebra, and Benson and Doty (Schur-Weyl duality over finite fields, 2009) for the spanning by finite points.

**Remark (Formalization).** The average is chosen, and only its properties are used. The bound $D < p^f$ keeps $\eta$ away from its junk value $0$ (Section 3), so the scaled trace is $p^{k^2f}\psi(1)$ in every degree used.

### Construction of the averaging map

Substitute $N$ generic matrices, one copy for each letter, in a form $h$, with the Frobenius twists of the twisted action (`New.FrobeniusCycle.substitutionOperator`). The result is a polynomial in the $N$ copies whose value at the identity in all copies is $h$.

**Definition (Partial average).** For linear forms $I_j$ and a set $J$ of copies, $\mathrm{Av}_J$ is the matrix obtained by applying $I_j$ in the copies $j \in J$ and $p^{c_0}$ times the evaluation at $1$ in the other copies. Then $\mathrm{Av}_\emptyset = p^{Nc_0}\cdot 1$.

Lean: `New.FrobeniusCycle.partialAverage` (New/UpperBound/ElementaryDivisors/AveragingMap.lean).

Lean: `New.FrobeniusCycle.partialAverage_empty` (New/UpperBound/ElementaryDivisors/AveragingMap.lean).

The bad monomials of the copy $j$ are those of row weight above $2c^*P^\ell$ for the vector $\rho = \mathrm{rootVector}(a, r)$, whose row weight is the degree in the row $r$ minus the degree in the row $a$. The key estimate links this weight in one copy to the defect at one letter.

**Lemma (Weight and defect).** Let $N n k(\ell + 2) \le P^\ell$ and $\ell \le N$, and let all $l_i$ be invariant under the Levi group of the blocks $r$, $k - r$. Apply the $l_i$ in all copies but the $j$-th to the translate by $g$ of $h$, and let the coefficient of $\alpha$ in the entry $\beta$ not be divisible by $w^c$. If the defect of $\beta$ at $j + \ell$ is above $3c^*$, then the row weight of $\alpha$ is above $2c^*P^\ell$. If the row weight is above $2c^*P^\ell$, then the defect is above $c^*$.

Lean: `New.FrobeniusCycle.lt_weight_and_lt_defect_of_not_dvd_coeff_contractOtherCopies` (New/UpperBound/ElementaryDivisors/AveragingMap.lean).

*Proof (main steps).* An invariant form kills the monomials whose row and column weights differ, since the diagonal torus acts on them by a nontrivial character of finite order. So the copies $i \ne j$ add nothing to the weight. For the copy $j$ the source computes the degrees of the substituted monomials: the row weight divided by $P^\ell$ is within $c^*$ of the defect at $j + \ell$ (`New.FrobeniusCycle.abs_weight_div_sub_defect_le`). The bound $Nnk(\ell+2) \le P^\ell$ controls the error terms. Both implications follow from $|x - y| \le c^*$. $\square$

**Theorem (Averaging map).** Let $r = a + 1$, $\ell + \ell = N$ and $Nk(\ell + 2)n + n + k < P^\ell$. Let $(b, b')$ be an edge pairing. For every $c$ there is a matrix $\mathrm{Av}$ with:

1. for all $h$, $\mathrm{Av}\,h \in \mathrm{defectConditions}(n, a, r, (w^c), 3c^*)$;
2. for all $h$ and all $h' \in \mathrm{allEdgesForms}(k, n, r)$, $w^c$ divides $h'\cdot(b \ast \mathrm{Av}\,h) - p^{Nc_0}\,h'\cdot(b \ast h)$.

Lean: `New.FrobeniusCycle.exists_average_mem_defectConditions_and_dvd_sub` (New/UpperBound/ElementaryDivisors/AveragingMap.lean). The two steps of the proof are `New.FrobeniusCycle.partialAverage_univ_mulVec_mem_defectConditions` and `New.FrobeniusCycle.pow_dvd_pairing_partialAverage_insert_sub` (same file).

*Proof.* Put $D = Nnk(\ell+2)P^\ell$. Then $D + k < D + P^\ell = (Nk(\ell+2)n + 1)P^\ell \le P^{2\ell} = P^N = q$, so $D + k \le |k_W|$ and $D < p^{fN}$. For each copy $j$ choose an average $I_j$ for the Levi group of $\mathrm{twoBlock}(k, r)$, the embedding $\iota_j$, $\rho = \mathrm{rootVector}(a, r)$, $t = 2c^*P^\ell$, the constant $p^{k^2fN} = p^{c_0}$ and the degree $D$. Let $\mathrm{Av} = \mathrm{Av}_{\mathrm{all}}$.

(1) Let $g$ be block diagonal and $\beta$ of defect above $3c^*$ at the letter $i = j + \ell$. The entry $\beta$ of $\rho(g)\mathrm{Av}\,h$ is $I_j$ applied to the polynomial that remains in the copy $j$ after the other averages, by invariance of all $I_i$ (`New.FrobeniusCycle.partialAverage_univ_mulVec_mem_defectConditions`). Modulo $w^c$ this polynomial has only monomials of row weight above $2c^*P^\ell$, by the first half of the lemma. $I_j$ kills them. So the entry is divisible by $w^c$.

(2) For $j \notin J$, $w^c$ divides the change of the pairing from $\mathrm{Av}_J$ to $\mathrm{Av}_{J \cup\{j\}}$ (`New.FrobeniusCycle.pow_dvd_pairing_partialAverage_insert_sub`). Indeed the change is $(I_j - p^{c_0}\mathrm{ev}_1)(\psi)$ for the pairing $\psi$ of $h'$ with the polynomials left in the copy $j$, and $\psi$ has degree at most $D$. By the property of averages it suffices that the bad coefficients of the conjugates of $\psi$ are divisible by $w^c$. Such a coefficient is a sum of terms: a coefficient of the remaining polynomial times the pairing of $h'$ with $\rho(g^{-1})e_\beta$. If the first factor is not divisible by $w^c$, the second half of the lemma gives defect above $c^*$, and the edge pairing corollary of Section 5 makes the pairing divisible by $w^c$. Now add the changes along the chain $\emptyset \subset \{j_1\} \subset \dots$ of all copies, starting from $\mathrm{Av}_\emptyset = p^{Nc_0}$. $\square$

### The edge conditions

**Definition (Edge condition).** For $r$, $c$, $\theta$ and weights $b$, a triple $(C, S, \mathrm{Av})$ is an edge condition if: $C$ is a submodule of $O^{\mathrm{Exp}}$ that contains $\mathrm{allEdgesForms}(k, n, r)$ and all multiples $w^c h$; $\mathrm{Av}\,h \in C$ for all $h$; $w^c$ divides $h'\cdot(b\ast\mathrm{Av}\,h) - p^{Nc_0}h'\cdot(b\ast h)$ for $h' \in \mathrm{allEdgesForms}$; $S$ is a subspace over the residue field $k_O$ that contains the reduction of every $h$ with $w^{c-1}h \in C$; and $[\mathrm{GL}_k(W) : P_r]\dim S \le (1 + \theta)|\mathrm{Exp}|$.

Lean: `New.FrobeniusCycle.IsEdgeCondition` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

**Lemma (Lowering the precision).** Let $0 < c$ and let $J$ be an ideal with $w \in J$. If $w^{c-1}h$ lies in $\mathrm{translatesIn}(\tau, (w^c), B)$, then $h$ lies in $\mathrm{translatesIn}(\tau, J, B)$.

Lean: `New.FrobeniusCycle.mem_translatesIn_of_pow_smul_mem` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* For $g$ in the Levi group and $\beta \in B$, $w^{c-1}\cdot w = w^c$ divides $w^{c-1}(\rho(g)h)_\beta$. Cancel $w^{c-1} \ne 0$ in the domain $O$: $w \mid (\rho(g)h)_\beta$, so it lies in $J$. $\square$

**Theorem (Edge conditions exist).** Let $p$ not be a unit of $O$, let the size conditions hold for $(k, n, r, \theta)$, and let $(b, b')$ be an edge pairing. With $c = 5Nc_0$ there is an edge condition $(C, S, \mathrm{Av})$ for $(r, c, \theta, b)$.

Lean: `New.FrobeniusCycle.exists_isEdgeCondition` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Since $c_0 \ge 1$ and $N \ge 2$, $c > 0$. Write $r = a + 1$. Take $C = \mathrm{defectConditions}(n, a, r, (w^c), 3c^*)$ over $O$ and $S = \mathrm{defectConditions}(n, a, r, 0, 3c^*)$ for the cycle reduced to $k_O$, which has characteristic $p$ (`New.FrobeniusCycle.charP_residueField`). The forms of $\mathrm{allEdgesForms}$ lie in $C$ by Section 5, and $w^ch \in C$ trivially. $\mathrm{Av}$ is the averaging map; its hypothesis $Nk(\ell+2)n + n + k < P^\ell$ is part 3 of the sizes lemma. If $w^{c-1}h \in C$, then by the last lemma with $J = \mathfrak m_O$, which contains $w$ (`New.FrobeniusCycle.sqrtPrime_mem_maximalIdeal`), the reduction of $h$ lies in $S$. For the dimension apply the theorem on few forms of bounded defect (Section 5) with $t = c^* \ge 3k \ge 2(k+1)$, $n > 1$, $\theta \le 1$ and part 5 of the sizes lemma. Its right side is $(1+\theta)|\mathrm{Mon}_k(n)|^N = (1+\theta)|\mathrm{Exp}|$. $\square$
