---
title: The norm of the chain
lean:
  - New/Determinant/Chain/TriangleNorms.lean
  - New/Determinant/Chain/ChainNorms.lean
  - New/Determinant/Chain/NormOfChain.lean
decls:
  - New.card_parabolic_blockNumber_succ
  - New.Data.exists_stdLevelIndex_lastLevel_eq
  - New.Data.inner_lowerChainAtLevel
  - New.Data.lowerChainAtLevel_injective
  - New.Data.exists_inner_weightedChain_eq
  - New.Data.exists_inner_chain_eq
  - New.Data.isRamifiedRatio_of_mem_sigma
  - New.Data.card_sigma_Ioc_le
  - New.Data.HasAbsUpToNormPower.exists_norm_div_eq_mul_prod_quotientRatio
  - New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The norm of the chain

This section compares the chain $\iota_\vartheta$ with the weighted chain of row $0$ of the triangle of Section 4. The two differ by the index of the level $J_\vartheta$ and by a dimension. Then the Gram theorem of Section 2 gives the Gram form of $\iota_\vartheta$, and the theorem on the norm of the chain follows.

### Counting block triangular groups

Let $N$ and $T$ be finite sets and $R$ a finite commutative ring. Let $P_j(R)$ be the group of invertible block upper triangular matrices with one diagonal block indexed by $N$ and $j$ diagonal blocks indexed by $T$. Its index set is $\mathrm{BI}_{j+1} = \mathrm{BI}_j \sqcup T$, with $\mathrm{BI}_0 = N$.

**Lemma (One more block).** $\#P_{j+1}(R) = \#P_j(R)\cdot\#\mathrm{Mat}_{\mathrm{BI}_j \times T}(R)\cdot\#\mathrm{GL}_T(R)$.

Lean: `New.card_parabolic_blockNumber_succ` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Write $g \in P_{j+1}(R)$ in blocks for $\mathrm{BI}_j \sqcup T$. The block number of $T$ is the largest, so $g$ is block triangular exactly when its upper left block $A$ is in the block triangular form for $j$ and its lower left block is $0$. Then $g = \begin{pmatrix} A & B \\ 0 & D\end{pmatrix}$, and $g$ is invertible exactly when $A$ and $D$ are invertible. So $g \mapsto (A, B, D)$ is a bijection onto $P_j(R) \times \mathrm{Mat}_{\mathrm{BI}_j\times T}(R) \times \mathrm{GL}_T(R)$. $\square$

By induction on $j$, the lemma gives the order of $P_j(R)$. For each $j$ there is $k_j \in \mathbb{N}$ such that for every finite commutative ring $R$
$$\#P_j(R) = \#\mathrm{GL}_N(R)\,(\#\mathrm{GL}_T(R))^j\,(\#R)^{k_j}.$$
For $j = 0$ there is one block, so $P_0(R) = \mathrm{GL}_N(R)$ and $k_0 = 0$. For the step, $\#\mathrm{Mat}_{\mathrm{BI}_j\times T}(R) = (\#R)^{\#\mathrm{BI}_j\cdot\#T}$, so the lemma gives $k_{j+1} = k_j + \#\mathrm{BI}_j\cdot\#T$. This number does not depend on $R$. In the source this is the lemma `exists_card_parabolic_blockNumber_eq` of namespace `New` ([TriangleNorms, line 101](lean:New/Determinant/Chain/TriangleNorms.lean#L101)). Its declaration has an explicit universe `.{u}`, and the name index of the handbook does not read such names. So the text gives it no statement of its own.

### The index of the last level

Let $N_n(\vartheta)$ be the weight of column $n$ of row $0$ (`triangleGLCard false ϑ n`). It is the product of $\#\mathrm{GL}_{\mathrm{BI}_n}(k_w)$ over the chosen places and the places $w \in Q$. Let $g(\vartheta)$ be the Gram factor of the first descent pair ([the Gram factor splits](/chapter/single-theta-lifts/#the-block-datum-is-sharp)). Let $K_0$ be the group of integral points on $Y_m$.

**Lemma (Index of the last level).** There are $C \in \mathbb{C}$ and $k \in \mathbb{Z}$ such that for every $m$-fold twist $\vartheta$
$$[K_0 : J_\vartheta] = C\,(\mathrm{Nm}\,Q)^k\,g(\vartheta)^m\,\frac{N_m(\vartheta)}{N_0(\vartheta)\,N_1(\vartheta)^m}.$$

Lean: `New.Data.exists_stdLevelIndex_lastLevel_eq` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* The index $[K_0 : J_\vartheta]$ is a product of local indices. At a chosen place it is $\#\mathrm{GL}_{Y_m}(k_w)$. At $w \in Q$ it is the index of $P_m(k_w)$ in $\mathrm{GL}_{\mathrm{BI}_m}(k_w)$. The weights $N_n$ and $g$ are products of the same kind. By Lagrange's theorem and the previous lemma, at $w \in Q$
$$[\mathrm{GL}_{\mathrm{BI}_n} : P_n]\cdot\#\mathrm{GL}_N(k_w)\,\#\mathrm{GL}_T(k_w)^n\,q_w^{k_n} = \#\mathrm{GL}_{\mathrm{BI}_n}(k_w).$$
This is the order of $P_n(k_w)$ above. Use it for $n = 1$ and $n = m$. At $w \in Q$ the Gram factor contains the index of the stabilizer of the first block, which is the index of $P_1$ (`New.Data.index_rangeParabolic_inl_eq`). After these substitutions the orders $\#\mathrm{GL}_N(k_w)$ and $\#\mathrm{GL}_T(k_w)$ cancel, and at $w \in Q$ there remains $q_w^k$ with $k = (k_1 - t\,\#N)\,m - k_m$. The factors at the chosen places do not depend on $\vartheta$. The trivial twist has no places in $Q$. So the value at $\vartheta = 1$ fixes them: $C = N_0(1)\,(N_1(1)/g(1))^m$. Each $N_n(\vartheta)$ is the order of a finite group, so no denominator is $0$. $\square$

### The chain and the weighted chain

Let $u = X_{0,m}$ be the weighted chain of row $0$, with the weights $N_n(\vartheta)$. Let $\#W$ be the dimension of the weight on $Y_m$ (`WeylIndex`).

**Lemma (The chain is a weighted chain).** For an $m$-fold twist $\vartheta$ and forms $x, y$ of level $J_M$ on $Y_0$,
$$\langle\iota_\vartheta x, \iota_\vartheta y\rangle = [K_0 : J_\vartheta]\cdot\#W\cdot\langle u\,x, u\,y\rangle.$$

Lean: `New.Data.inner_lowerChainAtLevel` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* The inner product of algebraic forms on the definite space $Y_m$ is a sum over the classes of the level. It is $[K_0 : J_\vartheta]\cdot\#W$ times the Petersson product of the functions ([the lift and its adjoint](/chapter/single-theta-lifts/#the-lift-and-its-adjoint)). The function of $\iota_\vartheta v$ is $u\,v$: each lift of $\iota_\vartheta$ carries as weight the index of a principal level, and this index is $N_n(\vartheta)$. $\square$

**Lemma (The chain is injective).** For every $m$-fold twist $\vartheta$, $\iota_\vartheta$ is injective.

Lean: `New.Data.lowerChainAtLevel_injective` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Let $\iota_\vartheta y = 0$. The previous lemma with $x = y$ gives $[K_0 : J_\vartheta]\,\#W\,\|u\,y\|^2 = 0$. The index and $\#W$ are not $0$. So $u\,y = 0$. The lifts form a triangle (Section 5), and chains of a triangle are injective (Section 2). So $y = 0$. $\square$

### The Gram form

**Lemma (Gram form of the weighted chain).** Let $\mathrm{mc}(\vartheta) = \#\mathrm{Mat}_{Y_1\times N}(O/\mathfrak{m}_\vartheta)$, with $\mathfrak{m}_\vartheta$ the product of the chosen places and the places of $Q$. There is $\kappa$ with absolute value $\prod_{0<i<j\leq m}\rho_{ij}$ up to a norm power such that for target forms $x, y$
$$\langle u\,x, u\,y\rangle = \kappa(\vartheta)\,\frac{N_0 N_1^m}{N_m}\,\mathrm{mc}(\vartheta)^{-m}\,\langle x, R(\vartheta)\,y\rangle.$$

Lean: `New.Data.exists_inner_weightedChain_eq` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Put $S_{\vartheta,i} = \mathrm{mc}(\vartheta)^{-1}R_{i+1,\vartheta^{i+1}}$ on $T$. The theorem on the norm of the first lift (Section 4) gives constants $C_i$ and a series. By Rallis' formula on the good forms ([the Rallis operator](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift)) the same series converges to $\langle x, R_{i+1,\vartheta^{i+1}}\,y\rangle$. Limits are unique. So for $i < m$
$$N_0\,\langle a_i\,x, a_i\,y\rangle = C_i\,\langle x, S_{\vartheta,i}\,y\rangle.$$
A constant has absolute value $1$ up to a norm power (Section 3, rules). The lifts form a triangle with the square moduli $\rho_{i+1,i+n+2}$ (Section 5). So the Gram theorem of Section 2 applies with $i = 0$ and $n = m$. It gives $\kappa$ and the formula with $S_{\vartheta,0}\cdots S_{\vartheta,m-1}$. This product is $\mathrm{mc}(\vartheta)^{-m}R(\vartheta)$, because scalars move out of a product. $\square$

**Theorem (Gram form of the chain).** There is $c$ with absolute value $\prod_{0<i<j\leq m}\rho_{ij}$ up to a norm power such that for every $m$-fold twist $\vartheta$ and target forms $x, y$
$$\langle\Theta_\vartheta x, \Theta_\vartheta y\rangle = c(\vartheta)\,c_Q^m\,\langle x, R(\vartheta)\,y\rangle.$$

Lean: `New.Data.exists_inner_chain_eq` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Combine the two lemmas above with the index lemma. The orders $N_0 N_1^m/N_m$ cancel, and there remains
$$\langle\Theta_\vartheta x, \Theta_\vartheta y\rangle = \#W\,C\,(\mathrm{Nm}\,Q)^k\,\kappa(\vartheta)\,\Big(\frac{g(\vartheta)}{\mathrm{mc}(\vartheta)}\Big)^m\langle x, R(\vartheta)\,y\rangle.$$
By [the Gram factor splits](/chapter/single-theta-lifts/#the-block-datum-is-sharp), $g(\vartheta)/\mathrm{mc}(\vartheta) = c_M\,c_Q$, and $c_M$ does not depend on $\vartheta$. Put $c = \kappa\cdot\#W\,C\,c_M^m\,(\mathrm{Nm}\,Q)^k$. The factor after $\kappa$ has absolute value $1$ up to a norm power, and the relation is multiplicative (Section 3, rules). $\square$

### The scalar

**Lemma (The pairs give ramified ratios).** For $0 < i < j \leq m$, $\rho_{ij}$ is a ramified ratio.

Lean: `New.Data.isRamifiedRatio_of_mem_sigma` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* This is the proposition on quotient ratios of Section 3. $\square$

**Lemma (Number of pairs).** There are at most $m \cdot m$ pairs $0 < i < j \leq m$.

Lean: `New.Data.card_sigma_Ioc_le` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* For each of the $m$ values of $i$ there are at most $m$ values of $j$. $\square$

So the product $\prod_{0<i<j\leq m}\rho_{ij}$ is nonnegative, and it is $1$ at $\vartheta = 1$, since each factor is a ramified ratio (Section 3).

**Lemma (Division by the trivial twist).** Let $c$ have absolute value $\prod_{0<i<j\leq m}\rho_{ij}$ up to a norm power, and let $c(1) \neq 0$. Then there is $e \in \mathbb{Z}$ with $|c(\vartheta)/c(1)| = (\mathrm{Nm}\,Q)^{e/2}\prod_{0<i<j\leq m}\rho_{ij}(\vartheta)$ for every $\vartheta$.

Lean: `New.Data.HasAbsUpToNormPower.exists_norm_div_eq_mul_prod_quotientRatio` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Apply the proposition on division by the trivial twist (Section 3). Its hypotheses $f \geq 0$ and $f(1) = 1$ are the two facts above. $\square$

### Proof of the theorem on the norm of the chain

**Theorem (Norm of the chain).** This is the theorem of Section 1: there are $C > 0$, $e$ and $c$ with $|c(\vartheta)| = C\,(\mathrm{Nm}\,Q)^{e/2}\prod_{0<i<j\leq m}\rho_{ij}(\vartheta)$ and $\Theta_\vartheta^*\Theta_\vartheta = c(\vartheta)\,c_Q^m\,R(\vartheta)$.

Lean: `New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* Take $c$ from the theorem on the Gram form. Case $c(1) = 0$. The chain $\Theta_1$ is injective, because $\iota_1$ is injective. For a target form $y$, $\|\Theta_1 y\|^2 = c(1)\,c_Q^m\,\langle y, R(1)\,y\rangle = 0$. So $\Theta_1 y = 0$ and $y = 0$. Then $T = 0$, and every endomorphism of $T$ is $0$. Take $C = 1$, $e = 0$ and $c(\vartheta) = \prod\rho_{ij}(\vartheta)$. The product is nonnegative, so $|c(\vartheta)|$ is the product. Both sides of the operator identity are $0$.

Case $c(1) \neq 0$. The previous lemma gives $e$. Put $C = |c(1)| > 0$. Then $|c(\vartheta)| = C\,|c(\vartheta)/c(1)| = C\,(\mathrm{Nm}\,Q)^{e/2}\prod\rho_{ij}(\vartheta)$. For target forms $x, y$,
$$\langle x, \Theta_\vartheta^*\Theta_\vartheta\,y\rangle = \langle\Theta_\vartheta x, \Theta_\vartheta y\rangle = \langle x, c(\vartheta)\,c_Q^m\,R(\vartheta)\,y\rangle.$$
Two endomorphisms with the same inner products against every $x$ are equal. $\square$

**Remark (Formalization).** The constants $C_i$ of the first lifts come from `choose!`. They are not computed, and the relation "absolute value up to a norm power" allows $C = 0$. So the proof cannot show $c(1) \neq 0$ from the formula. It treats the case $c(1) = 0$ apart, with junk values $C = 1$, $e = 0$ (finding F-071). The case is empty when $T \neq 0$, by injectivity. The proof of the comparison lemma uses `erw`, because the space of the last node of the triangle is $Y_m$ only after unfolding.

### Example: one lift

Let $m = 1$. Then $u = X_{0,1} = N_0\,a_{0,0}$ is one weighted arrow. There are no squares, so $\kappa = C_0$ up to the factor $N_0$. The index lemma gives $[K_0 : J_\vartheta] = C\,(\mathrm{Nm}\,Q)^k\,g/N_0$. So $\langle\Theta_\vartheta x, \Theta_\vartheta y\rangle$ is a constant times $(\mathrm{Nm}\,Q)^k\,c_Q\,\langle x, R_{1,\vartheta}\,y\rangle$. The product over pairs is empty, so $|c(\vartheta)|$ is $C(\mathrm{Nm}\,Q)^{e/2}$. This is the operator identity of one lift in [the operator identity](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift), up to the index.
