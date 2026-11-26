---
title: The block datum is sharp
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
  - New/UpperBound/Objects/AuxiliaryPair.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
  - Lib/SiegelWeil/RallisInner/Doubling.lean
  - Lib/General/LinearAlgebra/BlockEmbeddings.lean
decls:
  - New.card_isUnit_submatrix
  - New.DescentPair.residueBlockDatum
  - New.DescentPair.blockFn
  - New.DescentPair.blockDatum_eq_vacuumDatum
  - New.star_mulChar_det_mul_self
  - New.DescentPair.bijective_map_levelResidueAt
  - New.DescentPair.blockFn_normSq
  - New.SiegelWeil.IsSharpFn
  - New.SiegelWeil.IsSharp
  - New.SiegelWeil.IsSharpFn.isSharp
  - New.DescentPair.exists_reductionGL_eq_submatrix_of_blockFn_ne_zero
  - New.DescentPair.isSharpFn_blockFn
  - New.DescentPair.blockMass
  - New.DescentPair.isSharp_blockDatum
  - New.DescentPair.gramFactor
  - New.DescentPair.stdLevelIndex_mul_blockMass
  - New.DescentPair.twistFactor
  - New.DescentPair.chosenFactor
  - New.DescentPair.chosenFactor_ne_zero
  - New.DescentPair.stdLevelIndex_levelGroup_mul_card
  - New.DescentPair.gramFactor_div_card
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The block datum is sharp

Rallis' formula of Volume 6 applies to a finite datum that is sharp for a level $J$. This section proves that the block datum $\Psi_{\mathrm{bl}}$ of a descent pair is sharp for $J_M$, and it computes the mass of the datum. The mass then splits into a factor of the chosen places $M$ and the twist factor $c_Q$ of the places of the twist. Section 5 uses the two results.

All work in this section is finite. The block datum is a function on $n \times r$ matrices modulo $\pi_M Q$. By the Chinese remainder theorem, such a matrix is a family of matrices over the residue fields $k_w$ for $w \in M \sqcup Q$. Every statement reduces to a count over these fields.

Fix a descent pair $O$ with $W$ of rank $r$, $V = I_n$ and $n = r + t$. Write $\iota : r \hookrightarrow n$ for its inclusion of indices and $\psi_w$ for the tame part of its character $\mu$ at $w \in Q$.

### Counting matrices with an invertible block

**Lemma.** Let $R$ be a finite commutative ring and let $\iota : r \hookrightarrow n$ be an embedding of finite index sets. The number of $n \times r$ matrices over $R$ whose square block on the rows $\iota$ is invertible is

$$|\mathrm{GL}_r(R)|\cdot|R|^{(n - r)r}.$$

Lean: `New.card_isUnit_submatrix` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Split the rows of $n$ into the image of $\iota$ and its complement. The complement has $n - r$ elements. This gives a bijection from $n \times r$ matrices to pairs $(X', Y)$, with $X'$ an $r \times r$ matrix and $Y$ an $(n - r) \times r$ matrix. The condition is that $X'$ is a unit. There are $|\mathrm{GL}_r(R)|$ choices for $X'$ and $|R|^{(n-r)r}$ choices for $Y$. $\square$

### The block datum on matrices

**Definition (The residue block datum).** For a family $X = (X_w)$ of $n \times r$ matrices over the residue fields $k_w$, $w \in M \sqcup Q$, let

$$\Psi_{\mathrm{res}}(X) = \begin{cases}\prod_{w \in Q}\psi_w(\det X_w^\iota) & \text{if } X_w = I_\iota \text{ for every } w \in M,\\ 0 & \text{otherwise.}\end{cases}$$

Here $I_\iota$ is the inclusion matrix of $\iota$, with $1$ in the entries $(\iota(i), i)$ and $0$ elsewhere, and $X_w^\iota$ is the $r \times r$ block of $X_w$ on the rows $\iota$.

Lean: `New.DescentPair.residueBlockDatum` (New/UpperBound/Objects/AuxiliaryPair.lean).

**Definition (The block function).** The block function $\Psi_{\mathrm{bl}}$ on $n \times r$ matrices $x$ modulo $\pi_M Q$ is $\Psi_{\mathrm{res}}$ of the family of reductions $x_w$ of $x$ at the places $w \in M \sqcup Q$.

Lean: `New.DescentPair.blockFn` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma.** The block datum of the pair is the datum $\Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ of the block function: it is $\Psi_{\mathrm{bl}}$ at the places of $\pi_M Q$ and the vacuum at all other finite places.

Lean: `New.DescentPair.blockDatum_eq_vacuumDatum` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Both data are built over the places of the modulus $\pi_M Q$. Both functions factor through the reductions at these places, and there they agree with $\Psi_{\mathrm{res}}$. $\square$

The general datum $\Psi \otimes \mathrm{vac}$ of a function $\Psi$ on matrices modulo a modulus $\mathfrak m$ is `New.vacuumDatum` of Volume 6. The lemma lets this chapter use the results of Volume 6 for such data.

### The squared norm

Two small facts enter the count.

**Lemma.** Let $\chi$ be a complex multiplicative character of a finite field $F$, and let $X$ be a square matrix over $F$. Then $\overline{\chi(\det X)}\,\chi(\det X)$ is $1$ if $X$ is invertible and $0$ if it is not.

Lean: `New.star_mulChar_det_mul_self` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The conjugate of $\chi$ is $\chi^{-1}$, so the product is $(\chi^{-1}\chi)(\det X) = \mathbf 1(\det X)$. The trivial multiplicative character is $1$ on units and $0$ on non units. The matrix $X$ is invertible exactly when $\det X$ is a unit. $\square$

**Lemma (Chinese remainder theorem for matrices).** The map that sends an $n \times r$ matrix modulo $\pi_M Q$ to the family of its reductions at the places $w \in M \sqcup Q$ is a bijection onto $\prod_w \mathrm{Mat}_{n \times r}(k_w)$.

Lean: `New.DescentPair.bijective_map_levelResidueAt` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The map is injective, because a matrix modulo $\pi_M Q$ is determined by its reductions at the distinct primes that divide the modulus. The two sides have the same number of elements. An injective map between finite sets of the same size is bijective. $\square$

**Theorem (The norm of the block function).** Let $\mathsf G_Q = \prod_{w \in Q}\mathrm{GL}_r(k_w)$. Then

$$\sum_x |\Psi_{\mathrm{bl}}(x)|^2 = |\mathsf G_Q|\cdot\Bigl(\prod_{w \in Q} q_w\Bigr)^{tr},$$

where the sum runs over the $n \times r$ matrices $x$ modulo $\pi_M Q$.

Lean: `New.DescentPair.blockFn_normSq` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* For each place $w \in M \sqcup Q$ define a function $\mathrm{ind}_w$ on $\mathrm{Mat}_{n \times r}(k_w)$. For $w \in M$ it is the indicator of $I_\iota$. For $w \in Q$ it is the indicator of the matrices whose block on the rows $\iota$ is invertible.

1. For every $x$, $|\Psi_{\mathrm{bl}}(x)|^2 = \prod_w \mathrm{ind}_w(x_w)$. If $x_w \neq I_\iota$ at some $w \in M$, both sides are $0$. In the other case the factors at $M$ are $1$, and at $w \in Q$ the lemma on characters gives $|\psi_w(\det x_w^\iota)|^2 = \mathrm{ind}_w(x_w)$.
2. By the Chinese remainder theorem, the sum over $x$ is a sum over families $(X_w)$. The sum of a product of functions of separate variables is the product of the sums. So the sum is $\prod_w \sum_X \mathrm{ind}_w(X)$.
3. For $w \in M$ the sum is $1$. For $w \in Q$ the sum is the number of matrices with an invertible block. By the counting lemma with $R = k_w$, this number is $|\mathrm{GL}_r(k_w)|\,q_w^{tr}$.
4. The product over $Q$ is $|\mathsf G_Q|\,(\prod_Q q_w)^{tr}$. $\square$

**Example.** Take $r = 1$, $n = 2$, so $t = 1$. Let $M$ have one place and let $Q$ have one place $w$ with $q_w = 3$. At the place of $M$ only the matrix $I_\iota$ counts. At $w$ a $2 \times 1$ matrix over $\mathbb F_3$ counts when its entry on the row $\iota$ is not $0$. There are $2$ choices for this entry and $3$ for the other entry. So the sum is $6 = |\mathrm{GL}_1(\mathbb F_3)|\cdot 3^{1}$, as the theorem says.

### Sharp data in Volume 6

The next two definitions and the theorem come from [the Rallis inner product formula](/chapter/rallis-inner-product/). This chapter uses them as stated there.

Let $S$ be a hermitian space of rank $r$ and $T$ a hermitian space of rank $n$. Write $K_0$ for the integral points of the finite adelic group $U(S)(\mathbb{A}_f)$. For a modulus $\mathfrak m$ write $J(\mathfrak m)$ for the integral points that reduce to $1$ modulo $\mathfrak m$. For a subgroup $J$ write $[K_0 : J]$ for the index of $J \cap K_0$ in $K_0$.

**Definition (Sharp function).** Let $b$ be a character and $J$ a subgroup with $J(\mathfrak m) \leq J \leq K_0$. A function $\Psi \neq 0$ on $n \times r$ matrices modulo $\mathfrak m$ is sharp for $J$ if two conditions hold.

1. The group $J$ fixes the datum $\Psi \otimes \mathrm{vac}$ under the Weil representation with the characters $1$ and $b$.
2. There is a fixed $r \times n$ matrix $A$ such that for every $x$ with $\Psi(x) \neq 0$, the matrix $Ax$ is the reduction modulo $\mathfrak m$ of a point of $J$.

Lean: `New.SiegelWeil.IsSharpFn` (Lib/SiegelWeil/RallisInner/SharpData.lean).

**Definition (Sharp datum).** A finite datum $F$ is sharp for $J$ off a set of places $S_0$, with mass $c$, if the following hold.

1. $\langle F, F\rangle \neq 0$, and $F$ lies in the span of the finite translates of the vacuum.
2. For every vector $v$ of the Fock model, $v \otimes F$ is the vacuum at every set of places disjoint from $S_0$, and it is clean.
3. For every finite point $g$ that is integral off $S_0$, the matrix coefficient $\langle F, \omega(g)F\rangle$ is $\langle F, F\rangle$ if $g \in J \cap K_0$ and $0$ otherwise.
4. $c = \langle F, F\rangle / [K_0 : J]$.

Lean: `New.SiegelWeil.IsSharp` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Theorem (Sharp functions give sharp data).** Let $\Psi$ be sharp for $J$ relative to $b$. Suppose that all signs of $S$ agree or that $\mathfrak m \neq (1)$. Then $\Psi \otimes \mathrm{vac}$ is sharp for $J$ off the places of $\mathfrak m$ and their conjugates, with mass

$$c = \frac{\sum_x |\Psi(x)|^2}{|\mathrm{Mat}_{n \times r}(\mathcal O/\mathfrak m)|\cdot[K_0 : J]}.$$

Lean: `New.SiegelWeil.IsSharpFn.isSharp` (Lib/SiegelWeil/RallisInner/SharpData.lean).

Source: the formula for the matrix coefficient of a datum that is an indicator function modulo $\mathfrak m$ is the local computation in J.-S. Li, Crelle 428 (1992), for the vacuum and its translates. See also the discussion in Volume 6.

The idea of the proof is this. On $J$ the datum is fixed, so the coefficient is $\langle F, F\rangle$. If the coefficient at $g$ is not $0$, then some $x$ and $xg$ both lie in the support of $\Psi$. The second condition then makes $g$ integral at the places of $\mathfrak m$, and so in $K_0$, and then in $J$. The norm $\langle F, F\rangle$ is the mean of $|\Psi|^2$.

**Remark (Formalization).** Lean's `IsSharp` has two fields that a textbook would not list. The field `vacuum_off` says that $v \otimes F$ is the vacuum off $S_0$, and the field `clean` is a technical condition (`New.SiegelWeil.IsClean`) that the proof of Rallis' formula needs for the unfolding of the doubling integral. The hypothesis "all signs agree or $\mathfrak m \neq (1)$" serves only for `clean`. The mass is divided by `New.stdLevelIndex`, the index of $J \cap K_0$ in $K_0$. This index is finite and not $0$ here, so the division is not a junk value. The mass is never $0$ (`New.SiegelWeil.IsSharp.mass_ne_zero`).

### The block function is sharp

**Lemma.** Let $x$ be an $n \times r$ matrix modulo $\pi_M Q$ with $\Psi_{\mathrm{bl}}(x) \neq 0$. Then there is an integral point $k$ of $U(W)(\mathbb{A}_f)$ in $J_M$ whose reduction modulo $\pi_M Q$ is the block $x^\iota$ of $x$ on the rows $\iota$.

Lean: `New.DescentPair.exists_reductionGL_eq_submatrix_of_blockFn_ne_zero` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Let $B_w$ be the block on the rows $\iota$ of the reduction $x_w$.

1. At $w \in M$, $x_w = I_\iota$ because $\Psi_{\mathrm{bl}}(x) \neq 0$. The block of $I_\iota$ on the rows $\iota$ is $I_\iota^{\mathsf T} I_\iota = 1$. So $B_w = 1$.
2. At $w \in Q$, the factor $\psi_w(\det B_w)$ is not $0$. A multiplicative character is $0$ only on non units, so $\det B_w$ is a unit and $B_w$ is invertible.
3. The family $(B_w)$ is a family of invertible matrices over the residue fields. By `New.exists_reduceFamily_eq` it is the family of reductions of one integral point $k$ of $U(W)(\mathbb{A}_f)$.
4. The reductions of $k$ at $M$ are $1$, so $k \in J_M$. The reductions at all places of $\pi_M Q$ agree with those of $x^\iota$. So the reduction of $k$ modulo $\pi_M Q$ is $x^\iota$. $\square$

**Theorem.** The block function $\Psi_{\mathrm{bl}}$ is sharp for $J_M$ modulo $\pi_M Q$, relative to the character $\nu_V$, with the matrix $A = I_\iota^{\mathsf T}$.

Lean: `New.DescentPair.isSharpFn_blockFn` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* There are five conditions.

1. $J(\pi_M Q) \leq J_M$. A point that reduces to $1$ at every place of $\pi_M Q$ reduces to $1$ at every place of $M$.
2. $J_M \leq K_0$. The group $J_M$ is defined as a subgroup of the integral points.
3. $\Psi_{\mathrm{bl}} \neq 0$. Its squared norm $|\mathsf G_Q|\,(\prod_Q q_w)^{tr}$ is not $0$.
4. $J_M$ fixes $\Psi_{\mathrm{bl}} \otimes \mathrm{vac}$. Volume 9 proves the transformation law of the block datum under pairs $(k, k')$ of integral points. For $k \in J_M$ and $k' = 1$, the scalar of the law is a product of characters at the reductions of $k$ at $M$, which are $1$. So the scalar is $1$.
5. For $x$ with $\Psi_{\mathrm{bl}}(x) \neq 0$, $I_\iota^{\mathsf T}x = x^\iota$, and the lemma above gives $k \in J_M$ with reduction $x^\iota$. $\square$

**Definition (The mass of the block datum).** Let $\mathsf G_M = \prod_{w \in M}\mathrm{GL}_r(k_w)$. The mass of the block datum is

$$c_\Psi = \frac{|\mathsf G_Q|\,(\prod_Q q_w)^{tr}}{|\mathrm{Mat}_{n \times r}(\mathcal O/\pi_M Q)|\cdot|\mathsf G_M|}.$$

Lean: `New.DescentPair.blockMass` (New/Determinant/Norms/AdjointThetaLift.lean).

**Theorem (The block datum is sharp).** Suppose that all signs of $W$ agree or that $\pi_M Q$ has a place. Then the block datum is sharp for $J_M$ relative to $\nu_V$, off the places of $\pi_M Q$ and their conjugates, with mass $c_\Psi$.

Lean: `New.DescentPair.isSharp_blockDatum` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Apply the theorem of Volume 6 to the sharp function $\Psi_{\mathrm{bl}}$. Its mass is the squared norm of $\Psi_{\mathrm{bl}}$, divided by the number of matrices and by $[K_0 : J_M]$. The index $[K_0 : J_M]$ is the order of the kernel quotient $K_0 / J_M \cong \mathsf G_M$, that is $|\mathsf G_M|$. Insert the value of the squared norm. $\square$

In the $j$-th pair of the data, the chosen places are never empty (`New.Data.nonempty_modulus_places`). So the second case of the hypothesis holds, and Section 5 uses the theorem in that form.

### The constant of the Gram form

The Gram form of a lift has the factor $[K_0^V : K]\cdot c_\Psi$, where $K$ is the level of the pair on $V$. The class sum on $V$ brings the index $[K_0^V : K]$, and Rallis' formula brings the mass $c_\Psi$. The rest of this section computes this product.

**Definition (The Gram factor).** The Gram factor of the pair is

$$g_O = \frac{[K_0^V : K]\cdot|\mathsf G_Q|\cdot(\prod_Q q_w)^{tr}}{|\mathsf G_M|}.$$

Lean: `New.DescentPair.gramFactor` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma.** $[K_0^V : K]\cdot c_\Psi = g_O / |\mathrm{Mat}_{n \times r}(\mathcal O/\pi_M Q)|$.

Lean: `New.DescentPair.stdLevelIndex_mul_blockMass` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Insert the definitions and rearrange the quotient. $\square$

Write $f(q) = \prod_{i = t+1}^{t+r}(1 - q^{-i})$. This is the proportion of the $n \times r$ matrices over $\mathbb F_q$ that have rank $r$. Indeed, the number of such matrices is

$$\prod_{i=0}^{r-1}(q^n - q^i) = q^{nr}\prod_{i=0}^{r-1}(1 - q^{i-n}) = q^{nr}\,f(q),$$

since $i - n$ runs from $-n$ to $-(t+1)$.

**Definition (The twist factor and the chosen factor).** The twist factor of the pair is

$$c_Q = \Bigl(\prod_{w \in Q} q_w\Bigr)^{rt}\prod_{w \in Q} f(q_w).$$

The chosen factor of the pair is

$$c_M = \prod_{w \in M}\frac{f(q_w)}{|\mathrm{GL}_r(k_w)|}.$$

Lean: `New.DescentPair.twistFactor` (New/Determinant/Norms/AdjointThetaLift.lean), `New.DescentPair.chosenFactor` (New/Determinant/Norms/AdjointThetaLift.lean).

**Lemma.** The chosen factor is not $0$.

Lean: `New.DescentPair.chosenFactor_ne_zero` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Each $q_w$ is at least $2$. For $i \geq 1$, $q_w^i \neq 1$, so $1 - q_w^{-i} \neq 0$. The order of $\mathrm{GL}_r(k_w)$ is positive. $\square$

**Remark (Formalization).** The twist factor $c_Q$ is also never $0$, by the same argument. The source does not state this for `New.DescentPair.twistFactor`, and this chapter does not need it. The constant `New.Rows.twistFactor` of [the second comparison operator](/chapter/comparison-operator-2/) is a different number. Its proof of being nonzero (`New.Rows.twistFactor_ne_zero`) does not apply here.

**Lemma (The index of the level).** The product $[K_0^V : K]\cdot|\mathsf G_Q|$ is the product over all $w \in M \sqcup Q$ of the index in $\mathrm{GL}_n(k_w)$ of the stabilizer of the $r$ basis vectors $e_{\iota(1)}, \dots, e_{\iota(r)}$.

Lean: `New.DescentPair.stdLevelIndex_levelGroup_mul_card` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The level $K$ is the preimage in $K_0^V$ of a product of local groups. At $w \in M$ the local group is the stabilizer of the $r$ vectors. At $w \in Q$ it is a parabolic subgroup, the group of matrices that preserve the span of the other basis vectors. So $[K_0^V : K]$ is the product of the local indices. At $w \in Q$, the index of the parabolic times $|\mathrm{GL}_r(k_w)|$ is the index of the stabilizer (`New.index_rangeParabolic_mul_card_GL`). $\square$

**Theorem (The Gram factor splits).** The Gram factor divided by the number of $n \times r$ matrices modulo $\pi_M Q$ is $c_M\,c_Q$:

$$\frac{g_O}{|\mathrm{Mat}_{n \times r}(\mathcal O/\pi_M Q)|} = c_M\,c_Q.$$

Lean: `New.DescentPair.gramFactor_div_card` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The group $\mathrm{GL}_n(k_w)$ acts transitively on the $n \times r$ matrices of rank $r$. The stabilizer of $I_\iota$ is the stabilizer of the $r$ vectors. So the index of this stabilizer is the number of matrices of rank $r$, that is $q_w^{nr}f(q_w)$ (`New.cast_index_stabilizer_inclMatrix`).

1. By the lemma on the index, $[K_0^V : K]\cdot|\mathsf G_Q| = \prod_{w \in M \sqcup Q} q_w^{nr}f(q_w)$.
2. By the Chinese remainder theorem, the number of matrices modulo $\pi_M Q$ is $\prod_{w \in M \sqcup Q} q_w^{nr}$.
3. So the quotient is $\prod_{w \in M \sqcup Q} f(q_w)\cdot(\prod_Q q_w)^{tr}/|\mathsf G_M|$.
4. Split the product over $M \sqcup Q$. The part at $M$ with the factor $1/|\mathsf G_M|$ is $c_M$. The part at $Q$ with $(\prod_Q q_w)^{tr}$ is $c_Q$. $\square$

The factor $c_M$ depends only on the chosen places and the ranks $r$ and $t$. In the $j$-th pair these do not depend on the twist $\vartheta$. All dependence on $\vartheta$ is in $c_Q$. Section 5 uses this split to make the constant of the norm independent of $\vartheta$.
