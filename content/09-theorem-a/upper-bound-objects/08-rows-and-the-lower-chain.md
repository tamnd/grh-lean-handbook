---
title: Rows and the lower chain
lean:
  - New/UpperBound/Objects/Rows.lean
  - New/UpperBound/Objects/RowChain.lean
  - New/UpperBound/Objects/CharactersAtLevel.lean
decls:
  - New.Data.principalForms
  - New.Data.paramsCorrespond_descentPair
  - New.Data.liftY
  - New.Data.lastLevel
  - New.Data.lowerChain
  - New.Data.lowerChain_mem_levelSpace
  - New.Data.lowerChain_principalRep
  - New.Data.spaceChar_rankTwist
  - New.Data.tensorChainLift_eq_zero_of_ramified
  - New.Data.doubleLiftChain_eq_zero_of_ramified
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Rows and the lower chain

This section builds the second chain. The lower chain starts at the target forms on $Y_0$ and lifts them $m$ times to $Y_m$. Its spaces are indefinite until the last one. The section also proves two facts about the characters of the upper chain at the primes above $N$, which the composite lift needs.

### The spaces Y_j and W_j

For $j < m$, the space $Y_j$ is [chosen](/decl/New.Data.spaceY/) so that its Gram matrix is the identity on $X_j$ and antidiagonal on a string of $2\varrho + 1 - j$ further vectors, with entries $1$ except $-N$ at the middle vector. Its lattice basis is a graded basis times an integral matrix that is $1$ at every chosen place. For $j \ge m$ the space is standard. The space $W_j$ is diagonal of rank $r$, with signs that have $m - j$ minus signs.

### Forms and descent pairs

**Definition (Principal forms).** For a space $V$ of rank $r$, the principal forms are the forms on $V$ of the doubled parameter $2\varsigma$ that are fixed by the level of elements that reduce to $1$ at the chosen places.

Lean: `New.Data.principalForms` (New/UpperBound/Objects/Rows.lean).

The group $\bar G$ of Section 2 acts on principal forms through integral lifts. The [good forms](/decl/New.Data.goodForms/) are the image of $e_0$, and the [target forms](/decl/New.Data.targetForms/) are the good forms on $Y_0$. Theorem A bounds their dimension.

The $j$-th [descent pair](/decl/New.Data.descentPair/) has $W = W_j$, $V = I_{r+t}$, the character $\chi_j\vartheta^j$ of weight $-w_j$, and the level places of $\vartheta$.

**Lemma.** For $1 \le j \le m$, the doubled parameter $2\varsigma$ on $W_j$ and the doubled parameter of $V_j$ correspond under the block rule, with weights $m - j$ and $\lfloor (r+t)/2 \rfloor - w_j(\tau)$.

Lean: `New.Data.paramsCorrespond_descentPair` (New/UpperBound/Objects/Rows.lean).

*Proof.* At each place $\tau$, with $a$ the number of plus signs of $W_j$, the doubled parameter of $V_j$ is $\varsigma_\tau + w$ in the first $a$ positions, then a block $\lfloor t/2 \rfloor - i$ for $i < t$, then $\varsigma_\tau + w$ again, with $w = w_j(\tau)$, plus the constant $r - 2a$. So it is $2\varsigma_\tau$ with one block inserted at the centre $-w$. The grid centres of Section 4 are separated, and the size conditions give the gap $500(2r + t)^3 \le \Delta - t - 2$. The block rule for an inserted block, from [local theta in the Fock model](/chapter/local-theta/), then holds for the weights $\lfloor r/2 \rfloor - w$ and $\lfloor (r+t)/2 \rfloor - w$. The rule is applied to the parameter of $V_j$ less $2u$, with $u = m - j + w - \lfloor r/2 \rfloor$. A shift of the first weight by $u$ restores the parameter of $V_j$, and the first weight becomes $m - j$, the number of minus signs of $W_j$. $\square$

### The lower chain

**Definition (Lift along the rows).** Lift $j + 1$ from $Y_j$ to $Y_{j+1}$ is the theta lift with the datum $\varphi_\infty \otimes \Upsilon$: the chosen joint harmonic at infinity and a point datum at the finite places. It is multiplied by the index of the level of $Y_j$ in the standard level.

Lean: `New.Data.liftY` (New/UpperBound/Objects/RowChain.lean).

**Definition (The last level).** The level $J_m$ on $Y_m$ is the set of elements of the standard level that are $1$ modulo the chosen places and block upper triangular modulo each place of $Q$.

Lean: `New.Data.lastLevel` (New/UpperBound/Objects/RowChain.lean).

**Definition (Lower chain).** The lower chain $\iota_\vartheta$ is the composite of the $m$ lifts along the rows, from principal forms on $Y_0$ to forms on $Y_m$, read as algebraic forms of weight $\lambda^\circ$.

Lean: `New.Data.lowerChain` (New/UpperBound/Objects/RowChain.lean).

**Proposition.** For a principal form $y$ on $Y_0$, the form $\iota_\vartheta(y)$ lies in the space of level $J_m$ with the character $k \mapsto \prod_w \prod_{l < m} \psi_{l,w}(\det k_w^{(l+1)})$. Here $w$ runs over the level places, $k_w^{(l+1)}$ is the diagonal block $l + 1$ of $k$ modulo $w$, and $\psi_l$ is the tame character of lift $l + 1$.

Lean: `New.Data.lowerChain_mem_levelSpace` (New/UpperBound/Objects/RowChain.lean).

*Proof.* Each lift is equivariant for the levels of its two spaces, up to the tame character of the lift on the determinant of the new block. Induction on $j$ gives, for $k$ block upper triangular at each level place, $k \cdot \iota_\vartheta(y) = c\, \iota_\vartheta(s y)$, with $s$ the first block at the chosen places and $c$ the product of characters. For $k \in J_m$ the first block is $1$, so $s y = y$. $\square$

**Lemma.** For $s \in \bar G$ and a principal form $y$, $\iota_\vartheta(s y)$ is the right translate of $\iota_\vartheta(y)$ by a chosen element of the standard level on $Y_m$ that reduces to $\mathrm{diag}(s, 1)$ at the chosen places and to $1$ at $Q$.

Lean: `New.Data.lowerChain_principalRep` (New/UpperBound/Objects/RowChain.lean).

*Proof.* Apply the induction of the previous proof to $g = \mathrm{diag}(s, 1)$. Its diagonal blocks after the first are $1$, so every character factor is $1$. $\square$

### Characters of the upper chain at the level

The characters of the lifts of the upper chain are unramified above $N$, because the tame part of $\vartheta$ lives on $Q$, prime to $N$.

**Lemma.** The rank twist by $X_j$ of the chain character $\nu$, read as a Hecke character in rank $n_j$, is the base change $x \mapsto \nu(x/\bar x)$.

Lean: `New.Data.spaceChar_rankTwist` (New/UpperBound/Objects/CharactersAtLevel.lean).

*Proof.* The rank $n_j$ is even (Section 1), and for even rank the rank twist followed by the space character is the base change. $\square$

The next results use three objects from [the gain of short columns](/chapter/short-columns-gain/). Their file comes later in the order of the volume. CharactersAtLevel.lean reaches it through its import of MarkedPrimes.lean, the file of [the chain valuation](/chapter/chain-valuation/). The order is so because those chapters use the lower chain and the composite lift of this one. The three objects are stated here once.

**Definition (Scaling).** For a prime $w \mid \pi$, a scaling at $w$ is an integral idele of norm one that is $1$ at every place other than $w$ and $\bar w$.

Lean: `New.Data.IsScalingAt` (New/UpperBound/Size/ShortColumns.lean).

**Definition (Chosen scaling).** The chosen scaling $z_w$ is a scaling at $w$, taken by choice, whose component at $w$ has order $N - 1$ modulo $w$.

Lean: `New.Data.scalingGenerator` (New/UpperBound/Size/ShortColumns.lean).

**Definition (Ramified source forms).** A source form $\varphi$ is ramified if, for every $w \mid \pi$, $\sum_{0 \le i < N - 1} z_w^i \cdot \varphi = 0$.

Lean: `New.Data.ramifiedSourceForms` (New/UpperBound/Size/ShortColumns.lean).

**Theorem.** Let $w \mid \pi$, let $t$ be a tensor of data of the first $m'$ lifts, and let $j < m'$. Suppose $\omega(1, z_w)$, acting on factor $j$ alone, fixes $t$. Then the chain of lifts with data $t$ vanishes on every ramified source form.

Lean: `New.Data.tensorChainLift_eq_zero_of_ramified` (New/UpperBound/Objects/CharactersAtLevel.lean).

*Proof.* A ramified form is $\psi - z_w \psi$ for a source form $\psi$: the operator $z_w$ has order dividing $N - 1$ on source forms, and the kernel of $\sum_i z_w^i$ is the image of $1 - z_w$, as $N - 1$ is invertible in $\mathbb{C}$. Each lift commutes with the scaling: the character of the lift is unramified at $w$, so $\omega(z_w, z_w)$ acts trivially, and equivariance moves $z_w$ from stage $j$ to stage $j + 1$. Move $z_w$ through the first $j$ lifts by equivariance. At lift $j + 1$, equivariance for the pair $(1, z_w)$ says that $z_w$ times the lift with a datum is the lift with the datum moved by $\omega(1, z_w)$. That datum is fixed, so the two terms of $\psi - z_w\psi$ have the same image, and the chain is linear in $t$. $\square$

**Corollary.** In a chain of double lifts, if for some $i < p$ the operator $\omega(1, z_w)$ on the second factor fixes the datum $\tau_i$, then the chain vanishes on ramified source forms.

Lean: `New.Data.doubleLiftChain_eq_zero_of_ramified` (New/UpperBound/Objects/CharactersAtLevel.lean).

*Proof.* Regroup the $p$ pairs as $2p$ single factors. Then factor $2i + 1$ is fixed, and the theorem applies. $\square$

**Remark (Formalization).** The space $Y_j$ is chosen by `Exists.choose` from an existence lemma, and so is $z_w$. The lift `liftY` carries the factor of the level index, so that integrality is not lost. The group element in `lowerChain_principalRep` is a chosen lift `liftResidue` of $\mathrm{diag}(s, 1)$. The theorem on ramified forms is stated for any $m'$, not only for $m$.
