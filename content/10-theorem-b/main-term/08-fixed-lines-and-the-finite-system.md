---
title: Fixed lines and the finite system
lean:
  - New/Spanning/Frames/FixedLines.lean
  - New/Spanning/MainTerm/FiniteSieveSystem.lean
decls:
  - New.Filling.IsFillingData.massIntegral_mul_le_of_relIndex_eq
  - New.Filling.IsFillingData.exists_intermediateGroup_one_place
  - New.Filling.IsFillingData.exists_intermediateGroup_places
  - New.Filling.IsFillingData.massIntegral_full_le
  - New.Filling.IsFillingData.enorm_floorForm_zero_mul_le
  - New.Filling.IsFillingData.norm_floorForm_zero_div_massRatio_le
  - New.Filling.IsFillingData.exists_intermediateGroup_norm_floorForm_div_le
  - New.Filling.IsFillingData.posSemidef_lastEntryDensity
  - New.Filling.IsFillingData.exists_intermediateGroup_sieveSystem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Fixed lines and the finite system

The sieve of [Section 4](/chapter/main-term/#the-global-sieve) needs a sieve system at $T$. This section builds it from the forms of the floors of [the finite places](/chapter/finite-densities/), divided by the mass ratio. The bottom bound of the system is the gain of the main theorem: $(1 + b^{-6})(b^{6k})^{-\#S_g}$. The factor $(b^{6k})^{-1}$ for each $w \in S_g$ comes from the condition that the reduction fixes a line modulo $w$.

In this section $F$ is a filling datum at $T$ with modulus $g$, $K$ is the group of integral points at $T$, $K(g)$ its principal congruence subgroup, $\operatorname{vol}$ the Haar measure, and $\varkappa(Z) = \int_G\bigl|\int_Z\chi_g(yxy^{-1})\,dy\bigr|^2\,dx$ the [mass integral](/chapter/finite-densities/#the-finite-bessel-vector) of a group $Z$ with $K(g) \leq Z \leq K$.

### The gain from a fixed line

**Theorem (One place).** Let every place of $T$ be a chosen place or the conjugate of one. Let $K(g) \leq Z \leq K$ with $[K : Z] = p_0^r - 1$, where $r$ is the size of the matrices. Then
$$\varkappa(Z)\,\operatorname{vol}(K)\,b^{6k} \leq \varkappa(K)\,\operatorname{vol}(Z).$$

Lean: `New.Filling.IsFillingData.massIntegral_mul_le_of_relIndex_eq` (New/Spanning/Frames/FixedLines.lean).

*Proof.* Put $B = b^9$. Since $q \geq b^{10}$ at a chosen place, the non-units of $\mathcal O$ have volume at most $B^{-1}$. Choose $t$ with $t + 1 + n + 2 \cdot 10^9n^4 \leq k$, $6k \leq 9t$ and $t + 1 < r$; the sizes of [the data](/chapter/data-and-sizes/) allow this. The index gives $B^{t+1}\operatorname{vol}(Z) \leq \operatorname{vol}(K)$. The theorem [main term plus error](/chapter/finite-densities/#shells-decay-and-mass) with $Q = B$ gives the upper bound
$$\varkappa(Z) \leq \operatorname{vol}(Z)\operatorname{vol}(K(g))\bigl(\operatorname{vol}(Z) + B^{-(t+1)}\operatorname{vol}(K)\bigr).$$
The part of the outer integral of $\varkappa(K)$ over $K(g)$ gives the lower bound $\operatorname{vol}(K)^2\operatorname{vol}(K(g)) \leq \varkappa(K)$. Both terms of the upper bound are at most $B^{-(t+1)}\operatorname{vol}(K)$ times $\operatorname{vol}(Z)\operatorname{vol}(K(g))$. So $\varkappa(Z)\operatorname{vol}(K)B^{t} \leq \operatorname{vol}(K)^2\operatorname{vol}(K(g))\operatorname{vol}(Z) \leq \varkappa(K)\operatorname{vol}(Z)$, and $b^{6k} \leq B^t$. $\square$

The subgroup of index $p_0^r - 1$ is the stabilizer of a line: the fixer of a nonzero vector modulo $w$ has index $p^r - 1$ in the reduction of $K$ (`New.Filling.index_comap_vectorFixer`).

**Theorem (One block).** Let $o$ be either nothing or a place $w \in S_g$ such that $T$ consists of the places of a larger set $T_0$ equal to $w$ or $\bar w$. There is $Z$ with $K(g) \leq Z \leq K$ such that (a) $Z$ contains the component at $T$ of every integral element whose reduction lies in $\operatorname{fixer}(S_g, D)$, and (b) $\varkappa(Z)\operatorname{vol}(K)B \leq \varkappa(K)\operatorname{vol}(Z)$, with $B = b^{6k}$ if $o$ is a place and $B = 1$ otherwise.

Lean: `New.Filling.IsFillingData.exists_intermediateGroup_one_place` (New/Spanning/Frames/FixedLines.lean).

*Proof.* If $o$ is nothing, take $Z = K$. If $o = w$, take the preimage of the fixer of $D_w$; it contains $K(g)$ and the components of the elements of the fixer, and its index is $p_0^r - 1$. Apply the theorem on one place. $\square$

**Theorem (All places).** Let $M^{-1}$ be integral off $T$. There is $Z$ with $K(g) \leq Z \leq K$ such that (a) holds and $\varkappa(Z)\operatorname{vol}(K)(b^{6k})^{\#S_g} \leq \varkappa(K)\operatorname{vol}(Z)$.

Lean: `New.Filling.IsFillingData.exists_intermediateGroup_places` (New/Spanning/Frames/FixedLines.lean).

*Proof.* Split $T$ into the blocks $T \cap \{w, \bar w\}$ for $w \in S_g$ and the rest. The unitary group at $T$, its Haar measure, its character and its mass integral are products over the blocks. Take a group on each block by the theorem on one block, and take their product. Multiply the inequalities: each $w \in S_g$ gives one factor $b^{6k}$, and the rest gives $1$. $\square$

### The forms at $T$

**Lemma (Full mass).** $\varkappa(K) \leq \operatorname{vol}(K)\operatorname{vol}(K(g))(1 + b^{-6})$.

Lean: `New.Filling.IsFillingData.massIntegral_full_le` (New/Spanning/MainTerm/FiniteSieveSystem.lean).

*Proof.* Apply [main term plus error](/chapter/finite-densities/#shells-decay-and-mass) with $Z = K$ and $Q = 2$, and $t$ large: $\varkappa(K) \leq \operatorname{vol}(K)\operatorname{vol}(K(g))(\operatorname{vol}(K) + 2^{-t})$. By the matching lemma of [Section 6](/chapter/main-term/#kloosterman-sums-and-unfolding) the volumes are explicit powers of $M^f$, and $2^{-t}$ is small against them by the sizes of the data. $\square$

**Lemma (Floor zero).** $\|F_0(W_Z)\|\operatorname{unipotentMass}^2 \leq \varkappa(Z)$. If $\varkappa(Z)\operatorname{vol}(K)(b^{6k})^s \leq \varkappa(K)\operatorname{vol}(Z)$, then $\|F_0(W_Z)\|/\operatorname{massRatio}(Z) \leq (1 + b^{-6})(b^{6k})^{-s}$.

Lean: `New.Filling.IsFillingData.enorm_floorForm_zero_mul_le`, `New.Filling.IsFillingData.norm_floorForm_zero_div_massRatio_le` (New/Spanning/MainTerm/FiniteSieveSystem.lean).

*Proof.* The form of floor $0$ is the orbital integral of $W_Z$ at the identity, an integral of $|W_Z|^2$ over the unipotent cosets. The [mass integral as a correlation](/chapter/finite-densities/#the-finite-bessel-vector) bounds it by $\varkappa(Z)/\operatorname{unipotentMass}^2$. For the second claim divide by $\operatorname{massRatio}(Z) = \operatorname{vol}(Z)\operatorname{vol}(K(g))/\operatorname{unipotentMass}^2$ and use the hypothesis and the lemma on the full mass. $\square$

**Theorem (Bottom bound).** There is $Z$ with (a) such that $F_0(W_Z)/\operatorname{massRatio}(Z)$ is a real number in $[0, (1 + b^{-6})(b^{6k})^{-\#S_g}]$.

Lean: `New.Filling.IsFillingData.exists_intermediateGroup_norm_floorForm_div_le` (New/Spanning/MainTerm/FiniteSieveSystem.lean).

*Proof.* Take $Z$ from the theorem on all places and apply the lemma on floor zero with $s = \#S_g$. The form is a squared norm, so it is real and nonnegative. $\square$

**Lemma (Positivity at the top).** On finitely many heads $a_i$ with the same entry $t$ at $\varrho$, the matrix $(\rho_\pi(a_i, a_j))_{i,j}$ of last entry densities is positive semidefinite.

Lean: `New.Filling.IsFillingData.posSemidef_lastEntryDensity` (New/Spanning/MainTerm/FiniteSieveSystem.lean).

*Proof.* The matrix is Hermitian, since the fibre pairing is. For a vector $x$, the quadratic form $\sum x_i\bar x_j\rho_\pi(a_i, a_j)$ is $|\pi|^{-1}$ times the integral over the sphere of $\sum x_i\bar x_j P_{a_i,a_j}$, which is a nonnegative function by [continuity and positivity](/chapter/finite-densities/#the-top-floor). $\square$

**Theorem (The finite sieve system).** There is $Z$ with (a) such that the forms
$$J_j(p, q) = \frac{1}{\operatorname{massRatio}(Z)}\begin{cases}F_j(p, q; W_Z) & j \leq \varrho,\\ \rho_\pi(p, q) & j > \varrho,\end{cases}$$
form a sieve system at $T$ with the entry map $\operatorname{unitOrOne}$, the map $u \mapsto M^{-1}u^{-1}$, the character $\operatorname{charOnPlaces}(T)$, the bottom bound $(1 + b^{-6})(b^{6k})^{-\#S_g}$, the weights $\Lambda_{n^6}$ and the decay $\operatorname{frequencyDecay}(T)$.

Lean: `New.Filling.IsFillingData.exists_intermediateGroup_sieveSystem` (New/Spanning/MainTerm/FiniteSieveSystem.lean).

*Proof.* Take $Z$ from the theorem on the bottom bound; it gives the bound on $J_0$. The steps $j < \varrho$ are the descent of the floors in [shells, decay and mass](/chapter/finite-densities/#shells-decay-and-mass): $F_j$ is the integral of $F_{j+1}$ over the common entry, and the twisted integrals and the forms at unit frequencies are bounded by the decay times the weights. The step at $\varrho$ is [Fourier inversion at the last entry](/chapter/finite-densities/#the-top-floor). The top form is continuous, and positive semidefinite by the lemma on positivity. The sizes $10^{10}n^4 \leq n^6$ and $n^7 \leq k$ fit the weights and the decay of [Section 3](/chapter/main-term/#frequencies-and-poisson-summation) to the bounds of the finite chapter. $\square$
