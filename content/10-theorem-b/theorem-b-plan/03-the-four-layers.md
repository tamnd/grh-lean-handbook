---
title: The four layers of the proof
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - Lib/Adelic/TraceFormula/CuspidalComparison.lean
decls:
  - New.IsNearIsometry
  - New.isSpread_of_second_moment
  - New.Data.targetDim_eq_finrank_goodForms_spaceW
  - New.Data.finrank_principalForms_spaceW
  - New.Data.targetDim_le_card_mul_besselDegree_mul_mass
  - New.Data.bad_types_rare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The four layers of the proof

The proof of [Theorem](/decl/New.Data.isSpread_goodPoincare/) has four layers. Each layer uses only the statements of the layer above it, and not their proofs.

1. *Linear algebra.* Spread follows from two numbers: an error of near isometry and a second moment. Few translates then span almost everything. This layer knows nothing about automorphic forms.
2. *Dimension.* The dimension $d_T$ of the target is at most $\#\bar G \cdot \deg \cdot \mathrm{mass}_r$. The proof compares two spaces of forms by a trace formula, and on a definite space it counts the forms by a class number.
3. *Unfolding.* The inner products $\langle s\mathcal{P}a', \mathcal{P}a\rangle$ are sums over rational points of integrals of Bessel functions. This turns the two numbers of layer 1 into sums of amplitudes.
4. *Bounds.* The sums of amplitudes are cut into identity terms, main terms and remaining terms, and each part is bounded. The main term is computed by Kloosterman sums and bounded by a sieve over local densities. The remaining terms are bounded by counting lattice points.

This section states the results of the first two layers. [The next section](/chapter/theorem-b-plan/#unfolding-and-bounds) states those of the last two and assembles the proof of the input theorem. Throughout, $\|A\|$ is the Hilbert-Schmidt norm of a linear map $A$ between finite-dimensional inner product spaces, and $\mathrm{pr}_U$ is the orthogonal projection onto $U$.

### Layer 1: linear algebra

**Definition (Near isometry in mean square).** A linear map $A : S \to T$ is a *near isometry with the error* $\varepsilon$ if $\dim U - \varepsilon\dim S \leq \|A\,\mathrm{pr}_U\|^2$ for every subspace $U$ of $S$.

Lean: `New.IsNearIsometry` (New/Spanning/SecondMoment/FewTranslates.lean).

For an isometry, $\|A\,\mathrm{pr}_U\|^2 = \dim U$. So the condition says that $A$ loses, on every subspace at once, at most the share $\varepsilon$ of the whole dimension of $S$. It is a lower bound only. A map with large norm is a near isometry in this sense.

**Theorem (Spread from a second moment).** Let a finite group $\Gamma$ act unitarily on $T$ by $\rho$. Let $\mathrm{pr}_0$ be a symmetric projection on $T$ with $\mathrm{pr}_0\,\rho(s) = \rho(s)\,\mathrm{pr}_0$ for all $s$, and let $T_0$ be its range. Let $B : S \to T$ be linear and $\varepsilon \geq 0$. Suppose that $\mathrm{pr}_0 B$ is a near isometry with the error $\varepsilon$, and that

$$\dim T_0 \cdot \sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \leq |\Gamma|\,(1 + \varepsilon)(\dim S)^2.$$

Then the maps $\mathrm{pr}_0\,\rho(s)\,B : S \to T_0$, $s \in \Gamma$, spread with the error $\frac{3}{2}\varepsilon$.

Lean: `New.isSpread_of_second_moment` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $W \subseteq T_0$ have dimension $\alpha\dim T_0$. The sum $\sum_s \|\mathrm{pr}_W\,\rho(s)B\|^2$ is the Hilbert-Schmidt pairing of $\mathrm{pr}_W$ with $\Sigma = \sum_s \rho(s)BB^*\rho(s)^*$. Here $\|\mathrm{pr}_W\|^2 = \dim W$, and $\|\Sigma\|^2 = \sum_{s, t}\|B^*\rho(s^{-1}t)B\|^2 = |\Gamma|\sum_u\|B^*\rho(u)B\|^2$. By Cauchy-Schwarz and the hypothesis,

$$\Bigl(\sum_s\|\mathrm{pr}_W\,\rho(s)B\|^2\Bigr)^2 \leq \alpha\dim T_0\cdot|\Gamma|\sum_u\|B^*\rho(u)B\|^2 \leq \alpha(1 + \varepsilon)\,|\Gamma|^2(\dim S)^2.$$

So some $s$ has $\|\mathrm{pr}_W\,\rho(s)B\|^2 \leq \sqrt{\alpha(1 + \varepsilon)}\dim S$. Fix this $s$, put $A = \mathrm{pr}_0\,\rho(s)B$ and $U = A^{-1}(W)$. As $\rho(s)$ is unitary and commutes with $\mathrm{pr}_0$, $\|A\,\mathrm{pr}_U\| = \|\mathrm{pr}_0B\,\mathrm{pr}_U\|$, and the near isometry gives $\dim U - \varepsilon\dim S \leq \|A\,\mathrm{pr}_U\|^2$. As $A$ maps $U$ into $W$, $A\,\mathrm{pr}_U = \mathrm{pr}_W A\,\mathrm{pr}_U$, so $\|A\,\mathrm{pr}_U\|^2 \leq \|\mathrm{pr}_W A\|^2 = \|\mathrm{pr}_W\,\rho(s)B\|^2$. Finally $\sqrt{\alpha(1 + \varepsilon)} \leq (1 + \alpha + \varepsilon)/2$. Together, $\dim U \leq ((1 + \alpha)/2 + \frac{3}{2}\varepsilon)\dim S$. [The chapter on few translates](/chapter/few-translates/) gives the details. $\square$

If the images $\rho(s)B(S)$ were in random position, the mean of $\|B^*\rho(s)B\|^2$ would be $(\dim S)^2/\dim T_0$, and for irreducible $\rho$ this is the exact mean (Exercise 3). A family that attains it is a tight frame, in the sense of Benedetto and Fickus. The theorem says that a family within the factor $1 + \varepsilon$ of this value spreads.

The cover theorem, [Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/), then turns spread into few translates, as in the first section. So the whole volume reduces to two inequalities for the Poincaré map $P$ after scaling, with $\varepsilon = (8b^2)^{-1}$:

$$\text{(NI)}\quad e_0P \text{ is a near isometry with the error } \varepsilon, \qquad \text{(SM)}\quad d_T\sum_{s \in \bar G}\|P^*sP\|^2 \leq \#\bar G\,(1 + \varepsilon)(\dim X)^2.$$

The source proves (NI) with the error $5b^{-4}$ and (SM) with $9/b^4$ in place of $\varepsilon$. Both are much smaller than $(8b^2)^{-1}$.

### Layer 2: dimension

The inequality (SM) has the factor $d_T$ on the left. The moment computation of layer 4 gives $\sum_s\|P^*sP\|^2 \leq (1 + 9b^{-4})\,(\dim X)^2/(\deg\cdot\mathrm{mass}_r)$, where $\deg$ is a product of formal degrees over the real places and $\mathrm{mass}_r$ is the mass of the genus of the standard hermitian lattice of rank $r$. So (SM) needs an upper bound $d_T \leq \#\bar G\cdot\deg\cdot\mathrm{mass}_r$. This is the dimension layer. In the model case it is the statement $\dim S_k \approx \frac{k - 1}{4\pi}\cdot\frac{\pi}{3}$.

The target lives on the indefinite space $Y_0$, where no direct count is available. The source moves the count to definite spaces $W_j$. There the quotient is a finite class set, and a space of forms of free level has dimension (number of classes) times (dimension of the weight).

The move uses a comparison of traces, a special case of the simple trace formula of [the chapter on the simple trace formula](/chapter/trace-formula/). In the source it says that, for two hermitian spaces of the same rank over a CM field with an even number of infinite places, a Hecke operator that is cuspidal at a split place has the same trace on the forms of parameter $l$ and level $K$ of both spaces, if $l$ has a large gap at every infinite place. [The chapter on equal multiplicities](/chapter/equal-multiplicities/) states it with all its hypotheses.

**Theorem (Equal dimensions).** For each index $j$ with $1 \leq j \leq m$, the good forms on $W_j$ have dimension $d_T$, the dimension of the good forms on $Y_0$.

Lean: `New.Data.targetDim_eq_finrank_goodForms_spaceW`, `New.Data.trace_heckeOnGood_eq` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* The identity operator has the same trace on the good forms of $Y_0$ and of $W_j$, by the comparison of traces for the Hecke operators on good forms. The trace of the identity is the dimension. $\square$

**Lemma (Forms on the definite space).** The forms of principal level on the definite space $W_m$ have dimension

$$\dim = \#\bar G\cdot\mathrm{mass}_r\cdot\prod_{v}\deg_v,$$

where $v$ runs over the infinite places and $\deg_v$ is the formal degree of the parameter at $v$ for the definite signs.

Lean: `New.Data.finrank_principalForms_spaceW` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* The level is free: the rational points meet each of its conjugates trivially. So the forms are functions on the class set with values in the weight, and the dimension is the number of classes times the dimension of the weight. The level has index $\#\bar G$ in the maximal level, whose class sum is the mass. The dimension of the weight is the product of the compact formal degrees, by Weyl's dimension formula. $\square$

**Theorem (Dimension of the target).** $d_T \leq \#\bar G\cdot\deg\cdot\mathrm{mass}_r$, where $\deg$ is the product over the infinite places of the formal degrees of the Bessel systems of the filling.

Lean: `New.Data.targetDim_le_card_mul_besselDegree_mul_mass` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* By equal dimensions with $j = m$, $d_T$ is the dimension of the good forms on $W_m$. These are among the forms of principal level on $W_m$, whose dimension is given by the lemma. The two products of degrees agree, by Harish-Chandra's formula for the formal degree. $\square$

The bound is an inequality and not an equality because the good forms are only part of the forms of principal level. The argument does not need the exact value. A smaller target only helps (SM).

The good forms are cut out by the projection $e_0$. It is a tensor product of central idempotents $e_{p_0}$ and $e_{p_1}$ of the group algebras of the two factors of $\bar G$. The idempotent $e_{p_i}$ removes the bad types, the irreducible representations of $\mathrm{GL}_r$ over the residue fields above $p_i$ that the argument cannot use. The near isometry (NI) needs that $e_0$ removes little.

**Theorem (Bad types are rare).** The elements $e_{p_0}$ and $e_{p_1}$ are central idempotents. Their tensor product acts on the forms of principal level as the projection $e_0$ onto the good forms. For $i = 0, 1$, the coefficient of $1 - e_{p_i}$ at the identity has real part at most $b^{-8}/2$.

Lean: `New.Data.bad_types_rare`, `New.re_coeff_one_sub_sum_tupleIdem_le` (New/Spanning/SecondMoment/SpanningTheorem.lean, New/Spanning/MainTerm/BadTypes.lean).

The coefficient at the identity of a central idempotent is the share of the regular representation that it keeps. So the bad types carry at most the share $b^{-8}/2$ of the regular representation at each prime. The count uses the character theory of $\mathrm{GL}_n(\mathbb{F}_q)$ of [Volume 5, chapter 5](/chapter/finite-gln/).

**Remark (Formalization).** The comparison of traces is proved in the source for the operators that act as an element of the universal level algebra, and only on spaces with a large gap at every infinite place. The dimension layer uses it only through the traces of Hecke operators on the good forms.
