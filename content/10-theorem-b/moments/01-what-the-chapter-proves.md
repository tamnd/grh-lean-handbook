---
title: What the chapter proves
lean:
  - New/Spanning/Unfolding/SquareExpansion.lean
  - New/Spanning/Unfolding/MomentBounds.lean
  - New/Spanning/Unfolding/Moments.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter joins layer 3 and layer 4 of the proof of Theorem B. Layer 3 writes the Hilbert-Schmidt norms of the operators $P_s = P^*\rho(s)P$ as sums of squared blocks of amplitudes. Layer 4 bounds the blocks of each kind of term. This chapter puts the bounds together. It proves the two inputs of [the chapter on few translates](/chapter/few-translates/): the near isometry (NI) and the second moment (SM) of [the section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof). The place of the chapter in the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/), and its place in Theorem B is in [the section on unfolding and bounds](/chapter/theorem-b-plan/#unfolding-and-bounds).

### The setting

Fix admissible filling data $S$ of shape $\mathfrak{s}$ over a CM field $E$, in the sense of [Definition](/decl/New.Filling.IsAdmissible/). Most results also ask for a primitive root of unity of order $5040$ in $E$, or for Weil data on $E$, which include such a root. We use the notation of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/#what-the-chapter-proves) and of [the chapter on the remaining terms](/chapter/remaining-terms/#what-the-chapter-proves).

- $b \geq 1000$ is the size parameter. The two level primes satisfy $b^{10} \leq p_i \leq b^{11}$, and $M = p_0p_1 \leq b^{23}$.
- $f$ is the number of infinite places of $E$. Above each $p_i$ there are $f$ chosen places $w$, each of norm $p_i$.
- $k = |\kappa|$ is the rank of the definite space $X_0$, $\varrho$ is the number of hyperbolic planes, and $n = \varrho + 1$ is the length of the frame $e_1, \dots, e_\varrho, z$. The data give $10^5 \leq \varrho$, $1000(2\varrho + 2) \leq k \leq b$ and $\varrho + 1 \leq b$.
- $\bar G = G_0 \times G_1$, where $G_i$ is the product over the chosen places $w$ above $p_i$ of the groups $\mathrm{GL}_r(\mathbb{F}_w)$, with $r = 2\varrho + k + 1$ the rank of the space. The reduction map sends the stabilizer $K$ of the lattice onto $\bar G$.
- $R_0$ is the Bessel subgroup, $\mathsf{U}$ its unipotent part, and $\bar R_0$ the image in $\bar G$ of the integral points of $R_0$.
- The source is the Euclidean space with the basis $e_x$, $x = (c, i)$, where $c$ is a class and $i$ a coordinate of the Bessel function $W$. Its dimension is $D_X$.
- $\nu > 0$ is the covolume of the unipotent lattice of a class.
- $\mathcal{A}_T(c, s, c')$ is the block of the terms of a set $T$ for the full Bessel function, and $\mathcal{A}^\flat_T$ the block for the cut function. The block of all terms is $\mathcal{A} = \mathcal{A}_{\mathrm{univ}}$.
- $\mathsf{E}(A, \Omega)$ is the second moment of [Definition](/decl/New.Filling.secondMoment/), and $\mathsf{L}(T, \Omega)$ the second moment link by link of [Definition](/decl/New.Filling.linkSecondMoment/).
- $\mathcal{D}_{\mathrm{id}} = \#\bar R_0\cdot D_X$ and $\mathcal{D}_{\mathrm{main}} = D_X^2/(\deg\cdot\mathrm{mass}_r)$.

Admissibility gives the two comparisons

$$b^{11kf}\,\mathcal{D}_{\mathrm{id}} \leq \mathcal{D}_{\mathrm{main}} \leq (M/b^6)^{kf}\,\mathcal{D}_{\mathrm{id}}. \tag{1.1}$$

Their proof is in [the section on admissible data](/chapter/poincare-series/#the-data-are-admissible).

### The results

The chapter proves five theorems. Let $\rho$ be a representation of $\bar G$ on a finite-dimensional space $V$ and let $P$ have amplitude blocks: the entry $(x, y)$ of $P_s$ is the complex conjugate of $\mathcal{A}(c, s, c')_{i, i'}/\nu$.

1. *The expansion of the squares.* Over the set of $s$ that agree with an element of $\bar R_0$ above one prime $p_i$, the terms off $R_0$ have second moment at most $b^{-12}\mathcal{D}_{\mathrm{id}}$ ([Theorem](/decl/New.Filling.secondMoment_compl_besselS_le/)).
2. *The identity terms.* The terms in $R_0$ give a unitary representation $r_\psi$ of $\bar R_0$ on the source. Over the same sets, $\sum\|P_s - r_\psi(s)\|^2 \leq b^{-12}\mathcal{D}_{\mathrm{id}}$, and $\|P^*P - 1\|^2 \leq b^{-12}D_X$ ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le/)).
3. *The second moment over $\bar G$.* If $\rho$ is unitary, then $\sum_{s \in \bar G}\|P_s\|^2 \leq (1 + 9b^{-4})\mathcal{D}_{\mathrm{main}}$ ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le/)).
4. *The induced character.* The mean $\psi_U^\natural$ of the Bessel character over conjugates satisfies $\sum_{s \in \bar G}|\psi_U^\natural(s)|^2 \leq 2$ ([Theorem](/decl/New.Filling.sum_norm_reducedCharMean_sq_le/)).
5. *Good forms.* For central idempotents $g_0, g_1$ with $\operatorname{Re}(1 - g_i)(1) \leq b^{-8}/2$, the map $\rho(g_0\otimes g_1)P$ is a near isometry with the error $5b^{-4}$ ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp/)).

The merged chapters cite these results in several places. [The chapter on few translates](/chapter/few-translates/#positive-type-and-singular-minors) uses the lemma on positive type for the singular minors, which is applied in [the section on the whole group](/chapter/moments/#the-second-moment-over-the-whole-group). [The chapter on the anatomy of a term](/chapter/anatomy-of-a-term/) sorts the terms whose characters do not agree; their blocks cancel in [the section on the expansion](/chapter/moments/#the-expansion-of-the-squares). [The section on unfolding and bounds](/chapter/theorem-b-plan/#unfolding-and-bounds) states the results above in short form; this chapter gives the full statements and proofs.

### What the chapter uses

- The bounds of the remaining terms, [Theorem](/decl/New.Filling.secondMoment_remainingTerms_le/) and [Theorem](/decl/New.Filling.linkSecondMoment_le_of_le_meetNorm/), and the size of the cut, from [the chapter on the remaining terms](/chapter/remaining-terms/).
- The main term, [Theorem](/decl/New.Filling.linkSecondMoment_isOpenElement_le/), from [the chapter on the main term](/chapter/main-term/).
- The blocks, their moves under $\mathsf{U}$, the climbing of the flags, the meet norm and the fixers, from [the chapter on Poincaré series](/chapter/poincare-series/).
- The lemma on singular minors, [Theorem](/decl/New.card_mul_sum_det_eq_zero_le/), and the near isometries, from [the chapter on few translates](/chapter/few-translates/).
- The bound on the mass integral and the lower bound for the volume of $K$, from [the chapter on densities at the finite places](/chapter/finite-densities/).
- Convolution with a central idempotent is a contraction on $\ell^2$: [Theorem](/decl/New.IsCentralProj.sum_norm_sq_conv_le/) in [the chapter on congruence subgroups](/chapter/congruence-subgroups/) of Volume 4.

The file of the expansion imports the sum over the remaining terms, which [chapter 11](/chapter/remaining-terms/) explains. The file of the moment bounds imports the energy estimate, which [chapter 12](/chapter/main-term/) explains. Both come before this chapter. No file of this chapter imports a file that a later chapter of Volume 10 explains.

### A sketch of the proof

The model is the Petersson formula in rank one. There the square of a Poincaré series is a diagonal term plus a sum of Kloosterman terms. Here the diagonal term is the operator $r_\psi(s)$ of the terms in $R_0$, and the other terms split into the main terms and the remaining terms.

*Step 1.* An element $s$ near $\bar R_0$ (equal to an element of $\bar R_0$ above $p_i$) meets the frame at the $2f$ places above $p_i$. So its meet norm is at least $(M/b)^f$. A term off $R_0$ over such an $s$ either has characters that do not agree, and then the blocks cancel, or it is a remaining term. The crude bound on links and (1.1) then give $b^{-12}\mathcal{D}_{\mathrm{id}}$.

*Step 2.* The identity terms make $P$ an intertwiner: $\rho(t)P = Pr_\psi(t)$ for $t \in \bar R_0$. So $P_s - r_\psi(s)$ has the norm of $P^*P - 1$ for $s \in \bar R_0$. Step 1 gives $\#\bar R_0\,\|P^*P - 1\|^2 \leq b^{-12}\#\bar R_0D_X$.

*Step 3.* The function $s \mapsto \|P_s\|^2$ has positive type. The bound over $\bar G$ uses a maximal family of fixed vectors. On the fixer of such a family, the elements in scalar cosets of $\bar R_0$ are few, the elements that are not open are rare by the lemma on singular minors, and the open elements are bounded by the main term.

*Step 4.* The good forms. The part $(1 - e)P$ of a central idempotent $e$ of one factor has squared norm $\operatorname{tr}r_\psi(x) + \operatorname{tr}(P'_x)$ with $x = 1 - e$. The trace of $r_\psi$ is $D_X$ times a character $\psi_U$. Cauchy-Schwarz and Step 2 bound both parts.

### Conventions

Each amplitude is a Bochner integral, and each block is a sum `tsum` over the terms. In Lean an integral of a function that is not integrable is $0$, and a sum of a family that is not summable is $0$ (finding F-032 of [the register of findings](/chapter/register-of-findings/)). This chapter does not prove any integrability or summability. It uses only identities of blocks that hold for every value of these sums, and the bounds of chapters 11 and 12. [The section on conventions](/chapter/theorem-b-plan/#conventions-that-change-the-meaning) shows that the amplitudes are summable for admissible data, so the junk value does not occur there. The near isometry is the mean-square notion of [Definition](/decl/New.IsNearIsometry/) (finding F-059).

The plan of the volume says that this chapter shows each exchange of a sum and an integral with its convergence. The files of the chapter contain only three such exchanges, all in [the section on the induced character](/chapter/moments/#the-induced-character): a finite sum with an integral of continuous functions on a compact group, a sum of integrals of nonnegative functions over disjoint sets, and finite sums in $[0, \infty]$. The infinite exchanges of the unfolding are in [the chapter on Poincaré series](/chapter/poincare-series/).
