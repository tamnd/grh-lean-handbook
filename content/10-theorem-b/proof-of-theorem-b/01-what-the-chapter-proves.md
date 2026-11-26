---
title: What the chapter proves
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
decls:
  - New.Data.enough_forms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the last chapter of the volume. It assembles Theorem B from the results of the other chapters. It states Theorem B as Lean states it, and it gives the whole proof from the results of chapters 2 to 13 of this volume. Each of these results is recalled in one line with a link. The chapter tracks each constant and each hypothesis on the way. The last section maps the proof to files and declarations of the source.

[Theorem B and its plan](/chapter/theorem-b-plan/) gives the statement, the four layers and the short deduction of Theorem B from its input. This chapter does not repeat the motivation. It proves the steps that the plan only names: the bound for the dimension of the target, the bad types at the level primes, the scaling of the Poincaré map, the two inputs (NI) and (SM) for the data $D$, the spread of one translate, and the last count. All of these are in the two files New/Spanning/SecondMoment/SpanningTheorem.lean and New/Reduction/ShortAndEnough.lean.

### The statement

Fix parameters $P$ and admissible data $D$ for $P$. The letters are those of [the data and its sizes](/chapter/data-and-sizes/) and of [the plan](/chapter/theorem-b-plan/#theorem-b-and-its-input).

1. $b = D.b = e^{\log b}$ is the weight at the $b$-places.
2. $\bar G = D.\mathtt{chosenGL} = \prod_w \mathrm{GL}_r(\mathbb{F}_w)$ is the finite group, the product over the chosen places $w$ above the two level primes $p_0, p_1$.
3. The target is $D.\mathtt{targetForms}$, the image of the central idempotent $e_0$ on the forms of principal level on $Y_0$. Its dimension is $d_T = D.\mathtt{targetDim}$.
4. $X = D.\mathtt{SourceForm}$ is the space of source forms, and $\mathrm{src} = D.\mathtt{ramifiedSourceForms} \subseteq X$ is the space of ramified source forms.
5. $s\mathfrak{p} = D.\mathtt{normalizedPoincare}\ s$ is a linear map from $\mathrm{src}$ to the target, for each $s \in \bar G$.

**Theorem (Theorem B, enough forms).** The target has positive dimension, $0 < d_T$. There is a finite set $t$ of elements of $\bar G$ such that

$$\#t \cdot \dim \mathrm{src} \leq 5\, d_T \log(1 + 2b^2)$$

and

$$\Bigl(1 - \frac{4}{b^2}\Bigr) d_T \leq \dim \sum_{s \in t} s\mathfrak{p}(\mathrm{src}).$$

Lean: `New.Data.enough_forms` (New/Reduction/ShortAndEnough.lean).

In Lean the first inequality is `#t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2)`, an inequality of real numbers. The second is `(1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ s ∈ t, (D.normalizedPoincare s).range)`. The sum of subspaces is the supremum `⨆ s ∈ t` in the lattice of subspaces of the target. The dimension is `finrank`. The proof is in [the section from one translate to Theorem B](/chapter/proof-of-theorem-b/#from-one-translate-to-theorem-b).

The statement has no hypothesis other than the data $D$. Every size condition on $D$ that the proof uses is a consequence of the class of size bounds of the data. In the source these steps are proved by `D.le_of_hasLogBound`, `D.lt_of_hasLogBound`, `D.nat_le_of_hasLogBound` and `D.nat_lt_of_hasLogBound`. They come from the class `HasLogBound` of New/Reduction/Data/Magnitudes.lean, which proves an inequality between explicit sizes on the logarithmic scale. This chapter names each such inequality where it is used. [The table of sizes](/chapter/data-and-sizes/#the-table-of-sizes) explains why they hold: $b$ is very large, with $\log\log b$ above $6 \cdot 10^{13}$.

### The chain of the proof

The proof has six steps. The first five are in SpanningTheorem.lean. The last is in ShortAndEnough.lean.

1. The dimension of the target. $d_T \leq \#\bar G \cdot \deg \cdot \mathrm{mass}_r$. This is [the section on the dimension of the target](/chapter/proof-of-theorem-b/#the-dimension-of-the-target).
2. Bad types are rare. The idempotent $e_0$ is a tensor product of two central idempotents $e_{p_0}, e_{p_1}$, and the coefficient of $1 - e_{p_i}$ at the identity has real part at most $b^{-8}/2$. This is [the section on bad types at the level primes](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes).
3. The scaled Poincaré map $L$. It has amplitude blocks. So $e_0L$ is a near isometry with error $5b^{-4}$, and the second moment of $L$ is at most $(1 + 9b^{-4})$ times the main second moment. This is [the section on the scaled Poincaré map](/chapter/proof-of-theorem-b/#the-scaled-poincar-map).
4. The target is not zero.
5. One translate. The maps $\mathfrak{g}_s = \#\bar G \cdot e_0\, s\, \mathcal{P}$ spread with error $\tfrac32 (8b^2)^{-1}$. This is [the section on one translate](/chapter/proof-of-theorem-b/#one-translate).
6. The greedy cover with $\varepsilon = (8b^2)^{-1}$, then the restriction to the ramified forms. This gives Theorem B.

The map of the proof to files and declarations is in [the last section before the exercises](/chapter/proof-of-theorem-b/#the-map-of-the-proof).

### The results of the other chapters

The proof uses one or two results of each other chapter of the volume. Each is recalled here in one line.

1. [Theorem B and its plan](/chapter/theorem-b-plan/): the ramified forms have dimension at least $(1 - f/(N-1))\dim X$, and $f/(N-1) \leq b^{-8}$ ([Theorem](/decl/New.Data.le_finrank_ramifiedSourceForms/), [Theorem](/decl/New.Data.f_div_N_sub_one_le/)).
2. [Few translates suffice](/chapter/few-translates/): a near isometry with a second moment bound gives spread with error $\tfrac32\varepsilon$ ([Theorem](/decl/New.isSpread_of_second_moment/)), spread gives a greedy cover ([Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/)), and restriction to a subspace loses at most its codimension for each map ([Lemma](/decl/New.finrank_biSup_range_le/)).
3. [Equal multiplicities by the trace formula](/chapter/equal-multiplicities/): the good forms on $Y_0$ and on $W_j$ have the same dimension ([Theorem](/decl/New.Data.targetDim_eq_finrank_goodForms_spaceW/)), and bad types are rare at one prime ([Theorem](/decl/New.re_coeff_one_sub_sum_tupleIdem_le/)).
4. [Bessel functions at a real place](/chapter/bessel-real-place/): each real place has a Bessel system with the sizes of $D$ ([Theorem](/decl/New.Data.exists_besselSystem/)). The filling of $D$ chooses these systems.
5. [Frames, depth and gains](/chapter/local-frames/): the abstract bounds for local densities. They enter only through the second moment of chapter 13.
6. [Local densities at the real places](/chapter/real-densities/): the local bounds at a real place ([Theorem](/decl/New.Floors.exists_hasLocalBounds_of_isCutBessel/)). They enter through the main term.
7. [The anatomy of a term](/chapter/anatomy-of-a-term/): the sorting of the terms of an amplitude sum. It enters through the second moment.
8. [Local densities at the finite places](/chapter/finite-densities/): the densities at the finite places. They enter through the main term.
9. [Reduced points and frame counts](/chapter/frame-counts/): the counts of frames. They enter through the remaining terms.
10. [Poincaré series and unfolding](/chapter/poincare-series/): the filling of $D$ fits the space $Y_0$ ([Theorem](/decl/New.Data.filling_fits/)), the Petersson formula ([Theorem](/decl/New.Filling.Fits.petersson_poincare/)), and the Poincaré map of $D$ is the Poincaré series in coordinates ([Corollary](/decl/New.Data.poincare_eq_poincareMap_comp/)).
11. [The remaining terms](/chapter/remaining-terms/): the bound for the remaining terms. It enters through the second moment.
12. [The main term](/chapter/main-term/): the bound for the main term. It enters through the second moment.
13. [Moments of the Poincaré map](/chapter/moments/): a map with amplitude blocks scales well ([Lemma](/decl/New.Filling.hasAmplitudeBlocks_smul_of_inner_eq/)), gives a near isometry after a good projection ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp/)), and has a small second moment ([Theorem](/decl/New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le/)).

Chapters 5 to 9, 11 and 12 enter the proof of Theorem B only through the two theorems of chapter 13. This chapter uses those two theorems as they are stated, so it does not cite the inner results again.

### Background

The proof uses these results of earlier volumes. Each is stated in one line.

1. [Automorphic forms on unitary groups](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups): at a free level, the space of algebraic forms of a weight has dimension (number of classes) times (dimension of the weight) ([Theorem](/decl/New.finrank_levelSpace_smoothFormRep/)).
2. [Automorphic forms on unitary groups](/chapter/automorphic-forms/#automorphic-forms-as-algebraic-forms): forms on a definite space of a parameter are algebraic forms of a weight ([Definition](/decl/New.Space.algFormEquiv/)).
3. [Automorphic forms on unitary groups](/chapter/automorphic-forms/#hecke-operators-and-class-sums): at a free level the number of classes is the class sum ([Theorem](/decl/New.card_classes_eq_classSum/)), and the class sum grows by the relative index ([Theorem](/decl/New.classSum_one_of_le/)).
4. [The Siegel-Weil formula](/chapter/siegel-weil/#the-ratio-of-masses): the class sum of the standard level is the mass, and the mass is positive ([Theorem](/decl/New.classSum_stdRatPoints_eq_mass/)).
5. [Discrete series](/chapter/discrete-series/#orthogonality-rigidity-and-the-formal-degree): the formal degree of a discrete series is given by Weyl's formula ([Theorem](/decl/New.Orbital.harish_chandra_degree_and_orbital/)).
6. [Characters of GL_n over a finite field](/chapter/finite-gln/): a sum of the idempotents of tuples of labels is a central idempotent ([Theorem](/decl/New.isCentralProj_sum_tupleIdem/)).
7. [The objects of the upper bound](/chapter/upper-bound-objects/): $e_0$ is a central idempotent ([Theorem](/decl/New.Data.isCentralProj_e₀/)).
8. [The data and its sizes](/chapter/data-and-sizes/): the sizes of $D$, and the class `HasLogBound` that proves the size inequalities.
