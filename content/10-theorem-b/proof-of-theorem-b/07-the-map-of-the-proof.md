---
title: The map of the proof
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/Unfolding/Moments.lean
  - New/Spanning/Unfolding/PoincareSeries.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - New/Spanning/MainTerm/BadTypes.lean
  - New/Spanning/Bessel/FillingData.lean
  - New/UpperBound/Size/ShortColumns.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the proof

This section maps the whole proof of Theorem B to the files and declarations of the source. It reads from the statement down to the inputs. Each row names a declaration, its file and line at the pin, the chapter of this book that proves it, and the results that its proof calls. All names of the data are in the namespace `New.Data`, the names of filling data in `New.Filling`, and the general names in `New`.

### The top: ShortAndEnough.lean

The file New/Reduction/ShortAndEnough.lean holds the statement and the last step.

| Declaration | Line | Proof calls |
|---|---|---|
| `New.Data.enough_forms` | [448](lean:New/Reduction/ShortAndEnough.lean#L448) | `targetDim_pos`, `exists_le_finrank_iSup_range_normalizedPoincare` |
| `New.Data.exists_le_finrank_iSup_range_normalizedPoincare` | [410](lean:New/Reduction/ShortAndEnough.lean#L410) | `isSpread_goodPoincare`, `IsSpread.exists_few_le_finrank_iSup_range`, `five_halves_mul_one_add_log_le`, `le_finrank_ramifiedSourceForms`, `f_div_N_sub_one_le`, `range_normalizedPoincare`, `finrank_biSup_range_le` |
| `New.Data.targetDim_pos` | [403](lean:New/Reduction/ShortAndEnough.lean#L403) | `finrank_targetForms_ne_zero` |
| `New.Data.five_halves_mul_one_add_log_le` | [393](lean:New/Reduction/ShortAndEnough.lean#L393) | `le_of_hasLogBound`, `exp_one_lt_three`, `log_le_log` |
| `New.Data.range_normalizedPoincare` | [386](lean:New/Reduction/ShortAndEnough.lean#L386) | `invGainFactor_pos`, `LinearMap.range_smul`, `LinearMap.range_comp` |
| `New.Data.normalizedPoincare` | [185](lean:New/Reduction/ShortAndEnough.lean#L185) | definition: $c_B$ times `projectedPoincare` |
| `New.Data.projectedPoincare` | [180](lean:New/Reduction/ShortAndEnough.lean#L180) | definition: `goodPoincare` after `scaledInclusion` |
| `New.Data.scaledInclusion` | [174](lean:New/Reduction/ShortAndEnough.lean#L174) | definition: $c_{ss}^{-1}$ times the inclusion |
| `New.Data.seesawConst` | [170](lean:New/Reduction/ShortAndEnough.lean#L170) | `choose` of `seesaw_identity` |
| `New.Data.invGainFactor` | [93](lean:New/Reduction/ShortAndEnough.lean#L93) | definition |

These rows are proved in [the section from one translate to Theorem B](/chapter/proof-of-theorem-b/#from-one-translate-to-theorem-b).

### The ramified forms: ShortColumns.lean

| Declaration | Line | Chapter |
|---|---|---|
| `New.Data.ramifiedSourceForms` | [741](lean:New/UpperBound/Size/ShortColumns.lean#L741) | [the plan](/chapter/theorem-b-plan/#theorem-b-and-its-input) |
| `New.Data.le_finrank_ramifiedSourceForms` | [944](lean:New/UpperBound/Size/ShortColumns.lean#L944) | [the plan](/chapter/theorem-b-plan/#theorem-b-and-its-input) |
| `New.Data.f_div_N_sub_one_le` | [955](lean:New/UpperBound/Size/ShortColumns.lean#L955) | [the plan](/chapter/theorem-b-plan/#theorem-b-and-its-input) |

The bound for the ramified forms counts the kernel of $\prod_w(1 - z_w)$. Each factor has a kernel of dimension at most $D_X/(N - 1)$, and there are $f$ factors.

### The spanning theorem: SpanningTheorem.lean

The file New/Spanning/SecondMoment/SpanningTheorem.lean holds the five steps of the middle of the proof. The table lists them in the order of the file.

| Declaration | Line | Proof calls | Section |
|---|---|---|---|
| `New.Data.finrank_principalForms_spaceW` | [69](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L69) | `classAut_eq_bot_of_le_chosenLevel`, `classSum_one_of_le`, `relIndex_levelOf`, `classSum_stdRatPoints_eq_mass`, `Space.algFormEquiv`, `finrank_levelSpace_smoothFormRep`, `card_classes_eq_classSum`, `IsHCParam.prod_formalDegree` | [2](/chapter/proof-of-theorem-b/#the-dimension-of-the-target) |
| `New.Data.targetDim_le_card_mul_besselDegree_mul_mass` | [93](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L93) | `targetDim_eq_finrank_goodForms_spaceW`, `finrank_principalForms_spaceW`, `harish_chandra_degree_and_orbital` | [2](/chapter/proof-of-theorem-b/#the-dimension-of-the-target) |
| `New.Data.goodPoincare` | [120](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L120) | definition | [5](/chapter/proof-of-theorem-b/#one-translate) |
| `New.Data.levelRepresentation` | [125](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L125) | definition | [3](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes) |
| `New.Data.poincareScale` | [143](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L143) | definition | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.scaledPoincare` | [153](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L153) | definition | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.hasAmplitudeBlocks_scaledPoincare` | [168](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L168) | `poincare_eq_poincareMap_comp`, `hasAmplitudeBlocks_smul_of_inner_eq`, `petersson_poincare` | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.goodIdempotentAbove` | [184](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L184) | definition | [3](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes) |
| `New.Data.levelRepresentation_goodIdempotentAbove_eq` | [197](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L197) | `Equiv.piCurry`, `Finset.prod_univ_sum` | [3](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes) |
| `New.Data.re_coeff_one_sub_goodIdempotentAbove_le` | [221](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L221) | `re_coeff_one_sub_sum_tupleIdem_le`, five size bounds | [3](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes) |
| `New.Data.bad_types_rare` | [244](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L244) | the three lemmas above it | [3](/chapter/proof-of-theorem-b/#bad-types-at-the-level-primes) |
| `New.Data.isNearIsometry_e₀_comp_scaledPoincare` | [257](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L257) | `bad_types_rare`, `HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp` | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le` | [270](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L270) | `HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le` | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le` | [288](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L288) | `targetDim_le_card_mul_besselDegree_mul_mass`, `besselDegree_pos`, `mass_pos` | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.finrank_targetForms_ne_zero` | [307](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L307) | `IsNearIsometry.finrank_range_pos` | [4](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) |
| `New.Data.comap_scaledPoincare_eq_comap_goodPoincare` | [314](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L314) | `poincareScale_pos`, `Submodule.smul_mem_iff` | [5](/chapter/proof-of-theorem-b/#one-translate) |
| `New.Data.isSpread_goodPoincare` | [339](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L339) | `isSpread_of_second_moment`, `isCentralProj_e₀`, `IsNearIsometry.mono` | [5](/chapter/proof-of-theorem-b/#one-translate) |

### The inputs from other chapters

These are the results of other chapters that the two files above call. Each is proved in the chapter named.

| Declaration | File and line | Chapter |
|---|---|---|
| `New.isSpread_of_second_moment` | [FewTranslates.lean:320](lean:New/Spanning/SecondMoment/FewTranslates.lean#L320) | [few translates](/chapter/few-translates/#one-translate) |
| `New.IsSpread.exists_few_le_finrank_iSup_range` | [FewTranslates.lean:479](lean:New/Spanning/SecondMoment/FewTranslates.lean#L479) | [few translates](/chapter/few-translates/#the-greedy-cover) |
| `New.finrank_biSup_range_le` | [FewTranslates.lean:537](lean:New/Spanning/SecondMoment/FewTranslates.lean#L537) | [few translates](/chapter/few-translates/#the-greedy-cover) |
| `New.Data.targetDim_eq_finrank_goodForms_spaceW` | [EqualMultiplicities.lean:406](lean:New/Spanning/Multiplicities/EqualMultiplicities.lean#L406) | [equal multiplicities](/chapter/equal-multiplicities/#equal-traces-and-equal-multiplicities) |
| `New.re_coeff_one_sub_sum_tupleIdem_le` | [BadTypes.lean:228](lean:New/Spanning/MainTerm/BadTypes.lean#L228) | [equal multiplicities](/chapter/equal-multiplicities/#bad-types-are-rare) |
| `New.Data.exists_besselSystem` | [FillingData.lean:339](lean:New/Spanning/Bessel/FillingData.lean#L339) | [Bessel functions](/chapter/bessel-real-place/#the-bessel-system-of-the-data) |
| `New.Data.filling_fits` | [FillingAdmissible.lean:58](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L58) | [Poincaré series](/chapter/poincare-series/#the-data-are-admissible) |
| `New.Filling.Fits.petersson_poincare` | [PoincareSeries.lean:734](lean:New/Spanning/Unfolding/PoincareSeries.lean#L734) | [Poincaré series](/chapter/poincare-series/) |
| `New.Data.poincare_eq_poincareMap_comp` | [SeriesPeriod.lean:749](lean:New/Spanning/Unfolding/SeriesPeriod.lean#L749) | [Poincaré series](/chapter/poincare-series/#the-series-represents-the-period) |
| `New.Filling.hasAmplitudeBlocks_smul_of_inner_eq` | [Moments.lean:112](lean:New/Spanning/Unfolding/Moments.lean#L112) | [moments](/chapter/moments/#amplitude-blocks-and-the-bessel-translates) |
| `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le` | [Moments.lean:567](lean:New/Spanning/Unfolding/Moments.lean#L567) | [moments](/chapter/moments/#the-second-moment-over-the-whole-group) |
| `New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp` | [Moments.lean:1230](lean:New/Spanning/Unfolding/Moments.lean#L1230) | [moments](/chapter/moments/#good-forms) |

The instance `D.filling.IsAdmissible` ([FillingAdmissible.lean:743](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L743)) is the standing hypothesis of all results of `New.Filling` in this list. [The section on admissible data](/chapter/poincare-series/#the-data-are-admissible) proves it.

### The layers below the moments

The two theorems of Moments.lean at lines 567 and 1230 rest on the bounds of layer 4. The source reaches them through these files, and this book proves them in these chapters.

1. The identity terms and $\|L^*L - 1\|^2 \leq b^{-12}D_X$: New/Spanning/Unfolding/Moments.lean, in [the identity terms](/chapter/moments/#the-identity-terms).
2. The main term: New/Spanning/MainTerm, in [the main term](/chapter/main-term/), with the densities of [the real places](/chapter/real-densities/) and [the finite places](/chapter/finite-densities/), on the tools of [frames, depth and gains](/chapter/local-frames/).
3. The remaining terms: New/Spanning/RemainingTerms, in [the remaining terms](/chapter/remaining-terms/), with the counts of [reduced points and frame counts](/chapter/frame-counts/) and the sorting of [the anatomy of a term](/chapter/anatomy-of-a-term/).
4. The bounds over the open elements, $1 + 4b^{-4}$, and over the whole group, $1 + 9b^{-4}$: New/Spanning/Unfolding/MomentBounds.lean (lean:New/Spanning/Unfolding/MomentBounds.lean#L269), in [the second moment over the whole group](/chapter/moments/#the-second-moment-over-the-whole-group).

### The imports

The file ShortAndEnough.lean imports SpanningTheorem.lean and, for Theorem A, the files IntegralTargetForms, LocalDivisibility, SeesawIdentity and ArchimedeanSize. Theorem B takes three objects from these other imports. The first is the space of ramified source forms of ShortColumns.lean. The second is $c_B = D.\mathtt{invGainFactor}$, a product of powers of primes with exponents from `gainExponent`. The third is $c_{ss} = D.\mathtt{seesawConst}$, a unit chosen by `choose` from the existence statement `New.Data.seesaw_identity`. So the statement of Theorem B depends on the proof of the seesaw identity, because the choice needs that proof. The proof of Theorem B uses $c_B$ only through $c_B > 0$ and $c_{ss}$ only through $c_{ss} \neq 0$. No other result of the analysis of Theorem A enters the proof of Theorem B.

Lean accepts `New.Data.enough_forms`, if the reported checks of the source hold. This book does not claim more.
