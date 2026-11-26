---
title: The map of the proof
lean:
  - New/Congruences/FitTwistsExist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the proof

This section maps the proof to the declarations of the source. The first table lists the declarations of New/Congruences/FitTwistsExist.lean, in the order of the file. The second table lists the inputs from other files. The third part gives the tree of the proof. The line numbers are those of the pinned source. All paths are relative to grh/src.

### The file of the chapter

The file has 535 lines and 19 declarations. It imports five files: `New.Congruences.FirstOrder.DenominatorBound`, `New.Congruences.GaloisRepresentations.RowsFromEigensystems`, `New.Congruences.Selmer.TwistingTheorem`, `New.Determinant.Chain.NormOfChain` and `New.OneLift.HeckeValues.CentralAction`. All declarations are in the namespace `New.Selmer`, except the main theorem, which is `New.exists_isRegularFamily`.

| Declaration | Line | Proof calls | Section |
|---|---|---|---|
| `DenominatorLe.clearsProjection` | [51](lean:New/Congruences/FitTwistsExist.lean#L51) | `card_rowIndex`, `gcongr` | 4 |
| `sum_padicValNat_mul_log_le` | [65](lean:New/Congruences/FitTwistsExist.lean#L65) | `factorization_def`, `log_nat_eq_sum_factorization`, `posLog_le_posLog` | 6 |
| `sum_half_pow_mul_log_le` | [78](lean:New/Congruences/FitTwistsExist.lean#L78) | `log_le_self`, `hasSum_coe_mul_geometric_of_norm_lt_one` | 6 |
| `prod_Ioc_natB_le_pow` | [90](lean:New/Congruences/FitTwistsExist.lean#L90) | `prod_le_pow_card`, `Nat.card_Ioc` | 6 |
| `sum_defectBound_mul_log_le` | [109](lean:New/Congruences/FitTwistsExist.lean#L109) | `prod_Ioc_natB_le_pow`, `sum_padicValNat_mul_log_le` | 6 |
| `sum_localDefectBound_mul_log_le` | [137](lean:New/Congruences/FitTwistsExist.lean#L137) | `sum_defectBound_mul_log_le`, `le_of_hasLogBound` | 6 |
| `isNegligible_padicValNat_oddClassBound` | [158](lean:New/Congruences/FitTwistsExist.lean#L158) | `sum_padicValNat_mul_log_le`, `oddClassBound_le`, `log_classNumber_le`, `le_of_hasLogBound` | 6 |
| `isNegligible_twistError` | [176](lean:New/Congruences/FitTwistsExist.lean#L176) | the two elementary sums, `le_of_hasLogBound` | 6 |
| `isNegligible_denominatorError` | [192](lean:New/Congruences/FitTwistsExist.lean#L192) | `denominatorError_eq_natCast`, `isNegligible_padicValNat_oddClassBound`, `sum_padicValNat_mul_log_le`, `le_of_hasLogBound` | 6 |
| `isNegligible_padicValNat_card_stdClasses` | [213](lean:New/Congruences/FitTwistsExist.lean#L213) | `card_stdClasses_le_exp`, `principalLevel_le_chosenLevel`, `nat_le_of_hasLogBound`, `sum_padicValNat_mul_log_le` | 6 |
| `sum_clearingBound_add_padicValNat_le` | [232](lean:New/Congruences/FitTwistsExist.lean#L232) | `sum_localDefectBound_mul_log_le`, the three negligible lemmas, `sum_padicValNat_mul_log_le`, `le_of_hasLogBound` | 6 |
| `isRepOfType_one` | [265](lean:New/Congruences/FitTwistsExist.lean#L265) | `localConditions_char_of_finite_image_inertia`, `aroots_X_sub_C` | 3 |
| `exists_isMainSummand_mainPair` | [297](lean:New/Congruences/FitTwistsExist.lean#L297) | `exists_isMainSummand_of_isRepOfType`, `isLiftSetting_mainPair`, `isRepOfType_one`, `isMainSummandWeights_mainPair` | 3 |
| `range_goodLift_le_span_hasLiftHeckePolynomial` | [326](lean:New/Congruences/FitTwistsExist.lean#L326) | `range_goodLift_le`, `goodForms_inf_eigenPart_eq_bot_of_eq_bot`, `hasLiftHeckePolynomial_singleLift`, `isLiftSetting_descentPair`, `range_tupleIdem_le` | 3 |
| `exists_mFoldTwist_selmerLengthLe_inv_ratio_le` | [377](lean:New/Congruences/FitTwistsExist.lean#L377) | `exists_mFoldTwist_hasDivisibleSelmerLengthLe`, `norm_inv_le_exp_of_ellVal_le` | 5 |
| `denominatorLe_range_goodLift` | [415](lean:New/Congruences/FitTwistsExist.lean#L415) | `toAutChar_one_and_toTwist_one_and_Q_one`, `denominatorLe_clearingBound`, `range_goodLift_le_span_hasLiftHeckePolynomial` | 4 |
| `denominatorLe_span_trivialLift` | [444](lean:New/Congruences/FitTwistsExist.lean#L444) | `toAutChar_one_and_toTwist_one_and_Q_one`, `denominatorLe_clearingBound`, `isLiftSetting_mainPair`, `hasLiftHeckePolynomial_trivialLift`, `trivialLift_mem_range_typeProjection` | 4 |
| `exists_mFoldTwist_hasDenominatorsLe` | [475](lean:New/Congruences/FitTwistsExist.lean#L475) | `finite_setOf_inf_eigenPart_ne_bot`, `exists_isMainSummand_descentPair`, `exists_isMainSummand_mainPair`, `exists_mFoldTwist_selmerLengthLe_inv_ratio_le`, `coprime_prod_q_of_isAuxiliary`, `denominatorLe_range_goodLift`, `classAut_eq_bot_of_le_chosenLevel`, `clearsProjection`, `denominatorLe_span_trivialLift`, `norm_inner_starProjection_le` | 5 |
| `exists_isRegularFamily` | [517](lean:New/Congruences/FitTwistsExist.lean#L517) | `exists_mFoldTwist_hasDenominatorsLe`, `isNegligible_twistError`, `le_of_hasLogBound`, `HeightLe.of_le`, `sum_clearingBound_add_padicValNat_le` | 7 |

### The inputs from other files

Each row gives the input, its file and line, and the section of this chapter that states it. The last column names the chapter that proves it.

| Input | File and line | Here | Proved in |
|---|---|---|---|
| `exists_mFoldTwist_hasDivisibleSelmerLengthLe` | [Selmer/TwistingTheorem.lean:370](lean:New/Congruences/Selmer/TwistingTheorem.lean#L370) | 2 | [the twisting theorem](/chapter/twisting-theorem/) |
| `norm_inv_le_exp_of_ellVal_le` | [Selmer/TwistingTheorem.lean:55](lean:New/Congruences/Selmer/TwistingTheorem.lean#L55) | 2 | this chapter, Section 2 |
| `exists_isMainSummand_descentPair` | [RowsFromEigensystems.lean:480](lean:New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean#L480) | 2 | [main summands](/chapter/main-summands/) |
| `exists_isMainSummand_of_isRepOfType` | [RowsFromEigensystems.lean:391](lean:New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean#L391) | 2 | [main summands](/chapter/main-summands/) |
| `isMainSummandWeights_mainPair` | [RowsFromEigensystems.lean:202](lean:New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean#L202) | 2 | [main summands](/chapter/main-summands/) |
| `isLiftSetting_descentPair` | [AttachedRepresentations.lean:81](lean:New/Congruences/GaloisRepresentations/AttachedRepresentations.lean#L81) | 2 | [main summands](/chapter/main-summands/) |
| `isLiftSetting_mainPair` | [AttachedRepresentations.lean:123](lean:New/Congruences/GaloisRepresentations/AttachedRepresentations.lean#L123) | 2 | [main summands](/chapter/main-summands/) |
| `trivialLift_mem_range_typeProjection` | [AttachedRepresentations.lean:151](lean:New/Congruences/GaloisRepresentations/AttachedRepresentations.lean#L151) | 2 | [main summands](/chapter/main-summands/) |
| `localConditions_char_of_finite_image_inertia` | [Lib/PadicHodge/Characters.lean:993](lean:Lib/PadicHodge/Characters.lean#L993) | 2 | [tied traces](/chapter/tied-traces/) |
| `denominatorLe_clearingBound` | [FirstOrder/DenominatorBound.lean:1321](lean:New/Congruences/FirstOrder/DenominatorBound.lean#L1321) | 2 | [from a congruence to a Selmer class](/chapter/denominator-bound/) |
| `range_goodLift_le` | [Chain/NormOfChain.lean:499](lean:New/Determinant/Chain/NormOfChain.lean#L499) | 2 | [the chain determinant](/chapter/chain-determinant/) |
| `range_tupleIdem_le` | [Chain/NormOfChain.lean:454](lean:New/Determinant/Chain/NormOfChain.lean#L454) | 2 | [the chain determinant](/chapter/chain-determinant/) |
| `goodForms_inf_eigenPart_eq_bot_of_eq_bot` | [EqualMultiplicities.lean:398](lean:New/Spanning/Multiplicities/EqualMultiplicities.lean#L398) | 2 | [equal multiplicities](/chapter/equal-multiplicities/) |
| `finite_setOf_inf_eigenPart_ne_bot` | [HeckeEigensystems.lean:438](lean:New/Spanning/Multiplicities/HeckeEigensystems.lean#L438) | 2 | [equal multiplicities](/chapter/equal-multiplicities/) |
| `hasLiftHeckePolynomial_singleLift` | [Norms/AdjointThetaLift.lean:1030](lean:New/Determinant/Norms/AdjointThetaLift.lean#L1030) | 2 | [single theta lifts](/chapter/single-theta-lifts/) |
| `LValueData.hasLiftHeckePolynomial_trivialLift` | [CharacterLiftNorm.lean:215](lean:New/OneLift/HeckeValues/CharacterLiftNorm.lean#L215) | 2 | [character lifts](/chapter/character-lifts/) |
| `toAutChar_one_and_toTwist_one_and_Q_one` | [Twist/FitTwists.lean:69](lean:New/Determinant/Twist/FitTwists.lean#L69) | 2 | [twists and critical pairs](/chapter/twists-critical-pairs/) |
| `DenominatorLe.norm_inner_starProjection_le` | [CentralAction.lean:324](lean:New/OneLift/HeckeValues/CentralAction.lean#L324) | 2 | [Hecke values](/chapter/hecke-values/) |
| `coprime_prod_q_of_isAuxiliary` | [Selmer/ClassSums.lean:390](lean:New/Congruences/Selmer/ClassSums.lean#L390) | 2 | [the twisting theorem](/chapter/twisting-theorem/) |
| `classAut_eq_bot_of_le_chosenLevel` | [LiftChains.lean:535](lean:New/UpperBound/Objects/LiftChains.lean#L535) | 2 | [upper bound objects](/chapter/upper-bound-objects/) |
| `HeightLe.of_le` | [Lattices/Heights.lean:125](lean:New/Reduction/Lattices/Heights.lean#L125) | 2 | [twisted lattices](/chapter/twisted-lattices/) |
| `le_of_hasLogBound`, `nat_le_of_hasLogBound` | [Magnitudes.lean:405](lean:New/Reduction/Data/Magnitudes.lean#L405), [411](lean:New/Reduction/Data/Magnitudes.lean#L411) | 2 | [data and sizes](/chapter/data-and-sizes/) |
| `finite_criticalPair` | [ChosenPlaces.lean:307](lean:New/Derivatives/Field/ChosenPlaces.lean#L307) | 3 | [the field at the primes](/chapter/field-at-primes/) |
| `card_rowIndex` | [LabelsAndIndexTypes.lean:275](lean:New/UpperBound/Objects/LabelsAndIndexTypes.lean#L275) | 4 | [upper bound objects](/chapter/upper-bound-objects/) |
| `oddClassBound_le` | [TraceRelations.lean:82](lean:New/Congruences/FirstOrder/TraceRelations.lean#L82) | 6 | [from a congruence to a Selmer class](/chapter/denominator-bound/) |
| `log_classNumber_le` | [Data/Sizes.lean:161](lean:New/Reduction/Data/Sizes.lean#L161) | 6 | [data and sizes](/chapter/data-and-sizes/) |
| `card_stdClasses_le_exp` | [Size/Estimates.lean:303](lean:New/UpperBound/Size/Estimates.lean#L303) | 6 | [the archimedean size](/chapter/archimedean-size/) |
| `principalLevel_le_chosenLevel` | [LiftChains.lean:510](lean:New/UpperBound/Objects/LiftChains.lean#L510) | 6 | [upper bound objects](/chapter/upper-bound-objects/) |

### The tree of the proof

Each line is a result. The lines below it, indented, are the results that its proof uses. The inputs from other files are marked with an asterisk.

```
exists_isRegularFamily                                     (Section 7)
  exists_mFoldTwist_hasDenominatorsLe                      (Section 5)
    finite_setOf_inf_eigenPart_ne_bot *
    exists_isMainSummand_descentPair *
    exists_isMainSummand_mainPair                          (Section 3)
      exists_isMainSummand_of_isRepOfType *
      isLiftSetting_mainPair *
      isRepOfType_one                                      (Section 3)
        localConditions_char_of_finite_image_inertia *
      isMainSummandWeights_mainPair *
    exists_mFoldTwist_selmerLengthLe_inv_ratio_le          (Section 5)
      exists_mFoldTwist_hasDivisibleSelmerLengthLe *
      norm_inv_le_exp_of_ellVal_le *
    coprime_prod_q_of_isAuxiliary *
    denominatorLe_range_goodLift                           (Section 4)
      denominatorLe_clearingBound *
      range_goodLift_le_span_hasLiftHeckePolynomial        (Section 3)
        range_goodLift_le *
        goodForms_inf_eigenPart_eq_bot_of_eq_bot *
        hasLiftHeckePolynomial_singleLift *
        isLiftSetting_descentPair *
        range_tupleIdem_le *
    classAut_eq_bot_of_le_chosenLevel *
    DenominatorLe.clearsProjection                         (Section 4)
    denominatorLe_span_trivialLift                         (Section 4)
      denominatorLe_clearingBound *
      isLiftSetting_mainPair *
      hasLiftHeckePolynomial_trivialLift *
      trivialLift_mem_range_typeProjection *
    DenominatorLe.norm_inner_starProjection_le *
  isNegligible_twistError                                  (Section 6)
    sum_padicValNat_mul_log_le, sum_half_pow_mul_log_le    (Section 6)
  HeightLe.of_le *
  sum_clearingBound_add_padicValNat_le                     (Section 6)
    sum_localDefectBound_mul_log_le                        (Section 6)
      sum_defectBound_mul_log_le                           (Section 6)
        prod_Ioc_natB_le_pow                               (Section 6)
    isNegligible_twistError                                (Section 6)
    isNegligible_denominatorError                          (Section 6)
      isNegligible_padicValNat_oddClassBound               (Section 6)
        oddClassBound_le *, log_classNumber_le *
    isNegligible_padicValNat_card_stdClasses               (Section 6)
      card_stdClasses_le_exp *, principalLevel_le_chosenLevel *
```

The tree has two branches. The first branch, under `exists_mFoldTwist_hasDenominatorsLe`, works at one prime and uses all the Galois theory of the volume. The second branch, the sums, uses only the factorization of integers and the sizes of the data. The two branches meet only in Steps 2 and 4 of Section 7. There the bounds $e'_\ell$ and $\gamma_\ell$ of the first branch are summed by the second.
