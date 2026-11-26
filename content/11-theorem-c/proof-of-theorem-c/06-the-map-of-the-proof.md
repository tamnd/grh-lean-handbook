---
title: The map of the proof
lean:
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the proof

This section maps the proof of Theorem C to the declarations of the source. The first table lists the declarations of New/Determinant/Twist/LongForms.lean, in the order of the file. The second table lists the inputs from other files. The third part gives the tree of the proof. The line numbers are those of the pinned source. All paths are relative to grh/src.

### The file of the chapter

The file New/Determinant/Twist/LongForms.lean has eight declarations. Each row gives the declaration, its line, the results its proof calls, and the section of this chapter that states and proves it.

| Declaration | Line | Proof calls | Section |
|---|---|---|---|
| `IsAuxiliaryForm` | [43](lean:New/Determinant/Twist/LongForms.lean#L43) | a structure with two fields | 3 |
| `exists_span_isAuxiliaryForm_eq_top` | [59](lean:New/Determinant/Twist/LongForms.lean#L59) | `exists_span_short_lifts_eq_top`, `isRamifiedRatio_turnRatio`, `HasAbsUpToNormPower.exists_norm_div_eq`, `goodProjTranslate_mem_integralForms`, `normSqAt_goodProjTranslate_le`, `le_of_hasLogBound` | 3 |
| `HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio` | [108](lean:New/Determinant/Twist/LongForms.lean#L108) | `HasSmallRatios.heightLe_inv_rpow_mul_prod`, `isRamifiedRatio_turnRatio_of_mem` | 3 |
| `mul_completion_cost_le` | [120](lean:New/Determinant/Twist/LongForms.lean#L120) | `le_of_hasLogBound`, `gcongr`, `field` | 3 |
| `exists_hasSmallRatios_heightLe_liftDeterminant_div` | [139](lean:New/Determinant/Twist/LongForms.lean#L139) | `exists_isRegularFamily`, `heightLe_liftDeterminant_ratio` | 4 |
| `exists_chainDeterminant_one_div_eq` | [162](lean:New/Determinant/Twist/LongForms.lean#L162) | `exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` | 4 |
| `heightLe_chainDeterminant_one_div` | [180](lean:New/Determinant/Twist/LongForms.lean#L180) | `exists_chainDeterminant_one_div_eq`, `HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio`, `HeightLe.prod`, `HeightLe.pow`, `HeightLe.mul`, `le_of_hasLogBound` | 4 |
| `integral_forms_long` | [214](lean:New/Determinant/Twist/LongForms.lean#L214) | the five results above with `exists_extend_basis_of_span_eq_top`, `normSqAt_targetLattice`, `volume_targetLattice`, `injective_lift_targetLattice`, `covolume_add_index_nonneg`, `HeightLe.pow`, `le_of_hasLogBound` | 5 |

All the declarations are in the namespace `New.Data`. All take the data $D$ as a variable.

### The inputs from other files

Each row gives an input, its file and line, the chapter that proves it in this handbook, and the section of this chapter that states it. The chapters are named by their identifiers.

| Declaration | File and line | Chapter | Section |
|---|---|---|---|
| `New.HeightLe` | [Heights.lean, 41](lean:New/Reduction/Lattices/Heights.lean#L41) | twisted-lattices | 2 |
| `New.TwistedLattice.IndexLe` | [TwistedLattice.lean, 159](lean:New/Reduction/Lattices/TwistedLattice.lean#L159) | twisted-lattices | 2 |
| `New.TwistedLattice.CovolumeLe` | [TwistedLattice.lean, 275](lean:New/Reduction/Lattices/TwistedLattice.lean#L275) | twisted-lattices | 2 |
| `New.TwistedLattice.CovolumeLe.sumElim` | [TwistedLattice.lean, 330](lean:New/Reduction/Lattices/TwistedLattice.lean#L330) | twisted-lattices | 2 |
| `New.TwistedLattice.heightLe_pow_mul_det_gram` | [TwistedLattice.lean, 450](lean:New/Reduction/Lattices/TwistedLattice.lean#L450) | twisted-lattices | 2 |
| `New.TwistedLattice.covolume_add_index_nonneg` | [TwistedLattice.lean, 477](lean:New/Reduction/Lattices/TwistedLattice.lean#L477) | twisted-lattices | 2 |
| `New.Data.targetLattice` | [IntegralTargetForms.lean, 64](lean:New/Reduction/IntegralTargetForms.lean#L64) | integral-target-forms | 2 |
| `New.Data.normSqAt_targetLattice` | [IntegralTargetForms.lean, 102](lean:New/Reduction/IntegralTargetForms.lean#L102) | integral-target-forms | 2 |
| `New.Data.volume_targetLattice` | [IntegralTargetForms.lean, 108](lean:New/Reduction/IntegralTargetForms.lean#L108) | integral-target-forms | 2 |
| `New.Data.injective_lift_targetLattice` | [IntegralTargetForms.lean, 113](lean:New/Reduction/IntegralTargetForms.lean#L113) | integral-target-forms | 2 |
| `New.exists_extend_basis_of_span_eq_top` | [GramDeterminant.lean, 34](lean:Lib/General/LinearAlgebra/GramDeterminant.lean#L34) | none (general linear algebra) | 2 |
| `New.Data.lRatioProd` | [Moduli.lean, 57](lean:New/Determinant/Chain/Moduli.lean#L57) | chain-determinant | 3 |
| `New.Data.HasAbsUpToNormPower` | [Moduli.lean, 134](lean:New/Determinant/Chain/Moduli.lean#L134) | chain-determinant | 3 |
| `New.Data.HasAbsUpToNormPower.exists_norm_div_eq` | [Moduli.lean, 182](lean:New/Determinant/Chain/Moduli.lean#L182) | chain-determinant | 3 |
| `New.Data.IsRamifiedRatio` | [Moduli.lean, 218](lean:New/Determinant/Chain/Moduli.lean#L218) | chain-determinant | 3 |
| `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod` | [Moduli.lean, 227](lean:New/Determinant/Chain/Moduli.lean#L227) | chain-determinant | 3 |
| `New.Data.quotientRatio` | [Moduli.lean, 301](lean:New/Determinant/Chain/Moduli.lean#L301) | chain-determinant | 4 |
| `New.Data.turnRatio` | [Turns.lean, 607](lean:New/Determinant/AuxiliaryForms/Turns.lean#L607) | grids-paths-turns | 3 |
| `New.Data.isRamifiedRatio_turnRatio` | [Turns.lean, 637](lean:New/Determinant/AuxiliaryForms/Turns.lean#L637) | grids-paths-turns | 3 |
| `New.Data.exists_span_short_lifts_eq_top` | [SpanningForms.lean, 773](lean:New/Determinant/AuxiliaryForms/SpanningForms.lean#L773) | deep-level-poincare | 3 |
| `New.Data.goodProjTranslate_mem_integralForms` | [ArchimedeanSize.lean, 497](lean:New/UpperBound/Size/ArchimedeanSize.lean#L497) | archimedean-size | 3 |
| `New.Data.normSqAt_goodProjTranslate_le` | [ArchimedeanSize.lean, 526](lean:New/UpperBound/Size/ArchimedeanSize.lean#L526) | archimedean-size | 3 |
| `New.Data.denominatorBudget` | [FitTwists.lean, 153](lean:New/Determinant/Twist/FitTwists.lean#L153) | twists-critical-pairs | 4 |
| `New.Data.IsDenominatorBound` | [FitTwists.lean, 197](lean:New/Determinant/Twist/FitTwists.lean#L197) | twists-critical-pairs | 4 |
| `New.Data.HasSmallRatios` | [FitTwists.lean, 218](lean:New/Determinant/Twist/FitTwists.lean#L218) | twists-critical-pairs | 3 |
| `New.Data.IsRegularFamily` | [FitTwists.lean, 229](lean:New/Determinant/Twist/FitTwists.lean#L229) | twists-critical-pairs | 4 |
| `New.exists_isRegularFamily` | [FitTwistsExist.lean, 517](lean:New/Congruences/FitTwistsExist.lean#L517) | Volume 12 | 4 |
| `New.Data.heightLe_liftDeterminant_ratio` | [LiftVolumeHeight.lean, 729](lean:New/OneLift/LiftVolumeHeight.lean#L729) | lift-volume-height | 4 |
| `New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` | [NormOfChain.lean, 419](lean:New/Determinant/Chain/NormOfChain.lean#L419) | chain-determinant | 4 |
| `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` | [NormOfChain.lean, 436](lean:New/Determinant/Chain/NormOfChain.lean#L436) | chain-determinant | 4 |

The size inequalities all come from `New.Data.le_of_hasLogBound`, with the table of [the data and its sizes](/chapter/data-and-sizes/#the-table-of-sizes).

### The tree of the proof

The tree shows which result feeds which. An arrow $A \leftarrow B$ means that the proof of $A$ calls $B$. The leaves are the results of the other chapters.

1. Theorem C (`integral_forms_long`) $\leftarrow$ the frame, completion to a basis, the target lattice lemmas, and items 2, 3, 4, 5 and 6.
2. Single lifts at good twists $\leftarrow$ the existence of regular families (Volume 12) and the height of one lift determinant (chapter 16).
3. The inverse ratio $\leftarrow$ the inverted factorization and the scalar of the chain.
   - The inverted factorization $\leftarrow$ the factorization of the determinant (chapter 8).
   - The scalar of the chain $\leftarrow$ the height bound for quotient ratios (chapter 8).
4. Auxiliary forms $\leftarrow$ spanning forms with short lifts (chapter 11), the turn ratios (chapter 10), normalizing at the trivial twist (chapter 8), and the good part (Volume 9).
5. The scalar of the auxiliary forms $\leftarrow$ inverse products of ramified ratios (chapter 8) and the turn ratios (chapter 10).
6. The cost of completion $\leftarrow$ only the sizes.

The frame itself has its own tree in Volume 1. It uses the lattice inequality, adjoining short vectors, and the local bound ([twisted lattices](/chapter/twisted-lattices/#the-lattice-inequality)). The proof of the local bound uses the product formula through `New.HeightLe.neg_le_of_norm_map_le`.

### What the map shows

Three facts follow from the tables.

1. The proofs in the file of the chapter use no hypothesis beyond the data $D$. Every input is a declaration of another file that the source claims to prove.
2. The chapters 2 to 16 enter the proof through few declarations. Chapter 8 gives the most: the ratios, the normalization, the factorization and the two height bounds for products of ratios. Chapters 2, 10, 11 and 16 give the others. The remaining chapters enter only through the proofs of these declarations. The file LongForms.lean imports five files: FitTwistsExist, SpanningForms, LiftVolumeHeight, IntegralTargetForms and ArchimedeanSize.
3. Only one declaration of Volume 12 is used, `New.exists_isRegularFamily`. Its statement uses only definitions of chapter 2 of this volume. So the proof of Theorem C needs Volume 12 in Lean, but its statement and its use of the regular family can be read here.

**Remark.** The line numbers above are for the pinned source. A later version of the source can move them. The names stay the best reference.
