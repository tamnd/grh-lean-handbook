---
title: The map of the proof
lean:
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the proof

This section maps the proof of Theorem A to the source. The first table lists the declarations of part A of New/Reduction/ShortAndEnough.lean in the order of the file. The second table lists the inputs from other files. The last subsection gives the proof as a tree. The line numbers are those of the pinned source.

### The declarations of the file

All names are in the namespace `New.Data`. The column "uses" lists the results that the proof calls, other than rewriting lemmas of Mathlib.

| Declaration | Line | Uses | Section |
|---|---|---|---|
| `divisibilityError` | [41](lean:New/Reduction/ShortAndEnough.lean#L41) | `exists_err_gaugeLe_compositeLift` (choose) | 4 |
| `divisibilityError_nonneg` | [43](lean:New/Reduction/ShortAndEnough.lean#L43) | choose_spec, part 1 | 4 |
| `divisibilityError_eq_zero` | [49](lean:New/Reduction/ShortAndEnough.lean#L49) | choose_spec, part 2 | 4 |
| `sum_divisibilityError_mul_log_le` | [56](lean:New/Reduction/ShortAndEnough.lean#L56) | choose_spec, part 3 | 4 |
| `exists_colengthDvd_gaugeLe_divisibilityError` | [74](lean:New/Reduction/ShortAndEnough.lean#L74) | choose_spec, part 4 | 4 |
| `gainExponent` | [89](lean:New/Reduction/ShortAndEnough.lean#L89) | `gain`, `divisibilityError` | 4 |
| `invGainFactor` | [93](lean:New/Reduction/ShortAndEnough.lean#L93) | `smallNonsplitPrimes`, `gainExponent` | 4 |
| `prime_of_mem_smallNonsplitPrimes_union` | [98](lean:New/Reduction/ShortAndEnough.lean#L98) | primality of $N$ | 4 |
| `invGainFactor_pos` | [106](lean:New/Reduction/ShortAndEnough.lean#L106) | the previous lemma | 4 |
| `sum_log_smallNonsplitPrimes_union_le` | [112](lean:New/Reduction/ShortAndEnough.lean#L112) | `le_of_hasLogBound` | 4 |
| `log_invGainFactor_le` | [127](lean:New/Reduction/ShortAndEnough.lean#L127) | `gain_eq_zero`, `sum_divisibilityError_mul_log_le`, the previous lemma | 4 |
| `norm_invGainFactor` | [153](lean:New/Reduction/ShortAndEnough.lean#L153) | `chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes`, `gain_eq_zero`, `divisibilityError_eq_zero` | 4 |
| `seesawConst` | [170](lean:New/Reduction/ShortAndEnough.lean#L170) | `seesaw_identity` (choose) | 5 |
| `scaledInclusion` | [174](lean:New/Reduction/ShortAndEnough.lean#L174) | `seesawConst` | 5 |
| `projectedPoincare` | [180](lean:New/Reduction/ShortAndEnough.lean#L180) | `goodPoincare`, `scaledInclusion` | 5 |
| `normalizedPoincare` | [185](lean:New/Reduction/ShortAndEnough.lean#L185) | `invGainFactor`, `projectedPoincare` | 5 |
| `coe_normalizedPoincare` | [191](lean:New/Reduction/ShortAndEnough.lean#L191) | the centrality of $e_0$ | 5 |
| `integralRamified` | [208](lean:New/Reduction/ShortAndEnough.lean#L208) | `integralSourceForms` | 1 |
| `exists_lowerChain_poincare_eq` | [217](lean:New/Reduction/ShortAndEnough.lean#L217) | `seesaw_identity` (choose_spec) | 5 |
| `normSqAt_normalizedPoincare` | [231](lean:New/Reduction/ShortAndEnough.lean#L231) | `invGainFactor_pos`, the homogeneity of the Weyl norm | 5 |
| `span_short_integralRamified_eq_top` | [254](lean:New/Reduction/ShortAndEnough.lean#L254) | see the tree | 6 |
| `finrank_sourceForm_le_two_mul` | [290](lean:New/Reduction/ShortAndEnough.lean#L290) | `f_div_N_sub_one_le`, `le_finrank_ramifiedSourceForms` | 7 |
| `normalizedPoincare_mem_integralVectors` | [304](lean:New/Reduction/ShortAndEnough.lean#L304) | see the tree | 7 |
| `indexLe_of_mem_image_normalizedPoincare` | [342](lean:New/Reduction/ShortAndEnough.lean#L342) | see the tree | 7 |
| `indexLe_normalizedPoincare` | [373](lean:New/Reduction/ShortAndEnough.lean#L373) | `indexLe_card_mul`, the previous lemma | 7 |

Part B of the file starts at line 386 with `range_normalizedPoincare`. [The proof of Theorem B](/chapter/proof-of-theorem-b/) explains it.

### The inputs from other files

| Input | File and line | Proved in | Stated in |
|---|---|---|---|
| `exists_err_gaugeLe_compositeLift` | [LocalDivisibility.lean:494](lean:New/UpperBound/Divisibility/LocalDivisibility.lean#L494) | [the four cases](/chapter/divisibility/#the-four-cases) | 2 |
| `seesaw_identity` | [SeesawIdentity.lean:624](lean:New/UpperBound/Seesaw/SeesawIdentity.lean#L624) | [the assembly](/chapter/seesaw-identity-2/#the-assembly-and-the-seesaw-identity) | 2 |
| `weylNormSq_compositeLift_le` | [ArchimedeanSize.lean:436](lean:New/UpperBound/Size/ArchimedeanSize.lean#L436) | [the size of the composite lift](/chapter/archimedean-size/#the-size-of-the-composite-lift) | 2 |
| `goodProjTranslate_mem_integralForms` | [ArchimedeanSize.lean:497](lean:New/UpperBound/Size/ArchimedeanSize.lean#L497) | [the good part](/chapter/archimedean-size/#the-good-part) | 2 |
| `normSqAt_goodProjTranslate_le` | [ArchimedeanSize.lean:526](lean:New/UpperBound/Size/ArchimedeanSize.lean#L526) | [the good part](/chapter/archimedean-size/#the-good-part) | 2 |
| `span_isShort_ramifiedSourceForms_eq_top` | [ShortColumns.lean:1002](lean:New/UpperBound/Size/ShortColumns.lean#L1002) | [short ramified forms span](/chapter/short-columns-gain/#short-ramified-forms-span) | 2 |
| `le_finrank_ramifiedSourceForms` | [ShortColumns.lean:944](lean:New/UpperBound/Size/ShortColumns.lean#L944) | [scalings and ramified forms](/chapter/short-columns-gain/#scalings-and-ramified-forms) | 2 |
| `f_div_N_sub_one_le` | [ShortColumns.lean:955](lean:New/UpperBound/Size/ShortColumns.lean#L955) | [scalings and ramified forms](/chapter/short-columns-gain/#scalings-and-ramified-forms) | 2 |
| `gain_eq_zero` | [Estimates.lean:92](lean:New/UpperBound/Size/Estimates.lean#L92) | [prime sums and allowed losses](/chapter/archimedean-size/#prime-sums-and-allowed-losses) | 2 |
| `GaugeLe.zpow_neg_smul` | [LocalDivisibility.lean:116](lean:New/UpperBound/Divisibility/LocalDivisibility.lean#L116) | Section 3 | 3 |
| `ColengthDvd.comap` | [Colength.lean:64](lean:New/Reduction/Lattices/Colength.lean#L64) | [colength](/chapter/twisted-lattices/#colength) | 3 |
| `ColengthDvd.map` | [Colength.lean:74](lean:New/Reduction/Lattices/Colength.lean#L74) | [colength](/chapter/twisted-lattices/#colength) | 3 |
| `TwistedLattice.indexLe_of_colengthDvd` | [TwistedLattice.lean:188](lean:New/Reduction/Lattices/TwistedLattice.lean#L188) | [colength](/chapter/twisted-lattices/#colength) | 3 |
| `TwistedLattice.indexLe_card_mul` | [TwistedLattice.lean:220](lean:New/Reduction/Lattices/TwistedLattice.lean#L220) | [twisted lattices](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume) | 3 |
| `mem_integralVectors_targetLattice` | [IntegralTargetForms.lean:90](lean:New/Reduction/IntegralTargetForms.lean#L90) | [the target lattice](/chapter/integral-target-forms/#the-target-lattice) | 3 |
| `goodPoincare` | [SpanningTheorem.lean:120](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L120) | Volume 10 | 5 |
| `goodProjTranslate` | [FillingAdmissible.lean:132](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L132) | Volume 10 | 5 |
| `poincare` | [SeriesPeriod.lean:743](lean:New/Spanning/Unfolding/SeriesPeriod.lean#L743) | Volume 10 | 5 |
| `Θ` | [NormOfChain.lean:95](lean:New/Determinant/Chain/NormOfChain.lean#L95) | Volume 11 | 5 |

The last four are definitions. Their names are in `New.Data`, and so are the inputs without a prefix in the first column. The prefixes `GaugeLe`, `ColengthDvd` and `TwistedLattice` are in the namespace `New`.

### The tree of part (a)

The tree reads from the top down. Each line is a step, and the indented lines are its inputs.

1. Theorem A (a), `span_short_integralRamified_eq_top`.
    1. Short ramified forms span src, `span_isShort_ramifiedSourceForms_eq_top`. This reduces to one short form $\varphi$.
    2. Integrality of $\varphi$ at each $\iota$: property (I) of a short form.
    3. Seesaw identity for the trivial twist, `exists_lowerChain_poincare_eq 1`.
        1. `seesaw_identity` at the Bessel form and the Bessel point, with $c = c_{ss}$.
    4. Size of the chain, `weylNormSq_compositeLift_le`, with $B = \mathrm{err}_0$ from property (S).
    5. Size of the good part, `normSqAt_goodProjTranslate_le`. Adds $x^{99}$.
    6. Factor $c_B$ at infinity, `normSqAt_normalizedPoincare`. Adds $2\log c_B$.
    7. Bound for $\log c_B$, `log_invGainFactor_le`.
        1. Vanishing gain at $N$, `gain_eq_zero`.
        2. Property 3 of the errors, `sum_divisibilityError_mul_log_le`.
        3. Logarithms of the primes, `sum_log_smallNonsplitPrimes_union_le`.
    8. Size inequality (E), `le_of_hasLogBound`.

### The tree of part (b)

1. Theorem A (b), `indexLe_normalizedPoincare`.
    1. Index of a union, `TwistedLattice.indexLe_card_mul`.
    2. Index of one translate, `indexLe_of_mem_image_normalizedPoincare`.
        1. Index from colength, `TwistedLattice.indexLe_of_colengthDvd`, with $e(\ell) = D_X\,\mathrm{err}(\ell)$.
        2. Nonnegativity, `divisibilityError_nonneg`.
        3. The sum: `sum_divisibilityError_mul_log_le` and `finrank_sourceForm_le_two_mul`.
            1. `f_div_N_sub_one_le` and `le_finrank_ramifiedSourceForms`.
        4. The colength at $\iota$: `exists_colengthDvd_gaugeLe_divisibilityError`.
        5. Pull back, `ColengthDvd.comap`.
            1. Integral images, `normalizedPoincare_mem_integralVectors`.
                1. Integral target forms, `mem_integralVectors_targetLattice`.
                2. Seesaw identity for $\vartheta$, `exists_lowerChain_poincare_eq`.
                3. Removing a power, `GaugeLe.zpow_neg_smul`.
                4. Gain factor at a prime, `norm_invGainFactor`.
                5. Good part keeps integrality, `goodProjTranslate_mem_integralForms`.
        6. Push forward, `ColengthDvd.map`.

### Where the constants enter

| Constant | Where it is defined | Where it is used |
|---|---|---|
| $\mathrm{err}_0 = f a\log^3 b$ | `New.Data.errorUnit`, [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes) | short forms, size of the chain, property 3 |
| $x^{99}$ | the size of the good part | Step 4 of part (a) |
| $b$ | the bound for $\sum\log\ell$ | the floors in $c_B$, part (a) |
| $f a\log^4 b$ | the statement of part (a) | absorbs $x^{99} + 4\,\mathrm{err}_0 + 2b$ |
| $D_X\,\mathrm{err}(\ell)$ | property 4 | the exponent $e(\ell)$ of part (b) |
| $2$ | `finrank_sourceForm_le_two_mul` | the bound of part (b) |
| $\#t$ | the set of translates | the bound of part (b) |

The two parts share one object: the function $\mathrm{err}$. In part (a) it enters through $\log c_B$ and is bounded by property 3. In part (b) it enters through the colength and is bounded by property 3 again. The same bound $\mathrm{err}_0$ appears in both, so the size and the index are bounded by the same unit of loss.
