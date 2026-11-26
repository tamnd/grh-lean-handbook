---
title: Hypotheses and sizes
lean:
  - New/Reduction/Zeros/Criterion.lean
  - Lib/Analytic/EntireLFunction.lean
  - New/Reduction/Zeros/PrimeError.lean
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/OneLift/ComparisonOperator/ExchangeData.lean
  - New/Derivatives/Field/PrimeDecomposition.lean
  - New/Spanning/RemainingTerms/Sum.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/MainInequality.lean
  - New/Congruences/FitTwistsExist.lean
  - Lib/Weil/DualPair/GaloisLaw.lean
  - Lib/SiegelWeil/Formula/StrongApproximation.lean
  - Lib/SiegelWeil/RallisInner/Doubling.lean
  - Lib/General/Measure/QuadricDisintegration.lean
  - Lib/DiscreteSeries/Bruhat/FloorFibre.lean
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
  - New/Congruences/Lifting/CupProductBound.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Frames/FiniteShells.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
  - New/OneLift/HeckeValues/AlgebraicPartSize.lean
  - New/Derivatives/Vacuum/Divisibility.lean
  - Lib/Analytic/Primes.lean
  - New/Reduction/Data/Existence.lean
  - New/Reduction/Data/Sizes.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hypotheses and sizes

A theorem of the source is only as strong as its hypotheses are weak. This section lists the hypotheses that a reader must watch: hypotheses that the main theorem must discharge for every admissible choice, hypotheses that a structure bundles, hypotheses that a class or an instance supplies, and hypotheses that are never used. The second table lists the sizes: thresholds that two files state in two different forms, and bounds whose fit with the data has not been checked.

The general rule is this. A hypothesis of a theorem of `Lib` or `New` is harmless when every call site discharges it. Lean checks that each call site supplies a proof, so a discharged hypothesis is not a gap in the proof, if the reported checks hold. But a reader who reads one theorem alone does not see the call sites, and so does not see where the hypothesis comes from. A row of this section points to the place where it comes from, or says that no one has traced it.

### Hypotheses

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-076, explained | [New/Reduction/Zeros/Criterion.lean:37](lean:New/Reduction/Zeros/Criterion.lean#L37)-41 | The criterion asks the bound for every prime $d \equiv d_0 \bmod q_0$. The proof, from line 43 on, uses one $d$, chosen for the zero $\rho$. | The whole machine must run for every admissible $d$, but each run uses one $d$. | [landau-criterion](/chapter/landau-criterion/) |
| F-077, open | [Lib/Analytic/EntireLFunction.lean:76](lean:Lib/Analytic/EntireLFunction.lean#L76); [New/Reduction/Zeros/PrimeError.lean:414](lean:New/Reduction/Zeros/PrimeError.lean#L414) | `IsPolar` asks simple poles in $\operatorname{re} s > 0$ with residues $r$. `isPolar_primeRemainder` gives the residue as a sum of differences of orders of zeros. Its sign is the core of the method. | A person must check the residue and its sign line by line. | [polar-functions](/chapter/polar-functions/), [weighted-prime-remainder](/chapter/weighted-prime-remainder/) |
| F-078, explained | [New/Spanning/Unfolding/Setup.lean:501](lean:New/Spanning/Unfolding/Setup.lean#L501); [New/Spanning/Unfolding/FillingAdmissible.lean:743](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L743); [New/OneLift/ComparisonOperator/ExchangeData.lean:164](lean:New/OneLift/ComparisonOperator/ExchangeData.lean#L164) | `IsAdmissible` is the standing hypothesis of the unfolding. An instance discharges it for the data. `NeZero D.m` comes from `ten_thousand_le_m`. | Every theorem under the hypothesis is used with a proved instance. The bound $m \geq 10000$ is a standing size. | [poincare-series](/chapter/poincare-series/), [sizes](/chapter/sizes/) |
| F-079, open | [New/Derivatives/Field/PrimeDecomposition.lean:138](lean:New/Derivatives/Field/PrimeDecomposition.lean#L138); [New/Spanning/RemainingTerms/Sum.lean:67](lean:New/Spanning/RemainingTerms/Sum.lean#L67) | `HasPrimitiveRoot5040 E` is a hypothesis of many files. An instance gives it for `P.E s`. | It is not checked that this instance reaches the field $E$ of `enough_forms`. | [cm-fields](/chapter/cm-fields/), [proof-of-theorem-b](/chapter/proof-of-theorem-b/) |
| F-080, open | [New/Spanning/Unfolding/SeriesPeriod.lean:144](lean:New/Spanning/Unfolding/SeriesPeriod.lean#L144), 170, 258, 282, 406 | `hj_genericConst : WeilData.j * Y.genericConst = -(S.M * S.deltaE)⁻¹` is a hypothesis of five lemmas of the file. No use of these lemmas outside the file was found. | It is not traced where, or whether, the hypothesis is discharged for the data. | [poincare-series](/chapter/poincare-series/) |
| F-081, explained | [New/Determinant/Twist/LongForms.lean:43](lean:New/Determinant/Twist/LongForms.lean#L43), 214; [New/Reduction/MainInequality.lean:134](lean:New/Reduction/MainInequality.lean#L134) | `IsAuxiliaryForm` bundles integrality and a norm bound. `integral_forms_long` (Theorem C, line 214) takes four hypotheses. It is used once, in the main inequality. | Theorem C is conditional. The book must show where each hypothesis comes from. | [proof-of-theorem-c](/chapter/proof-of-theorem-c/) |
| F-082, explained | [New/Congruences/FitTwistsExist.lean:517](lean:New/Congruences/FitTwistsExist.lean#L517) | `exists_isRegularFamily` supplies the regular twists that Theorem C needs. | It is the only output of the folder `Congruences`. | [proof-of-regular-families](/chapter/proof-of-regular-families/) |
| F-083, explained | [Lib/Weil/DualPair/GaloisLaw.lean:214](lean:Lib/Weil/DualPair/GaloisLaw.lean#L214); `Lib/Weil/Seesaw.lean:663`; `New/Determinant/AuxiliaryForms/DiagonalTurns.lean:360` | `ScalesTranslations` is a structure of hypotheses. It is built in `New/UpperBound/Kernels/JetConjugatesAndBounds.lean` (line 85). `seesaw_periods` needs the span hypothesis `h_span`, and `DiagonalTurns` gives it. | The Galois law of `Lib` is proved from a structure that `New` discharges. | [weil-representation](/chapter/weil-representation/), [theta-lifts-seesaw](/chapter/theta-lifts-seesaw/) |
| F-084, open | [Lib/SiegelWeil/Formula/StrongApproximation.lean:162](lean:Lib/SiegelWeil/Formula/StrongApproximation.lean#L162); [Lib/SiegelWeil/RallisInner/Doubling.lean:121](lean:Lib/SiegelWeil/RallisInner/Doubling.lean#L121), 136 | `h_torus`, `IsClean` and `IsSharp` are hypotheses of the results of Siegel-Weil and of Rallis. | It is not checked that every call site discharges them in the intended way. | [siegel-weil](/chapter/siegel-weil/), [rallis-inner-product](/chapter/rallis-inner-product/) |
| F-085, explained | [Lib/General/Measure/QuadricDisintegration.lean:37](lean:Lib/General/Measure/QuadricDisintegration.lean#L37)-38, 50; `New/Spanning/MainTerm/FillingLevel.lean:424`; `Lib/PadicHodge/Limit/TraceLimit.lean:498` | The theorems of the file assume the class `Place` (line 50). A global instance `TraceOne` (lines 37-38) takes the element $2^{-1}$. `FillingLevel` builds a `Floors.Place`. `IsTraceLimit` bundles continuity, nondegeneracy of the trace, approximants, jumps and uniform convergence. | The disintegration is conditional on the class. The theorem on trace limits is proved from the structure. | [finite-densities](/chapter/finite-densities/), [kisin-frames](/chapter/kisin-frames/) |
| F-086, open | [Lib/DiscreteSeries/Bruhat/FloorFibre.lean:336](lean:Lib/DiscreteSeries/Bruhat/FloorFibre.lean#L336); `Lib/Adelic/QuotientMeasure/Basic.lean:574` | The hypotheses `_hq` and `_h_finite` are named as unused. The research notes say that instance search uses `_h_finite`. | A full list of unused hypotheses needs a build with the linter. | [reading-the-lean](/chapter/reading-the-lean/) |
| F-087, open | [New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean:324](lean:New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L324), 329 | `stdClassSum_gramForm_eq_zero` (line 324) assumes $2r + 2N + 3 < n$ as the explicit hypothesis `h_rank` (line 329), on the cardinalities of the index types. The bound is not part of `FitsParams`. | It is not checked against the stable range of the literature. | [false-lifts](/chapter/false-lifts/) |
| F-088, open | [New/Congruences/Lifting/CupProductBound.lean:1145](lean:New/Congruences/Lifting/CupProductBound.lean#L1145)-1147 | `killsCokernel_of_isUnramified` needs $5 \leq p$. | The handling of $p = 2$ and $p = 3$ is not traced. | [cup-products](/chapter/cup-products/) |
| F-089, explained | [New/UpperBound/Divisibility/LocalDivisibility.lean:494](lean:New/UpperBound/Divisibility/LocalDivisibility.lean#L494), 508 | `exists_err_gaugeLe_compositeLift` gives its bound only for twists with $p$ coprime to `ϑ.normQ`. | Later steps must use only such twists at $p$. | [divisibility](/chapter/divisibility/) |

### Sizes

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-090, explained | [New/Spanning/Unfolding/Setup.lean:113](lean:New/Spanning/Unfolding/Setup.lean#L113); [New/Spanning/Frames/RealPlaceGauge.lean:302](lean:New/Spanning/Frames/RealPlaceGauge.lean#L302); `New/Spanning/Bessel/FillingData.lean:260`; `New/Spanning/MainTerm/GlobalSieve.lean:847`, 1070 | `Filling` asks $10^5 \leq \varrho$. `RealPlaceSizes` asks $10^8 \leq \varrho$. `FillingData` builds `RealPlaceSizes` for the data. The sieve uses `ten_pow_five_le_varrho`. | The two thresholds differ. The stronger one holds for the data. The sieve needs only $\varrho \geq 10^5$. | [sizes](/chapter/sizes/), [main-term](/chapter/main-term/) |
| F-091, explained | [New/Spanning/Frames/RealPlaceGauge.lean:288](lean:New/Spanning/Frames/RealPlaceGauge.lean#L288)-302; [New/Spanning/Frames/FiniteShells.lean:58](lean:New/Spanning/Frames/FiniteShells.lean#L58) | `RealPlaceSizes` asks $\rho = b^{6n+2} \geq 8r$, $k = s + 3n + 6 \geq n^7$ and $s > 10^9 n^3$. `FiniteShells` has the hypotheses $r + 10^8 n^4 \leq k$ and $t + 10^{10} n^4 \leq k$ on its local variables $r$ and $t$. | These must fit with $k \leq f$ and with the field of the reduction. The $r$ of `FiniteShells` is a variable of the file, not the $r$ of the data. | [sizes](/chapter/sizes/), [real-densities](/chapter/real-densities/) |
| F-092, open | [New/Reduction/Data/AdmissibleData.lean:50](lean:New/Reduction/Data/AdmissibleData.lean#L50)-52 | `constantBound` adds `vacuumBoundConst`, $2d + 6$, $q_0$, the absolute Chowla-Selberg constant and cyclotomic terms. | The thresholds "for large $x$" depend on $d$. The criterion uses one $d$ at a time (F-076). | [data-and-sizes](/chapter/data-and-sizes/) |
| F-093, explained | [New/Reduction/Data/AdmissibleData.lean:111](lean:New/Reduction/Data/AdmissibleData.lean#L111)-117, 186, 311; [New/Spanning/Unfolding/Setup.lean:142](lean:New/Spanning/Unfolding/Setup.lean#L142) | $2^s = m^{22}$ and $q_1 = 3\, l_0\, m^{22} q_0$. `Filling` asks $b^{19} \leq M$. The lemma on the data uses $M$ in $[b^{20}, b^{22}]$ (line 311). | These fix the field $E$. The table of sizes of the book gives $[b^{20}, b^{22}]$. | [sizes](/chapter/sizes/) |
| F-094, open | [New/Congruences/FirstOrder/TraceRelations.lean:106](lean:New/Congruences/FirstOrder/TraceRelations.lean#L106)-109 | `denominatorError` contains $((4t + 1)\, h^{22} + h)$ times $v_\ell$ of `chosenGroupOrder`, with the half gap $h = r^8$. | It is not checked that this fits the budget for all admissible data. | [denominator-bound](/chapter/denominator-bound/) |
| F-095, open | [New/OneLift/HeckeValues/AlgebraicPartSize.lean:136](lean:New/OneLift/HeckeValues/AlgebraicPartSize.lean#L136); `New/Derivatives/Sharpness/BoundAttained.lean:381-382` | Every conjugate of the algebraic part is at most $\exp(x^{34})$. The weights $l$ lie in $[w, w + x^{42}]$, where $w$ is the base weight. | It is not known whether this is the bound of the original proof, and how much room it leaves. | [hecke-values](/chapter/hecke-values/), [sharpness](/chapter/sharpness/) |
| F-096, open | [New/Derivatives/Vacuum/Divisibility.lean:215](lean:New/Derivatives/Vacuum/Divisibility.lean#L215), 224 | `norm_jet_minorProd_jetSeries_le` has a factor $N^3$. | It must stay small against the main terms. No one has checked the budget. | [integral-vacuum](/chapter/integral-vacuum/) |
| F-097, open | [Lib/Analytic/Primes.lean:389](lean:Lib/Analytic/Primes.lean#L389); [New/Reduction/Data/Existence.lean:911](lean:New/Reduction/Data/Existence.lean#L911), 642-649 | `Existence` uses the prime theorem with the window $x^{\varepsilon/6}$ (lines 642-649) and $A = n + 7$. | It is not checked that the uniformity of the theorem is what the data need. | [primes-in-windows](/chapter/primes-in-windows/), [data-exist](/chapter/data-exist/) |
| F-098, explained | [New/Reduction/Data/Sizes.lean:161](lean:New/Reduction/Data/Sizes.lean#L161); [New/Reduction/Data/AdmissibleData.lean:28](lean:New/Reduction/Data/AdmissibleData.lean#L28)-29, 342; `New/Reduction/Data/LevelAndTwists.lean:234` | $\log h_E \leq x^{30}$. The minimal level has its logarithm in $[m \log b, 24\, m \log b]$. The level $N$ has $\log N$ in $[m \log b, 30\, m \log b]$. | The class number enters the table of sizes. The second range adds a small shift. It is not a conflict. | [sizes](/chapter/sizes/) |
| F-099, open | [New/UpperBound/Size/ArchimedeanSize.lean:436](lean:New/UpperBound/Size/ArchimedeanSize.lean#L436) | In `weylNormSq_compositeLift_le` the gain at small nonsplit primes enters with a factor $2$. | It is not known whether this is a real loss or whether it cancels in `ShortAndEnough`. | [archimedean-size](/chapter/archimedean-size/) |

### Reading the hypotheses

The hypotheses of the first table are of three kinds.

The first kind is a universal hypothesis of the main criterion. In F-076 the criterion of Landau's type asks the one-sided bound for every admissible $d$, but its proof uses one $d$ at a time. So the thresholds of the proof can depend on $d$, as F-092 shows, without any harm. A reader who reads "for $x$ large" in a chapter of the outline must read "for $x$ large in terms of $d$".

The second kind is a hypothesis that a structure, a class or an instance supplies. F-078, F-079, F-083 and F-085 are of this kind. Lean checks that the instance exists at each use. So the only question for a reader is which instance it is. In F-078 and F-083 the register has found the instance. In F-079 it has not traced the instance to the field of the main theorem on enough forms, and the row is open.

The third kind is an explicit hypothesis of a lemma whose discharge the register has not traced. F-080, F-084, F-087 and F-088 are of this kind. Each is a gap in the reading, not in the proof. Lean must have checked a proof of the hypothesis at every call site, if the reported checks hold. But the book cannot explain the argument until it knows where that proof is. For F-080 the five lemmas with the hypothesis are not used outside their file, as far as the register has found. So it is possible that they are not on the path of the main theorem. A dependency closure, as in F-008, would answer this.
