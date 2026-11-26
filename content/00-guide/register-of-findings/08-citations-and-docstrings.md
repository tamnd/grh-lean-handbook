---
title: Citations and docstrings
lean:
  - Lib/Analytic/Primes.lean
  - Lib/Analytic/QuadraticTwist.lean
  - Lib/Weil/DualPair/GaloisLaw.lean
  - New/Congruences/Lifting/SafeMoves.lean
  - New/Congruences/Lifting/CutExponentBounds.lean
  - New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean
  - New/Spanning/Frames/BesselVector.lean
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Derivatives/FormalGroup/Exponent.lean
  - Lib/Cohomology/PointClass/LinearIndependence.lean
  - Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean
  - New/Reduction/ShortAndEnough.lean
  - Main.lean
  - New/Determinant/Twist/FitTwists.lean
  - Lib/Cohomology/WoodsHole.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Sizes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Citations and docstrings

The source cites the literature in its file heads and in `grh/REFERENCES.md`. It explains itself in docstrings, in the heads of files, in `grh/GUIDE.md` and in `grh/INDEX.md`. All of this text has the same author as the code (F-002), and no person has checked it. This section lists the places where a reader must not take the text at its word: citations that no one has compared with the cited work, citations of works that the file does not use, and documents that say more or less than the Lean text.

The rule of the book is simple. Where a document and the Lean text disagree, the book follows the Lean text, because the kernel checks the Lean text and checks no document. Where a citation has not been checked, the book reports it as a citation of the source, and does not present it as the origin of the argument.

### Citations

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-100, open | `grh/REFERENCES.md:3-8`; `grh/INDEX.md:29` | Of 228 compared citations, 66 have a confirmed place, 35 have a place at second hand, 119 have a found work with no place, and 8 were not compared. The last column of the tables of `INDEX.md` is headed "related work". | Most citations do not give a checked theorem number. A related work is not the source of a proof. | [claim-and-status](/chapter/claim-and-status/) |
| F-101, open | `grh/REFERENCES.md:10`, 244 and after | The citations of 122 files were not checked, and 68 of these files give places. The list includes `Lib/Analytic/Landau` and `Lib/Analytic/ZeroSymmetry`. | Core analytic files have unchecked sources. | [claim-and-status](/chapter/claim-and-status/) |
| F-102, explained | [Lib/Analytic/Primes.lean:22](lean:Lib/Analytic/Primes.lean#L22)-25 | The file cites Montgomery and Vaughan, Corollary 11.19, but proves a weaker result by another method (F-066). | The book must cite the method that the file uses, not only the theorem that it names. | [primes-in-windows](/chapter/primes-in-windows/) |
| F-103, open | [Lib/Analytic/QuadraticTwist.lean:42](lean:Lib/Analytic/QuadraticTwist.lean#L42)-43, 533; `grh/REFERENCES.md:62`, 159 | Jutila (1975) and Heath-Brown (1995) are cited with no place. The file replaces the large sieve of Heath-Brown by a weaker count. | See F-067. The faithfulness of the zero-density input to these works is not checked. | [polya-vinogradov](/chapter/polya-vinogradov/) |
| F-104, open | [Lib/Weil/DualPair/GaloisLaw.lean:38](lean:Lib/Weil/DualPair/GaloisLaw.lean#L38)-39; [New/Congruences/Lifting/SafeMoves.lean:46](lean:New/Congruences/Lifting/SafeMoves.lean#L46); [New/Congruences/Lifting/CutExponentBounds.lean:63](lean:New/Congruences/Lifting/CutExponentBounds.lean#L63); [New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean:52](lean:New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean#L52) | Recent preprints are cited: Trias, arXiv 2601.16141, and several works dated 2026. | These sources are new and not refereed. The book must say which results of these files are new. | [regular-families-plan](/chapter/regular-families-plan/), [theta-lifts-seesaw](/chapter/theta-lifts-seesaw/) |
| F-105, open | [New/Spanning/Frames/BesselVector.lean:39](lean:New/Spanning/Frames/BesselVector.lean#L39); [New/Spanning/Frames/RealPlaceGauge.lean:60](lean:New/Spanning/Frames/RealPlaceGauge.lean#L60) | The 22 files of `Frames` point to other files for related work and cite almost nothing. | It is not known whether the methods are new or adapted. | [real-densities](/chapter/real-densities/), [finite-densities](/chapter/finite-densities/) |
| F-106, open | `grh/GUIDE.md:62` | The grids, paths and $m^2$ turns have no cited source in the guide. | It decides how much exposition the chapter needs. It is not known whether the combinatorics is new. | [grids-paths-turns](/chapter/grids-paths-turns/) |
| F-107, explained | `grh/ATTRIBUTION.md`; [New/Derivatives/FormalGroup/Exponent.lean:37](lean:New/Derivatives/FormalGroup/Exponent.lean#L37)-41 | `ATTRIBUTION.md` lists the declarations that adapt definitions, statements or proofs of Mathlib. The head of `Exponent.lean` names earlier bounds of Bannai and Kobayashi "which are not used". | These declarations are not original to the project. A cited work is not always an input of the proof. | [claim-and-status](/chapter/claim-and-status/), [cm-formal-group](/chapter/cm-formal-group/) |

### Documents against code

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-108, explained | `grh/INDEX.md:203`; [Lib/Cohomology/PointClass/LinearIndependence.lean:40](lean:Lib/Cohomology/PointClass/LinearIndependence.lean#L40)-42 | `INDEX.md` says that point classes "detect degrees of zero-cycles". The file proves only linear independence. | The book follows the file. | [schemes-through-points](/chapter/schemes-through-points/) |
| F-109, explained | `grh/INDEX.md:204`; [Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean:4](lean:Lib/Cohomology/ProjectiveLine/TiltedLineFormula.lean#L4)-13 | `INDEX.md` calls the file a Künneth formula over a field. The head of the file describes a projective line formula for the tilted theory. | The book follows the file. | [cohomology-ext](/chapter/cohomology-ext/) |
| F-110, explained | [New/Reduction/ShortAndEnough.lean:168](lean:New/Reduction/ShortAndEnough.lean#L168) | The docstring calls `seesawConst` "a non-zero constant". This is true, since it is a unit, but the identity that it belongs to can be trivial (F-068). | The word "non-zero" can mislead a reader into reading the identity as a proof of nonvanishing. | [seesaw-identity-2](/chapter/seesaw-identity-2/) |
| F-111, explained | [Main.lean:11](lean:Main.lean#L11); `grh/README.md:18`; [New/Determinant/Twist/FitTwists.lean:119](lean:New/Determinant/Twist/FitTwists.lean#L119), 125 | `Main.lean` says "trivial character", and the README says "principal character". Both mean $\chi = 1$. The docstring of the field says `2 ≤ z`, but the field forces $z \geq 10$ (F-038). | The book uses one word for $\chi = 1$. The docstring understates the bound. | [notation](/chapter/notation/), [twists-critical-pairs](/chapter/twists-critical-pairs/) |
| F-112, explained | [Lib/Cohomology/WoodsHole.lean:214](lean:Lib/Cohomology/WoodsHole.lean#L214) | `woods_hole` is in the namespace `ellAdicCohom`, but it uses only `HodgeH` and the Hodge-Tate map. It is the vanishing half of the formula of Atiyah and Bott. | The name and the namespace suggest more than the content. | [congruence-relation](/chapter/congruence-relation/), [cohomology-ext](/chapter/cohomology-ext/) |
| F-119, explained | [New/Reduction/Data/AdmissibleData.lean:147](lean:New/Reduction/Data/AdmissibleData.lean#L147)-148; [New/Reduction/Data/Sizes.lean:206](lean:New/Reduction/Data/Sizes.lean#L206) | No disagreement. The field `levelPrime_mem` puts $p_0, p_1$ in $[b^{10}, b^{11}]$. The lemma `levelPrime_mem_Ioo` states only the weaker $(b^2, N)$. The docstrings follow the field, and the lemma is a consequence, used where only $b^2 < p < N$ is needed. | Cite the field for the size of $p_0$ and $p_1$, not the lemma. | [data-and-sizes](/chapter/data-and-sizes/) |
| F-122, explained | [New/Reduction/ShortAndEnough.lean:168](lean:New/Reduction/ShortAndEnough.lean#L168)-170 | The same point as F-110, seen from the definition. `seesawConst` is the constant chosen from `seesaw_identity` (line 170), which is only a unit of `ℂˣ`. If $c_0 C / d = 0$, both sides of the identity are $0$. | Do not repeat the docstring. A chapter on the seesaw identity must say what the identity gives when the factor is $0$. | [seesaw-identity-2](/chapter/seesaw-identity-2/) |

### Why citations matter here

The source is a formal proof. A citation is not needed for its validity: the kernel checks every step, if the reported checks hold. So why does the register list citations at all?

The reason is the reader. A reader who wants to understand a step of the source looks for the paper that the step follows. If the file cites a theorem that it does not prove, as in F-102, the reader looks in the wrong place. If the file cites a work with no place, as in most citations of F-100, the reader must search the work. If the cited work is a recent preprint, as in F-104, the reader cannot rely on a referee. And if a folder cites nothing, as in F-105 and F-106, the reader cannot tell whether its method is new, and so cannot tell how much of the method the book must explain from first principles.

The source itself is honest about this. Its file `REFERENCES.md` reports the state of its own citations, with the counts of F-100 and the list of F-101. The register repeats these counts so that a chapter of the book does not present a citation as checked when the source says it is not.

### Why docstrings matter here

A docstring is the first thing a reader of a declaration sees. In most of the source the docstrings are accurate and careful. The rows above are the exceptions that the writers of this book found.

The rows are of two kinds. In F-108 and F-109 an index describes a file in words that are stronger than, or different from, what the file proves. The book follows the file. In F-110, F-111 and F-122 a docstring is true but can mislead: a constant that is a unit is called "non-zero", which is correct, but the identity around it can be trivial; a docstring says `2 ≤ z` where the field forces more. In F-112 a name suggests a wider content. In each case the Lean text is the authority.

The row F-119 is not a disagreement. It is in this table because a reader of the source could take it for one: a field gives a strong range, and a lemma with a similar name gives a weak one. The register records that the two agree, and says which one to cite.

A writer who finds a new disagreement adds a row to this table. The row gives the document and its line, the declaration and its line, the two claims side by side, and the claim that the book follows.
