---
title: The open questions
lean:
  - New/Reduction/PrimeSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The open questions

The research notes of this book asked 85 questions about the source. Many of them overlap. The plan of the book merged them into the 69 questions below. Each question names the findings that it concerns, so a reader can go from a question to the rows of the earlier sections, and back.

A question is open until a person writes an answer in an issue of the repository, or until a chapter of the book answers it from the source and cites the lines. Two questions are open as issues now: Q-02 and Q-04. Together they use the three issues 15 to 17. Q-01 is answered in [the origin of the proof](/chapter/claim-and-status/#the-origin-of-the-proof), and its issue 18 is closed. The answer to a question changes the status of its findings, not the other way round.

### The table

| Q | Question | Findings | Status |
|---|---|---|---|
| Q-01 | Is the original Lean proof of Alpöge public? What does `remark.pdf` contain? Which steps use other arguments? | F-003 | answered in [the origin of the proof](/chapter/claim-and-status/#the-origin-of-the-proof), [issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18) closed |
| Q-02 | Can we get the logs of `#print axioms`, of the export, of the three checkers and of Comparator? What was the stand-in sandbox? A third party has published its own logs of all of these at the pin (`https://math.mit.edu/~drew/shortgrh/`). The logs of the authors and the stand-in are still open. | F-004, F-005 | open, [issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15), [issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16) |
| Q-03 | How does Comparator check the definitions when `definition_names` is empty? Confirm with its documents. | F-006 | open |
| Q-04 | Was the claim that `Lib/Speed` can be emptied checked on v4.35.0? | F-019 | open, [issue 17](https://github.com/tamnd/grh-lean-handbook/issues/17) |
| Q-05 | Which declarations do the five theorems not use? A dependency closure would answer it. | F-008 | open |
| Q-06 | Where is nonvanishing recovered for $\kappa$, the seesaw constant, the branching matrix and $\beta$? | F-068, F-069, F-073, F-074 | open; F-121 shows that no use goes through `ne_zero_of_squareCommutes` |
| Q-07 | Who compiles the list of definitions of `Lib` that differ from the textbook? | F-052 | open; Section 5 starts the list |
| Q-08 | Where do $5040$ and the constants $6$ and $12$ of `Sharpness` come from? Is $d \equiv q_0/2 - 1$ needed for the criterion only, or also for the field? | F-058, F-015 | open |
| Q-09 | Does the compact `Lib` hold the same results split more finely, or other results? | F-117 | open |
| Q-10 | Why is $m$ about $\sqrt{x}$? Which constraint stops the method at $1/2$? | F-093 | open |
| Q-11 | Is the dependence of the thresholds on $d$ stated clearly enough? | F-092, F-076 | open |
| Q-12 | What does `exists_entireL_quadTwist_ne_zero` prove, and is it faithful to Jutila and Heath-Brown? | F-067, F-103 | open |
| Q-13 | What are the statements behind `divisibilityError` and `seesawConst` in human form? | F-042 | open |
| Q-14 | Why is `CovolumeLe` needed only for the trivial twist? | F-060 | open |
| Q-15 | Where is the Behrend set used in Theorem C, and is the bound strong enough? | F-093 | open |
| Q-16 | Check `totalRemainder_eq` ([New/Reduction/PrimeSums.lean:177](lean:New/Reduction/PrimeSums.lean#L177)) by hand for the boundary terms. | F-077 | open |
| Q-17 | Which cited sources give real arguments, and which are background only? | F-100, F-107 | open |
| Q-18 | Does any statement depend on the splitting character that `instWeilDataE` picks? | F-043 | open |
| Q-19 | Which twists are used at which primes, given the coprimality in `exists_err_gaugeLe_compositeLift`? | F-089 | open |
| Q-20 | Is the factor $2$ on the gain a real loss, or does it cancel? | F-099 | open |
| Q-21 | Does the factor $N^3$ stay small against the main terms? | F-096 | open |
| Q-22 | How are $p = 2$ and $p = 3$ handled in the formal group and in `Lifting`? | F-088 | open |
| Q-23 | Is there a clean order of reading, given imports in both directions? Should `DefiniteKernelSize` and `Sharpness` go with `OneLift`? | F-106 | open |
| Q-24 | Is the Chowla-Selberg formula proved in full, and does `New` need $u$ to be algebraic? | F-064 | open |
| Q-25 | Where is `hj_genericConst` discharged? | F-080 | open |
| Q-26 | Is the concrete $\varrho$ at least $10^8$, and how do $k \leq f$ and $1000\,(2\varrho + 2)^9 \leq k$ fit with the field? | F-090, F-091 | open in part; F-090 shows that the data satisfy $10^8 \leq \varrho$ |
| Q-27 | Does `HasPrimitiveRoot5040` reach the field of `enough_forms`? | F-079 | open |
| Q-28 | Which lemmas move a `tsum` or an integral without explicit summability? | F-032 | open |
| Q-29 | What pins down `classCutoff` and `sublatticeBasis`? | F-046 | open |
| Q-30 | Is the Bessel function of the source the Bessel model of Furusawa and Shalika, or of Baruch? | F-050 | open |
| Q-31 | Is the simple trace formula proved in full in `Lib/Adelic/TraceFormula`? | F-035 | open |
| Q-32 | How does `IsNearIsometry` relate to the usual notion for the operator norm? | F-059 | open |
| Q-33 | Are the methods of `Frames` new or adapted? | F-105 | open |
| Q-34 | Is the factor $C$ of `exchange_identity` ever needed exactly? | F-070 | open |
| Q-35 | Does `Data` force $m$ even for `ThreeExchanges`? | F-028 | open |
| Q-36 | Are `D.r * β` in `ClearsProjection` and `card r * β` in `Selmer.DenominatorLe` the same at every use? | F-094 | open |
| Q-37 | Is `RankOneIndex z` ever used with $z < 10$? | F-038 | open |
| Q-38 | Is the inner product on `SecondFactorFormValues` the Petersson product? | F-027 | open |
| Q-39 | Is $2r + 2N + 3 < n$ sharp, and does it match the stable range? | F-087 | open |
| Q-40 | Should `IsNegligible` be taught with `FitTwists` or with `Congruences`? | F-082 | open, a question of the plan of the book |
| Q-41 | Is $\exp(x^{34})$ the bound of the original proof, and is there room for it? | F-095 | open |
| Q-42 | Do the lines with `respectTransparency false` in the files on false lifts and gluing maps show a definitional mismatch? | F-021 | open |
| Q-43 | Is the combinatorics of turns new or adapted? | F-106 | open |
| Q-44 | Does `denominatorError` fit the budget for all data, and where is the largeness of $x$ used? | F-094 | open |
| Q-45 | What does `exists_length_shaOdd_le` prove, and from what? | F-045, F-061 | open |
| Q-46 | Is "most Frobenii" used only through Chebotarev, or with a finite set that can depend on the twist? | F-053 | open |
| Q-47 | Is `localChart` compared with another embedding? | F-044 | open |
| Q-48 | Which results in `Lifting` are new, and which are published? | F-104 | open |
| Q-49 | Which file proves the nonvanishing of the $U(2)$ period for $z = 1$ in `ClassSums`? | F-069 | open |
| Q-50 | Is the mismatch of `DecidableEq` in `FitTwistsExist` part of a wider diamond on `ChosenIndex`? | F-025 | open |
| Q-51 | Does instance search find `HasGap` with an unexpected gap? | F-030 | open |
| Q-52 | Do even class orders stay out of the whole chain into `clearingBound`? | F-045 | open |
| Q-53 | Check the sign of the residue of `isPolar_primeRemainder` line by line. | F-077 | open |
| Q-54 | Is the uniformity of the prime theorem what `Existence` needs? | F-097 | open |
| Q-55 | Is the Ext cohomology on test rings equal to étale cohomology for the varieties used? Does `HodgeH` agree with Hodge cohomology? | F-055 | open |
| Q-56 | Should the book follow `INDEX.md` or the files where they disagree? | F-108, F-109 | answered: the book follows the files |
| Q-57 | Who audits `OscillatorPair` in `Lib/Weil`? | F-050 | open |
| Q-58 | Do the constants of the gap ($500 n^3 + 10 n^5$, $13 N^3 \leq B$) match what `New` supplies? | F-030 | open |
| Q-59 | Does `New` need exact characteristic polynomials, or semisimplicity of Frobenius, beyond `Attached` and `PolyKillsAt`? | F-053, F-054 | open |
| Q-60 | Are the Selmer bounds always used as upper bounds? | F-061 | open |
| Q-61 | Does anything need the theorem of Albert, Brauer, Hasse and Noether, or the Hasse principle at real places, in the form of the textbook? | F-052 | open |
| Q-62 | Do the global instances create diamonds that a statement of `New` picks up? | F-023, F-024 | open |
| Q-63 | Does surjective multiplication give connected fibres on the bases used? Is the `Pic` built by hand equal to the one of Mathlib? | F-062 | open |
| Q-64 | Are `h_torus`, the hypothesis on the fixed part in `SortedExponents`, and `IsSharp` discharged at every call site? | F-084 | open |
| Q-65 | Is control at one embedding, with no dimension, enough for every use of `exists_galois_rep`? | F-049 | open |
| Q-66 | How does the PEL datum of the source compare with the one of Kottwitz? | F-052 | open |
| Q-67 | Which hypotheses are unused? A build with the linter would answer it. | F-086 | open |
| Q-68 | Is `wave c = exp(c - conj c)` consistent with the additive character in `Lib/DiscreteSeries`? | F-034 | open |
| Q-69 | Check the citations of the unchecked files and of the recent preprints. | F-101, F-104 | open |

### Questions that the source answers

The notes asked some questions that the source answers directly. They are not in the table.

- Note b asked whether `vacuumBoundConst` depends only on the parameters. It does: its type is `(P : Parameters) → ℕ` (F-042).
- Note b asked whether Theorem C is free of `sorry`. It is: no file of `grh/src` contains `sorry` (F-007).
- Note c asked whether the division in the ratio of a comparison operator is safe. F-072 answers this in part: the field `ratio_ne_zero` holds for the operator of the proof. The notes also ask about $e_0$ and `goodForms`, and F-072 does not settle these.

### How to close a question

A person who answers a question writes the answer in an issue, with the lines of the source that support it. Then a writer of the book changes the status of the question in this table to "answered", with a link to the issue, and changes the status of each of its findings in the earlier sections. If the answer shows a new point, the writer adds a new finding with the next free number. The number of the question does not change, and an answered question stays in the table, so that a reader can see what was asked and what the answer was.
