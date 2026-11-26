---
title: The plan checked
lean:
  - New/Congruences/FitTwistsExist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The plan checked

This section compares what other chapters say about the assembly with the source. It covers [regular families: the plan](/chapter/regular-families-plan/), the chapters of Volume 11 that state the result, and the rows of the guide that point to this chapter. Each claim was checked against the pinned source.

### The claims that agree

1. The top file `New/Congruences/FitTwistsExist.lean` has 535 lines and imports the five files of Section 8 ([the map of the files](/chapter/regular-families-plan/#the-map-of-the-files)).
2. The statement of `New.exists_isRegularFamily` and the definitions of `IsRegularFamily`, `HasSmallRatios`, `IsDenominatorBound`, `HasDenominatorsLe` and `ClearsProjection` are as the plan states them ([denominators and regular families](/chapter/regular-families-plan/#denominators-and-regular-families)).
3. The bad places are the places above $\ell \cdot (M N)$, and the twist error is $e'_\ell = (4f + 3) r v_\ell(N_g) + 2^{-\ell}$. This agrees with the plan and with [the four inputs](/chapter/theorem-c-plan/#the-four-inputs) of Volume 11.
4. The constants of [the denominator budget](/chapter/regular-families-plan/#the-denominator-budget) are those of Section 6: $\beta_\ell$, $\gamma_\ell = \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$, the bound $4 \cdot 10^6 e^{180} f (m/k) b \log b$ for the local defect, and the exponents $999$, $4000$, $2000$ and $30$.
5. The sum of the twist errors is at most $x^{999} \leq x_1$, as the plan says.
6. The five steps of [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) are the steps of the source, in the same order. The statements of Steps 1 to 5 match the source. The proof of Step 5, a twist at one prime, matches the source step by step: the finite set $\mathcal{S}$, the two families, the twisting theorem for two families, the coprimality from $\tau^1$, the two clauses, and the trivial stabilizers.
7. The use of `convert` at lines 463 and 464 is as the plan and the row F-025 of the register say.
8. The only use of the theorem in the source is at line 144 of `New/Determinant/Twist/LongForms.lean`, as [the four inputs](/chapter/theorem-c-plan/#the-four-inputs) says. The bound $\exp(e'_\ell \log \ell)$ on the inverse ratios and the condition $\ell \nmid \mathrm{Nm}\,Q$ are as stated there.

### The differences

(a) **An exponent is missing.** [Regular families](/chapter/twists-critical-pairs/#regular-families-of-twists) in Volume 11 (line 98 of its file) says that negligible numbers are used in Volume 12 "with the exponents $999$, $4000$ and $2000$". The source also uses the exponent $30$, in `isNegligible_padicValNat_card_stdClasses`, for the valuations of $h_{\mathrm{std}}$. These enter the budget through $\gamma_\ell$.

(b) **Volume 11 imports two files of the folder.** [The map of the files](/chapter/regular-families-plan/#the-map-of-the-files) says that `SelmerHypotheses.lean` "is also the only file of the folder that Volume 11 imports". But `New/Determinant/Twist/LongForms.lean`, a file of Volume 11, imports `New.Congruences.FitTwistsExist` at its line 1. The claim is true of the path through `TwistedValueHeights.lean`, but not of the folder as a whole.

(c) **The theorem is not the only output of the folder.** The row F-082 of [hypotheses and sizes](/chapter/register-of-findings/#hypotheses-and-sizes) says that `exists_isRegularFamily` "is the only output of the folder `Congruences`". But `New/OneLift/HeckeValues/TwistedValueHeights.lean` uses two lemmas of `SelmerHypotheses.lean`: `isChosen_levelPlaces_chosenPlace` (line 252) at its lines 514 and 766, and `TameChar.tamePart_eq_one_of_isChosen` (line 243) at its line 515. [The chapters of the volume](/chapter/theorem-c-plan/#the-chapters-of-the-volume) in Volume 11 (line 90 of its file 06) agrees that Volume 11 uses the Selmer hypotheses. The theorem is the only output of the top file and the only deep output of the folder.

(d) **The import row of this chapter.** The list of imports in [the map of the files](/chapter/regular-families-plan/#the-map-of-the-files) gives `12 proof-of-regular-families <- 1`. By the rule of that list, each row gives the chapters whose files the files of the chapter import. The file of this chapter is `FitTwistsExist.lean`. It imports files of chapters 5, 10 and 11, the same as the row of chapter 1, which also covers this file. The row should read `<- 5, 10, 11`, or it should say that it means a dependence of the text.

(e) **The reading path counts ten chapters.** [Reading paths](/chapter/how-to-read/#reading-paths) (line 71 of its file 03) says "Volume 12, all ten chapters" and lists ten. The volume has twelve chapters. The list leaves out [tied traces](/chapter/tied-traces/) and [exponent lattices](/chapter/exponent-lattices/).

(f) **The number of the chapter.** The spec of the handbook numbers this chapter as item 10 of Volume 12. In `volume.yaml` it is chapter 12. The text of the handbook follows `volume.yaml`.

(g) **Small points of Step 1 and Step 2.**

1. The proof of Step 1 in the plan starts with "a nonzero good eigenform". The source treats $y = 0$ as a separate case first, since the lift of $0$ is $0$.
2. The plan says that in Step 1 "the type $c$ moves to a type in lift setting". In the source, $c$ itself is a lift setting for the descent pair (`isLiftSetting_descentPair`). Nothing moves.
3. The plan does not name `isRepOfType_one`, the lemma on the trivial representation (Section 3). It says only that the main summands of the main pairs come from the trivial representation.
4. The plan indexes the summands of rank one by the main pairs $p$. The source indexes them by the pairs $(p, j)$ with $p$ a main pair for $j$. The two agree, since the summand of $(p, j)$ does not use $j$, but the index types differ.

### What the differences mean

None of the differences changes the theorem or its proof. Differences (a), (b), (c) and (e) are statements about the source or the handbook that are too strong or incomplete. Difference (d) is an error in a table. Difference (f) is a matter of numbering. The points of (g) concern the level of detail. The source claims the theorem, and Lean accepts it, if the reported checks hold.
