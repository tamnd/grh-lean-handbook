---
title: Exercises and notes
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 6. As before, $b \geq 1000$, $\varepsilon = (8b^2)^{-1}$, $d_T$ is the dimension of the target, $D_X$ is the dimension of the source forms, and $\mathrm{src}$ is the space of ramified source forms.

**Exercise 1.** Check the arithmetic of the last step. Show that $1 - 16\varepsilon - 2/b^2 = 1 - 4/b^2$. Then show that the condition $\varepsilon < 1/16$ of the greedy cover holds if $b^2 > 2$, and that $b^2 \geq 2$ gives only $\varepsilon \leq 1/16$. Which size bound does the source use for the strict inequality?

*Hint.* $16\varepsilon = 2/b^2$. Read the call of `IsSpread.exists_few_le_finrank_iSup_range` in [the section from one translate to Theorem B](/chapter/proof-of-theorem-b/#from-one-translate-to-theorem-b). It passes `D.lt_of_hasLogBound`.

**Exercise 2.** Prove the inequality of [the lemma on the logarithm](/decl/New.Data.five_halves_mul_one_add_log_le/) by hand for $b = 1000$:

$$\frac52\Bigl(1 + \log\frac{1}{16\varepsilon}\Bigr) \leq 5\log(1 + 2b^2).$$

Then find the smallest real $b \geq 1$ for which the proof of the source still works, that is, for which $\log(1 + 2b^2) \geq 1$ and $(16\varepsilon)^{-1} \leq 1 + 2b^2$.

*Hint.* $(16\varepsilon)^{-1} = b^2/2$. The Lean term `log (16 * (8 * D.b ^ 2)⁻¹)⁻¹` is the logarithm of $(16\varepsilon)^{-1}$, because the postfix inverse binds to the argument of `log`. The first condition asks $1 + 2b^2 \geq e$.

**Exercise 3.** Let $F$ be a subspace of a space $W$ of dimension $d > 0$, with share $\alpha = \dim F/d$. Suppose that the maps $B_s : V \to W$ spread with error $\eta$ and that $\dim V \geq 1$. Show that one greedy step with an $s$ from the spread property gives

$$\dim(F + \operatorname{range}B_s) \geq \dim F + \Bigl(\frac{1 - \alpha}{2} - \eta\Bigr)\dim V.$$

Deduce that the share $1 - \alpha$ that is not covered shrinks by the factor $1 - \dim V/(2d)$, up to the error, at each step.

*Hint.* $\dim(F + \operatorname{range}B_s) = \dim F + \dim B_s(V) - \dim(F \cap B_s(V))$, and $\dim B_s(V) - \dim(F \cap B_s(V)) = \dim V - \dim B_s^{-1}(F)$. Compare with [the greedy cover](/chapter/few-translates/#the-greedy-cover).

**Exercise 4.** The proof of Theorem B uses $c_B$ only through $c_B > 0$ and $c_{ss}$ only through $c_{ss} \neq 0$. Prove that for every linear map $T$ and every nonzero scalar $c$, $\operatorname{range}(cT) = \operatorname{range}T$. Deduce that Theorem B stays true if $c_B$ and $c_{ss}$ are replaced by any other nonzero numbers. Why does the source still need the definitions of $c_B$ and $c_{ss}$ in the statement of Theorem B?

*Hint.* For the last question, compare the statement of Theorem B with the statement of Theorem A in the same file. Both are about the same maps `normalizedPoincare s`.

**Exercise 5.** In the bound on the ramified loss, each translate loses at most $\dim X - \dim\mathrm{src} \leq b^{-8}D_X$ dimensions. Use the count $\#t\cdot D_X \leq 5d_T\log(1 + 2b^2)$ to show that the total loss is at most $5b^{-8}\log(1 + 2b^2)\,d_T$. Show that this is at most $2d_T/b^2$ for $b \geq 1000$. Then find how large the loss of each translate could be, as a power of $b$, before this step fails.

*Hint.* $\log(1 + 2b^2) \leq \log 3 + 2\log b$ for $b \geq 1$. A loss of $b^{-k}D_X$ per translate gives a total of about $10b^{-k}\log b\,d_T$.

**Exercise 6.** The near isometry has error $5b^{-4}$ and the moment has error $9b^{-4}$, but the proof of [the theorem on one translate](/chapter/proof-of-theorem-b/#one-translate) uses the larger error $\varepsilon = (8b^2)^{-1}$ for both. Redo the last step with $\varepsilon = 9b^{-4}$ and find the factor in front of $d_T$ in the count and the share of the target that is covered. Is the new count smaller or larger than the count of Theorem B?

*Hint.* With $\varepsilon = 9b^{-4}$, the count is $\tfrac52(1 + \log(16\varepsilon)^{-1})\,d_T$, of size about $10\,d_T\log b$, and the cover misses at most $144b^{-4}d_T$. The ramified loss of $2/b^2$ then dominates.

## Notes and references

Theorem B is the spanning half of the reduction. It says that few translates of the image of the ramified source forms span almost all of the target. It is one of the two theorems of New/Reduction/ShortAndEnough.lean, with Theorem A on short forms. This chapter has assembled it from the chapters of Volume 10. The statement and the proof are those of the source at the pin. Lean accepts `New.Data.enough_forms`, if the reported checks of the source hold.

The proof has a simple outer form. A second moment bound for the translates $e_0\,s\,P$ gives a spread statement for one translate. A greedy cover then turns the spread statement into a bound for a few translates. The hard part is the second moment bound, which is the content of chapters 2 to 13 of this volume. This chapter adds only the bookkeeping: the dimension of the target, the match of the projection $e_0$ with the two idempotents at the level primes, the scaling of the Poincaré map, and the passage to the ramified forms.

The source names two works for the outer form, in the file header of New/Spanning/SecondMoment/FewTranslates.lean. For rank bounds from second moments it names Welch, 1974. For greedy covering with a logarithmic loss it names Wolsey, "An analysis of the greedy algorithm for the submodular set covering problem", 1982, in the form "Wolsey, Greedy algorithm for the submodular set covering problem, 1982". This book has not compared the statements of the source with these works.

For the Poincaré series and the Bessel functions, the header of New/Spanning/Bessel/FillingData.lean names Petersson, "Über die Entwicklungskoeffizienten der automorphen Formen", 1932, and the NIST Digital Library of Mathematical Functions, section 10.22. In the words of the source, the integrals of Bessel functions at the real places replace Petersson's J-Bessel kernel in the proof that few translates almost span the target forms. The same header names work of Baruch on Bessel distributions and of Comtat and others on a Kuznetsov formula for $\mathrm{GSp}(4)$. This book has not compared the source with these works.

The constants of Theorem B are not optimal, and the source does not claim that they are. The factor $5\log(1 + 2b^2)$ in the count comes from the greedy cover with $\varepsilon = (8b^2)^{-1}$ and the lemma on the logarithm. The loss $4/b^2$ is the sum of two halves: $2/b^2$ from the cover and $2/b^2$ from the ramified forms. [The section from one translate to Theorem B](/chapter/proof-of-theorem-b/#from-one-translate-to-theorem-b) lists the three places where the plan in chapter 1 differs from the source. They are matters of statement and do not change the proof.

The formalization has three points that the reader of the Lean text must keep in mind. First, the constant $c_{ss}$ is a unit chosen by `choose`, so it is a complex number and not a positive real. Second, the greedy cover is applied to the maps `goodPoincare` on the source forms and not to the scaled map in coordinates. Third, the instance `WeilData` of the field $E$ comes from the instance `New.Parameters.instWeilDataE`, and its splitting character is chosen with `.some`. [The scaled Poincaré map](/chapter/proof-of-theorem-b/#the-scaled-poincar-map) and [the map of the proof](/chapter/proof-of-theorem-b/#the-map-of-the-proof) give the details.
