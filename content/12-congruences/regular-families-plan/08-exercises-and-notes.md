---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Show that $\sum_{l \geq 0} l z^{l} = z/(1 - z)^2$ for $|z| < 1$. Deduce that $\sum_{l \in T} (1/2)^{l} \log l \leq 2$ for every finite set $T$ of natural numbers, as in the lemma on the small terms of Section 5.

*Hint.* Differentiate the geometric series and multiply by $z$. Use $\log l \leq l$ and the convention $\log 0 = 0$.

**Exercise 2.** Prove the lemma on the clearing bound per row of Section 5 in the case $r' = 1$, $t' = t$ and $\mathrm{sel} = \mathrm{ram} = e'_\ell$, and show that it is then an equality. For which values of $r'$ is the lemma an equality when $\mathrm{sel} = \mathrm{ram} = e'_\ell$ and $t' = t$?

*Hint.* With these values the left side is $(1 + 2t) e'_\ell + \mathrm{localDefectBound}(\ell) + e_\ell + v_\ell(N_g)$, which is $\beta_\ell$ by definition. For $r' > 1$ the right side grows by $(r' - 1)$ times $(1 + 2t) e'_\ell + e_\ell + v_\ell(N_g)$, and this is positive since $e'_\ell \geq 2^{-\ell} > 0$. So equality holds only for $r' = 1$.

**Exercise 3.** In the rank-two model of Section 4, take $a = 3$, so that $N = 10$. Find an integral vector whose projection to $Z = \mathbb{C}u$ has the denominator $10$, and find the congruences between $u$ and a multiple of $u'$ modulo $2$ and modulo $5$. Over $O = \mathbb{Z}[i]$, the prime $2$ ramifies and $5$ splits. Compute the index of $L_Z$ in $\mathrm{pr}_Z(L)$ and its factorization into the parts at $2$ and at $5$.

*Hint.* The vector $e_1$ has the projection $u/10$. We have $3u' - u = -10 e_1$. The index is $\mathrm{Nm}(10) = 100 = 2^2 \cdot 5^2$, by the proposition on projections of a unimodular lattice. In the language of the source, the $2$-part costs $2 \log 2$ and the $5$-part costs $2 \log 5$, and the sum $\log 100$ is the logarithm of the index, as in the identity $\sum_\ell v_\ell(A) \log \ell = \log A$.

**Exercise 4.** In the final comparison of Section 5, the quotient of the local loss by the budget is $4 \cdot 10^6 e^{180} m^2/(x \log^2 b)$. Suppose that the number of lifts were $m = x^{\theta}$ for some $\theta > 0$. Show that for $\theta \leq 1/2$ the quotient is at most $4 \cdot 10^6 e^{180}/\log^2 b$. What is needed of $b$ for the quotient to stay small when $\theta > 1/2$? Why does a larger $m$ help the main argument, and where does this proof stop it?

*Hint.* The quotient is $4 \cdot 10^6 e^{180} x^{2\theta - 1}/\log^2 b$. For $\theta \leq 1/2$, $x^{2\theta - 1} \leq 1$. For $\theta > 1/2$, the quotient is small only if $\log^2 b$ is larger than $4 \cdot 10^6 e^{180} x^{2\theta - 1}$, so $\log b$ must grow like a power of $x$. The bound $b \geq x^{10^{12}}$ gives only $\log b \geq 10^{12} \log x$. In the main argument, the star inequality bounds $m$ times the remainder, so a larger $m$ gives a smaller remainder ([the plan in one page](/chapter/theorem-and-plan/#the-plan-in-one-page)). The local loss per lift grows like $m/k$, while the budget per lift falls like $1/(mk)$.

**Exercise 5.** Let $e_\ell$ be negligible with the exponent $C$, with $C$ at most $10^6$. Use the lemma on heights from local bounds of Section 2 to show that a family $y$ with $\|\iota(y_\kappa)\| \leq \exp(e_\ell \log \ell)$ for every $\kappa = (\ell, \iota)$ has height at most $x_1$. Which line of the proof of the theorem on regular families is this?

*Hint.* Put $e''_\ell = e_\ell \log \ell$. Then $\sum_{\ell \in T} e''_\ell \leq x^{C} \leq x^{10^6} \leq x_1$ for every finite set $T$ of primes. This is the line `height_le j p s hp := HeightLe.of_le h_error ...` of `New.exists_isRegularFamily`, with $C = 999$ and $e_\ell = e'_\ell$.

**Exercise 6.** The twisting theorem of Section 6 gives $\mathrm{ellVal}(\iota_\ell(p.\mathrm{ratio}(\xi, s))) \leq e'_\ell$, and the twisting theorem for two families turns this into $\|\iota_\ell(p.\mathrm{ratio}(\xi, s)^{-1})\| \leq \exp(e'_\ell \log \ell)$. Show that the first statement implies that the ratio is not $0$, and so that both $L$-values in the ratio are not $0$. Show that the second statement holds trivially when the ratio is $0$, by the conventions of Lean. Which of the two statements does the definition of regular families keep?

*Hint.* $\mathrm{ellVal}(0) = \infty$, and $e'_\ell$ is finite. The ratio is a quotient of two real numbers, with $x/0 = 0$ in Lean; so a nonzero ratio has a nonzero numerator and a nonzero denominator. If the ratio is $0$, its inverse is $0$ by $0^{-1} = 0$, and $\|0\| = 0 \leq \exp(e'_\ell \log \ell)$. The definition `HasSmallRatios` keeps only the bound for the inverse ratios, so the regular family does not record that the $L$-values are not $0$.

## Notes and references

The theorem of this volume is `New.exists_isRegularFamily` in [FitTwistsExist.lean](lean:New/Congruences/FitTwistsExist.lean#L517). The definitions of Section 3 are in `New/Determinant/Twist/FitTwists.lean`, except `New.Selmer.DenominatorLe`, which is in `New/OneLift/TestedForms.lean`. All the bookkeeping of Section 5 is in the top file, and this chapter follows it in full. The deep steps of Section 6 are stated, not proved, here.

The link between congruences and Selmer classes in Section 4 is the method of Ribet, K. A. Ribet, *A modular construction of unramified p-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976), 151 to 162. The theorem of Ribet in Section 4 is the main result of that paper. Its converse direction, that a nonzero $\omega^{1-k}$-part forces $p \mid B_k$, is the earlier theorem of Herbrand. The proposition on projections of a unimodular lattice is a standard fact of the theory of lattices, and its proof in Section 4 is complete.

For the twisting theorem, the source names three related works in `New/Congruences/Selmer/TwistingTheorem.lean`: Mazur and Rubin, *Diophantine stability* (2018); Kriz and Nordentoft, *Horizontal p-adic L-functions* (2023); and Hida, *Non-vanishing modulo p of Hecke L-values* (2004). The source says that twists of $\ell$-power order at new primes that kill a Selmer group or keep $L$-values barely divisible are known in the literature. This chapter does not compare the statements of these works with the statement of the source.

The research note f §2 of this book, which the volume plan names for this chapter, has two errors. First, it gives the location of `DenominatorLe` as `Determinant/OneLift/TestedForms.lean`. The file is `New/OneLift/TestedForms.lean`, at line 413. Second, it says that the ratios of $L$-values have small $\ell$-adic denominators, and so it counts them in the budget. In Lean the ratios have a separate height bound $x_1$ through the twist error, by `HeightLe.of_le`, and only the denominators of the projections enter the budget. Two open questions of the notes are settled by the source. The error term $\mathrm{denominatorError}$ fits the budget, by `New.Selmer.isNegligible_denominatorError` and `New.Selmer.sum_clearingBound_add_padicValNat_le`. The index type of the rows has $r$ elements, by `New.Data.card_rowIndex`.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
