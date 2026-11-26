---
title: Exercises and notes
lean:
  - New/Congruences/FitTwistsExist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 1 to 7. The sizes are those of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).

**Exercise 1.** Show that $\sum_{n \geq 0} n\, 2^{-n} = 2$. Deduce the lemma on the geometric sum of Section 6. Then show that $\sum_{\ell \text{ prime}} 2^{-\ell} \log \ell < 1$.

*Hint.* Differentiate $\sum_n y^n = 1/(1 - y)$ and put $y = 1/2$. For the last part, the terms at $\ell = 2, 3, 5$ are about $0.173$, $0.137$ and $0.050$, and the rest is at most $\sum_{n \geq 7} n 2^{-n} = 2 - \sum_{n \leq 6} n 2^{-n}$.

**Exercise 2.** Let $a = 360$ and $T = \{2, 3\}$. Compute $\sum_{\ell \in T} v_\ell(a) \log \ell$ and compare it with $\log a$. Show that in the lemma on valuations and logarithms equality holds for $a = b$ if and only if $T$ contains every prime factor of $a$.

*Hint.* $360 = 2^3 \cdot 3^2 \cdot 5$. The sum is $\log 72$. The missing term is $\log 5$. Each term $v_\ell(a) \log \ell$ with $\ell \mid a$ is positive.

**Exercise 3.** Let $b, h \in \mathbb{N}$ with $h \geq 1$. Show that the interval $(b - 30h^3, b + 30h^3]$, with truncated subtraction, has at most $60h^3$ elements. Find when it has fewer.

*Hint.* If $b \geq 30h^3$, it has exactly $60h^3$ elements. If $b < 30h^3$, the lower end is $0$ and the interval has $b + 30h^3 < 60h^3$ elements. Compare with [the product lemma](/decl/New.Selmer.prod_Ioc_natB_le_pow/).

**Exercise 4.** Show that $\gamma_\ell \geq (1 + 2t)\, 2^{-\ell} \log \ell > 0$ for every prime $\ell$. Deduce that no finite set of primes carries all of the denominator bound. Explain why the budget is still met.

*Hint.* All terms of $\beta_\ell$ are $\geq 0$, and the twist error has the term $2^{-\ell}$. The sum over all primes of $(1 + 2t) 2^{-\ell} \log \ell$ is at most $2(1 + 2t)$ by Exercise 1. This is far below the budget.

**Exercise 5.** Show that the main term of Section 6 has the ratio
$$\frac{4 \cdot 10^6 e^{180} f (m/k)\, b \log b}{f a \log^3 b/(m k)} = \frac{4 \cdot 10^6 e^{180} m^2}{x \log^2 b}$$
to the budget, for $a = x b$. Which of the sizes of the data make this ratio less than $1$?

*Hint.* Cancel $f$, $b$ and $k$. Use the bounds on $m$ in terms of $x$, and that $\log b$ is large against every power of $x$ of fixed degree. The source does not write this out. It uses one call of `le_of_hasLogBound`.

**Exercise 6.** The splitting theorem of Section 3 uses the systems that occur on $W_m$, not on $W_j$. Write the proof of Section 5 with the systems of $W_j$ in place of those of $W_m$. Which step needs a change, and why is the version of the source simpler?

*Hint.* The index type $A$ would be the dependent sum of the sets $\mathcal{S}_j$ over $j$. This is still finite. The source avoids the dependent type, and the theorem on equal multiplicities (Section 2) shows that the sets $\mathcal{S}_j$ lie in $\mathcal{S}_m$.

**Exercise 7.** In Section 4, the lemma on clearing from a denominator bound drops the bound on inner products. Explain why clause 2 of `HasDenominatorsLe` is not a case of clause 1. What does the projection bound add?

*Hint.* Clause 1 is about the space $Z_{\vartheta, j}$ of rank $r$ lifts. Clause 2 is about a different pair, the lift from $U(1)$ to $U(2z)$, and a line in it. The projection bound turns integrality of $\Lambda(\mathrm{pr}\,y)$ and the bound on inner products into a bound on $\langle \mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi' \rangle$, at the cost of $v_\ell(h_{\mathrm{std}}) \log \ell$.

## Notes and references

The method of this chapter is the method of Ribet. A congruence between a lift and a form that is not a lift gives a nontrivial Selmer class, and a twist with small Selmer groups therefore bounds the congruences. Ribet used this to construct unramified extensions: K. A. Ribet, *A modular construction of unramified p-extensions of Q(μ_p)*, Invent. Math. 34 (1976), 151 to 162. The source names three later works in the docstring of the top file. They are K. Prasanna, *Integrality of a ratio of Petersson norms and level-lowering congruences*, Ann. of Math. 163 (2006), for the integrality of ratios of periods; K. Klosin, on congruences among modular forms on $U(2,2)$ and the Bloch and Kato conjecture, 2009; and B. Mazur and K. Rubin, *Ranks of twists of elliptic curves and Hilbert's tenth problem*, Invent. Math. 181 (2010), for twists that lower Selmer ranks. This book has not compared the source with these works.

The deep steps of the proof are in other chapters. Ribet's method in all ranks is in [from a congruence to a Selmer class](/chapter/denominator-bound/), with [Ribet elements](/chapter/ribet-elements/), [first-order deformations](/chapter/first-order-deformations/), [tied traces](/chapter/tied-traces/) and [the local loss](/chapter/local-loss/). The twist with short Selmer groups is in [the twisting theorem](/chapter/twisting-theorem/), with [tied Selmer groups](/chapter/tied-selmer-groups/), [exponent lattices](/chapter/exponent-lattices/) and [cup products](/chapter/cup-products/). The main summands are in [main summands](/chapter/main-summands/). This chapter only joins them.

Several merged chapters cite this chapter. [The four inputs](/chapter/theorem-c-plan/#the-four-inputs) and [the chapters of the volume](/chapter/theorem-c-plan/#the-chapters-of-the-volume) of Volume 11 cite the existence of regular families and its last step at one prime. Sections 5 and 7 state and prove both. [Regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists) cites the plan at one prime, in Section 5. [Regular families: the plan](/chapter/regular-families-plan/) cites the assembly of the chain, in Sections 3 to 7. The outline [Theorem C, long forms](/chapter/theorems-a-b-c/#theorem-c-long-forms) cites the construction of the family by Ribet's method and Selmer groups, in Sections 4 and 5. The register of findings cites the rows F-025 and F-082. Section 4 discusses F-025, and Section 9 discusses F-082.

The source file is New/Congruences/FitTwistsExist.lean. Its statements are those of Sections 3 to 7. The source claims these proofs, and Lean accepts them, if the reported checks hold. Section 9 lists the points where the plan of the volume and other chapters differ from the source.

Status: drafted by a model. No person has checked this chapter against the Lean source.
