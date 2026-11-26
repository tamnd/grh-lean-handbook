---
title: Exercises
lean:
  - New/UpperBound/Size/ShortColumns.lean
  - New/Derivatives/Sharpness/NearPairs.lean
  - New/UpperBound/Divisibility/JetExponent.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $W$ be a complex inner product space and $u, w \in W$. Show that $\|u - w\|^2 \le 2\|u\|^2 + 2\|w\|^2$, with equality if and only if $w = -u$. Deduce the factor $4$ in the lemma on translates (Section 2) for a translate that keeps the norms of the values, and show that the factor cannot be lowered.

*Hint.* The parallelogram law is $\|u - w\|^2 + \|u + w\|^2 = 2\|u\|^2 + 2\|w\|^2$. For the last claim, use the eigenvalue $-1$ of the example in Section 4.

**Exercise 2.** Let $p = 3$ be inert in $K$ and let $d = 7$. Compute $\gamma_3$ and $\gamma_7$ from the definition $\gamma_p = 1/(p-1) - \rho_p$, and check the values against the series $\sum_{e\in I_p}v(\pi_p)p^{-e}$ of Section 5.

*Hint.* $\gamma_3 = \frac12 - \frac18 = \frac38$, and $\sum_{e\text{ odd}}3^{-e} = \frac13\cdot\frac98 = \frac38$. For $p = d = 7$, $v(\pi_7) = \frac12$, $\rho_7 = \frac1{12}$, and $\gamma_7 = \frac16 - \frac1{12} = \frac1{12} = \frac12\sum_{e\ge1}7^{-e}$.

**Exercise 3.** Check the lemma on Legendre's formula with digits (Section 6) for $p = 3$ and $n = 100$. Compute $v_3(100!)$ in two ways: by the recursion $v(n!) = \lfloor n/p\rfloor + v(\lfloor n/p\rfloor!)$, and by the digit sum. Find the least $K$ with $100 < 3^K$ and check that $100/2 - K \le v_3(100!) \le 100/2$.

*Hint.* The recursion gives $33 + 11 + 3 + 1 = 48$. In base $3$, $100 = 10201_3$, with digit sum $4$, and $(100 - 4)/2 = 48$. The least $K$ is $5$, since $3^4 = 81$ and $3^5 = 243$.

**Exercise 4.** Let $p$ be a prime with $p \le k$ and $\chi_K(p) \ne 1$. Show that the number of near pairs at $p$ is at most $\#\Phi_b/2$.

*Hint.* Map each near pair to its start and to its end. By the lemmas of Section 6, the starts are distinct, the ends are distinct, and no end is a start. So the starts and the ends are $2\#\{\text{near pairs}\}$ distinct elements of $\Phi_b$.

**Exercise 5.** Take $n^\sharp = 3$ and $l = 10$ in the definition of the loss product. Compute $l^-$ and $B_l$, and check that $l^-!\,B_l = l!$. For $p = 2$, check $v_2(3!) \le v_2(B_l)$ and $n^\sharp/p - 1 \le v_2(B_l)$. Then take $l = 2$ and say what changes.

*Hint.* $l^- = 7$ and $B_{10} = 8\cdot9\cdot10 = 720 = 2^4\cdot3^2\cdot5$. So $v_2(B_{10}) = 4$, $v_2(3!) = 1$ and $n^\sharp/2 - 1 = \frac12$. For $l = 2$, $l^- = 0$ and $B_2 = 3! = 6$, so $l! = 2$ divides $l^-!\,B_2 = 6$ but is not equal to it.

**Exercise 6.** For reals $y, z$ show that $y - (y - z)_+ = \min(y, z)$. For a place $\tau$, deduce the identity $R_\tau = (\kappa(\tau)\gamma_p - s_p(\kappa(\tau), \tau))/v(\pi_p)$ of Section 6 directly from the series. Why must both series converge before the subtraction?

*Hint.* Treat the cases $y \le z$ and $y > z$. For the last question: a `tsum` of a series that does not converge is $0$, so term by term subtraction is valid only for summable families. Here both families are bounded by $\kappa(\tau)/p^e$ on $I_p$.

**Exercise 7.** In the example at the end of Section 7, let $\tau$ and $\tau' = u(-p^e)\tau$ be $a$-places outside $S$ for one odd $e$. Compute the term of the gain and the partner term at this $e$, and show that their difference is at least $a/p^e - a/x_1 - x^{60}$. Explain why the theorem that only collisions lose cannot hold without the term $\mathrm{coll}_p(S)$ when $a/p^e$ is large.

*Hint.* The partner term has $L_\tau/p^e - L_{\tau'} \le a/p - a < 0$, so its first positive part is $0$. The low column part of the gain is matched by the second positive part, up to $x^{60}$, by the lemma on low columns. The weight of $\tau'$ is $a/x_1$, since $\tau'$ is not a $b$-place.

## Notes and references

The three Lean files of this chapter are New/UpperBound/Size/ShortColumns.lean, New/Derivatives/Sharpness/NearPairs.lean and New/UpperBound/Divisibility/JetExponent.lean. The handbook states every result of these files that the other chapters use, with the proof that the files give.

The plan of this volume once listed the chapters in another order, and it placed the file on near pairs in Volume 11. The order of the volume file is the one used here. The results on near pairs are used in Volume 11 by [the divisibility is sharp](/chapter/sharpness/), through New/Derivatives/Sharpness/Cases.lean. Theorem A does not use them.

The formula $v_p(n!) = \sum_{i\ge1}\lfloor n/p^i\rfloor = (n - s_p(n))/(p - 1)$, with $s_p(n)$ the sum of the base $p$ digits of $n$, is Legendre's formula. Section 6 uses it in the form proved in Lib/General/Algebra/IntegralPowerSeries.lean. The parallelogram law behind the factor $4$ in Sections 2 and 4 holds in every inner product space.

The short bases at a free level come from [reduction theory](/chapter/reduction-theory/). The evaluation vectors of the Weyl modules come from [Weyl modules](/chapter/weyl-modules/). The scales, the weights and the table of sizes are in [the data and its sizes](/chapter/data-and-sizes/). The predicted divisibility and the count are in [the count and the divisibility of standard data](/chapter/normal-forms/), and the theta kernels that the file ShortColumns.lean imports are in [theta kernels and gauges](/chapter/theta-kernels-gauges/).

The users of this chapter are [the proof of Theorem A](/chapter/proof-of-theorem-a/), for the short ramified forms, and [divisibility prime by prime](/chapter/divisibility/), for the bound on the divisibility bound. The scalings of Section 3 are also stated in [the objects of the upper bound](/chapter/upper-bound-objects/), Section 8. These chapters check the steps of a formal argument. They do not claim that the argument as a whole is correct.
