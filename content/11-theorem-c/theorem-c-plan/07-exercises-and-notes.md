---
title: Exercises
lean:
  - New/Reduction/Lattices/Heights.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $q = 3/4$ and $M = 5$. Write out the terms of [the product formula for the rationals](/decl/New.log_product_formula/) and check that their sum is $0$. Then take $q = 7/4$ and $M = 5$. Show that the sum is not $0$, and say which hypothesis of the theorem fails.

*Hint.* For $q = 3/4$ the terms are $\log 3 - 2\log 2$, $2\log 2$ and $-\log 3$. For $q = 7/4$ the prime $7$ is not less than $M$.

**Exercise 2.** Show that the constant family $0$ has height at most $c$ for every real $c$. Then show that [the theorem that a nonzero number is not small everywhere](/decl/New.HeightLe.neg_le_of_norm_map_le/) is false for $z = 0$: find $c$ and $c'$ with $|\sigma 0| \leq e^{c'}$ for every $\sigma$ and $-c > c'$.

*Hint.* Take $H = 1$, $\alpha = c$ and $h = 0$ in the definition of [height](/decl/New.HeightLe/). Then take $c = 1$ and $c' = -2$.

**Exercise 3.** Let $y_1 = (1/2, 1/2)$ and $y_2 = (1/2, -1/2)$ in $\mathbb{Q}^2$. Compute the Gram determinant $G$, the smallest integer $Q \geq 1$ with $Q y_i \in \mathbb{Z}^2$, the covolume $c = d h$ with $e^h = \max\|y_i\|^2$, and the index $\delta = d\log Q$, as in the determinant version of Section 2. Check that $0 \leq c + 2\delta$. Is the inequality sharp here?

*Hint.* $G = 1/4$, $Q = 2$, $h = -\log 2$, so $c = -2\log 2$ and $\delta = 2\log 2$. Then $c + 2\delta = 2\log 2$. Compare with the integer $Q^{2d}G = 4$: the loss is the factor $4$, which the model inequality does not see.

**Exercise 4.** The hypothesis of Theorem C is $(1 - 4/b^2)\,d \leq n$, and the family extends by $n'$ auxiliary forms to a basis, so $n + n' = d$. Prove that $n' \leq 4d/b^2$. Then prove that $n'(2x_1^2b^2 + b) \leq d\,b$ when $4(2x_1^2 + b^{-1}) \leq b$. Show that the last condition holds when $x_1 \geq 2$ and $x_1^{10^6} \leq b$.

*Hint.* This is the arithmetic of [the lemma on the cost of completion](/decl/New.Data.mul_completion_cost_le/). For the last step, $8x_1^2 + 4 \leq x_1^{10}$ for $x_1 \geq 2$.

**Exercise 5.** The source defines $\mathrm{denominatorBudget} = f a\log^3 b/(mk)$. Show that $k\log b\cdot\mathrm{denominatorBudget} = f a\log^4 b/m$. The height bound for one lift is $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$. Add the bounds of the $m$ lifts and show that the sum is $d\,(f a\log^4 b - \mathrm{mainAmount})$. Which row of the table of the three errors in Section 3 does this give?

*Hint.* Use $\mathrm{mainAmount} = m k\cdot\mathrm{directionAmount}$. The answer is the row of the denominators.

**Exercise 6.** In the [square law](/decl/New.Exchange.SquareCommutes/) the scalar is a quotient, and in Lean $x/0 = 0$. Suppose that the denominator of the scalar of one square is $0$. What does the law then say about the composite of the lifts around that square? Explain why [the theorem on the scalars of the squares](/decl/New.Exchange.IsTriangle.ne_zero_of_squareCommutes/) excludes this case for a triangle with nonzero weights and $V \neq 0$, and find the hypothesis of the theorem that its proof uses for this.

*Hint.* If $\beta'(t) = 0$, the law says only that $w_t(n)\,a(d\,y) = 0$. The chains of a triangle with nonzero weights are injective, and $V \neq 0$ gives a nonzero vector that they do not kill.

**Exercise 7.** The ratio of a critical pair is a quotient of two absolute values of $L$-values. Use [the nonvanishing on the line](/decl/New.AutChar.HasWeight.L_ne_zero/) to show that the denominator is not $0$, and so that [the ratio is not zero](/decl/New.Data.CriticalPair.ratio_ne_zero/). Then explain why [the positivity of the algebraic part](/decl/New.Data.CriticalPair.algPart_pos/) is not needed for this.

*Hint.* Both $L$-values are taken at the real point $z \geq 1$, and both characters have nonzero weight. Positivity is used for the formula of the ratio as a quotient of algebraic parts, not for its nonvanishing.

## Notes and references

The product formula is in Neukirch, *Algebraic Number Theory*, Chapter III, §1, and Section 1.4 of Bombieri and Gubler, *Heights in Diophantine Geometry*. The heights of Section 2 differ from those of Bombieri and Gubler, Chapter 1: the number may depend on the prime, with one multiplier for all primes.

The argument of Section 2, a lower bound for a nonzero algebraic number from bounds at every place, is the basic step of many proofs in transcendence theory. The source names related work in its docstrings. For determinants of size and divisibility it names Bost, *Algebraic leaves of algebraic foliations over number fields* (2001), and Laurent, *Linear forms in two logarithms and interpolation determinants* (1994). For heights it names Gaudron, *Pentes des fibrés vectoriels adéliques sur un corps global* (2006). For the bound of the norm of a lift by an integral form and a denominator it names Böcherer, Dummigan and Schulze-Pillot, *Yoshida lifts and Selmer groups* (2012), X. Zhang (2018), and Hida, *Congruences of cusp forms and special values of their zeta functions* (1981). For norms of lifts of Hecke characters it names Prasanna, *Integrality of a ratio of Petersson norms* (2006). This book has not compared these works with the source, and it does not claim that the source follows any of them.

Status: drafted by a model. No person has checked this chapter against the Lean source.
