---
title: Exercises and notes
lean:
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 1 to 5. The sizes are those of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes): $m^2 \leq 4x$, $r \leq 3x^5$, $t = 5r$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$, $a = xb$, $f \geq 1$ and $\log b \geq 1$.

**Exercise 1.** Prove the cost of completion by hand. Let $n, n' \in \mathbb{N}$ with $(1 - 4/b^2)\,d \leq n$ and $d = n + n'$. Show that $n' \leq 4d/b^2$, and then that $n'(2x_1^2b^2 + b) \leq d\cdot 4(2x_1^2 + b^{-1})$. Show last that $4(2x_1^2 + b^{-1}) \leq b$.

*Hint.* Subtract the hypothesis from $d = n + n'$. For the last step, $b^{-1} \leq 1$ and $8x_1^2 + 4 \leq x_1^{10} \leq b$ for $x_1 \geq 2$. Compare with [the cost of completion](/decl/New.Data.mul_completion_cost_le/).

**Exercise 2.** Show that $2\,m\,m\,(t\,x_1) \leq b$. Then show that the scalar of the auxiliary forms and the scalar of the chain together cost at most $2d\,b$ in Theorem C, and explain why the source still writes the error as $3\,d\,fa\log^4 b$.

*Hint.* $2m^2tx_1 \leq 2\cdot 4x\cdot 15x^5\cdot x_1 = 120x^6x_1$, and $120x^6 \leq x_1$. The scalar of the auxiliary forms enters through $n'b \leq d\,b$, the scalar of the chain through the term $d\,b$ of $b_{\mathrm{volume}}$. Both are absorbed by $b \leq fa\log^4 b$.

**Exercise 3.** Let $\mathrm{err}_0 = fa\log^3 b$ and $\mathrm{denominatorBudget} = \mathrm{err}_0/(mk)$. Show that $k\log b\cdot\mathrm{denominatorBudget} = fa\log^4 b/m$. Then show that the $m$ bounds of [single lifts at good twists](/chapter/proof-of-theorem-c/#a-twist-for-each-prime-and-the-inverse-ratio) sum to $d(fa\log^4 b - \mathrm{mainAmount})$.

*Hint.* The source needs $k \neq 0$ and $m \neq 0$ for `field_simp`. Both are positive by the sizes. For the sum, $\mathrm{mainAmount} = m\,k\cdot\mathrm{directionAmount}$, and the index set $[1, m]$ has $m$ elements.

**Exercise 4.** Let $y$ have index at most $\delta$ in a twisted lattice. Show that $\delta \geq 0$. Then show that Theorem C gives nothing when $\mathrm{mainAmount} \leq 3fa\log^4 b$ and $c \geq 0$.

*Hint.* The condition of the index holds for every finite set of primes, so also for the empty set. Read [index at most δ](/decl/New.TwistedLattice.IndexLe/). In the second part, the left side of Theorem C is at most $0$.

**Exercise 5.** Consider the case $n' = 0$, that is, $n = d$. Write out the proof of Theorem C in this case. Which inputs are not needed? Which constant becomes $0$?

*Hint.* No auxiliary forms are adjoined, so the term $n'(b_{\mathrm{short}} + b_{\mathrm{denom}})$ is $0$. The source does not split the cases. The frame of [the theorem on a twist for each prime](/decl/New.TwistedLattice.covolume_add_index_nonneg/) holds for every $n'$, and the proof uses the scalar $\gamma$ only through the forms $z_i$.

**Exercise 6.** Derive the inverted factorization from the factorization. Let $Z(\vartheta)/Z(1) = s(\vartheta)^d\prod_{j=1}^m Z_j(\vartheta)/Z_j(1)$ with $s(\vartheta)$ real. Show that $Z(1)/Z(\vartheta) = (s(\vartheta)^{-1})^d\prod_{j=1}^m Z_j(1)/Z_j(\vartheta)$, with the conventions of Lean for division by zero.

*Hint.* Use $(u/v)^{-1} = v/u$, $(uv)^{-1} = u^{-1}v^{-1}$, $(u^d)^{-1} = (u^{-1})^d$ and that the inverse of a product is the product of the inverses. Each holds in a field also when a factor is $0$, as $0^{-1} = 0$ in Lean. Compare with [the inverted factorization](/decl/New.Data.exists_chainDeterminant_one_div_eq/).

**Exercise 7.** In the main inequality, $c = nL$ with $L = \mathrm{mainAmount} - m\cdot\mathrm{rem} + fa\log^4 b$ and $\delta = d\cdot 10\log(1 + 2b^2)\,\mathrm{err}_0$. Assume $n = d$. Use Theorem C to show that $m\cdot\mathrm{rem} \leq 4fa\log^4 b + 20\log(1 + 2b^2)\,\mathrm{err}_0$.

*Hint.* Divide $d(\mathrm{mainAmount} - 3fa\log^4 b) \leq dL + 2\delta$ by $d > 0$. For $n < d$ the term $(d - n)\,\mathrm{mainAmount}$ appears, and the source bounds it with $n \geq (1 - 4/b^2)d$. See [the main inequality](/chapter/main-inequality/#the-main-inequality).

## Notes and references

The proof of this chapter is a lower bound for the covolume of a lattice from its behavior at every place. It is the step of the height argument of the source that combines the archimedean and the nonarchimedean bounds. The local step uses the product formula for a nonzero algebraic number. The source names Bombieri and Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006, Chapter 1, for heights. The heights of this chapter differ from theirs: the number may depend on the prime, with one multiplier for all primes ([heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers)).

The bound for the covolume of a family with adjoined short vectors uses Fischer's inequality and Hadamard's inequality for positive semidefinite Gram matrices. The source names both in New/Reduction/Lattices/TwistedLattice.lean. A standard reference is Horn and Johnson, *Matrix Analysis*, Cambridge University Press, second edition, 2013.

The factorization of the chain determinant rests on the inner product formula of Rallis, *L-Functions and the Oscillator Representation*, Lecture Notes in Mathematics 1245, Springer, 1987. The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) gives the form that the source uses. This book has not compared the source with that work.

Several merged chapters cite this chapter. The chapter [twists, critical pairs and regular families](/chapter/twists-critical-pairs/#regular-families-of-twists) cites the theorem on single lifts at good twists. Section 4 states and proves it. The chapter [twisted lattices](/chapter/twisted-lattices/#the-lattice-inequality) cites the application of the frame to the target lattice. Step 6 of Section 5 gives it. The chapters [the height of one lift determinant](/chapter/lift-volume-height/#the-height-bound) and [Hecke values of character lifts](/chapter/hecke-values/) cite the combination of the height bounds into Theorem C. Steps 1, 5 and 7 of Section 5 give it, and the constants table of Section 5 shows where the term $-d\,k\cdot\mathrm{directionAmount}$ becomes the main amount. The outline [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-c-long-forms) refers to this chapter for the full proof.

The source file is New/Determinant/Twist/LongForms.lean. Its statements are those of Sections 3 to 5. The source claims these proofs, and Lean accepts them, if the reported checks hold. Section 7 lists the points where the plan of the volume differs from the source.

Status: drafted by a model. No person has checked this chapter against the Lean source.
