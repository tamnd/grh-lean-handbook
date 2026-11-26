---
title: Exercises and notes
lean:
  - New/OneLift/ComparisonOperator/GluingMaps.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 8. The pair is the $j$-th descent pair at a twist $\vartheta$, with $W_j$ of rank $r$, $V_j = V'' \oplus V^\circ$, and the choices $i$ with matrices $\Lambda$.

**Exercise 1.** Let $T$ be a linear map between finite dimensional inner product spaces, and $c$ a number. Show that $cT = S$ if $c\langle\zeta, Ty\rangle = \langle\zeta, Sy\rangle$ for all $\zeta$ and $y$. Use this to derive the operator form of the seesaw identity from its form with inner products. Then show that $c'_\vartheta = 0$ would force $\Theta^\circ = 0$.

*Hint.* Take $\zeta = cTy - Sy$. This is the step `ext_inner_left` in the proof of the seesaw.

**Exercise 2.** In the proof of injectivity of $\Theta^\circ$, the test tuple $\eta$ is $\zeta$ in copy $i$ and $0$ in the other copies. Write out $\langle\eta, \Theta^\circ y\rangle$ with the formula for the inner product of $\Theta^\circ$, and show that only the term $i$ is left. Why must the glue factor $c^\circ_i$ be nonzero for the argument to work?

*Hint.* The pairing $\Theta(\zeta)$ is conjugate linear in $\zeta$, so $\Theta(0) = 0$.

**Exercise 3.** Check the rank conditions of the chapter for $m = 2$ and $r = 212$, so $k$ can be any integer with $209 < k \leq 212$. Compute $t = 5r$, $\mathrm{rank}\,V'' = r + 9m + 1$, $\mathrm{rank}\,V^\circ = t - 9m - 1$ and the condition $r + 2\,\mathrm{rank}\,V'' + 3 < t$ of the false lifts. Also check $2r < \mathrm{rank}\,V^\circ$, the convergent range used in Step 2 of products span.

*Hint.* $\mathrm{rank}\,V'' = 231$, $\mathrm{rank}\,V^\circ = 1041$, and $r + 2\cdot 231 + 3 = 677 < 1060$.

**Exercise 4.** The gluing map has the factor $M^{l_1}$. Show that without it the gluing map can fail to keep integrality. Take a Cartan product whose gauge is $\|M\|^{-l_1}$ times the product of the gauges of its factors, and compute the gauge of $M^{l_1}$ times it at a place over a prime $l$ that divides $M$. What happens at a prime $l$ prime to $M$?

*Hint.* The gauge of $M^{l_1}v$ is $\|M\|^{l_1}$ times the gauge of $v$. At $l$ prime to $M$, $\|M\| = 1$ and the factor does nothing.

**Exercise 5.** The norm bound for the gluing map is stated only at the trivial twist. Find the step of its proof that uses $\vartheta = 1$. Then explain why the comparison operator needs the bound only at $\vartheta = 1$, given the seesaw identity and the formula $|c'_\vartheta|^2 = C/\Gamma_j(\vartheta)$.

*Hint.* Look at the first factor bound and at the lemma that every place of the level contains $\varpi^2$. The seesaw sends the problem at $\vartheta$ to the fixed map $\Theta^\circ$.

**Exercise 6.** In the example of Section 6, replace $B = b^{n_*}$ by $B = 2$. Does the contradiction $(4B + 1)\cdot 2B^{-19} < 1$ still hold? Find the least integer $B \geq 1$ for which it holds.

*Hint.* For $B = 1$ the left side is $10$. For $B = 2$ it is $18\cdot 2^{-19}$.

## Notes and references

**What the chapter gives.** The source claims that the comparison operator of [the height of one lift determinant](/chapter/lift-volume-height/) exists with four properties: a nonzero ratio, orthogonality to the false lifts, integrality, and a squared norm of at most $\exp(3fmb\log^2 b)^2$. This chapter supplies the gluing map, the seesaw identity $c'_\vartheta\,\mathrm{glue}_\vartheta^*\Theta_{j,\vartheta} = \Theta^\circ$ with $c'_\vartheta \neq 0$, and the bounds of Section 8. Lean accepts these results, if the reported checks hold. The construction of the operator from them is in the later chapter.

**The seesaw.** The name comes from Kudla's seesaw principle for two dual pairs $(U(W_j), U(V_j))$ and $(U(W_j)\times U(W_j), U(V'')\times U(V^\circ))$, where the theta kernel of $V_j$ restricts to the product of the two kernels. The source does not use the principle in its general form. It proves the needed case by hand: the descent of a product form is a sum of products of a first factor series and a kernel of $(W_j, V^\circ)$ ([the descent of product forms](/chapter/comparison-operator-1/#descent-of-product-forms)). The scalar $c'_\vartheta$ comes from the three exchanges of Sections 2 to 4.

**Why products span.** The argument of Sections 5 and 6 replaces an appeal to the density of products of theta series. A good form orthogonal to all products $\mathsf{F}_i\,\Theta(\zeta)$ is zero by a peak argument: near a peak the functions $\mathsf{F}_i$ approximate a fixed holomorphic function $\mathsf{F}^0$ ([approximation near a peak](/chapter/comparison-operator-2/#approximation-near-a-peak)), and the isolation estimate of [the first part](/chapter/comparison-operator-1/#isolation) turns this into a contradiction. The gain $b^{-20n_*}$ from the sparse sums pays for two losses of size $b^{n_*}$.

**False lifts.** The orthogonality to the false lifts rests on the vanishing of the periods of false lifts, proved in [false lifts](/chapter/false-lifts/). That chapter is earlier in this volume. Section 8 states its two results once and checks their hypotheses: the hyperplane sums, the descent, and the tame part at the places of $Q$.

**Formalization.** The definitions of the glued lattice, the first factor scale and the twist factor use `choose`. The number $C$ in $|c'_\vartheta|^2 = C/\Gamma_j(\vartheta)$ is not known to be nonzero in Lean until $c'_\vartheta \neq 0$ is proved through the injectivity of $\Theta^\circ$. The uses of `seal` and `set_option` only control definitional unfolding.

**Where the results go.** The seesaw identity, the injectivity of $\Theta^\circ$, the integrality and the norm bound of the gluing map enter [the height of one lift determinant](/chapter/lift-volume-height/).
