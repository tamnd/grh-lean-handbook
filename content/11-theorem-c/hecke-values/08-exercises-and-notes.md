---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 7.

**Exercise 1.** Let $G$ be a finite abelian group and $s : G \to \mathbb{C}$. Show that $\sum_{\psi\in\hat G}\frac{1}{\#G}\sum_{g\in G}\psi(g)s(g) = s(1)$. Deduce the lemma on twisted means of Section 6 for an ultrametric norm, with $z = 1$.

*Hint.* Exchange the sums and use $\sum_\psi\psi(g) = \#G$ if $g = 1$ and $0$ otherwise.

**Exercise 2.** In the pigeonhole lemma of Section 6, let $G = \mathbb{Z}/2$, $a = (1, 4)$ and $b = (2, 1)$, with $\iota$ the usual absolute value. Then $V^2 = (1\cdot 2)(4\cdot 1) = 8$. For $\psi = 0$ find the factorisation $\phi + \chi = 0$ that the proof chooses, and check $|V| \leq |a(\phi)b(\chi)|$.

*Hint.* The two candidates are $a(0)b(0) = 2$ and $a(1)b(1) = 4$, and $|V| = \sqrt 8$.

**Exercise 3.** Show that $\mathrm{jetSize}(i) = \log i! + i\log(M/\Omega)$ is increasing in $i$ when $M \geq \Omega$. Explain why the proof of the height of the untwisted norm in Section 5 needs $c_\tau - z \geq \kappa_\tau$ and not an upper bound.

*Hint.* $\mathrm{jetSize}(i+1) - \mathrm{jetSize}(i) = \log(i+1) + \log(M/\Omega)$. The jet sizes enter $\log|\sigma H|$ with a minus sign.

**Exercise 4.** Check the count of Section 7: for $m$ even, the sets $(0, 7(m/2)]$, $(0, m]$ and $(0, m/2]$ have together $5m$ elements. For $k$ even, the set $(7(m/2), 7(m/2) + k/2]$ has $k/2$ elements. Deduce the bound $10\,m\,x_1 + k(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$ from the heights $x_1$ and $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$ of single inverse ratios.

*Hint.* The product of ratios is squared, so each height is counted twice.

**Exercise 5.** Let $\varphi \neq 0$ in a Hilbert space and $\mathrm{pr}$ the orthogonal projection to $\mathbb{C}\varphi$. Prove $\langle\mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle = \langle\Xi, \varphi\rangle\langle\varphi, \Xi'\rangle/\|\varphi\|^2$, with the inner product linear in the second variable.

*Hint.* $\mathrm{pr}\,\Xi = \frac{\langle\varphi, \Xi\rangle}{\|\varphi\|^2}\varphi$.

**Exercise 6.** In the seesaw of Section 6 the blocks have sizes $12$, $4$, $4$ and $2z - 20$. The theorem on periods of false lifts needs $2\#r + 2\#N + 3 < \#n$ with $\#r = 1$ and $\#N = 20$. For which $z$ does this hold? Why does a main pair satisfy it?

*Hint.* The condition is $45 < 2z$. A main pair has $z > m \geq 10000$.

**Exercise 7.** Let $q$ be flat on $2z$ indices. Show that the lift data of $q$ have row lengths $0$ and that the weight of the lift has dimension $1$. Use this to explain why $r \leq 4f$ in the lemma on the size of a squared norm of Section 5 holds for flat pairs, but only $r \geq -4f$ for main pairs.

*Hint.* The row length at $\tau$ is $c_\tau - z$. For a main pair, $\log d$ can be large.

**Exercise 8.** In Step 3 of the height of the inverse ratio (Section 7), the second test form is taken at the place $\iota\circ\mathrm{conj}$. Show that $|\iota(\overline{x})|$ at $\iota$ equals $|(\iota\circ\mathrm{conj})(x)|$, and use it to turn the bound of Section 6 at $\iota\circ\mathrm{conj}$ into a bound for $|\iota\langle\varphi, \Xi'\rangle|$. Why is it important that $\rho$ is real?

*Hint.* $\langle\varphi, \Xi'\rangle = \overline{\langle\Xi', \varphi\rangle}$, and $\overline{c_0\rho} = \bar c_0\rho$ only when $\rho$ is real.

## Notes and references

**Sources.** The files are New/OneLift/HeckeValues/CentralAction.lean, PeriodAtOne.lean, AlgebraicPartIntegrality.lean, AlgebraicPartSize.lean and TwistedValueHeights.lean of the source. The statements of this chapter are those of these files. The source claims that the bounds combine to Theorem C in [the proof of Theorem C](/chapter/proof-of-theorem-c/), through [the height of one lift determinant](/chapter/lift-volume-height/).

**Literature.** Norms of theta lifts of Hecke characters are $L$-values by the Rallis inner product formula. The source file names three related works: K. Prasanna, *Integrality of a ratio of Petersson norms and level-lowering congruences*, Ann. of Math. 163 (2006); J. Coates, Z. Liang and R. Sujatha, *The Tate-Shafarevich group for elliptic curves with complex multiplication II*, Milan J. Math. 78 (2010), after N. Katz (1977); and Y.-S. Lee, *Hida family of theta lift from U(1) to definite U(2)* (2024). The method of this chapter, test forms orthogonal to false lifts and the seesaw on four blocks, is specific to the source.

**Forward references.** TwistedValueHeights.lean imports files of three later chapters of this volume: [false lifts](/chapter/false-lifts/), [the divisibility is sharp](/chapter/sharpness/) and [the comparison operator, part 2](/chapter/comparison-operator-2/). Section 6 and Section 7 state the results used. It also imports a file of Volume 12 for two lemmas on chosen places.

**Findings.** F-095 (open): the bound $\exp(x^{34})$ for the conjugates of flat algebraic parts, and the range $[\kappa, \kappa + x^{42}]$ of jet degrees. F-120 and F-033 (explained): the nonvanishing and the positivity of the ratio.

**Order of the plan.** The plan of the volume ([the chapters of the volume](/chapter/theorem-c-plan/#the-chapters-of-the-volume)) says that this chapter proves that the algebraic part is positive. That proof, `algPart_pos`, is in [the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part). The norm formula `inner_trivialLift_self_eq_L` is proved in [the norm of the lift](/chapter/character-lifts/#the-norm-of-the-lift).
