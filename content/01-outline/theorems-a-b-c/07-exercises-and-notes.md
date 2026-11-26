---
title: Exercises and notes
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

1. *The model case is sharp.* Let $Q \geq 1$ be an integer and let $y_i = e_i/Q$ in $\mathbb{R}^d$, for the standard basis $e_1, \dots, e_d$. Compute the covolume $c = \log|\det(y)|^2$ and the index $\delta = d\log Q$, and show that $c + 2\delta = 0$. Then let $y_1, \dots, y_d$ be any independent vectors with $Qy_i \in \mathbb{Z}^d$ and $\|y_i\|^2 \leq e^h$, and show that $dh + 2d\log Q \geq 0$. *Hint.* $Q^d\det(y)$ is a nonzero integer.

2. *The step of the greedy cover.* Let $0 < \varepsilon_0$ and $0 \leq \alpha < 1$ with $16\varepsilon_0 < 1 - \alpha$. Show that $(1 - \alpha)/2 - 3\varepsilon_0/2 \geq \frac{2}{5}(1 - \alpha)$. *Hint.* $13/32 > 2/5$.

3. *The number of translates.* Let $b^2 \geq 2$ and $\varepsilon_0 = (8b^2)^{-1}$. Show that $\frac{5}{2}(1 + \log(1/(16\varepsilon_0))) \leq 5\log(1 + 2b^2)$. *Hint.* $1/(16\varepsilon_0) = b^2/2 \leq 1 + 2b^2$, and $1 + 2b^2 \geq 5 > e$.

4. *The budget.* Show that $20\log(1 + 2b^2) \leq 60\log b$ for $b \geq 3$. Deduce that the sum of the three errors in the table of Section 1 is at most $64 f a\log^4 b$ when $\log b \geq 1$. *Hint.* $1 + 2b^2 \leq b^3$ for $b \geq 3$.

5. *The cost of completion.* Let $n + n' = d$ and $n \geq (1 - 4/b^2)\,d$. Show that $n' \leq 4d/b^2$, and that $n'(2x_1^2b^2 + b) \leq d\cdot 4(2x_1^2 + b^{-1})$. Explain why the factor $b^2$ in the size of an auxiliary form does not appear in the final cost.

6. *A unit says nothing.* Let $A, B : V \to W$ be linear maps and $a \in \mathbb{C}$ with $A = aB$. Define $u \in \mathbb{C}^\times$ by $u = a^{-1}$ if $a \neq 0$ and $u = 1$ if $a = 0$, and put $A' = u\,a\,B$. Show that $A = u^{-1}A'$ in both cases, and that $A' = 0$ if $a = 0$. Conclude that an identity of the form $A = c\,A'$ with a unit $c$, where $A'$ carries the factor $u\,a$, holds whether or not $a = 0$, and so it does not show that $a \neq 0$. Compare with the Remark (Formalization) on the seesaw constant in Section 2.

7. *The sign in the assembly.* Let $d \geq n > 0$, and let $\mathrm{main}, \mathrm{loss}, R, I$ be real numbers with $d(\mathrm{main} - 3\,\mathrm{loss}) \leq n(\mathrm{main} - R + \mathrm{loss}) + dI$. Show that if $\mathrm{main} + \mathrm{loss} \geq 0$, then $nR \leq d(4\,\mathrm{loss} + I)$. Find numbers with $\mathrm{main} + \mathrm{loss} < 0$ for which the conclusion fails. Which lemma of the source supplies $\mathrm{main} + \mathrm{loss} \geq 0$?

### Notes and references

This chapter follows the source files New/Reduction/ShortAndEnough.lean and New/Determinant/Twist/LongForms.lean, and the header of New/Reduction/MainInequality.lean, whose table of errors and list of cancellations Sections 1 and 6 reproduce.

The lower bound of Theorem C is an argument of the kind used for interpolation determinants and for slopes of adelic vector bundles: a nonzero algebraic number cannot be small at every place, by the product formula. The source names Bost, *Algebraic leaves of algebraic foliations over number fields* (2001), and Laurent, *Linear forms in two logarithms and interpolation determinants* (1994), as related work for twisted lattices. For heights it names Gaudron, *Pentes des fibrés vectoriels adéliques sur un corps global* (2006), and Bombieri and Gubler, *Heights in Diophantine Geometry* (2006), Chapter 1. The definition of height in Section 1 differs from the textbook height of a point in projective space: it is a bound for a family indexed by the pairs $\iota$, with one multiplier for all $\iota$, so that each prime may use its own twist.

For Theorem B the source names Petersson, *Über die Entwicklungskoeffizienten der automorphen Formen* (1932), for spanning by Poincaré series, and Muić, *Spectral decomposition of compactly supported Poincaré series and existence of cusp forms* (2010). It names Benedetto and Fickus, *Finite normalized tight frames* (2003), for the link between the least second moment and tight frames. For the linear algebra of Section 4 it names Welch (1974) for rank bounds from second moments, and Wolsey (1982), on the greedy algorithm for the submodular set covering problem, for the greedy cover with a logarithmic loss.

For the regular families of Theorem C the source names Prasanna, *Integrality of a ratio of Petersson norms* (2006), after Ribet (1976) and Wiles; Klosin, *Congruences among modular forms on U(2,2) and the Bloch-Kato conjecture* (2009); and Mazur and Rubin, *Ranks of twists of elliptic curves* (2010). For the height of one lift determinant it names Böcherer, Dummigan and Schulze-Pillot, *Yoshida lifts and Selmer groups* (2012); X. Zhang, *Special L-values and Selmer groups of Siegel modular forms of genus 2* (2018); and Hida, *Congruences of cusp forms and special values of their zeta functions* (1981). For the main inequality as a whole it names Pritsker (2005), Granville and Stark (2000), Bombieri, *Counting points on curves over finite fields*, Séminaire Bourbaki 430 (1973), and van Frankenhuijsen (2008), as earlier bounds of sums over primes by size against divisibility. This book has not compared these citations with the statements of the source.

The method of Theorem A, a lift of a Poincaré series computed by a seesaw identity and bounded by its divisibility at the primes, is the subject of Volume 9. The use of `choose` for the divisibility errors and the seesaw constant does not change the content of the statements (Section 2), but these constants cannot be computed from their definitions.

Status: drafted by a model. No person has checked this chapter against the Lean source.
