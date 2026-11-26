---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of the chapter. The valuation $v$ on $\mathbb{C}_p$ has $v(p) = 1$.

**Exercise 1.** Let $K \ge 1$ and $l = p^K - 1$. Show that Legendre's bound of Section 2 is an equality for one variable: $v_p(l!) = l/(p-1) - (\lfloor \log_p l \rfloor + 1)$. Show that for $l = p^K$ the bound is not an equality.

*Hint.* All $K$ digits of $p^K - 1$ in base $p$ are $p - 1$, so $s_p(l) = K(p-1)$, and $\lfloor \log_p(p^K - 1)\rfloor = K - 1$. For $l = p^K$ the digit sum is $1$, and $\lfloor \log_p l \rfloor + 1 = K + 1$.

**Exercise 2.** Show that the direction set of Section 2 has exactly $fN \cdot N(N-1)/2$ elements, where $f = |\Phi|$ and $N = |n'|$. Compare with the bound $fN^3$ of `New.card_directionVar_le` for $N = 2$ and for large $N$.

*Hint.* For a fixed place and row, the indices are the pairs $(h, k)$ with $k < h < N$, and $\sum_{h < N} h = N(N-1)/2$. For $N = 2$ the exact number is $f$ times $2$, and the bound is $8f$. For large $N$ the quotient of the bound by the exact number tends to $2$.

**Exercise 3.** Let $Q$ be a homogeneous polynomial of degree $l$ and $F$ a power series in the variables $\sigma$. Prove the lemma on rescaled jets of Section 6: $\mathrm{jet}(Q)(F(az)) = a^l\, \mathrm{jet}(Q)(F)$. Use it to show the following consequence of the integrality theorem of Section 8: if $f \in \mathrm{Std}_\delta(V)$ with $\delta \ne 0$, and $c = \bar\delta d\, p^k$ with $k \ge 0$, then $v(\mathrm{jet}(Q)(J_{c\,\mathrm{jetScale}} f)) \ge lk$ for every homogeneous $Q$ of degree $l$ with $p$-integral coefficients.

*Hint.* For a monomial $z^\alpha$ of degree $l$, the coefficient of $z^\alpha$ in $F(az)$ is $a^l F_\alpha$. The jet is linear in $Q$. For the consequence, $c/(\bar\delta d) = p^k$.

**Exercise 4.** Let $p$ be inert in $K$. Show that $\sum_{e \text{ odd}} p^{-e} = p/(p^2 - 1)$. Let $p = d$ be ramified, with $v(\pi_d) = 1/2$. Show that $\tfrac12 \sum_{e \ge 1} d^{-e} = 1/(2d - 2)$. These are the gains per box $\gamma_p$ and $\gamma_d$ in the examples of Section 4.

*Hint.* Both are geometric series. For the first, factor out $p^{-1}$ and sum in $p^{-2}$.

**Exercise 5.** The lemma "A point where a combination is large" of Section 5 uses that the residue field $k$ of $\mathcal{O}$ is infinite. Give a polynomial over $\mathbb{F}_p$ that is not zero and has the value $0$ at every point of $\mathbb{F}_p$. Explain why the lemma can fail if $\mathcal{O}$ is replaced by $\mathbb{Z}_p$.

*Hint.* Take $x^p - x$. Over $\mathbb{Z}_p$, let $b_1 = 1$ and $b_2 = x^p - x$, which have linearly independent reductions. With $\alpha_1 = p$ and $\alpha_2 = 1$, the value $p + (y^p - y)$ has valuation at least $1$ at every $y \in \mathbb{Z}_p$, by Fermat's little theorem, while $\|\alpha_2\| = 1$.

**Exercise 6.** In the example of Section 5, with $|n| = 1$, $|n'| = 2$ and $B$ columns of height one at one place, let $F$ be a series over $\mathbb{C}_p$ and let $y_0$ be integral. Show that $\|\mathrm{jet}(P_y)(F)\| = \|y_0\|^B\, \|\mathrm{schurJet}_\kappa(F)_{i',i}\|$. Deduce that the inequality of the theorem of Section 5 fails for $y_0 = p$ when the Schur entry is not zero, so the choice of the point matters.

*Hint.* The jet along $P_y$ is $y_0^B$ times the Schur entry. For $y_0 = p$ the factor is $p^{-B} < 1$.

**Exercise 7.** Let $p$ be inert, and let $\kappa$ have $B$ columns of height one at one place $\tau$ and nothing else, with no partner $-p^e\tau$, $e$ odd, equal to $\tau$. Assume that $D_p(\kappa) = \gamma_p B$, as in the example of Section 4 for $B = 1$. Find the least $B$ for which the divisibility bound of Section 8 is positive when $f = 1$, $N = 2$ and $p = 3$.

*Hint.* Here $\gamma_3 = 3/8$, and the bound is $\tfrac38 B - 8(1 + \log_3 B)$. Test $B = 100$, $B = 150$ and $B = 200$. Exercise 2 shows that the true number of variables for $N = 2$ is $2$, not $8$; redo the computation with $2$ in place of $8$, to see the effect of the loose bound.

## Notes and references

The count of this chapter, the change of directions and the integrality and divisibility of standard data are those of the source in New/Derivatives/Divisibility and New/Derivatives/Vacuum. The literature on the $p$-adic divisibility of the coefficients of theta functions and of formal groups with complex multiplication is listed in the remark at the end of Section 4. This chapter does not compare its statements with those works, and the source gives no places in them for its statements.

Legendre's formula for $v_p(m!)$ is classical, and the source has it in the form `New.padicValNat_factorial_mem_Icc`, in [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/). The Schur matrix and the polynomials $b_i$ are the integral Weyl modules of [integral Weyl modules and branching](/chapter/weyl-modules/). For the theory of these modules over the integers, see J. A. Green, *Polynomial Representations of $GL_n$*, Lecture Notes in Mathematics 830 (1980), and K. Akin, D. A. Buchsbaum and J. Weyman, *Schur functors and Schur complexes*, Adv. in Math. 44 (1982). The theta products and their normal form at a non-split prime are in [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/), and the background on the CM curve, its formal group and the period is in [CM elliptic curves](/chapter/cm-elliptic-curves/).

The loss $fN^3(1 + \log_p \max(B, 1))$ in the count comes from two places: Legendre's bound for the factorials, which loses $\lfloor\log_p B\rfloor + 1$ for each variable, and the number of new variables, which the source bounds by $fN^3$. The exact number is $fN^2(N-1)/2$ (Exercise 2). The loss is of lower order than $\gamma_p B$ as $B$ grows, with $N$ fixed. The question how large the factor $N^3$ must be is open in the project files (F-096, question Q-21).

The divisibility theorems of Section 8 are used in [theta kernels and gauges](/chapter/theta-kernels-gauges/), where the source file New/UpperBound/Kernels/ThetaLiftGauge.lean imports New/Derivatives/Vacuum/Divisibility.lean. The integral vacuum that gives the standard data is in [the integral vacuum](/chapter/integral-vacuum/), and the overall plan is in [the plan of Theorem A](/chapter/theorem-a-plan/).
