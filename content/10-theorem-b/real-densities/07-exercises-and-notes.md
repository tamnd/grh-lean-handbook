---
title: Exercises and notes
lean:
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Frames/RealShells.lean
  - New/Spanning/Frames/RealBandLimits.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $m > 0$ be the largest modulus of an entry of $x - 1$. Show that $x$ lies in the dyadic shell $S_i$ with $i = \max(0, \lceil \log_2 m \rceil)$. Which shell contains $x = 1$? Show that the shells are pairwise disjoint.

*Hint.* The set of $l$ with $m \leq 2^l$ is $\{l : l \geq \log_2 m\}$. For $x = 1$ every $l$ works, so $x \in S_0$. A set of natural numbers has at most one least element.

**Exercise 2.** Check the exponents in the [lemma on the scale](/decl/New.Floors.IsCutBessel.two_mul_div_pow_le_of_pow_le/). Show that $(11n + 1) \cdot 99n + 1 \leq 2400 n^2$ for every $n \geq 1$. Find the least exponent $E$ such that the same proof works with $L^{E n^2}$ in place of $L^{2400 n^2}$ for all $n \geq 1$.

*Hint.* The left side is $1089 n^2 + 99 n + 1 \leq 1189 n^2$. The proof needs $1089 n^2 + 99n + 1 \leq E n^2$ for all $n \geq 1$, and $n = 1$ is the worst case. So $E = 1189$.

**Exercise 3.** Let $R = 10$, $K = 2$ and let $p$ start with $p_0 = 1/2$, $p_1 = 1/3$, $p_2 = 100$. Compute the head weights $\Lambda_{R,K}(i, p)$ for $i = 1, 2, 3$. For $\rho = 4$ and $q = p$, follow the induction in [the gauge for two heads](/decl/New.Floors.IsCutBessel.exists_gauge_isHead/) and find the scale $L$ for $j = 2$.

*Hint.* The partial products are $\delta_0 = 1/2$, $\delta_1 = 1/6$ and $\delta_2 = 50/3$. The weights are $4$, $4 \cdot 36 = 144$ and $0$, since $|\delta_2| > R$. The scales are $\rho = 4$ for $j = 0$, then $\max(4, |\delta_0|^{-1}) = 4$, then $\max(4, |\delta_1|^{-1}) = 6$. So $L = 6$. The lemma gives $L^2 = 36 \leq \rho^2 \Lambda(2, p) \Lambda(2, q) = 16 \cdot 144^2$, which is far from sharp here.

**Exercise 4.** Let $\ell_K(t) = t^K \min(1, t)^6$. Show that the decay $\beta(\xi) = \Theta\, b^{2000 n^9}\, \ell_K(|\xi|^{-1})$ is decreasing in $|\xi|$. Show that $\beta(\xi) = \Theta\, b^{2000n^9} |\xi|^{-K}$ for $|\xi| \leq 1$ and $\beta(\xi) = \Theta\, b^{2000n^9} |\xi|^{-K-6}$ for $|\xi| \geq 1$. Explain why the extra power $6$ helps when $\beta$ is integrated over $\xi \in \mathbb C$.

*Hint.* Both $t^K$ and $\min(1, t)^6$ are increasing in $t \geq 0$. The integral of $|\xi|^{-K-6}$ over $|\xi| \geq 1$ in $\mathbb C$ converges for $K + 6 > 2$, with no condition on $K$ beyond $K \geq 0$.

**Exercise 5.** Show that $c_F\, \lambda\, (\lambda |I|)^2 = \lambda \operatorname{vol} U(k)/\operatorname{vol} U(r)$. Deduce [the bound on the constant](/decl/New.Floors.IsCutBessel.enorm_formConst_mul_le_one/) from the bound on $\lambda$ of [Section 2](/chapter/real-densities/#haar-measure-and-the-floors). What goes wrong in the formula for $c_F$ if $\lambda = \infty$ is allowed?

*Hint.* Cancel $(\lambda |I|)^2$ in the definition of $c_F$. For $\lambda = \infty$ the real part `toReal` is $0$, so the source value of $c_F$ is a division by $0$, which Lean sets to $0$.

**Exercise 6.** In the [mass at a real place](/decl/New.Floors.IsCutBessel.norm_floorForm_zero_le/), the near positions give $(1 + b^{-12})^2/\deg$ and the remote positions give $b^{-12}/\deg$. For $b = 2$, compute the gap between $1 + b^{-10}$ and the sum of the two numerators. For which $b \geq 2$ is the gap smallest relative to $b^{-10}$?

*Hint.* The sum is $1 + 3 b^{-12} + b^{-24}$, so the gap is $b^{-10} - 3b^{-12} - b^{-24}$. Divide by $b^{-10}$ to get $1 - 3 b^{-2} - b^{-14}$. This is increasing in $b$, so $b = 2$ gives the smallest ratio, about $0.25$.

## Notes and references

The sizes $\rho$, $s$ and $b$ come from [the data and their sizes](/chapter/data-and-sizes/). The conventions of this volume, with the threshold $10^8 \leq \varrho$, are in [the plan of Theorem B](/chapter/theorem-b-plan/#conventions-that-change-the-meaning). The general machine of floors, gauges, depth and shells is in [the chapter on frames](/chapter/local-frames/). The Bessel functions, cut pairs and the Schur bounds are in [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/). Haar measure and its uniqueness up to a positive factor are in G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 2.2.

The model case of Section 1 uses polar coordinates on $\mathbb C^{s+1}$ and the series of the exponential function. The bottom form uses the Cauchy-Schwarz and Minkowski inequalities in $L^2$.

Three points of the source were found while the chapter was written. First, the docstring of the bound of the forms writes the factor $(\pi/\|y\|)^{2(k-5)}$, and the Lean statement writes $(\operatorname{kernelBound}/\operatorname{mod}(y))^{|\mathrm{Free}|}$. At $\mathbb C$ the two are the same number. Second, RealBandLimits.lean imports `Lib.Cohomology.Etale.Basic`, which the file does not use. Third, the three files of this chapter import Bessel/Basic.lean, which imports the sieve system of [the chapter on the main term](/chapter/main-term/). Section 1 states the sieve system in full for this reason.

The numerical constants, such as $10^9 n^4$, $2000 n^9$ and $9999 n$, follow the source. They are not optimal. The proofs need only that they are large enough for the comparisons of exponents.

Status: drafted by a model from the Lean source at pin 72fead1 and the research notes. The chapter states what the source states. It does not claim that the source proof is correct, and it does not claim that the Generalized Riemann Hypothesis is proved.
