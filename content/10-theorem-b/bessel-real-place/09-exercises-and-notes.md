---
title: Exercises
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/GramSection.lean
  - New/Spanning/Bessel/OpenCellBound.lean
  - New/Spanning/Bessel/FillingData.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $Z$ be an invertible complex $(\varrho + 1) \times (\varrho + 1)$ matrix, $D_\varrho(Z)$ its leading principal minor of order $\varrho$ and $\xi(Z)$ the last diagonal entry of $Z^{-1}$. Show that $\xi(Z) = D_\varrho(Z)/\det Z$ and that $\mathsf g(Z) = |\det Z|^2(1 - |\xi(Z)|^2)$. Deduce that $Z$ lies in the open cell $\Omega$ if and only if $\mathsf g(Z) > 0$, also for $Z$ not invertible ([Lemma](/decl/New.RealPlace.mem_openCell_iff/)).

*Hint.* Use Cramer's rule for the entry $(\varrho, \varrho)$ of $Z^{-1}$. For $\det Z = 0$, show that $\mathsf g(Z) = -|D_\varrho(Z)|^2 \leq 0$.

**Exercise 2.** Take $\varrho = 0$. Then $Z$ is a number $z = h(z_0, yz_0)$ and the empty minor is $1$. Compute $\mathsf g$, $\xi$, $\nu$ and $\Omega$. Show that $Z$ is bounded in the cell by $P \geq 1$ if and only if $|z| \leq P$ and $|z|^2 - 1 \geq |z|^2/P^2$.

*Hint.* $\mathsf g(z) = |z|^2 - 1$, $\xi = 1/z$, and $\Omega = \{|z| > 1\}$. The bound $\|Z^{-1}\| \leq P$ follows from $|z| > 1$.

**Exercise 3.** Show that $\mathsf g(Z^*) = \mathsf g(Z)$. Deduce that $\gamma$ and $\gamma^{-1}$ have the same Gram discriminant, which the proof of the theorem on one pairing uses.

*Hint.* Leading principal minors commute with the conjugate transpose, and $\det Z^* = \overline{\det Z}$. For the second part use $Z(\gamma^{-1}) = Z(\gamma)^*$, which holds because $\gamma$ is an isometry for $h$.

**Exercise 4.** Let $M \geq 1$, $n \geq 1$, $M_0 = M^{9n}$ and $P = (M_0^5)^n$. Show that $P^{2000n^2}M_0^5(M P^{40})^{2n^2} = M^{93600n^4 + 2n^2 + 45n}$ and that this is at most $M^{10^5n^4}$.

*Hint.* $P = M^{45n^2}$. For the inequality, $2n^2 + 45n \leq 47n^4$.

**Exercise 5.** Let $k \leq r$ and let $b \geq \pi$ be such that $(2\varrho + 1)k \leq r^2$ and $\operatorname{vol}U(k)/\operatorname{vol}U(r) \leq (b^r)^r$. Show that $\Theta \leq b^{2r^2}$ ([Lemma](/decl/New.Data.scaledVolumeRatio_le/)).

*Hint.* $\Theta = \pi^{(2\varrho+1)k}\operatorname{vol}U(k)/\operatorname{vol}U(r)$, and $\pi^{(2\varrho+1)k} \leq b^{r^2}$.

**Exercise 6.** Fix $\deg > 0$, $\rho \geq 1$, $d > 0$ and $k \geq 1$. Show that $\operatorname{pb}$ decreases as $\mathsf g$ grows on $\mathsf g > 0$. Then compute the value that Lean gives to $\operatorname{pb}$ at $\mathsf g = 0$, and explain why the open cell bound has the hypothesis $\mathsf g > 0$.

*Hint.* Both factors are positive and decreasing in $\mathsf g$. In Lean $x/0 = 0$ and $0^m = 0$ for $m > 0$, so the junk value is $0$, and item 2 of the open cell bound would force $\nu(G_1) = 0$.

**Exercise 7.** With $\operatorname{vol}U(j) = \prod_{i < j}\sigma(i + 1)$ and $\sigma(m) = 2\pi^m/(m - 1)!$, show that $c_G > 0$ in general, and that $c_G = 1/\pi$ for $\varrho = 0$ and $k = 1$.

*Hint.* Here $r = 2$, $\operatorname{vol}U(1) = 2\pi$, $\operatorname{vol}U(2) = 4\pi^3$ and $\sigma(1) = 2\pi$. Positivity is `New.Shape.openCellConst_pos`.

## Notes and references

The model case in rank one is the Fourier coefficient formula of H. Petersson, *Über die Entwicklungskoeffizienten der automorphen Formen*, Acta Mathematica 58 (1932), with the $J$-Bessel function. For the Bessel function $J_\nu$ see NIST Digital Library of Mathematical Functions, §10.22, on integrals. The formal degree of a discrete series as a polynomial in the parameter is due to Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Mathematica 116 (1966). The mean value inequality of [Section 7](/chapter/bessel-real-place/#the-open-cell-bound) compares fibre measures of a Gram map; the source cites C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Annals of Mathematics 36 (1935), for such measures.

The source also cites E. M. Baruch on Bessel distributions on the open cell (2001 to 2004) and Comtat et al., *Effective Kuznetsov trace formula for GSp(4)* (2025). We give these as the source gives them and have not compared them with the chapter.

The stationary point, the average over the fixer, the cut at $b^{6n+2}$, the Schur bound with the words of length $2n^2$ and the exponents $550n^2$, $2000n^2$ and $10^5n^4$ follow the source. They are not optimized. In the case $\varrho = 0$ of Exercise 2, the open cell is the set $|z| > 1$, and the bound of the open cell grows like a power of $1/(|z|^2 - 1)$ as $z$ tends to the unit circle. The local bounds come from [the chapter on real densities](/chapter/real-densities/), and the sieve that uses them is in [the chapter on the main term](/chapter/main-term/).

The statements in this chapter are those of Lean. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument proves Theorem B in the sense of a refereed proof, and it does not claim that the Generalized Riemann Hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
