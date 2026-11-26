---
title: Exercises and notes
lean:
  - New/Spanning/MainTerm/SieveSystem.lean
  - New/Spanning/MainTerm/KloostermanSum.lean
  - New/Spanning/MainTerm/EnergyEstimate.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

1. *The large sieve.* Let $F(t) = (\sin(\pi\delta t)/(\pi\delta t))^2$ for $\delta > 0$, with $\hat F$ the triangle of height $1/\delta$ on $(-\delta, \delta)$. Show that $\int_0^{1/2}|\sum_i a_ie(x_it)|^2\,dt \leq c\,\delta^{-1}\sum_i|a_i|^2$ for $\delta$-spaced points $x_i$ and an absolute constant $c$. *Hint.* Scale $t$ so that $F \geq 4/\pi^2$ on the range, and follow the [model case](/chapter/main-term/#what-the-chapter-proves).

2. *Products of systems.* Let $J$ and $J'$ be sieve systems with bottom bounds $E$ and $E'$. Show that the bottom bound of the product is $EE'$ and that the decay of a product at a frequency $(\xi, \xi')$ with $\xi \neq 0$ is at most $\beta(\xi)$ times the norm of the other form. *Hint.* Use the [product of sieve systems](/chapter/main-term/#sieve-systems) and the bound $\|J'_i\| \leq \Lambda\Lambda'$.

3. *Classical Kloosterman sums.* Let $G = \mathrm{GL}_2(\mathbb Q_p)$, $\mathsf U$ the upper unipotent group, $\chi(u(x)) = \psi(x)$, $K(p^0) = \mathrm{GL}_2(\mathbb Z_p)$. For $x = \begin{pmatrix}0 & -1/c\\ c & 0\end{pmatrix}$ with $c = p^m$, $m \geq 1$, and $s = 1$, show that the [Kloosterman sum](/chapter/main-term/#kloosterman-sums-and-unfolding) is $\sum_{d \in (\mathbb Z/c)^\times}\psi((d + \bar d)/c)$. *Hint.* Solve $u(a)^{-1}xu(a') \in K$ by the Bruhat decomposition.

4. *Integrals over cosets.* Take $G = \mathbb R$ with the Lebesgue measure, $J = G$ and $f = 1$ in the [lemma on integrals over cosets](/chapter/main-term/#kloosterman-sums-and-unfolding). Show that the textbook identity fails, since the left side is $\infty$ and $\mu(J)$ is $\infty$. Show that both sides of the Lean statement are $0$. *Hint.* The Lean value of $\mu(J)$ as a real number is $0$ when $\mu(J) = \infty$, and the Bochner integral of a function that is not integrable is $0$.

5. *The fixed line.* Let $V = \mathbb F_q^r$ with a nondegenerate Hermitian form and $D \neq 0$. Show that the index of the stabilizer of $D$ in the unitary group is the number of nonzero vectors of the norm of $D$, and compare with $p^r - 1$ in [one place](/chapter/main-term/#fixed-lines-and-the-finite-system). *Hint.* The unitary group acts transitively on the nonzero vectors of a fixed norm by Witt's theorem.

6. *The constant $1 + b^{-4}$.* Show that $(1 + b^{-6})^2(1 + b^{-9})(1 + b^{-10}) \leq 1 + b^{-4}$ for $b \geq 2$. *Hint.* Expand and bound each cross term by $b^{-6}$; see [the sieve constant](/chapter/main-term/#the-energy-estimate).

### Notes and references

**What the source states.** The chapter follows the files New/Spanning/MainTerm/*.lean and New/Spanning/Frames/FixedLines.lean of the source, edition `grh/`, at the pinned commit. The source claims the theorem on the main term with no hypothesis beyond admissibility. Lean accepts it, if the reported checks hold. This chapter does not claim that the proof is correct, and the theorem is one step of the plan of [Theorem B](/chapter/theorem-b-plan/), not a proof of GRH.

**Sizes.** The filling datum asks $1000(2\varrho + 2) \leq k$, the sieve asks $10^5 \leq \varrho$, and the real places ask $10^8 \leq \varrho$. The second and third are finding F-090 of [the register of findings](/chapter/register-of-findings/#hypotheses-and-sizes): the larger bound implies the smaller one, so no case is lost. The exponents $270n^2$, $2403n^9$ and $6k$ are not optimized.

**Reading order.** Sections 2 to 4 do not use the data at $T$, and they can be read as a chapter on one-sided sieves. Sections 5 to 8 do not use the sieve. Section 9 is the only place where the two parts meet. A reader who wants only the shape of the argument can read the sketch of Section 1 and then Section 9.

**Junk values.** Sums are Lean `tsum`s and integrals are Bochner integrals. Both are $0$ when the family is not summable or the function is not integrable. In this chapter every such sum is either finite or a sum of nonnegative terms in $[0, \infty]$, and the remarks of each section say where a junk value could enter.

**Imports.** No file of the chapter imports a file of a later chapter of the volume. The files import [the remaining terms](/chapter/remaining-terms/), [Poincaré series and unfolding](/chapter/poincare-series/) and [the anatomy of a term](/chapter/anatomy-of-a-term/), which come earlier. Conversely, Bessel/Basic.lean of [Bessel functions at a real place](/chapter/bessel-real-place/) imports SieveSystem.lean of this chapter.

**Literature.** Kloosterman sums as local orbital integrals and the normal forms for the Bessel double cosets go back to the relative trace formula: H. Jacquet and Y. Ye, *Germs of Kloosterman integrals for GL(3)*, 1999; H. Jacquet, *Smooth transfer of Kloosterman integrals*, 2003, and *Kloosterman identities over a quadratic extension*, 2004; Y. Liu, *Relative trace formulae toward Bessel and Fourier-Jacobi periods*, 2014. Siegel's formula is from C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, 1935. Large sieves for Kloosterman sums with a loss of a constant or of $X^\varepsilon$ are in J.-M. Deshouillers and H. Iwaniec, *Kloosterman sums and Fourier coefficients of cusp forms*, 1982, and V. Blomer and J. Buttcane, *Global decomposition of GL(3) Kloosterman sums and the spectral large sieve*, 2015. The source states that the one-sided sieve with a constant close to $1$ is its own step.
